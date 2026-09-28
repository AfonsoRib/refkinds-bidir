{-# LANGUAGE OverloadedStrings #-}

-- | Lower named surface syntax into the locally nameless core.
module Desugar
  ( lowerType
  , lowerKind
  , lowerPredicate
  , lowerExpr
  ) where

import qualified Types as T

lowerType :: T.SType -> T.Type
lowerType = lowerTypeWith []

lowerKind :: T.SKind -> T.Rkind
lowerKind = lowerKindWith []

lowerPredicate :: T.SPred -> T.Pred
lowerPredicate = lowerPredicateWith [] Nothing

lowerExpr :: T.SExpr -> T.Expr
lowerExpr = lowerExprWith [] []

lowerTypeWith :: [T.Identifier] -> T.SType -> T.Type
lowerTypeWith typeNames surface = case surface of
  T.STUnit -> T.TUnit
  T.STInt -> T.TInt
  T.STBool -> T.TBool
  T.STString -> T.TString
  T.STTrue -> T.TTrue
  T.STFalse -> T.TFalse
  T.STLabel label -> T.TLabel label
  T.STRecNil -> T.TRecNil
  T.STRecCons label field rest -> T.TRecCons (go label) (go field) (go rest)
  T.STArrow domain codomain -> T.TArrow (go domain) (go codomain)
  T.STVar name -> maybe (T.TVar (T.typeName name)) T.TBound
    (bindingIndex name typeNames)
  T.STLambda binder body ->
    T.TLambda binder (lowerTypeWith (binder : typeNames) body)
  T.STApp function argument -> T.TApp (go function) (go argument)
  T.STAnn ty kind -> T.TAnn (go ty) (lowerKindWith typeNames kind)
  T.STForall binder domain body -> T.TForall binder
    (lowerKindWith typeNames domain) (lowerTypeWith (binder : typeNames) body)
  T.STLet (T.SDecl binder definition) body ->
    T.TLet (T.Decl binder (go definition))
      (lowerTypeWith (binder : typeNames) body)
  T.STRec binder definition body -> T.TRec binder
    (lowerTypeWith (binder : typeNames) definition)
    (lowerTypeWith (binder : typeNames) body)
  T.STIf predicate yes no -> T.TIf (go predicate) (go yes) (go no)
  T.STEq left right -> binary T.BEq left right
  T.STNot predicate -> unary T.BNot predicate
  T.STHead record -> unary T.BHead record
  T.STHeadLabel record -> unary T.BHeadLabel record
  T.STTail record -> unary T.BTail record
  T.STDom function -> unary T.BDom function
  T.STImg function -> unary T.BImg function
  T.STRef element -> T.TRef (go element)
  T.STRefOf reference -> unary T.BRefOf reference
  T.STCol element -> T.TCol (go element)
  T.STColOf collection -> unary T.BColOf collection
  T.STConcat left right -> binary T.BConcat left right
  T.STEmpty record -> unary T.BEmpty record
  T.STOr left right -> binary T.BOr left right
  T.STAnd left right -> binary T.BAnd left right
  T.STIsRec record -> unary T.BIsRec record
  where
    go = lowerTypeWith typeNames
    unary operation operand = T.unaryTypeOp operation (go operand)
    binary operation left right = T.binaryTypeOp operation (go left) (go right)

lowerKindWith :: [T.Identifier] -> T.SKind -> T.Rkind
lowerKindWith typeNames surface = case surface of
  T.SKPlain base -> T.bTrue (lowerBaseKindWith typeNames base)
  T.SKBase base (T.SRefined binder predicate) ->
    T.KBase (lowerBaseKindWith typeNames base)
      (T.refinement binder
        (lowerPredicateWith typeNames (Just binder) predicate))
  T.SKPi binder domain codomain -> T.KPi binder
    (lowerKindWith typeNames domain)
    (lowerKindWith (binder : typeNames) codomain)
  T.SKGen binder domain codomain -> T.KGen binder
    (lowerKindWith typeNames domain)
    (lowerKindWith (binder : typeNames) codomain)

lowerBaseKindWith :: [T.Identifier] -> T.SBaseKind -> T.BaseKind
lowerBaseKindWith _ base = case base of
  T.SBKType -> T.BKType
  T.SBKBool -> T.BKBool
  T.SBKLabel -> T.BKLabel
  T.SBKRec -> T.BKRec
  T.SBKFun -> T.BKFun
  T.SBKRef -> T.BKRef
  T.SBKCol -> T.BKCol

lowerPredicateWith
  :: [T.Identifier] -> Maybe T.Identifier -> T.SPred -> T.Pred
lowerPredicateWith typeNames refinementName surface = case surface of
  T.SPVar name
    | Just name == refinementName -> T.PBound 0
    | otherwise -> maybe (T.PVar (T.typeName name)) T.PTypeBound
        (bindingIndex name typeNames)
  T.SPLabel name -> T.PLabel name
  T.SPUnit -> T.PUnit
  T.SPInt -> T.PInt
  T.SPBool -> T.PBool
  T.SPString -> T.PString
  T.SPTrue -> T.PTrue
  T.SPFalse -> T.PFalse
  T.SPRecNil -> T.PRecNil
  T.SPRecCons label field rest -> T.PRecCons (go label) (go field) (go rest)
  T.SPArrow domain codomain -> T.PArrow (go domain) (go codomain)
  T.SPRef element -> T.PRef (go element)
  T.SPCol element -> T.PCol (go element)
  T.SPInterp1 operation operand -> T.PInterp1 operation (go operand)
  T.SPInterp2 operation left right -> T.PInterp2 operation (go left) (go right)
  T.SPLabSet record -> T.PLabSet (go record)
  T.SPMember label labels -> T.PMember (go label) (go labels)
  T.SPSubset left right -> T.PSubset (go left) (go right)
  T.SPApart left right -> T.PApart (go left) (go right)
  where
    go = lowerPredicateWith typeNames refinementName

lowerExprWith :: [T.Identifier] -> [T.Identifier] -> T.SExpr -> T.Expr
lowerExprWith termNames typeNames surface = case surface of
  T.SEUnit -> T.EUnit
  T.SEInteger value -> T.EInteger value
  T.SEBoolean value -> T.EBoolean value
  T.SENot expression -> T.ENot (go expression)
  T.SEString value -> T.EString value
  T.SEStringConcat left right -> T.EStringConcat (go left) (go right)
  T.SEVar name -> maybe (T.EVar (T.termName name)) T.EBound
    (bindingIndex name termNames)
  T.SEAnn expression ty -> T.EAnn (go expression) (lowerTypeWith typeNames ty)
  T.SELambda binder body ->
    T.ELambda binder (lowerExprWith (binder : termNames) typeNames body)
  T.SEApp function argument -> T.EApp (go function) (go argument)
  T.SELet binder definition body -> T.ELet binder (go definition)
    (lowerExprWith (binder : termNames) typeNames body)
  T.SELetRec binder ty definition body ->
    T.ELetRec binder (lowerTypeWith typeNames ty)
      (lowerExprWith (binder : termNames) typeNames definition)
      (lowerExprWith (binder : termNames) typeNames body)
  T.SELabel label -> T.ELabel label
  T.SERecordNil -> T.ERecordNil
  T.SERecordCons label field rest -> T.ERecordCons label (go field) (go rest)
  T.SEHead expression -> T.EHead (go expression)
  T.SEHeadLabel expression -> T.EHeadLabel (go expression)
  T.SETail expression -> T.ETail (go expression)
  T.SEConcat left right -> T.EConcat (go left) (go right)
  T.SERef expression -> T.ERef (go expression)
  T.SERefOf expression -> T.ERefOf (go expression)
  T.SEAssign reference value -> T.EAssign (go reference) (go value)
  T.SEIf condition yes no -> T.EIf (go condition) (go yes) (go no)
  T.SETLambda binder body ->
    T.ETLambda binder (lowerExprWith termNames (binder : typeNames) body)
  T.SETApp expression ty -> T.ETApp (go expression) (lowerTypeWith typeNames ty)
  where
    go = lowerExprWith termNames typeNames

bindingIndex :: Eq a => a -> [a] -> Maybe Int
bindingIndex target = seek 0
  where
    seek _ [] = Nothing
    seek index (name : rest)
      | target == name = Just index
      | otherwise = seek (index + 1) rest
