module Support.AstInvariants
  ( validateTypeAst
  , validateKindAst
  , validateExprAst
  , validateContextAst
  , validateAnfType
  , validateAnfExpr
  ) where

import Context hiding (implicationConstraint)
import Types

-- These checks are test instrumentation. Production code relies on surface
-- lowering and ANF elaboration to construct well-scoped core syntax.
validateTypeAst :: Type -> Either String ()
validateTypeAst = checkType 0 0

validateKindAst :: Rkind -> Either String ()
validateKindAst = checkKind 0 0

validateExprAst :: Expr -> Either String ()
validateExprAst = go 0 0
  where
    go expressionDepth typeDepth expression = case expression of
      EBound index -> checkIndex "term" expressionDepth index
      ELambda _ body -> go (expressionDepth + 1) typeDepth body
      ELet _ definition body ->
        go expressionDepth typeDepth definition >>
        go (expressionDepth + 1) typeDepth body
      ELetRec _ declared definition body ->
        checkType typeDepth 0 declared >>
        go (expressionDepth + 1) typeDepth definition >>
        go (expressionDepth + 1) typeDepth body
      ETLambda _ body -> go expressionDepth (typeDepth + 1) body
      ETApp body ty -> go expressionDepth typeDepth body >> checkType typeDepth 0 ty
      EAnn body ty -> go expressionDepth typeDepth body >> checkType typeDepth 0 ty
      EIf condition yes no -> mapM_ (go expressionDepth typeDepth) [condition, yes, no]
      ENot value -> go expressionDepth typeDepth value
      EStringConcat left right -> both expressionDepth typeDepth left right
      EApp function argument -> both expressionDepth typeDepth function argument
      ERecordCons _ field tailExpression -> both expressionDepth typeDepth field tailExpression
      EHead value -> go expressionDepth typeDepth value
      EHeadLabel value -> go expressionDepth typeDepth value
      ETail value -> go expressionDepth typeDepth value
      EConcat left right -> both expressionDepth typeDepth left right
      ERef value -> go expressionDepth typeDepth value
      ERefOf value -> go expressionDepth typeDepth value
      EAssign reference value -> both expressionDepth typeDepth reference value
      _ -> pure ()
    both expressionDepth typeDepth left right =
      go expressionDepth typeDepth left >> go expressionDepth typeDepth right

validateContextAst :: Context -> Either String ()
validateContextAst context = do
  mapM_ (validateKindAst . entryKind . snd) (ctxEnv context)
  mapM_ (validateTypeAst . snd) (ctxTermEnv context)

validateAnfType :: Type -> Either String ()
validateAnfType ty = validateTypeAst ty >>
  if isAnfType ty then pure () else Left "type is not in ANF"

validateAnfExpr :: Expr -> Either String ()
validateAnfExpr expression = validateExprAst expression >>
  if isAnfExpr expression then pure () else Left "expression is not in ANF"

-- Keep the complete ANF grammar here, independently of the production
-- elaborator, so tests detect missing or incorrectly classified operands.
isAnfType :: Type -> Bool
isAnfType ty
  | isTypeAtom ty = True
  | Just (operation, arguments) <- saturatedTypeOpView ty
  , operation `elem` [BAnd, BOr] =
      all isAnfType arguments
isAnfType (TApp function argument) = isTypeAtom function && isTypeVariable argument
isAnfType (TAnn value _) = isAnfType value
isAnfType (TLet (Decl _ definition) body) = all isAnfType [definition, body]
isAnfType (TRec _ definition body) = all isAnfType [definition, body]
isAnfType (TIf condition yes no) = all isAnfType [condition, yes, no]
isAnfType _ = False

isTypeAtom :: Type -> Bool
isTypeAtom ty = case ty of
  TUnit -> True
  TInt -> True
  TBool -> True
  TString -> True
  TTrue -> True
  TFalse -> True
  TLabel {} -> True
  TRecNil -> True
  TVar {} -> True
  TBound {} -> True
  TRecCons label field rest -> all isTypeAtom [label, field, rest]
  TArrow domain image -> all isTypeAtom [domain, image]
  TRef element -> isTypeAtom element
  TCol element -> isTypeAtom element
  TLambda _ body -> isAnfType body
  TAnn value _ -> isTypeAtom value
  TForall _ _ body -> isAnfType body
  PBIn {} -> True
  _ -> False

isTypeVariable :: Type -> Bool
isTypeVariable TVar {} = True
isTypeVariable TBound {} = True
isTypeVariable _ = False

isAnfExpr :: Expr -> Bool
isAnfExpr expression
  | isExprAtom expression = True
isAnfExpr (EApp function argument) = isExprAtom function && isTermVariable argument
isAnfExpr (ENot value) = isExprAtom value
isAnfExpr (EStringConcat left right) = all isExprAtom [left, right]
isAnfExpr (ETApp value ty) = isExprAtom value && isAnfType ty
isAnfExpr (ELet _ definition body) = all isAnfExpr [definition, body]
isAnfExpr (ELetRec _ ty definition body) =
  isAnfType ty && all isAnfExpr [definition, body]
isAnfExpr (ERecordCons _ field rest) = all isExprAtom [field, rest]
isAnfExpr (EConcat left right) = all isExprAtom [left, right]
isAnfExpr (EHead value) = isExprAtom value
isAnfExpr (EHeadLabel value) = isExprAtom value
isAnfExpr (ETail value) = isExprAtom value
isAnfExpr (ERef value) = isExprAtom value
isAnfExpr (ERefOf value) = isExprAtom value
isAnfExpr (EAssign reference value) = all isExprAtom [reference, value]
isAnfExpr (EIf condition yes no) = isExprAtom condition && all isAnfExpr [yes, no]
isAnfExpr (EAnn value ty) = isAnfExpr value && isAnfType ty
isAnfExpr _ = False

isExprAtom :: Expr -> Bool
isExprAtom expression = case expression of
  EUnit -> True
  EInteger {} -> True
  EBoolean {} -> True
  EString {} -> True
  EVar {} -> True
  EBound {} -> True
  ELabel {} -> True
  ERecordNil -> True
  ELambda _ body -> isAnfExpr body
  ETLambda _ body -> isAnfExpr body
  EAnn body ty -> isExprAtom body && isAnfType ty
  _ -> False

isTermVariable :: Expr -> Bool
isTermVariable EVar {} = True
isTermVariable EBound {} = True
isTermVariable _ = False

checkType :: Int -> Int -> Type -> Either String ()
checkType typeDepth refinementDepth ty = case ty of
  TBound index -> checkIndex "type" typeDepth index
  TLambda _ body -> recur (typeDepth + 1) refinementDepth body
  TForall _ domain body -> checkKind typeDepth refinementDepth domain >> recur (typeDepth + 1) refinementDepth body
  TAnn value kind -> recur typeDepth refinementDepth value >> checkKind typeDepth refinementDepth kind
  TLet (Decl _ definition) body ->
    recur typeDepth refinementDepth definition >> recur (typeDepth + 1) refinementDepth body
  TRec _ definition body ->
    recur (typeDepth + 1) refinementDepth definition >>
    recur (typeDepth + 1) refinementDepth body
  _ -> mapM_ (recur typeDepth refinementDepth) (typeChildren ty)
  where
    recur = checkType

checkKind :: Int -> Int -> Rkind -> Either String ()
checkKind typeDepth refinementDepth kind = case kind of
  KBase base (Refined _ predicate) -> do
    checkPred typeDepth (refinementDepth + 1) predicate
  KPi _ domain codomain ->
    checkKind typeDepth refinementDepth domain >>
    checkKind (typeDepth + 1) refinementDepth codomain
  KGen _ domain codomain ->
    checkKind typeDepth refinementDepth domain >>
    checkKind (typeDepth + 1) refinementDepth codomain

checkIndex :: String -> Int -> Int -> Either String ()
checkIndex namespace depth index
  | index < 0 || index >= depth =
      Left ("exposed " ++ namespace ++ " index " ++ show index)
  | otherwise = pure ()

checkPred :: Int -> Int -> Pred -> Either String ()
checkPred td rd p = case p of
  PBound i -> checkIndex "refinement" rd i
  PTypeBound i -> checkIndex "type" td i
  _ -> mapM_ (checkPred td rd) (predChildren p)
