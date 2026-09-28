{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RoleAnnotations #-}

-- | Syntax and alpha-equivalence for the locally nameless core.
module Types where

import qualified Data.Aeson as Aeson
import qualified Data.Functor.Const as Const
import qualified Data.Functor.Identity as Identity
import qualified Data.List as List
import qualified Data.String as String
import qualified GHC.Generics as Generics

-- -----------------------------------------------------------------------------
-- Names and namespaces
-- -----------------------------------------------------------------------------

data TypeNamespace
data TermNamespace
data RefinementNamespace

-- Nominal roles prevent coercing names across namespaces.
type role Name nominal
newtype Name namespace = Name String deriving (Eq, Ord, Generics.Generic)
type TypeName = Name TypeNamespace
type TermName = Name TermNamespace
type RefName = Name RefinementNamespace

instance Show (Name namespace) where show = show . nameText
instance String.IsString (Name namespace) where fromString = Name
instance Aeson.ToJSON (Name namespace) where
  toJSON = Aeson.toJSON . nameText
instance Aeson.FromJSON (Name namespace) where
  parseJSON value = Name <$> Aeson.parseJSON value

nameText :: Name namespace -> String
nameText (Name text) = text

typeName :: String -> TypeName
typeName = Name
termName :: String -> TermName
termName = Name
refName :: String -> RefName
refName = Name

data LogicName = TypeSymbol TypeName | RefSymbol RefName
  deriving (Eq, Ord, Generics.Generic)
instance Show LogicName where show = show . logicNameText
instance String.IsString LogicName where fromString = TypeSymbol . typeName
instance Aeson.ToJSON LogicName where
  toJSON (TypeSymbol n) = Aeson.toJSON ("type" :: String, nameText n)
  toJSON (RefSymbol n) = Aeson.toJSON ("refinement" :: String, nameText n)
instance Aeson.FromJSON LogicName where
  parseJSON value = do
    (namespace, text) <- Aeson.parseJSON value
    case namespace :: String of
      "type" -> pure (TypeSymbol (typeName text))
      "refinement" -> pure (RefSymbol (refName text))
      _ -> fail "unknown logical namespace"
logicNameText :: LogicName -> String
logicNameText (TypeSymbol n) = nameText n
logicNameText (RefSymbol n) = nameText n

-- -----------------------------------------------------------------------------
-- Core types, kinds, and predicates
-- -----------------------------------------------------------------------------

type Identifier = String

data Decl = Decl Identifier Type
  deriving (Eq, Ord, Show, Generics.Generic, Aeson.ToJSON, Aeson.FromJSON)

data BaseKind
  = BKType
  | BKBool
  | BKLabel
  | BKRec
  | BKFun
  | BKRef
  | BKCol
  deriving (Eq, Ord, Show, Generics.Generic, Aeson.ToJSON, Aeson.FromJSON)

-- Refinements contain only the independent first-order predicate tree.
data Refinement = Refined Identifier Pred
  deriving (Eq, Ord, Show, Generics.Generic, Aeson.ToJSON, Aeson.FromJSON)

data Rkind
  = KBase BaseKind Refinement
  | KPi Identifier Rkind Rkind
  | KGen Identifier Rkind Rkind
  deriving (Eq, Ord, Show, Generics.Generic, Aeson.ToJSON, Aeson.FromJSON)

data TypeOp
  = BEq
  | BNot
  | BHead
  | BHeadLabel
  | BTail
  | BDom
  | BImg
  | BRefOf
  | BColOf
  | BConcat
  | BEmpty
  | BOr
  | BAnd
  | BIsRec
  deriving (Eq, Ord, Show, Generics.Generic, Aeson.ToJSON, Aeson.FromJSON)

typeOpArity :: TypeOp -> Int
typeOpArity operation = case operation of
  BEq -> 2
  BNot -> 1
  BHead -> 1
  BHeadLabel -> 1
  BTail -> 1
  BDom -> 1
  BImg -> 1
  BRefOf -> 1
  BColOf -> 1
  BConcat -> 2
  BEmpty -> 1
  BOr -> 2
  BAnd -> 2
  BIsRec -> 1

-- Predicates are first-order syntax, with independent type/refinement indices.
data Pred
  = PVar TypeName | PRefVar RefName | PTypeBound Int | PBound Int
  | PLabel Identifier
  | PUnit
  | PInt
  | PBool
  | PString
  | PTrue
  | PFalse
  | PRecNil
  | PRecCons Pred Pred Pred
  | PArrow Pred Pred
  | PRef Pred
  | PCol Pred
  | PInterp1 TypeOp Pred
  | PInterp2 TypeOp Pred Pred
  | PLabSet Pred
  | PMember Pred Pred
  | PSubset Pred Pred
  | PApart Pred Pred
  deriving (Eq, Ord, Show, Generics.Generic, Aeson.ToJSON, Aeson.FromJSON)

refinement :: Identifier -> Pred -> Refinement
refinement = Refined

-- Structural conversion only: this boundary never evaluates executable code.
typeToPred :: Type -> Pred
typeToPred ty = case typeToPredMaybe ty of
  Just predicate -> predicate
  Nothing -> error
    ("predicate encoding error: unsupported type computation: " ++ show ty)

typeToPredMaybe :: Type -> Maybe Pred
typeToPredMaybe ty
  | Just (operation, operands) <- saturatedTypeOpView ty =
      case operands of
        [operand] -> PInterp1 operation <$> typeToPredMaybe operand
        [left, right] ->
          PInterp2 operation <$> typeToPredMaybe left <*> typeToPredMaybe right
        _ -> Nothing

typeToPredMaybe ty = case ty of
  TVar n -> Just (PVar n)
  TBound i -> Just (PTypeBound i)
  TLabel l -> Just (PLabel l)
  TAnn t _ -> typeToPredMaybe t
  TUnit -> Just PUnit
  TInt -> Just PInt
  TBool -> Just PBool
  TString -> Just PString
  TTrue -> Just PTrue
  TFalse -> Just PFalse
  TRecNil -> Just PRecNil
  TRecCons a b c ->
    PRecCons <$> typeToPredMaybe a <*> typeToPredMaybe b <*> typeToPredMaybe c
  TArrow a b -> PArrow <$> typeToPredMaybe a <*> typeToPredMaybe b
  TRef a -> PRef <$> typeToPredMaybe a
  TCol a -> PCol <$> typeToPredMaybe a
  _ -> Nothing

traversePredChildren :: Applicative f => (Pred -> f Pred) -> Pred -> f Pred
traversePredChildren f p = case p of
  PRecCons a b c -> PRecCons <$> f a <*> f b <*> f c
  PArrow a b -> PArrow <$> f a <*> f b
  PRef a -> PRef <$> f a
  PCol a -> PCol <$> f a
  PInterp1 operation operand -> PInterp1 operation <$> f operand
  PInterp2 operation left right -> PInterp2 operation <$> f left <*> f right
  PLabSet record -> PLabSet <$> f record
  PMember label labels -> PMember <$> f label <*> f labels
  PSubset left right -> PSubset <$> f left <*> f right
  PApart left right -> PApart <$> f left <*> f right
  atom -> pure atom

mapPredChildren :: (Pred -> Pred) -> Pred -> Pred
mapPredChildren f = Identity.runIdentity . traversePredChildren
  (Identity.Identity . f)

predChildren :: Pred -> [Pred]
predChildren = Const.getConst . traversePredChildren (Const.Const . (:[]))

foldMapPred :: Monoid m => (Pred -> m) -> Pred -> m
foldMapPred f p = f p <> foldMap (foldMapPred f) (predChildren p)

alphaEqPredicate :: Pred -> Pred -> Bool
alphaEqPredicate = (==)

data Type
  = TUnit
  | TInt
  | TBool
  | TString
  | TTrue
  | TFalse
  | TLabel Identifier
  | TRecNil
  | TRecCons Type Type Type
  | TArrow Type Type
  | TRef Type
  | TCol Type
  | TVar TypeName
  | TBound Int
  | TLambda Identifier Type
  | TApp Type Type
  | TAnn Type Rkind
  | TForall Identifier Rkind Type
  | TLet Decl Type
  | TRec Identifier Type Type
  | TIf Type Type Type
  | PBIn TypeOp
  deriving (Eq, Ord, Show, Generics.Generic, Aeson.ToJSON, Aeson.FromJSON)

typeOpApp :: TypeOp -> [Type] -> Type
typeOpApp operation = foldl TApp (PBIn operation)

unaryTypeOp :: TypeOp -> Type -> Type
unaryTypeOp operation operand = typeOpApp operation [operand]

binaryTypeOp :: TypeOp -> Type -> Type -> Type
binaryTypeOp operation left right = typeOpApp operation [left, right]

unaryPredOp :: TypeOp -> Pred -> Pred
unaryPredOp = PInterp1

binaryPredOp :: TypeOp -> Pred -> Pred -> Pred
binaryPredOp = PInterp2

unarySurfacePredOp :: TypeOp -> SPred -> SPred
unarySurfacePredOp = SPInterp1

binarySurfacePredOp :: TypeOp -> SPred -> SPred -> SPred
binarySurfacePredOp = SPInterp2

typeOpView :: Type -> Maybe (TypeOp, [Type])
typeOpView = collect []
  where
    collect operands (TApp function argument) =
      collect (argument : operands) function
    collect operands (PBIn operation) = Just (operation, operands)
    collect _ _ = Nothing

saturatedTypeOpView :: Type -> Maybe (TypeOp, [Type])
saturatedTypeOpView ty = do
  result@(operation, operands) <- typeOpView ty
  if length operands == typeOpArity operation then Just result else Nothing

bTrue :: BaseKind -> Rkind
bTrue bk = KBase bk (refinement "v" PTrue)

baseSubkind :: BaseKind -> BaseKind -> Bool
baseSubkind k1 k2
  | k1 == k2 = True
  | otherwise = case (k1, k2) of
      (BKBool, BKType) -> True
      (BKLabel, BKType) -> True
      (BKRec, BKType) -> True
      (BKFun, BKType) -> True
      (BKRef, BKType) -> True
      (BKCol, BKType) -> True
      _ -> False

freshKindBinder :: [Identifier] -> Identifier -> Identifier
freshKindBinder used base
  | base `notElem` used = base
  | otherwise = head
      [cand | i <- [0 :: Integer ..], let cand = base ++ show i,
        cand `notElem` used]

-- Traversals
traverseTypeChildren :: Applicative f => (Type -> f Type) -> Type -> f Type
traverseTypeChildren f t = case t of
  TRecCons l ty r -> TRecCons <$> f l <*> f ty <*> f r
  TArrow d i -> TArrow <$> f d <*> f i
  TRef e -> TRef <$> f e
  TCol e -> TCol <$> f e
  TLambda b body -> TLambda <$> pure b <*> f body
  TApp fn arg -> TApp <$> f fn <*> f arg
  TAnn term k -> TAnn <$> f term <*> pure k
  TForall b k body -> TForall <$> pure b <*> pure k <*> f body
  TLet (Decl b d) body -> TLet <$> (Decl b <$> f d) <*> f body
  TRec b d body -> TRec <$> pure b <*> f d <*> f body
  TIf c whenT whenF -> TIf <$> f c <*> f whenT <*> f whenF
  _ -> pure t

mapTypeChildren :: (Type -> Type) -> Type -> Type
mapTypeChildren f = Identity.runIdentity . traverseTypeChildren
  (Identity.Identity . f)

typeChildren :: Type -> [Type]
typeChildren = Const.getConst . traverseTypeChildren (Const.Const . (:[]))

-- Expose the head constructor only; forall retains its own parameter domain.
stripAnnotations :: Type -> Type
stripAnnotations (TAnn t _) = stripAnnotations t
stripAnnotations t = t

-- The universal carries its own domain independently of outer annotations.
universalView :: Type -> Maybe (Identifier, Rkind, Type)
universalView (TForall hint domain body) = Just (hint, domain, body)
universalView (TAnn body _) = universalView body
universalView _ = Nothing

-- Type lambdas remain checking-only and still need their Pi contracts.
-- Universals carry their own domains and need no retained outer classifier.
retainKind :: Type -> Rkind -> Type
retainKind ty k = case k of
  KPi {} -> case ty of
    TAnn _ KPi {} -> ty
    _ -> TAnn ty k
  _ -> ty

-- Alpha-equivalence
alphaEq :: Type -> Type -> Bool
alphaEq = go [] []
  where
    go _ _ (TVar n1) (TVar n2) = n1 == n2
    go _ _ (TBound i1) (TBound i2) = i1 == i2
    go e1 e2 (TLambda _ t1) (TLambda _ t2) = go e1 e2 t1 t2
    go e1 e2 (TForall _ k1 t1) (TForall _ k2 t2) = alphaEqKind k1 k2 && go e1 e2 t1 t2
    go e1 e2 (TLet (Decl _ d1) t1) (TLet (Decl _ d2) t2) =
      go e1 e2 d1 d2 && go e1 e2 t1 t2
    go e1 e2 (TRec _ d1 t1) (TRec _ d2 t2) =
      go e1 e2 d1 d2 && go e1 e2 t1 t2
    go env1 env2 (TApp f1 a1) (TApp f2 a2) =
      go env1 env2 f1 f2 && go env1 env2 a1 a2
    go env1 env2 (TArrow d1 i1) (TArrow d2 i2) =
      go env1 env2 d1 d2 && go env1 env2 i1 i2
    go env1 env2 (TRef e1) (TRef e2) =
      go env1 env2 e1 e2
    go env1 env2 (TCol e1) (TCol e2) =
      go env1 env2 e1 e2
    go env1 env2 (TRecCons l1 t1 r1) (TRecCons l2 t2 r2) =
      go env1 env2 l1 l2 && go env1 env2 t1 t2 && go env1 env2 r1 r2
    go _ _ (PBIn operation1) (PBIn operation2) = operation1 == operation2
    go env1 env2 (TIf c1 t1 f1) (TIf c2 t2 f2) =
      go env1 env2 c1 c2 && go env1 env2 t1 t2 && go env1 env2 f1 f2
    go env1 env2 (TAnn t1 k1) (TAnn t2 k2) =
      go env1 env2 t1 t2 && alphaEqKind k1 k2
    go _ _ (TLabel l1) (TLabel l2) = l1 == l2
    go _ _ TUnit TUnit = True
    go _ _ TInt TInt = True
    go _ _ TBool TBool = True
    go _ _ TString TString = True
    go _ _ TTrue TTrue = True
    go _ _ TFalse TFalse = True
    go _ _ TRecNil TRecNil = True
    go _ _ _ _ = False

alphaEqKind :: Rkind -> Rkind -> Bool
alphaEqKind (KBase bk1 (Refined _ p1)) (KBase bk2 (Refined _ p2)) =
  bk1 == bk2 && alphaEqPredicate p1 p2
alphaEqKind (KPi _ d1 c1) (KPi _ d2 c2) =
  alphaEqKind d1 d2 && alphaEqKind c1 c2
alphaEqKind (KGen _ d1 c1) (KGen _ d2 c2) =
  alphaEqKind d1 d2 && alphaEqKind c1 c2
alphaEqKind _ _ = False

-- -----------------------------------------------------------------------------
-- Core terms
-- -----------------------------------------------------------------------------

data Expr
  = EUnit
  | EInteger !Int
  | EBoolean !Bool
  | ENot !Expr
  | EString !String
  | EStringConcat !Expr !Expr
  | EVar !TermName
  | EBound !Int
  | EAnn !Expr !Type
  | ELambda !Identifier !Expr
  | EApp !Expr !Expr
  | ELet !Identifier !Expr !Expr
  | ELetRec !Identifier !Type !Expr !Expr
  | ELabel !Identifier
  | ERecordNil
  | ERecordCons !Identifier !Expr !Expr
  | EHead !Expr
  | EHeadLabel !Expr
  | ETail !Expr
  | EConcat !Expr !Expr
  | ERef !Expr
  | ERefOf !Expr
  | EAssign !Expr !Expr
  | EIf !Expr !Expr !Expr
  | ETLambda !Identifier !Expr
  | ETApp !Expr !Type
  deriving (Eq, Ord, Show, Generics.Generic, Aeson.ToJSON, Aeson.FromJSON)

traverseExprChildren :: Applicative f => (Expr -> f Expr) -> Expr -> f Expr
traverseExprChildren f expression = case expression of
  ELambda binder body -> ELambda binder <$> f body
  ENot body -> ENot <$> f body
  EStringConcat left right -> EStringConcat <$> f left <*> f right
  EAnn body ty -> EAnn <$> f body <*> pure ty
  EApp function argument -> EApp <$> f function <*> f argument
  ELet binder definition body -> ELet binder <$> f definition <*> f body
  ELetRec binder ty definition body ->
    ELetRec binder ty <$> f definition <*> f body
  ERecordCons label field rest -> ERecordCons label <$> f field <*> f rest
  EHead body -> EHead <$> f body
  EHeadLabel body -> EHeadLabel <$> f body
  ETail body -> ETail <$> f body
  EConcat left right -> EConcat <$> f left <*> f right
  ERef body -> ERef <$> f body
  ERefOf body -> ERefOf <$> f body
  EAssign left right -> EAssign <$> f left <*> f right
  EIf condition ifTrue ifFalse -> EIf <$> f condition <*> f ifTrue <*> f ifFalse
  ETLambda binder body -> ETLambda binder <$> f body
  ETApp body ty -> ETApp <$> f body <*> pure ty
  _ -> pure expression

exprChildren :: Expr -> [Expr]
exprChildren = Const.getConst . traverseExprChildren (Const.Const . (:[]))

mapExprChildren :: (Expr -> Expr) -> Expr -> Expr
mapExprChildren f = Identity.runIdentity . traverseExprChildren
  (Identity.Identity . f)

alphaEqExpr :: Expr -> Expr -> Bool
alphaEqExpr = go [] []
  where
    go leftEnv rightEnv left right = case (left, right) of
      (EVar x, EVar y) -> x == y
      (EBound i, EBound j) -> i == j
      (ELambda x body1, ELambda y body2) -> bind x y body1 body2
      (ELet x d1 body1, ELet y d2 body2) ->
        go leftEnv rightEnv d1 d2 && bind x y body1 body2
      (ELetRec x t1 d1 body1, ELetRec y t2 d2 body2) ->
        alphaEq t1 t2 && bind x y d1 d2 && bind x y body1 body2
      (EAnn e1 t1, EAnn e2 t2) -> alphaEq t1 t2 && recurse e1 e2
      (ETLambda _ b1, ETLambda _ b2) -> recurse b1 b2
      (ETApp e1 t1, ETApp e2 t2) -> recurse e1 e2 && alphaEq t1 t2
      (EUnit, EUnit) -> True
      (EInteger x, EInteger y) -> x == y
      (EBoolean x, EBoolean y) -> x == y
      (EString x, EString y) -> x == y
      (ELabel x, ELabel y) -> x == y
      (ERecordNil, ERecordNil) -> True
      (ENot x, ENot y) -> recurse x y
      (EStringConcat a b, EStringConcat c d) -> recurse a c && recurse b d
      (EApp a b, EApp c d) -> recurse a c && recurse b d
      (ERecordCons l a b, ERecordCons r c d) -> l == r && recurse a c && recurse b d
      (EHead x, EHead y) -> recurse x y
      (EHeadLabel x, EHeadLabel y) -> recurse x y
      (ETail x, ETail y) -> recurse x y
      (EConcat a b, EConcat c d) -> recurse a c && recurse b d
      (ERef x, ERef y) -> recurse x y
      (ERefOf x, ERefOf y) -> recurse x y
      (EAssign a b, EAssign c d) -> recurse a c && recurse b d
      (EIf a b c, EIf d e f) -> recurse a d && recurse b e && recurse c f
      _ -> False
      where
        recurse = go leftEnv rightEnv
        bind _ _ body1 body2 = go leftEnv rightEnv body1 body2

-- -----------------------------------------------------------------------------
-- Named surface syntax
-- -----------------------------------------------------------------------------

data SDecl = SDecl Identifier SType
  deriving (Eq, Ord, Show, Generics.Generic, Aeson.ToJSON, Aeson.FromJSON)

data SBaseKind
  = SBKType
  | SBKBool
  | SBKLabel
  | SBKRec
  | SBKFun
  | SBKRef
  | SBKCol
  deriving (Eq, Ord, Show, Generics.Generic, Aeson.ToJSON, Aeson.FromJSON)

data SRefinement = SRefined Identifier SPred
  deriving (Eq, Ord, Show, Generics.Generic, Aeson.ToJSON, Aeson.FromJSON)

data SKind
  = SKPlain SBaseKind
  | SKBase SBaseKind SRefinement
  | SKPi Identifier SKind SKind
  | SKGen Identifier SKind SKind
  deriving (Eq, Ord, Show, Generics.Generic, Aeson.ToJSON, Aeson.FromJSON)

data SPred
  = SPVar Identifier | SPLabel Identifier
  | SPUnit
  | SPInt
  | SPBool
  | SPString
  | SPTrue
  | SPFalse
  | SPRecNil
  | SPRecCons SPred SPred SPred
  | SPArrow SPred SPred
  | SPRef SPred
  | SPCol SPred
  | SPInterp1 TypeOp SPred
  | SPInterp2 TypeOp SPred SPred
  | SPLabSet SPred
  | SPMember SPred SPred
  | SPSubset SPred SPred
  | SPApart SPred SPred
  deriving (Eq, Ord, Show, Generics.Generic, Aeson.ToJSON, Aeson.FromJSON)

-- Surface variables are deliberately all named.  Namespace resolution is
-- performed by Desugar while crossing into the locally nameless core.
data SType
  = STUnit
  | STInt
  | STBool
  | STString
  | STTrue
  | STFalse
  | STLabel Identifier
  | STRecNil
  | STRecCons SType SType SType
  | STArrow SType SType
  | STVar Identifier
  | STLambda Identifier SType
  | STApp SType SType
  | STAnn SType SKind
  | STForall Identifier SKind SType
  | STLet SDecl SType
  | STRec Identifier SType SType
  | STIf SType SType SType
  | STEq SType SType
  | STNot SType
  | STHead SType
  | STHeadLabel SType
  | STTail SType
  | STDom SType
  | STImg SType
  | STRef SType
  | STRefOf SType
  | STCol SType
  | STColOf SType
  | STConcat SType SType
  | STEmpty SType
  | STOr SType SType
  | STAnd SType SType
  | STIsRec SType
  deriving (Eq, Ord, Show, Generics.Generic, Aeson.ToJSON, Aeson.FromJSON)

data SExpr
  = SEUnit
  | SEInteger Int
  | SEBoolean Bool
  | SENot SExpr
  | SEString String
  | SEStringConcat SExpr SExpr
  | SEVar Identifier
  | SEAnn SExpr SType
  | SELambda Identifier SExpr
  | SEApp SExpr SExpr
  | SELet Identifier SExpr SExpr
  | SELetRec Identifier SType SExpr SExpr
  | SELabel Identifier
  | SERecordNil
  | SERecordCons Identifier SExpr SExpr
  | SEHead SExpr
  | SEHeadLabel SExpr
  | SETail SExpr
  | SEConcat SExpr SExpr
  | SERef SExpr
  | SERefOf SExpr
  | SEAssign SExpr SExpr
  | SEIf SExpr SExpr SExpr
  | SETLambda Identifier SExpr
  | SETApp SExpr SType
  deriving (Eq, Ord, Show, Generics.Generic, Aeson.ToJSON, Aeson.FromJSON)

-- -----------------------------------------------------------------------------
-- Name analysis
-- -----------------------------------------------------------------------------

class FreeVariables a where
  freeNames :: a -> [LogicName]

freeVariables :: FreeVariables a => a -> [Identifier]
freeVariables = map logicNameText . freeNames

freeTypeVariables :: Type -> [TypeName]
freeTypeVariables ty = [name | TypeSymbol name <- freeNames ty]

freshName :: [Identifier] -> Identifier
freshName used = freshKindBinder ("x" : used) "x"

instance FreeVariables Pred where
  freeNames = List.nub . freePredNames

instance FreeVariables Type where
  freeNames = List.nub . freeTypeNames

instance FreeVariables Rkind where
  freeNames = List.nub . freeKindNames

instance FreeVariables Expr where
  freeNames = List.nub . freeExprNames

freePredNames :: Pred -> [LogicName]
freePredNames predicate = case predicate of
  PVar name -> [TypeSymbol name]
  PRefVar name -> [RefSymbol name]
  _ -> concatMap freePredNames (predChildren predicate)

freeKindNames :: Rkind -> [LogicName]
freeKindNames kind = case kind of
  KBase _ (Refined _ predicate) -> freePredNames predicate
  KPi _ domain codomain -> freeKindNames domain ++ freeKindNames codomain
  KGen _ domain codomain -> freeKindNames domain ++ freeKindNames codomain

freeTypeNames :: Type -> [LogicName]
freeTypeNames ty = case ty of
  TVar name -> [TypeSymbol name]
  TAnn body kind -> freeTypeNames body ++ freeKindNames kind
  TForall _ domain body -> freeKindNames domain ++ freeTypeNames body
  _ -> concatMap freeTypeNames (typeChildren ty)

-- FreeVariables Expr intentionally reports only names that can occur in
-- logical obligations. Term names are still included by allExprNames below.
freeExprNames :: Expr -> [LogicName]
freeExprNames expression = case expression of
  EAnn body ty -> freeExprNames body ++ freeTypeNames ty
  ELetRec _ ty definition body ->
    freeTypeNames ty ++ freeExprNames definition ++ freeExprNames body
  ETApp body ty -> freeExprNames body ++ freeTypeNames ty
  _ -> concatMap freeExprNames (exprChildren expression)

allTypeNames :: Type -> [Identifier]
allTypeNames = List.nub . occupiedTypeNames

allKindNames :: Rkind -> [Identifier]
allKindNames = List.nub . occupiedKindNames

allExprNames :: Expr -> [Identifier]
allExprNames = List.nub . occupiedExprNames

occupiedPredNames :: Pred -> [Identifier]
occupiedPredNames predicate = case predicate of
  PVar name -> [nameText name]
  PRefVar name -> [nameText name]
  _ -> concatMap occupiedPredNames (predChildren predicate)

occupiedKindNames :: Rkind -> [Identifier]
occupiedKindNames kind = case kind of
  KBase _ (Refined hint predicate) -> hint : occupiedPredNames predicate
  KPi hint domain codomain ->
    occupiedKindNames domain ++ hint : occupiedKindNames codomain
  KGen hint domain codomain ->
    occupiedKindNames domain ++ hint : occupiedKindNames codomain

occupiedTypeNames :: Type -> [Identifier]
occupiedTypeNames ty = case ty of
  TVar name -> [nameText name]
  TLambda hint body -> hint : occupiedTypeNames body
  TAnn body kind -> occupiedTypeNames body ++ occupiedKindNames kind
  TForall hint domain body ->
    occupiedKindNames domain ++ hint : occupiedTypeNames body
  TLet (Decl hint definition) body ->
    occupiedTypeNames definition ++ hint : occupiedTypeNames body
  TRec hint definition body ->
    hint : occupiedTypeNames definition ++ occupiedTypeNames body
  _ -> concatMap occupiedTypeNames (typeChildren ty)

occupiedExprNames :: Expr -> [Identifier]
occupiedExprNames expression = case expression of
  EVar name -> [nameText name]
  ELambda hint body -> hint : occupiedExprNames body
  ELet hint definition body ->
    occupiedExprNames definition ++ hint : occupiedExprNames body
  ELetRec hint ty definition body ->
    occupiedTypeNames ty ++ hint : occupiedExprNames definition ++ occupiedExprNames body
  ETLambda hint body -> hint : occupiedExprNames body
  EAnn body ty -> occupiedExprNames body ++ occupiedTypeNames ty
  ETApp body ty -> occupiedExprNames body ++ occupiedTypeNames ty
  _ -> concatMap occupiedExprNames (exprChildren expression)

-- -----------------------------------------------------------------------------
-- Locally nameless type operations
-- -----------------------------------------------------------------------------

data SubstitutionError
  = UnsupportedPredicateEmbedding !Type
  deriving (Eq, Show)

renderSubstitutionError :: SubstitutionError -> String
renderSubstitutionError (UnsupportedPredicateEmbedding ty) =
  "unsupported type computation in predicate: " ++ show ty

mapScopedPred :: (Int -> Int -> Pred -> Pred) -> Pred -> Pred
mapScopedPred f = Identity.runIdentity . walkPred
  (\td rd -> Identity.Identity . f td rd) 0 0

walkPred :: Monad m => (Int -> Int -> Pred -> m Pred)
  -> Int -> Int -> Pred -> m Pred
walkPred f td rd predicate = traversePredChildren go predicate >>= f td rd
  where
    go = walkPred f td rd

traverseScopedType :: Monad m => (Int -> Int -> Type -> m Type)
  -> (Int -> Int -> Pred -> m Pred) -> Type -> m Type
traverseScopedType typeNode predNode = walkType typeNode predNode 0 0

traverseScopedKind :: Monad m => (Int -> Int -> Type -> m Type)
  -> (Int -> Int -> Pred -> m Pred) -> Rkind -> m Rkind
traverseScopedKind typeNode predNode = walkKind typeNode predNode 0 0

mapScopedType :: (Int -> Int -> Type -> Type)
  -> (Int -> Int -> Pred -> Pred) -> Type -> Type
mapScopedType typeNode predNode = Identity.runIdentity . traverseScopedType
  (\td rd -> Identity.Identity . typeNode td rd)
  (\td rd -> Identity.Identity . predNode td rd)

mapScopedKind :: (Int -> Int -> Type -> Type)
  -> (Int -> Int -> Pred -> Pred) -> Rkind -> Rkind
mapScopedKind typeNode predNode = Identity.runIdentity . traverseScopedKind
  (\td rd -> Identity.Identity . typeNode td rd)
  (\td rd -> Identity.Identity . predNode td rd)

walkType :: Monad m => (Int -> Int -> Type -> m Type)
  -> (Int -> Int -> Pred -> m Pred)
  -> Int -> Int -> Type -> m Type
walkType typeNode predNode td rd ty = (case ty of
  TLambda hint body -> TLambda hint <$> nested body
  TForall hint domain body -> TForall hint <$> kind domain <*> nested body
  TAnn body classifier -> TAnn <$> go body <*> kind classifier
  TLet (Decl hint definition) body ->
    TLet <$> (Decl hint <$> go definition) <*> nested body
  TRec hint definition body -> TRec hint <$> nested definition <*> nested body
  other -> traverseTypeChildren go other) >>= typeNode td rd
  where
    go = walkType typeNode predNode td rd
    nested = walkType typeNode predNode (td + 1) rd
    kind = walkKind typeNode predNode td rd

walkKind :: Monad m => (Int -> Int -> Type -> m Type)
  -> (Int -> Int -> Pred -> m Pred)
  -> Int -> Int -> Rkind -> m Rkind
walkKind typeNode predNode td rd classifier = case classifier of
  KBase base (Refined hint predicate) ->
    KBase base . Refined hint <$> walkPred predNode td (rd + 1) predicate
  KPi hint domain codomain ->
    KPi hint <$> go domain <*> walkKind typeNode predNode (td + 1) rd codomain
  KGen hint domain codomain ->
    KGen hint <$> go domain <*> walkKind typeNode predNode (td + 1) rd codomain
  where
    go = walkKind typeNode predNode td rd

abstractType :: TypeName -> Type -> Type
abstractType name = abstractTypeBody [name]

abstractTypeBody :: [TypeName] -> Type -> Type
abstractTypeBody names =
  mapScopedType (closeTypes names) (closePredTypes names)

abstractKind :: TypeName -> Rkind -> Rkind
abstractKind name =
  mapScopedKind (closeTypes [name]) (closePredTypes [name])

closeTypes :: [TypeName] -> Int -> Int -> Type -> Type
closeTypes names td _ ty = case ty of
  TVar name -> maybe ty (TBound . (td +))
    (lookup name (zip (reverse names) [0..]))
  TBound index | index >= td -> TBound (index + length names)
  _ -> ty

closePredTypes :: [TypeName] -> Int -> Int -> Pred -> Pred
closePredTypes names td _ predicate = case predicate of
  PVar name -> maybe predicate (PTypeBound . (td +))
    (lookup name (zip (reverse names) [0..]))
  PTypeBound index | index >= td -> PTypeBound (index + length names)
  _ -> predicate

unabstractType :: TypeName -> Type -> Type
unabstractType name =
  mapScopedType (openTypeName 0 name) (openPredName 0 name)

unabstractKind :: TypeName -> Rkind -> Rkind
unabstractKind name =
  mapScopedKind (openTypeName 0 name) (openPredName 0 name)

openTypeName :: Int -> TypeName -> Int -> Int -> Type -> Type
openTypeName target name td _ (TBound index)
  | index == target + td = TVar name
  | index > target + td = TBound (index - 1)
openTypeName _ _ _ _ ty = ty

openPredName :: Int -> TypeName -> Int -> Int -> Pred -> Pred
openPredName target name td _ (PTypeBound index)
  | index == target + td = PVar name
  | index > target + td = PTypeBound (index - 1)
openPredName _ _ _ _ predicate = predicate

scopedPredicateOf :: Type -> Either SubstitutionError Pred
scopedPredicateOf ty = case typeToPredMaybe ty of
  Just predicate -> Right predicate
  Nothing -> Left (UnsupportedPredicateEmbedding ty)

instantiateType :: Type -> Type -> Either SubstitutionError Type
instantiateType replacement = instantiateTypeBody [replacement]

instantiateTypeBody :: [Type] -> Type -> Either SubstitutionError Type
instantiateTypeBody replacements = traverseScopedType
  (openTypes 0 replacements) (openPredTypes 0 replacements)

instantiateTypeAt :: Int -> Type -> Type -> Either SubstitutionError Type
instantiateTypeAt target replacement = traverseScopedType
  (openTypes target [replacement]) (openPredTypes target [replacement])

instantiateKindAt :: Int -> Type -> Rkind -> Either SubstitutionError Rkind
instantiateKindAt target replacement = traverseScopedKind
  (openTypes target [replacement]) (openPredTypes target [replacement])

openTypes :: Int -> [Type] -> Int -> Int -> Type
  -> Either SubstitutionError Type
openTypes target replacements td rd ty = pure $ case ty of
  TBound index | index >= lower && index < lower + length replacements ->
    shiftRefinementIndices 0 rd
      (shiftTypeIndices 0 lower (reverse replacements !! (index - lower)))
  TBound index | index >= lower + length replacements ->
    TBound (index - length replacements)
  _ -> ty
  where
    lower = target + td

openPredTypes :: Int -> [Type] -> Int -> Int -> Pred
  -> Either SubstitutionError Pred
openPredTypes target replacements td rd predicate = case predicate of
  PTypeBound index | index >= lower && index < lower + length replacements ->
    liftPred lower rd <$> scopedPredicateOf (reverse replacements !! (index - lower))
  PTypeBound index | index >= lower + length replacements ->
    pure (PTypeBound (index - length replacements))
  _ -> pure predicate
  where
    lower = target + td

instantiatePiKind :: Type -> Rkind -> Either SubstitutionError Rkind
instantiatePiKind argument (KPi _ _ codomain) =
  instantiateKindAt 0 argument codomain
instantiatePiKind _ classifier = pure classifier

shiftTypeIndices :: Int -> Int -> Type -> Type
shiftTypeIndices cutoff delta = mapScopedType
  (shiftTypeOccurrence cutoff delta)
  (shiftPredTypeOccurrence cutoff delta)

shiftTypeOccurrence :: Int -> Int -> Int -> Int -> Type -> Type
shiftTypeOccurrence cutoff delta td _ (TBound index)
  | index >= cutoff + td = TBound (index + delta)
shiftTypeOccurrence _ _ _ _ ty = ty

shiftPredTypeOccurrence :: Int -> Int -> Int -> Int -> Pred -> Pred
shiftPredTypeOccurrence cutoff delta td _ (PTypeBound index)
  | index >= cutoff + td = PTypeBound (index + delta)
shiftPredTypeOccurrence _ _ _ _ predicate = predicate

shiftRefinementIndices :: Int -> Int -> Type -> Type
shiftRefinementIndices cutoff delta =
  mapScopedType (\_ _ -> id) (shiftPredRefOccurrence cutoff delta)

shiftPredRefOccurrence :: Int -> Int -> Int -> Int -> Pred -> Pred
shiftPredRefOccurrence cutoff delta _ rd (PBound index)
  | index >= cutoff + rd = PBound (index + delta)
shiftPredRefOccurrence _ _ _ _ predicate = predicate

liftPred :: Int -> Int -> Pred -> Pred
liftPred td rd = mapScopedPred $ \typeDepth refDepth ->
  shiftPredRefOccurrence 0 rd typeDepth refDepth
    . shiftPredTypeOccurrence 0 td typeDepth refDepth

openPredicate :: Pred -> Pred -> Pred
openPredicate replacement = mapScopedPred open
  where
    open td rd (PBound index)
      | index == rd = liftPred td rd replacement
      | index > rd = PBound (index - 1)
    open _ _ predicate = predicate

-- -----------------------------------------------------------------------------
-- Locally nameless term operations
-- -----------------------------------------------------------------------------

traverseScopedExpr :: Monad m => (Int -> Int -> Expr -> m Expr)
  -> (Int -> Type -> m Type) -> Expr -> m Expr
traverseScopedExpr node ty = go 0 0
  where
    go ed td expression = (case expression of
      ELambda hint body -> ELambda hint <$> go (ed + 1) td body
      ELet hint definition body ->
        ELet hint <$> go ed td definition <*> go (ed + 1) td body
      ELetRec hint classifier definition body -> ELetRec hint <$> ty td classifier
        <*> go (ed + 1) td definition <*> go (ed + 1) td body
      ETLambda hint body -> ETLambda hint <$> go ed (td + 1) body
      EAnn body classifier -> EAnn <$> go ed td body <*> ty td classifier
      ETApp body argument -> ETApp <$> go ed td body <*> ty td argument
      other -> traverseExprChildren (go ed td) other) >>= node ed td

mapScopedExpr :: (Int -> Int -> Expr -> Expr)
  -> (Int -> Type -> Type) -> Expr -> Expr
mapScopedExpr node ty = Identity.runIdentity . traverseScopedExpr
  (\ed td -> Identity.Identity . node ed td)
  (\td -> Identity.Identity . ty td)

shiftExprTermIndices :: Int -> Int -> Expr -> Expr
shiftExprTermIndices cutoff delta = mapScopedExpr shift (const id)
  where
    shift ed _ (EBound index)
      | index >= cutoff + ed = EBound (index + delta)
    shift _ _ expression = expression

shiftExprTypeIndices :: Int -> Int -> Expr -> Expr
shiftExprTypeIndices cutoff delta = mapScopedExpr (\_ _ -> id)
  (\td -> shiftTypeIndices (cutoff + td) delta)

liftExpr :: Int -> Int -> Expr -> Expr
liftExpr ed td = shiftExprTypeIndices 0 td . shiftExprTermIndices 0 ed

openExprTerm :: Expr -> Expr -> Expr
openExprTerm replacement = mapScopedExpr open (const id)
  where
    open ed td (EBound index)
      | index == ed = liftExpr ed td replacement
      | index > ed = EBound (index - 1)
    open _ _ expression = expression

closeExprTerm :: TermName -> Expr -> Expr
closeExprTerm name = mapScopedExpr close (const id)
  where
    close ed _ (EVar current) | current == name = EBound ed
    close ed _ (EBound index) | index >= ed = EBound (index + 1)
    close _ _ expression = expression

instantiateExprType :: Type -> Expr -> Either SubstitutionError Expr
instantiateExprType replacement = traverseScopedExpr keep
  (\td -> instantiateTypeAt td replacement)
  where
    keep _ _ = pure

unabstractExprType :: TypeName -> Expr -> Expr
unabstractExprType name = mapScopedExpr (\_ _ -> id)
  (\td -> mapScopedType (openTypeName td name) (openPredName td name))

closeExprType :: TypeName -> Expr -> Expr
closeExprType name = mapScopedExpr (\_ _ -> id)
  (\outer -> mapScopedType
    (\td rd -> closeTypes [name] (outer + td) rd)
    (\td rd -> closePredTypes [name] (outer + td) rd))
