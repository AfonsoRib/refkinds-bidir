{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}

-- | Locally nameless opening, substitution, shifting, and name analysis.
module Substitution
  ( Substitutable(..)
  , FreeVariables(..)
  , freeVariables
  , freeTypeVariables
  , freshName
  , freePredNames
  , freeKindNames
  , freeTypeNames
  , freeExprNames
  , allTypeNames
  , allKindNames
  , allExprNames
  , occupiedPredNames
  , occupiedKindNames
  , occupiedTypeNames
  , occupiedExprNames
  , mapScopedPred
  , mapScopedType
  , mapScopedKind
  , abstractType
  , abstractTypeBody
  , abstractKind
  , unabstractType
  , unabstractKind
  , instantiateType
  , instantiateTypeBody
  , instantiateTypeAt
  , instantiateKindAt
  , instantiatePiKind
  , shiftTypeIndices
  , shiftRefinementIndices
  , openPredicate
  , shiftExprTermIndices
  , shiftExprTypeIndices
  , openExprTerm
  , closeExprTerm
  , instantiateExprType
  , unabstractExprType
  , closeExprType
  ) where

import qualified Types as T

class FreeVariables value where
  freeNames :: value -> [T.LogicName]

instance FreeVariables T.Pred where
  freeNames = T.freeNames

instance FreeVariables T.Type where
  freeNames = T.freeNames

instance FreeVariables T.Rkind where
  freeNames = T.freeNames

instance FreeVariables T.Expr where
  freeNames = T.freeNames

freeVariables :: FreeVariables value => value -> [T.Identifier]
freeVariables = map T.logicNameText . freeNames

freeTypeVariables :: T.Type -> [T.TypeName]
freeTypeVariables = T.freeTypeVariables

freshName :: [T.Identifier] -> T.Identifier
freshName = T.freshName

freePredNames :: T.Pred -> [T.LogicName]
freePredNames = T.freePredNames

freeKindNames :: T.Rkind -> [T.LogicName]
freeKindNames = T.freeKindNames

freeTypeNames :: T.Type -> [T.LogicName]
freeTypeNames = T.freeTypeNames

freeExprNames :: T.Expr -> [T.LogicName]
freeExprNames = T.freeExprNames

allTypeNames :: T.Type -> [T.Identifier]
allTypeNames = T.allTypeNames

allKindNames :: T.Rkind -> [T.Identifier]
allKindNames = T.allKindNames

allExprNames :: T.Expr -> [T.Identifier]
allExprNames = T.allExprNames

occupiedPredNames :: T.Pred -> [T.Identifier]
occupiedPredNames = T.occupiedPredNames

occupiedKindNames :: T.Rkind -> [T.Identifier]
occupiedKindNames = T.occupiedKindNames

occupiedTypeNames :: T.Type -> [T.Identifier]
occupiedTypeNames = T.occupiedTypeNames

occupiedExprNames :: T.Expr -> [T.Identifier]
occupiedExprNames = T.occupiedExprNames

class Substitutable target replacement where
  substitute :: replacement -> target -> target

instance Substitutable T.Type T.Type where
  substitute replacement target = direct
    (T.instantiateType replacement target)

instance Substitutable T.Rkind T.Type where
  substitute replacement target = direct
    (T.instantiateKindAt 0 replacement target)

instance Substitutable T.Pred T.Pred where
  substitute = T.openPredicate

instance Substitutable T.Expr T.Expr where
  substitute = T.openExprTerm

instance Substitutable T.Expr T.Type where
  substitute replacement target = direct
    (T.instantiateExprType replacement target)

direct :: Either T.SubstitutionError value -> value
direct result = case result of
  Right value -> value
  Left problem -> error
    ("predicate encoding error: " ++ T.renderSubstitutionError problem)

mapScopedPred :: (Int -> Int -> T.Pred -> T.Pred) -> T.Pred -> T.Pred
mapScopedPred = T.mapScopedPred

mapScopedType :: (Int -> Int -> T.Type -> T.Type)
  -> (Int -> Int -> T.Pred -> T.Pred) -> T.Type -> T.Type
mapScopedType = T.mapScopedType

mapScopedKind :: (Int -> Int -> T.Type -> T.Type)
  -> (Int -> Int -> T.Pred -> T.Pred) -> T.Rkind -> T.Rkind
mapScopedKind = T.mapScopedKind

abstractType :: T.TypeName -> T.Type -> T.Type
abstractType = T.abstractType

abstractTypeBody :: [T.TypeName] -> T.Type -> T.Type
abstractTypeBody = T.abstractTypeBody

abstractKind :: T.TypeName -> T.Rkind -> T.Rkind
abstractKind = T.abstractKind

unabstractType :: T.TypeName -> T.Type -> T.Type
unabstractType = T.unabstractType

unabstractKind :: T.TypeName -> T.Rkind -> T.Rkind
unabstractKind = T.unabstractKind

instantiateType :: T.Type -> T.Type -> Either T.SubstitutionError T.Type
instantiateType = T.instantiateType

instantiateTypeBody
  :: [T.Type] -> T.Type -> Either T.SubstitutionError T.Type
instantiateTypeBody = T.instantiateTypeBody

instantiateTypeAt
  :: Int -> T.Type -> T.Type -> Either T.SubstitutionError T.Type
instantiateTypeAt = T.instantiateTypeAt

instantiateKindAt
  :: Int -> T.Type -> T.Rkind -> Either T.SubstitutionError T.Rkind
instantiateKindAt = T.instantiateKindAt

instantiatePiKind
  :: T.Type -> T.Rkind -> Either T.SubstitutionError T.Rkind
instantiatePiKind = T.instantiatePiKind

shiftTypeIndices :: Int -> Int -> T.Type -> T.Type
shiftTypeIndices = T.shiftTypeIndices

shiftRefinementIndices :: Int -> Int -> T.Type -> T.Type
shiftRefinementIndices = T.shiftRefinementIndices

openPredicate :: T.Pred -> T.Pred -> T.Pred
openPredicate = T.openPredicate

shiftExprTermIndices :: Int -> Int -> T.Expr -> T.Expr
shiftExprTermIndices = T.shiftExprTermIndices

shiftExprTypeIndices :: Int -> Int -> T.Expr -> T.Expr
shiftExprTypeIndices = T.shiftExprTypeIndices

openExprTerm :: T.Expr -> T.Expr -> T.Expr
openExprTerm = T.openExprTerm

closeExprTerm :: T.TermName -> T.Expr -> T.Expr
closeExprTerm = T.closeExprTerm

instantiateExprType
  :: T.Type -> T.Expr -> Either T.SubstitutionError T.Expr
instantiateExprType = T.instantiateExprType

unabstractExprType :: T.TypeName -> T.Expr -> T.Expr
unabstractExprType = T.unabstractExprType

closeExprType :: T.TypeName -> T.Expr -> T.Expr
closeExprType = T.closeExprType
