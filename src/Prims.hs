{-# LANGUAGE OverloadedStrings #-}
module Prims
  ( bTrue
  , unitKind
  , intKind
  , stringKind
  , boolKind
  , trueKind
  , falseKind
  , labelKind
  , nonEmptyRecordKind
  , singletonKind
  , singletonKindAt
  , typeOpKind
  ) where

import qualified Types as T

bTrue :: T.BaseKind -> T.Rkind
bTrue = T.bTrue

unitKind :: T.Rkind
unitKind = singletonKind T.PUnit

intKind :: T.Rkind
intKind = singletonKind T.PInt

stringKind :: T.Rkind
stringKind = singletonKind T.PString

boolKind :: T.Rkind
boolKind = singletonKind T.PBool

trueKind :: T.Rkind
trueKind = singletonKindAt T.BKBool T.PTrue

falseKind :: T.Rkind
falseKind = singletonKindAt T.BKBool T.PFalse

labelKind :: T.Identifier -> T.Rkind
labelKind label = T.KBase T.BKLabel
  (T.refinement "l" (T.PInterp2 T.BEq (T.PBound 0) (T.PLabel label)))

nonEmptyRecordKind :: T.Rkind
nonEmptyRecordKind = T.KBase T.BKRec
  (T.refinement "r" (T.PInterp1 T.BNot
    (T.PInterp1 T.BEmpty (T.PBound 0))))

singletonKind :: T.Pred -> T.Rkind
singletonKind = singletonKindAt T.BKType

singletonKindAt :: T.BaseKind -> T.Pred -> T.Rkind
singletonKindAt kind predicate = T.KBase kind
  (T.Refined "v" (T.PInterp2 T.BEq (T.PBound 0) predicate))

-- Built-in type operations are ordinary dependent type functions. Their
-- applications are checked solely through these classifiers.
typeOpKind :: T.TypeOp -> T.Rkind
typeOpKind operation = case operation of
  T.BEq -> binaryKind T.BKType T.BKType T.BKBool T.BEq
  T.BNot -> unaryKind T.BKBool T.BKBool T.BNot
  T.BHead -> T.KPi "record" nonEmptyRecordKind
    (singletonKind (T.PInterp1 T.BHead (T.PTypeBound 0)))
  T.BHeadLabel -> T.KPi "record" nonEmptyRecordKind
    (singletonKindAt T.BKLabel
      (T.PInterp1 T.BHeadLabel (T.PTypeBound 0)))
  T.BTail -> T.KPi "record" nonEmptyRecordKind
    (recordResult (T.PInterp1 T.BTail (T.PTypeBound 0)))
  T.BDom -> T.KPi "function" (bTrue T.BKFun)
    (singletonKind (T.PInterp1 T.BDom (T.PTypeBound 0)))
  T.BImg -> T.KPi "function" (bTrue T.BKFun)
    (singletonKind (T.PInterp1 T.BImg (T.PTypeBound 0)))
  T.BRefOf -> T.KPi "reference" (bTrue T.BKRef)
    (singletonKind (T.PInterp1 T.BRefOf (T.PTypeBound 0)))
  T.BColOf -> T.KPi "collection" (bTrue T.BKCol)
    (singletonKind (T.PInterp1 T.BColOf (T.PTypeBound 0)))
  T.BConcat -> T.KPi "left" (bTrue T.BKRec)
    (T.KPi "right" (T.KBase T.BKRec (T.Refined "candidate"
      (T.PApart
        (T.PLabSet (T.PTypeBound 0))
        (T.PLabSet (T.PBound 0)))))
      (recordResult (T.PInterp2 T.BConcat
        (T.PTypeBound 1) (T.PTypeBound 0))))
  T.BEmpty -> unaryKind T.BKType T.BKBool T.BEmpty
  T.BOr -> binaryKind T.BKBool T.BKBool T.BKBool T.BOr
  T.BAnd -> binaryKind T.BKBool T.BKBool T.BKBool T.BAnd
  T.BIsRec -> unaryKind T.BKType T.BKBool T.BIsRec

unaryKind :: T.BaseKind -> T.BaseKind -> T.TypeOp -> T.Rkind
unaryKind input output operation = T.KPi "operand" (bTrue input)
  (singletonKindAt output (T.PInterp1 operation (T.PTypeBound 0)))

binaryKind
  :: T.BaseKind -> T.BaseKind -> T.BaseKind -> T.TypeOp -> T.Rkind
binaryKind leftKind rightKind outputKind operation =
  T.KPi "left" (bTrue leftKind)
    (T.KPi "right" (bTrue rightKind)
      (singletonKindAt outputKind
        (T.PInterp2 operation (T.PTypeBound 1) (T.PTypeBound 0))))

recordResult :: T.Pred -> T.Rkind
recordResult result = T.KBase T.BKRec (T.Refined "v"
  (T.PInterp2 T.BAnd
    (T.PInterp2 T.BEq (T.PBound 0) result)
    (T.PInterp1 T.BIsRec (T.PBound 0))))
