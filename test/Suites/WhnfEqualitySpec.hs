{-# LANGUAGE OverloadedStrings #-}
module Suites.WhnfEqualitySpec (tests) where

import Check (checkTypeEquality, checkTypeEqualityWhnf)
import Context
import Suites.Common (parseTestKind, parseTestType)
import Support.Errors (assertErrorContaining)
import Test.Tasty
import Test.Tasty.HUnit
import Types

tests :: TestTree
tests = testGroup "Experimental WHNF equality"
  [ testCase "reference selector reduces below TRef" $
      both emptyContext (bTrue BKType)
        "TRef (refOf (TRef TInt))" "TRef TInt"
  , testCase "collection selector reduces below TCol" $
      both emptyContext (bTrue BKType)
        "TCol (colOf (TCol TInt))" "TCol TInt"
  , testCase "different reference elements remain unequal" $
      neither emptyContext (bTrue BKType) "TRef TInt" "TRef TBool"
  , testCase "nested neutral applications compare their arguments" $ do
      let ctx = addTypeVar "F" (parseTestKind "Pi X :: KType. KType")
            (addTypeVar "G" (parseTestKind "Pi X :: KType. KType") emptyContext)
      both ctx (bTrue BKType)
        "F (G (refOf (TRef TInt)))" "F (G TInt)"
      neither ctx (bTrue BKType) "F (G TInt)" "F (G TBool)"
  , testCase "arrows and record fields compare recursively" $ do
      let computed = unaryTypeOp BRefOf (TRef TInt)
          row field = TRecCons (TLabel "x") field TRecNil
      compareBoth emptyContext (bTrue BKFun)
        (TArrow computed TBool) (TArrow TInt TBool)
      compareBoth emptyContext (bTrue BKRec)
        (row computed) (row TInt)
  , testCase "beta reduction exposes a nested application result" $
      both emptyContext (bTrue BKType)
        "((fun X -> X) :: Pi X :: KType. KType) (refOf (TRef TInt))"
        "TInt"
  , testCase "alpha-equivalent binders" $ do
      both emptyContext (parseTestKind "KGen X :: KType. KType")
        "forall X :: KType. X"
        "forall Y :: KType. Y"
      both emptyContext (parseTestKind "Pi X :: KType. KType")
        "fun X -> X" "fun Y -> Y"
  , testCase "stuck selectors stay neutral" $ do
      let ctx = addTypeVar "R"
            (parseTestKind "{v :: KRef | refOf v == TInt}") emptyContext
      both ctx (bTrue BKType) "refOf R" "refOf R"
      neither ctx (bTrue BKType) "refOf R" "TInt"
  , testCase "lambda body reduction differs from opaque full evaluation" $ do
      let kind = parseTestKind "Pi X :: KType. KType"
          left = parseTestType "fun X -> refOf (TRef X)"
          right = parseTestType "fun Y -> Y"
      checkTypeEqualityWhnf emptyContext kind left right >>= (@?= ())
      assertErrorContaining "invalid-kind error"
        (checkTypeEquality emptyContext kind left right)
  ]
  where
    both ctx kind left right = do
      let a = parseTestType left
          b = parseTestType right
      compareBoth ctx kind a b

    compareBoth ctx kind a b = do
      checkTypeEquality ctx kind a b >>= (@?= ())
      checkTypeEqualityWhnf ctx kind a b >>= (@?= ())

    neither ctx kind left right = do
      let a = parseTestType left
          b = parseTestType right
      assertErrorContaining "invalid-kind error" (checkTypeEquality ctx kind a b)
      assertErrorContaining "invalid-kind error" (checkTypeEqualityWhnf ctx kind a b)
