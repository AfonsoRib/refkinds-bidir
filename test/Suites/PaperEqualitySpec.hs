{-# LANGUAGE OverloadedStrings #-}
module Suites.PaperEqualitySpec (tests) where

import Check (checkTypeEquality)
import Context hiding (implicationConstraint)
import Parser
import Suites.Common (checkExpr)
import Types
import Test.Tasty
import Test.Tasty.HUnit
import Support.Errors (assertError)

kind :: String -> Rkind
kind = either error id . parseKind
ty :: String -> Type
ty = either error id . parseType

constant :: Context
constant = addTypeVar "F" (kind "Pi X :: KType. { v :: KType | v == TInt }") emptyContext

reject :: Show value => IO value -> Assertion
reject = assertError

same :: Context -> Rkind -> String -> String -> Assertion
same ctx k a b = checkTypeEquality ctx k (ty a) (ty b) >>= (@?= ())

different :: Context -> Rkind -> String -> String -> Assertion
different ctx k a b = reject (checkTypeEquality ctx k (ty a) (ty b))

tests :: TestTree
tests = testGroup "Paper-directed semantic equality"
  [ testCase "constant result contracts do not replace alpha-equivalence" $
      different constant (bTrue BKType) "F TInt" "F TBool"
  , testCase "constant result contracts reject a different result type" $
      reject (checkTypeEquality constant (bTrue BKType) (ty "F TInt") TBool)
  , testCase "term conversion rejects result-contract-only equality" $
      reject (checkExpr (addTermVar "x" (ty "F TInt") constant) (EVar "x") (ty "F TBool"))
  , testCase "unconstrained application results are not identified" $ do
      let ctx = addTypeVar "F" (kind "Pi X :: KType. KType") emptyContext
      reject (checkTypeEquality ctx (bTrue BKType) (ty "F TInt") (ty "F TBool"))
  , testCase "different abstract applications remain distinct" $ do
      let ctx = addTypeVar "G" (kind "Pi X :: KType. {v :: KType | v == TInt}") constant
      different ctx (bTrue BKType) "F TInt" "G TBool"
  , testCase "dependent result contracts do not rewrite applications" $ do
      let ctx = addTypeVar "F" (kind "Pi X :: KType. {v :: KType | v == X}") emptyContext
      different ctx (bTrue BKType) "F TInt" "TInt"
      reject (checkTypeEquality ctx (bTrue BKType) (ty "F TBool") TInt)
  , testCase "nested result contracts do not rewrite applications" $ do
      let ctx = addTypeVar "G" (kind "Pi X :: KType. {v :: KType | v == X}") constant
      different ctx (bTrue BKType) "G (F TBool)" "TInt"
      reject (checkTypeEquality ctx (bTrue BKType) (ty "G (F TBool)") TBool)
  , testCase "curried neutral applications remain distinct from results" $ do
      let ctx = addTypeVar "F"
            (kind "Pi X :: KType. Pi Y :: {v :: KType | v == X}. {v :: KType | v == Y}")
            emptyContext
      different ctx (bTrue BKType) "F TInt TInt" "TInt"
  , testCase "application congruence requires alpha-equivalent arguments" $ do
      let ctx = addTypeVar "F" (kind "Pi X :: KType. KType")
            (addLocalTypeVar "A" (kind "{v :: KType | v == TInt}") emptyContext)
      different ctx (bTrue BKType) "F A" "F TInt"
  , testCase "Pi comparison uses alpha-equivalence without extensionality" $ do
      different emptyContext (kind "Pi X :: KType. KType")
        "fun X -> X" "fun Y -> refOf (TRef Y)"
      reject (checkTypeEquality emptyContext (kind "Pi X :: KType. KType")
        (ty "fun X -> TInt") (ty "fun Y -> TBool"))
  , testCase "abstract functions are not extensionally identified" $
      different constant (kind "Pi X :: KType. KType") "F" "fun X -> TInt"
  , testCase "constructor comparison computes components as needed" $
      same emptyContext (bTrue BKType) "TRef (refOf (TRef TInt))" "TRef TInt"
  , testCase "refined neutral function types remain syntactically distinct" $ do
      let ctx = addLocalTypeVar "A" (kind "{v :: KFun | dom v == TInt && img v == TBool}") emptyContext
      different ctx (bTrue BKType) "A" "TInt -> TBool"
  , testCase "universal refinements do not replace alpha-equivalence" $
      different emptyContext (kind "KGen X :: {v :: KType | v == TInt}. KType")
        "(forall A :: {v :: KType | v == TInt}. refOf (TRef A)) :: KGen A :: {v :: KType | v == TInt}. KType"
        "(forall B :: {v :: KType | TInt == v}. TInt) :: KGen B :: {v :: KType | TInt == v}. KType"
  , testCase "malformed result contracts cannot become proof assumptions" $ do
      let ctx = addTypeVar "F" (kind "Pi X :: KType. {v :: KType | head v == TInt}") emptyContext
      reject (checkTypeEquality ctx (bTrue BKType) (ty "F TInt") TInt)
  , testCase "open result contracts do not create equality witnesses" $ do
      let ctx = addTypeVar "A" (bTrue BKType)
            (addTypeVar "F" (kind "Pi X :: KType. {v :: KType | v == A}") emptyContext)
      reject (checkTypeEquality ctx (bTrue BKType) (ty "F TInt") (TVar "A"))
  , testCase "result witnesses cannot capture other free values" $ do
      let ctx = addLocalTypeVar "x0" (bTrue BKType) constant
      reject (checkTypeEquality ctx (bTrue BKType) (ty "F TInt") (TVar "x0"))
  , testCase "reflexivity cannot bypass kind validation" $
      reject (checkTypeEquality emptyContext (bTrue BKType) ((unaryTypeOp BHead) TInt) ((unaryTypeOp BHead) TInt))
  ]
