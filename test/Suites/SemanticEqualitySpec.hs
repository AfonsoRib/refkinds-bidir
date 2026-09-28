{-# LANGUAGE OverloadedStrings #-}
module Suites.SemanticEqualitySpec (tests) where

import Test.Tasty
import Test.Tasty.HUnit
import Context hiding (implicationConstraint)
import Types
import Check (checkTypeEquality)
import Suites.Common (checkExpr, synthExpr, parseTestKind, parseTestTerm, parseTestType)
import System.Timeout (timeout)
import Support.Errors (assertError, assertErrorContaining, captureError)

tests :: TestTree
tests = testGroup "Semantic Equality"
  [ testCase "beta equality validates its function annotation" $
      same emptyContext (bTrue BKType) "((fun X -> X) :: Pi X :: KType. KType) TInt" "TInt"
  , testCase "let equality" $
      same emptyContext (bTrue BKType) "let X = TInt in X" "TInt"
  , testCase "selector equality" $ do
      same emptyContext (bTrue BKType) "head [| `p : TInt |]" "TInt"
      same emptyContext (bTrue BKRec) "tail [| `p : TInt |]" "[||]"
  , testCase "different concrete types do not convert" $
      assertErrorContaining "invalid-kind error"
        (checkTypeEquality emptyContext (bTrue BKType) TInt TBool)
  , testCase "Pi equality is alpha-equivalence after historical CBV" $ do
      same emptyContext (parseTestKind "Pi x :: KType. KType")
        "fun x -> x" "fun y -> y"
      assertErrorContaining "invalid-kind error" (checkTypeEquality emptyContext
        (parseTestKind "Pi x :: KType. KType")
        (parseTestType "fun x -> x") (parseTestType "fun y -> refOf (TRef y)")
        )
  , testCase "kind assumptions do not equate opaque names with concrete types" $ do
      let ctx = addTypeVar "Alias" (bTrue BKType) emptyContext
      assertErrorContaining "invalid-kind error"
        (checkTypeEquality ctx (bTrue BKType) (TVar "Alias") TInt)
  , testCase "function components compute at function kind" $
      same emptyContext (bTrue BKFun)
        "(((fun x -> x) :: Pi x :: KType. KType) TInt) -> TBool" "TInt -> TBool"
  , testCase "neutral application arguments compute" $
      same (addTypeVar "F" (parseTestKind "Pi x :: KType. KType") emptyContext)
        (bTrue BKType) "F (dom (TInt -> TBool))" "F TInt"
  , testCase "alpha equivalent polymorphic types" $
      same emptyContext (parseTestKind "KGen A :: KType. KType") "forall a :: KType. a" "forall b :: KType. b"
  , testCase "dependent locally nameless kinds are reflexive" $ do
      let kind = parseTestKind
            "Pi row :: KRec. Pi label :: { candidate :: KLabel | member candidate row }. KType"
          renamed = parseTestKind
            "Pi record :: KRec. Pi key :: { value :: KLabel | member value record }. KType"
      assertBool "kind reflexivity" (alphaEqKind kind kind)
      assertBool "binder hints preserve indices" (alphaEqKind kind renamed)
  , testCase "records references and collections convert" $
      same emptyContext (bTrue BKRec)
        "[| `x : TRef (TCol TInt) |]" "[| `x : TRef (TCol TInt) |]"
  , testCase "independent scoped variables do not establish equality" $
      assertError (checkTypeEquality (addLocalTypeVar "A" (bTrue BKType)
        (addLocalTypeVar "B" (bTrue BKType) emptyContext))
        (bTrue BKType) (TVar "A") (TVar "B"))
  , testCase "reflexivity cannot bypass a failed kind obligation" $
      assertError (checkTypeEquality emptyContext (bTrue BKType)
        ((unaryTypeOp BHead) TRecNil) ((unaryTypeOp BHead) TRecNil))
  , testCase "both validations precede evaluation" $ do
      let divergent = parseTestType
            "letrec F :: Pi X :: KType. KType = fun X -> F X in F TInt"
      result <- timeout 2000000
        (captureError (checkTypeEquality emptyContext (bTrue BKType)
          divergent ((unaryTypeOp BHead) TRecNil)))
      case result of
        Just (Left _) -> pure ()
        Just (Right ()) -> assertFailure "invalid right operand was accepted"
        Nothing -> assertFailure "validation diverged before rejecting the right operand"
  , testCase "semantic term conversion rejects a non-alpha ambient type" $ do
      let ctx = addTypeVar "A" (KBase BKType (refinement "v"
            ((binaryPredOp BEq (PBound 0) PUnit)))) emptyContext
      assertErrorContaining "subtype error"
        (checkExpr ctx (parseTestTerm "()") (TVar "A"))
  , testCase "term conditionals require a checking goal" $ do
      assertErrorContaining "type error"
        (synthExpr emptyContext (parseTestTerm "if True then () else ()"))
  ]
  where
    same ctx kind left right = checkTypeEquality ctx kind
      (parseTestType left) (parseTestType right) >>= (@?= ())
