{-# LANGUAGE OverloadedStrings #-}

module Suites.BehaviorCatalogueSpec (tests) where

import ANF (elaborate)

import Parser (parseExpr)
import Suites.Common
import Support.AstInvariants (validateAnfType)
import Test.Tasty
import Test.Tasty.HUnit
import Types

-- Semantic catalogue entries are mapped to the focused executable scenarios
-- in test/coverage.  This suite intentionally retains only assertions whose
-- subject really is syntax, ANF, binder hygiene, or an operational boundary.
tests :: TestTree
tests = testGroup "Catalogue structural regressions"
  [ testCase "test instrumentation rejects non-ANF type AST" $ do
      let nonAnf = parseTestType "(fun value -> value) (TInt TInt)"
      case validateAnfType nonAnf of
        Left _ -> pure ()
        Right () -> assertFailure "expected non-ANF AST rejection"

  , testCase "type elaboration produces ANF" $ do
      let source = parseTestType
            "[| headLabel [| `field : TInt |] : head [| `field : TInt |] |]"
      validateAnfType (elaborate source) @?= Right ()

  , testCase "term alpha-equivalence ignores binder hints" $ do
      let first = parseTestTerm "fun left -> left"
          second = parseTestTerm "fun right -> right"
      assertBool "lowered lambdas are alpha-equivalent" (alphaEqExpr first second)

  , testCase "multi-field records lower deterministically" $
      parseTestTerm "[first = 1, second = True]" @?=
        ERecordCons "first" (EInteger 1)
          (ERecordCons "second" (EBoolean True) ERecordNil)

  , testCase "fresh names avoid all supplied binders" $ do
      let first = freshName ["x"]
          second = freshName ["x", first]
      assertBool "fresh names differ" (first /= second)

  , testCase "locally nameless close/open preserves binding" $ do
      let closed = abstractType "original" (TVar "original")
      unabstractType "fresh" closed @?= TVar "fresh"

  , testCase "invalid source is rejected" $
      case parseExpr "@@@" of
        Left _ -> pure ()
        Right parsed -> assertFailure ("invalid syntax parsed as " ++ show parsed)

  ]
