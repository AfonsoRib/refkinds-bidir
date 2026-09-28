{-# LANGUAGE OverloadedStrings #-}

module Suites.PaperExamplesSpec (tests) where

import Test.Tasty
import Test.Tasty.HUnit
import Context hiding (implicationConstraint)
import Check (checkTypeEquality)
import Types
import Suites.Common (checkExpr, parseTestTerm, parseTestType)

tests :: TestTree
tests = testGroup "Paper Examples"
  [ testCase "paper addField record extension" $ do
      let ext = parseTestTerm "[q = True | [p = 1]]"
          expected = parseTestType "[| `q : TBool, `p : TInt |]"
      checkExpr emptyContext ext expected >>= (@?= ())

  , testCase "paper term record concatenation" $ do
      let concatenated = parseTestTerm "[p = 1] @ [q = True]"
          expected = parseTestType "[| `p : TInt, `q : TBool |]"
      checkExpr emptyContext concatenated expected >>= (@?= ())

  , testCase "paper type record concatenation reduces to its record" $ do
      let concatenated = parseTestType "[| `p : TInt |] @ [| `q : TBool |]"
          expected = parseTestType "[| `p : TInt, `q : TBool |]"
      checkTypeEquality emptyContext (bTrue BKRec) concatenated expected
        >>= (@?= ())
  ]
