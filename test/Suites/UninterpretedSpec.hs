module Suites.UninterpretedSpec (tests) where

import Parser (parseType, parseKind)
import Test.Tasty
import Test.Tasty.HUnit

tests :: TestTree
tests = testGroup "Retired logical functions"
  [ testCase "logical applications are rejected in types" $
      mapM_ (reject . parseType) ["uninterp f(TInt)", "uninterp f()", "uninterp f(TInt, TBool)"]
  , testCase "logical applications are rejected in predicates" $
      mapM_ (reject . parseKind)
        ["{ v :: KType | uninterp f(v) == TInt }", "{ v :: KType | uninterp p(v) }"]
  ]
  where
    reject (Left _) = pure ()
    reject (Right _) = assertFailure "retired logical syntax was accepted"
