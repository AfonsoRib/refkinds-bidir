{-# LANGUAGE OverloadedStrings #-}

module Suites.ParsedSyntaxSpec (tests) where

import Context (emptyContext)
import Parser (parseExpr, parseType)
import Suites.Common (checkExpr, synthExpr)
import Test.Tasty
import Test.Tasty.HUnit
import qualified Types

tests :: TestTree
tests = testGroup "Parsed source syntax"
  [ testCase "parsed integer source synthesizes its type" $ do
      expression <- parseTerm "1"
      synthExpr emptyContext expression >>= (@?= expectedInteger)

  , testCase "parsed local binding checks against a parsed type" $ do
      expression <- parseTerm "let value = 1 in value"
      checkExpr emptyContext expression expectedInteger >>= (@?= ())

  , testCase "parsed lambda checks against a parsed arrow type" $ do
      expression <- parseTerm "fun value -> value"
      expected <- parseExpectedType "TInt -> TInt"
      checkExpr emptyContext expression expected >>= (@?= ())

  , testCase "parsed conditional checks against a parsed type" $ do
      expression <- parseTerm "if True then 1 else 2"
      expected <- parseExpectedType "TInt"
      checkExpr emptyContext expression expected >>= (@?= ())
  ]
  where
    expectedInteger = case parseType "TInt" of
      Right ty -> ty
      Left err -> error err

parseTerm :: String -> IO Types.Expr
parseTerm source = case parseExpr source of
  Right expression -> pure expression
  Left err -> assertFailure err >> fail "unreachable parser failure"

parseExpectedType :: String -> IO Types.Type
parseExpectedType source = case parseType source of
  Right ty -> pure ty
  Left err -> assertFailure err >> fail "unreachable parser failure"
