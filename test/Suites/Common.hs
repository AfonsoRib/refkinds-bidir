{-# LANGUAGE OverloadedStrings #-}

module Suites.Common
  ( check, synth, sub, checkExpr, synthExpr
  , universalDomainConstraint
  , parseTestTerm
  , parseTestType
  , parseTestKind
  , assertVCValid
  , assertVCInvalid
  , assertClosedValid
  , assertClosedInvalid
  , assertAccept
  , assertReject
  ) where

import Data.Text (Text)
import qualified Data.Text as T
import qualified Check
import qualified Check as ExprCheck
import Context hiding (implicationConstraint)
import Parser
import Support.Errors (assertError)
import Types
import Constraint
import Test.Tasty.HUnit (Assertion, assertFailure, (@?=))

parseTestTerm :: Text -> Expr
parseTestTerm txt =
  case parseExpr (T.unpack txt) of
    Left err -> error ("Parser error in test: " ++ show err)
    Right e -> e

parseTestType :: Text -> Type
parseTestType txt =
  case parseType (T.unpack txt) of
    Left err -> error ("Parser error in test: " ++ show err)
    Right t -> t

parseTestKind :: Text -> Rkind
parseTestKind txt =
  case parseKind (T.unpack txt) of
    Left err -> error ("Parser error in test: " ++ show err)
    Right k -> k

assertVCValid :: Cstr -> IO Bool
assertVCValid c = do
  res <- checkValid c
  res @?= Valid
  pure True

assertVCInvalid :: Cstr -> IO Bool
assertVCInvalid c = do
  assertError (checkValid c)
  pure True

assertClosedValid :: Cstr -> Assertion
assertClosedValid constraint = do
  freeVariables constraint @?= []
  checkValid constraint >>= (@?= Valid)

assertClosedInvalid :: Cstr -> Assertion
assertClosedInvalid constraint = do
  freeVariables constraint @?= []
  assertError (checkValid constraint)

assertAccept :: Either a b -> Bool
assertAccept (Right _) = True
assertAccept (Left _) = False

assertReject :: Either a b -> Bool
assertReject (Left _) = True
assertReject (Right _) = False

check :: Context -> Type -> Rkind -> Cstr
check = Check.checkKind
synth :: Context -> Type -> (Cstr, Rkind)
synth = Check.synthKind
sub :: Context -> Rkind -> Rkind -> Cstr
sub = Check.sub
checkExpr :: Context -> Expr -> Type -> IO ()
checkExpr = ExprCheck.checkType

synthExpr :: Context -> Expr -> IO Type
synthExpr = ExprCheck.synthType

-- Generate the constraint attached to an actual universal domain. This is a
-- use-site obligation, not a standalone classifier-formation pass.
universalDomainConstraint :: Context -> Rkind -> Cstr
universalDomainConstraint ctx k =
  fst (Check.synthKind ctx (TForall "parameter" k TInt))
