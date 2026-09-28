{-# LANGUAGE OverloadedStrings #-}

module Suites.TermValidationSpec (tests, solverProbe) where

import ANF (elaborate)
import Check
import Context hiding (implicationConstraint)
import Suites.Common (checkExpr, synthExpr)
import Support.Universal (forallType)
import Test.Tasty
import Test.Tasty.HUnit
import Types
import Support.Errors (assertErrorContaining, captureError)

tests :: TestTree
tests = testGroup "Validated term judgments"
  [ testCase "literal synthesis returns its type directly" $
      synthType emptyContext (EInteger 1) >>= (@?= TInt)

  , testCase "annotation results remain unevaluated after ANF" $ do
      let written = (unaryTypeOp BRefOf) (TRef TInt)
          expression = EAnn (EInteger 1) written
      synthType emptyContext expression >>= (@?= elaborate written)
      synthExpr emptyContext expression >>= (@?= elaborate written)

  , testCase "application discharges its premises internally" $ do
      let function = EAnn (ELambda "x" (EBound 0)) (TArrow TInt TInt)
          ctx = addTermVar "argument" TInt emptyContext
      synthType ctx (EApp function (EVar "argument")) >>= (@?= TInt)

  , testCase "type application reports kind failure directly" $ do
      let domain = KBase BKRec
            (refinement "r" ((unaryPredOp BNot) ((unaryPredOp BEmpty (PBound 0)))))
          universal = forallType "R" domain TUnit
          ctx = addTermVar "poly" universal emptyContext
          nonempty = TRecCons (TLabel "field") TInt TRecNil
      synthType ctx (ETApp (EVar "poly") nonempty) >>= (@?= TUnit)
      assertErrorContaining "invalid-kind error"
        (synthType ctx (ETApp (EVar "poly") TRecNil))

  , testCase "recursive declarations validate their written type" $
      assertErrorContaining "unbound type variable" (checkType emptyContext
        (ELetRec "f" (TVar "Missing") EUnit EUnit) TUnit
        )

  , testCase "type-lambda refinements scope internal kind checks" $ do
      let domain = KBase BKType (refinement "a"
            ((binaryPredOp BEq (PBound 0) PInt)))
          expected = forallType "A" domain TInt
          expression = ETLambda "A" (EInteger 1)
      checkType emptyContext expression expected >>= (@?= ())
      checkExpr emptyContext expression expected >>= (@?= ())

  , testCase "alpha-equal fallback returns unit" $ do
      checkType emptyContext (EInteger 1) TInt >>= (@?= ())

  , testCase "universal subkinding is discharged inside conversion" $ do
      let sourceDomain = KBase BKType (refinement "a"
            ((binaryPredOp BEq (PBound 0) PInt)))
          equivalentDomain = KBase BKType (refinement "b"
            ((binaryPredOp BEq PInt (PBound 0))))
          source = forallType "A" sourceDomain (TBound 0)
          equivalent = forallType "B" equivalentDomain (TBound 0)
          broad = forallType "C" (bTrue BKType) (TBound 0)
          ctx = addTermVar "poly" source emptyContext
      checkType ctx (EVar "poly") equivalent >>= (@?= ())
      assertErrorContaining "invalid-kind error"
        (checkType ctx (EVar "poly") broad)

  , testCase "record formation rejects duplicate labels directly" $
      let rest = TRecCons (TLabel "a") TInt TRecNil
          ctx = addTermVar "rest" rest emptyContext
      in assertErrorContaining "duplicate record label: a" (synthType ctx
        (ERecordCons "a" (EInteger 1) (EVar "rest")))

  , testCase "neutral leaves are rejected structurally" $ do
      let kind = KBase BKType (refinement "a"
            ((binaryPredOp BEq (PBound 0) PInt)))
          ctx = addTermVar "x" (TVar "A")
            (addLocalTypeVar "A" kind emptyContext)
      assertErrorContaining "subtype error" (checkType ctx (EVar "x") TInt)
  ]

solverProbe :: String -> IO ()
solverProbe mode = do
  result <- captureError $ case mode of
    "kind" -> synthType emptyContext (EAnn EUnit (TVar "Missing"))
    _ -> synthType emptyContext EUnit
  putStrLn $ case result of
    Left message -> message
    Right value -> show value
