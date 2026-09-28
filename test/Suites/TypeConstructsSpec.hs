{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}

module Suites.TypeConstructsSpec (tests) where

import Test.Tasty
import Test.Tasty.HUnit
import Context hiding (implicationConstraint)
import Constraint (cPred)
import Types
import Check hiding (sub)
import Suites.Common
import qualified Control.Exception as Exception
import Support.Errors (assertError, assertPureError)

tests :: TestTree
tests = testGroup "Under-Tested Type Constructs"
  [ testGroup "Function Destructors (TDom, TImg)"
      [ testCase "synth TDom synthesizes Type kind with valid VC" $ do
          let (c, kd) = synth emptyContext
                (parseTestType "dom (TInt -> TBool)")
          _ <- assertVCValid c
          case kd of
            KBase BKType _ -> pure ()
            other -> assertFailure ("Expected refined Type kind, got: " ++ show other)

      , testCase "synth TImg synthesizes Type kind with valid VC" $ do
          let (c, kd) = synth emptyContext
                (parseTestType "img (TInt -> TBool)")
          _ <- assertVCValid c
          case kd of
            KBase BKType _ -> pure ()
            other -> assertFailure ("Expected refined Type kind, got: " ++ show other)

      , testCase "synth TDom rejects non-function types structurally" $ do
          assertPureError (synth emptyContext (parseTestType "dom TInt"))

      , testCase "synth TImg rejects non-function types structurally" $ do
          assertPureError (synth emptyContext (parseTestType "img [||]"))

      , testCase "semantic equality for TDom and TImg" $ do
          checkTypeEquality emptyContext (bTrue BKType)
            (parseTestType "dom (TBool -> TUnit)") TBool
          checkTypeEquality emptyContext (bTrue BKType)
            (parseTestType "img (TBool -> TUnit)") TUnit
      ]

  , testGroup "Reference Destructor (TRefOf)"
      [ testCase "synth TRefOf synthesizes Type kind with valid VC" $ do
          let (c, kd) = synth emptyContext
                (parseTestType "refOf (TRef TBool)")
          _ <- assertVCValid c
          case kd of
            KBase BKType _ -> pure ()
            other -> assertFailure ("Expected refined Type kind, got: " ++ show other)

      , testCase "synth TRefOf rejects non-reference types structurally" $ do
          assertPureError (synth emptyContext (parseTestType "refOf TInt"))

      , testCase "semantic equality for TRefOf" $ do
          checkTypeEquality emptyContext (bTrue BKType)
            (parseTestType "refOf (TRef TBool)") TBool
      ]

  , testGroup "Collection Type & Destructor (TCol, TColOf)"
      [ testCase "synth TCol synthesizes Col kind with valid VC" $ do
          let (c, kd) = synth emptyContext (parseTestType "TCol TInt")
          _ <- assertVCValid c
          case kd of
            KBase BKCol _ -> pure ()
            other -> assertFailure ("Expected refined Col kind, got: " ++ show other)

      , testCase "synth TColOf synthesizes Type kind with valid VC" $ do
          let (c, kd) = synth emptyContext
                (parseTestType "colOf (TCol TBool)")
          _ <- assertVCValid c
          case kd of
            KBase BKType _ -> pure ()
            other -> assertFailure ("Expected refined Type kind, got: " ++ show other)

      , testCase "synth TColOf rejects non-collection types structurally" $ do
          assertPureError (synth emptyContext (parseTestType "colOf TBool"))

      , testCase "semantic equality for TColOf" $ do
          checkTypeEquality emptyContext (bTrue BKType)
            (parseTestType "colOf (TCol TUnit)") TUnit
      ]

  , testGroup "Type-Level Conditionals (TIf)"
      [ testCase "check TIf verifies branches under explicit guards" $ do
          let cond = parseTestType "if TInt == TInt then TInt else TInt"
          _ <- assertVCValid (check emptyContext cond (bTrue BKType))
          pure ()
      ]

  , testGroup "Type Annotation (TAnn)"
      [ testCase "synth TAnn synthesizes annotated kind" $ do
          let ann = parseTestType "TInt :: KType"
          let (c, kd) = synth emptyContext ann
          _ <- assertVCValid c
          assertEqual "Synthesized annotated kind" (bTrue BKType) kd

      , testCase "synth TAnn rejects invalid kind annotations structurally" $ do
          let ann = parseTestType "TInt :: KRec"
          assertPureError (synth emptyContext ann)
      ]

  , testGroup "Type-Level Recursion (TRec)"
      [ testCase "recursive type definition is admitted" $ do
          let recTy = parseTestType "letrec F :: Pi X :: KType. KType = fun X -> X in F TInt"
          _ <- assertVCValid (checkRaw emptyContext recTy (bTrue BKType))
          pure ()
      ]

  , testGroup "Primitive Types (TUnit, TBool)"
      [ testCase "synth TUnit synthesizes refined Type kind" $ do
          let (c, _) = synth emptyContext (parseTestType "TUnit")
          _ <- assertVCValid c
          pure ()

      , testCase "synth TBool synthesizes refined Type kind" $ do
          let (c, _) = synth emptyContext (parseTestType "TBool")
          _ <- assertVCValid c
          pure ()

      , testCase "synthExpr on EUnit and EBoolean" $ do
          synthExpr emptyContext (parseTestTerm "()") >>= (@?= TUnit)
          synthExpr emptyContext (parseTestTerm "True") >>= (@?= TBool)
      ]

  , testGroup "Predicate interpreted record concatenation"
      [ testCase "IConcat computes a disjoint record for the solver" $ do
          let left = PRecCons (PLabel "p") PInt PRecNil
              right = PRecCons (PLabel "q") PBool PRecNil
              result = PRecCons (PLabel "p") PInt right
          valid <- assertVCValid (cPred
            ((binaryPredOp BEq ((binaryPredOp BConcat left right)) result)))
          assertBool "interpreted concatenation VC valid" valid
      ]

  , testGroup "Type Record Concatenation (TConcat)"
      [ testCase "TConcat synthesizes a refined record kind" $ do
          let (constraint, inferred) = synth emptyContext
                (parseTestType "[| `p : TInt |] @ [| `q : TBool |]")
          _ <- assertVCValid constraint
          case inferred of
            KBase BKRec _ -> pure ()
            other -> assertFailure
              ("Expected refined Rec kind, got: " ++ show other)

      , testCase "empty TConcat reduces to TRecNil" $
          checkTypeEquality emptyContext (bTrue BKRec)
            ((binaryTypeOp BConcat) TRecNil TRecNil) TRecNil >>= (@?= ())
      ]
  ]
