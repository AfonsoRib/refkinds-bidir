{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE BlockArguments #-}

module Suites.TypeCheckerSpec (tests) where

import Parser (parseKind)
import Test.Tasty
import Test.Tasty.HUnit
import Constraint
import Context
import Types
import Check (synthRaw, checkRaw)
import Suites.Common
import qualified Control.Exception as Exception
import Support.Errors (assertError, assertPureError)

tests :: TestTree
tests = testGroup "Type Checker and Synthesis"
  [ testCase "synthesis of base types" (do
      let (c, kd) = synth emptyContext (parseTestType "TInt")
      valid <- assertVCValid c
      assertBool "VC valid" valid
      assertBool ("Expected refined Type kind, got: " ++ show kd)
        (case kd of { KBase BKType _ -> True; _ -> False }))

  , testCase "string types synthesize singleton kinds" (do
      let (_, actual) = synth emptyContext TString
      actual @?= KBase BKType (refinement "v"
        ((binaryPredOp BEq (PBound 0) PString)))
      let good = checkRaw emptyContext TString
            (parseTestKind "{ v :: KType | v == TString }")
      assertClosedValid good
      let bad = checkRaw emptyContext TString
            (parseTestKind "{ v :: KType | v == TInt }")
      assertClosedInvalid bad
      let alias = checkRaw emptyContext
            (parseTestType "let Text = TString in Text")
            (parseTestKind "{ v :: KType | v == TString }")
      assertClosedValid alias)

  , testCase "type lets require a checking goal" $ do
      mapM_ (\(source, goal) -> do
        let ty = parseTestType source
        assertPureError (synthRaw emptyContext ty)
        let vc = checkRaw emptyContext ty (parseTestKind goal)
        assertClosedValid vc)
        [ ("let X = TInt in X", "{ v :: KType | v == TInt }")
        , ("let X = TInt in let X = TBool in X", "{ v :: KType | v == TBool }")
        , ("let X = TString in fun Y -> X", "Pi Y :: KType. { v :: KType | v == TString }")
        ]
      let bad = checkRaw emptyContext
            (parseTestType "let X = TInt in X")
            (parseTestKind "{ v :: KType | v == TBool }")
      assertClosedInvalid bad

  , testCase "guarded obligations avoid context and expected-kind names" $ do
      let body = cPred ((binaryPredOp BEq (PVar "guard") (PVar "targetOnly")))
          guard = (unaryPredOp BEmpty (PVar "q"))
      case cGuard ["guard0"] guard body of
        CAll (Bind name _ predicate) obligation -> do
          assertBool "dummy is fresh" (logicNameText name `notElem` (freeVariables predicate ++ freeVariables obligation ++ ["guard0"]))
        _ -> assertFailure "missing guard"
      let ctx = addTypeVar "q" (bTrue BKRec) emptyContext
      let vc = checkRaw ctx
            (parseTestType "if not empty q then head q else TInt") (bTrue BKType)
      assertClosedValid (cAll (bind "q" BKRec PTrue) vc)
      let bad = checkRaw ctx
            (parseTestType "if empty q then head q else TInt") (bTrue BKType)
      assertClosedInvalid (cAll (bind "q" BKRec PTrue) bad)

  , testCase "unannotated type lambda rejects synthesis" $ do
      let lam = parseTestType "fun X -> X"
      assertPureError (synth emptyContext lam)

  , testCase "unannotated type lambda checks against Pi kind" $ do
      let lam = parseTestType "fun X -> X"
          piKind = parseTestKind "Pi X :: KType. KType"
      case check emptyContext lam piKind of
        c -> do
          valid <- assertVCValid c
          assertBool "Identity type lambda checks against Pi X:Type. Type" valid

  , testCase "multi-argument type application preserves the remaining Pi kind" $ do
      let mapKind = parseTestKind
            "Pi row :: KRec. Pi transform :: (Pi field :: KType. KType). { mapped :: KRec | labels mapped == labels row }"
          expected = parseTestKind
            "Pi transform :: (Pi field :: KType. KType). { mapped :: KRec | labels mapped == labels Row }"
          ctx = addTypeVar "Map" mapKind (addTypeVar "Row" (bTrue BKRec) emptyContext)
      case synth ctx (parseTestType "Map Row") of
        (constraint, actual) -> do
          assertBool "remaining dependent Pi kind is instantiated" (alphaEqKind expected actual)
          valid <- assertVCValid constraint
          assertBool "partial application VC is valid" valid

  , testCase "ANF temporaries cannot capture nested type-lambda binders" $ do
      let body = parseTestType
            "fun row -> fun transform -> if empty row then [||] else [| \"fixed\" : transform (head row) |]"
          kind = parseTestKind
            "Pi row :: KRec. Pi transform :: (Pi field :: KType. KType). KRec"
      case checkRaw emptyContext body kind of
        constraint -> do
          valid <- assertVCValid constraint
          assertBool "nested transformed-row lambda VC is valid" valid

  , testCase "record type synthesis" $ do
      let recTy = parseTestType "[| `p : TInt |]"
      case synth emptyContext recTy of
        (c, kd) -> do
          valid <- assertVCValid c
          assertBool "VC valid" valid
          case kd of
            KBase BKRec _ -> pure ()
            other -> assertFailure ("Expected refined Rec kind, got: " ++ show other)

  , testCase "reference type synthesis" $ do
      let refTy = parseTestType "TRef TInt"
      case synth emptyContext refTy of
        (c, kd) -> do
          valid <- assertVCValid c
          assertBool "VC valid" valid
          case kd of
            KBase BKRef _ -> pure ()
            other -> assertFailure ("Expected refined Ref kind, got: " ++ show other)

  , testCase "forall polymorphic type synthesis yields Gen K" $ do
      let allTy = parseTestType "((forall X :: KType. X -> X) :: KGen X :: KType. KType)"
      case synth emptyContext allTy of
        (c, kdSynth) -> do
          valid <- assertVCValid c
          assertBool "forallType VC valid" valid
          assertEqual "Synthesizes the outer annotation"
            (KGen "X" (bTrue BKType) (bTrue BKType)) kdSynth

  , testCase "quantified refinements close their binder and reject false equality" $ do
      let ty = parseTestType "forall X :: { r :: KRec | not (empty r) }. ((X -> head X) :: KFun)"
      let vc = checkRaw emptyContext ty
            (parseTestKind "KGen X :: {r :: KRec | not (empty r)}. KFun")
      assertClosedValid vc
      assertError (Exception.evaluate (checkRaw emptyContext ty
        (parseTestKind "{ t :: KType | t == TInt }")))

  , testCase "applications use declared precision and validate their domain" $ do
      let weak = parseTestType "let Id :: Pi X :: KType. KType = fun X -> X in fun Y -> Id Y"
          ty = parseTestType "let Id :: Pi X :: KType. { r :: KType | r == X } = fun X -> X in fun Y -> Id Y"
      let weakVC = checkRaw emptyContext weak
            (parseTestKind "Pi Y :: KType. { r :: KType | r == Y }")
      assertClosedInvalid weakVC
      let good = checkRaw emptyContext ty
            (parseTestKind "Pi Y :: KType. { r :: KType | r == Y }")
      assertClosedValid good
      let bad = checkRaw emptyContext ty
            (parseTestKind "Pi Y :: KType. { r :: KType | r == TInt }")
      assertClosedInvalid bad
      let invalid = parseTestType "let Id :: Pi X :: { t :: KType | t == TInt }. KType = fun X -> X in Id TBool"
      let invalidVC = checkRaw emptyContext invalid (bTrue BKType)
      assertClosedInvalid invalidVC

  , testCase "a selector result depends on its declared source contract" $ do
      let program = "let First :: Pi row :: { r :: KRec | not (empty r) }. { v :: KType | v == head row } = fun row -> head row in First Fields"
          goal = parseTestKind "{ v :: KType | v == TString }"
          weak = parseTestKind "{ r :: KRec | not (empty r) }"
          strong = parseTestKind "{ r :: KRec | r == [| `field : TString |] }"
      mapM_ (\(kind, validate) -> do
        let vc = checkRaw
              (addTypeVar "Fields" kind emptyContext) (parseTestType program) goal
            scoped = implicationConstraint "Fields" kind vc
        validate scoped)
        [(weak, assertClosedInvalid), (strong, assertClosedValid)]

  , testCase "refinements reject user type applications before reduction" $
      mapM_ (\label -> assertBool "application rejected by predicate parser" (assertReject
        (parseKind ("{ x :: KRec | member (((fun x -> x) :: Pi x :: KLabel. KLabel) " ++ label ++ ") x }"))))
        ["`p", "`q"]

  , testCase "forall checks at KGen and plain KType" $ do
      let allTy = parseTestType "((forall X :: KType. X -> X) :: KGen X :: KType. KType)"
      assertClosedValid (check emptyContext allTy (bTrue BKType))
      assertClosedValid
        (check emptyContext allTy (parseTestKind "KGen X :: KType. KType"))

  , testCase "type conditional with contradictory branches fails solver validation" $ do
      let cond = parseTestType "if TInt == TInt then TInt else TBool"
          goal = parseTestKind "{ v :: KType | v == TBool }"
      case check emptyContext cond goal of
        c -> do
          invalid <- assertVCInvalid c
          assertBool "Contradictory TIf branch rejected by solver" invalid
  ]
