{-# LANGUAGE OverloadedStrings #-}
module Suites.SurfaceLoweringSpec (tests) where

import Test.Tasty
import Test.Tasty.HUnit

import ANF (elaborateExpr)
import Desugar (lowerExpr, lowerKind)
import Parser
import Types

tests :: TestTree
tests = testGroup "Surface to locally nameless core"
  [ testCase "surface parser retains named binders" $
      parseSurfaceExpr "fun x -> x" @?= Right (SELambda "x" (SEVar "x"))

  , testCase "compatibility parser lowers term binders" $
      parseExpr "fun x -> fun y -> x" @?=
        Right (ELambda "x" (ELambda "y" (EBound 1)))

  , testCase "nested shadowing selects the nearest binder" $
      lowerExpr (SELambda "x" (SELambda "x" (SEVar "x"))) @?=
        ELambda "x" (ELambda "x" (EBound 0))

  , testCase "term and type namespaces may share spelling" $
      lowerExpr (SELambda "x" (SETLambda "x" (SEAnn (SEVar "x") (STVar "x")))) @?=
        ELambda "x" (ETLambda "x" (EAnn (EBound 0) (TBound 0)))

  , testCase "refinement and type binders use distinct indices" $
      lowerKind
        (SKPi "a" (surfaceBase SBKType)
          (SKBase SBKType (SRefined "v"
            (binarySurfacePredOp BEq (SPVar "v") (SPVar "a"))))) @?=
        KPi "a" (bTrue BKType)
          (KBase BKType (refinement "v"
            ((binaryPredOp BEq (PBound 0) (PTypeBound 0)))))

  , testCase "free variables remain named" $
      lowerExpr (SELambda "x" (SEApp (SEVar "free") (SEVar "x"))) @?=
        ELambda "x" (EApp (EVar "free") (EBound 0))

  , testCase "label nodes survive surface lowering" $ do
      lowerExpr (SELabel "field") @?= ELabel "field"
      lowerExpr (SEHeadLabel (SEVar "row")) @?=
        EHeadLabel (EVar "row")

  , testCase "constructors stay native while selectors lower to operations" $ do
      parseSurfaceType "TRef TInt" @?= Right (STRef STInt)
      parseSurfaceType "refOf (TRef TInt)" @?=
        Right (STRefOf (STRef STInt))
      parseSurfaceType "TCol TBool" @?= Right (STCol STBool)
      parseSurfaceType "colOf (TCol TBool)" @?=
        Right (STColOf (STCol STBool))
      parseType "TRef TInt" @?= Right (TRef TInt)
      parseType "refOf (TRef TInt)" @?= Right ((unaryTypeOp BRefOf) (TRef TInt))
      parseType "TCol TBool" @?= Right (TCol TBool)
      parseType "colOf (TCol TBool)" @?= Right ((unaryTypeOp BColOf) (TCol TBool))

  , testCase "ANF names avoid existing free names" $ do
      let normalized = elaborateExpr (EApp (EApp (EVar "x0") EUnit) EUnit)
      case normalized of
        ELet generated _ _ -> assertBool "generated name is fresh" (generated /= "x0")
        other -> assertFailure ("expected an introduced let, got " ++ show other)

  , testCase "core term alpha equivalence ignores binder hints" $
      assertBool "locally nameless lambdas are alpha equivalent"
        (alphaEqExpr (ELambda "x" (EBound 0)) (ELambda "y" (EBound 0)))
  ]

surfaceBase :: SBaseKind -> SKind
surfaceBase base = SKBase base (SRefined "v" SPTrue)
