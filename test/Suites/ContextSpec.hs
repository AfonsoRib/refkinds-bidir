{-# LANGUAGE OverloadedStrings #-}

module Suites.ContextSpec (tests) where

import qualified Control.Exception as Exception
import qualified Constraint as C
import qualified Context as Ctx
import qualified Prims as P
import qualified Test.Tasty as Tasty
import qualified Test.Tasty.HUnit as HUnit
import qualified Types as T
import qualified Support.Errors as Errors

tests :: Tasty.TestTree
tests = Tasty.testGroup "Checker context"
  [ HUnit.testCase "empty context has no entries or lookups" $ do
      Ctx.ctxEnv Ctx.emptyContext HUnit.@?= []
      Ctx.ctxTermEnv Ctx.emptyContext HUnit.@?= []
      Ctx.ctxProofBinders Ctx.emptyContext HUnit.@?= []
      Ctx.lookupKind "missing" Ctx.emptyContext HUnit.@?= Nothing
      Ctx.lookupTermVar "missing" Ctx.emptyContext HUnit.@?= Nothing

  , HUnit.testCase "type entries store kinds and newer entries shadow older ones" $ do
      let typeKind = P.bTrue T.BKType
          functionKind = T.KPi "A" typeKind typeKind
          typeContext = Ctx.addTypeVar "Alias" typeKind
            (Ctx.addTypeVar "Alias" functionKind Ctx.emptyContext)
          termContext = Ctx.addTermVar "value" T.TBool
            (Ctx.addTermVar "value" T.TInt typeContext)
      Ctx.ctxEnv typeContext HUnit.@?=
        [ ("Alias", Ctx.KindEntry typeKind)
        , ("Alias", Ctx.KindEntry functionKind)
        ]
      Ctx.lookupKind "Alias" typeContext HUnit.@?= Just typeKind
      Ctx.lookupTermVar "value" termContext HUnit.@?= Just T.TBool

  , HUnit.testCase "only local type entries enter proof scope" $ do
      let kind = P.bTrue T.BKType
          ambient = Ctx.addTypeVar "Ambient" kind Ctx.emptyContext
          local = Ctx.addLocalTypeVar "Local" kind ambient
      Ctx.ctxProofBinders ambient HUnit.@?= []
      Ctx.ctxProofBinders local HUnit.@?= [("Local", kind)]

  , HUnit.testCase "freshness includes classifier and term dependencies" $ do
      let kind = T.KBase T.BKType
            (T.Refined "v" (T.binaryPredOp T.BEq
              (T.PBound 0) (T.PVar "kindDependency")))
          context = Ctx.addLocalTypeVar "local" kind
            (Ctx.addTypeVar "alias" (P.bTrue T.BKType)
              (Ctx.addTermVar "term" (T.TVar "termDependency")
                Ctx.emptyContext))
          names = Ctx.contextFreshNames context
      mapM_ (\name -> HUnit.assertBool ("missing " ++ name)
        (name `elem` names))
        [ "local", "alias", "term", "kindDependency", "termDependency" ]

  , HUnit.testCase "nonbase proof parameters reject residual uses" $ do
      let typeKind = P.bTrue T.BKType
          piKind = T.KPi "A" typeKind typeKind
          genKind = T.KGen "A" typeKind typeKind
          unused = C.cPred ((T.binaryPredOp T.BEq (T.PVar "Other") T.PInt))
          used name = C.cPred ((T.binaryPredOp T.BEq (T.PVar name) T.PInt))
      Ctx.implicationConstraint "F" piKind unused HUnit.@?= unused
      Ctx.implicationConstraint "G" genKind unused HUnit.@?= unused
      assertUnsupported
        (Ctx.implicationConstraint "F" piKind (used "F"))
      assertUnsupported
        (Ctx.implicationConstraint "G" genKind (used "G"))
  ]

assertUnsupported :: Show a => a -> HUnit.Assertion
assertUnsupported value = Errors.assertError (Exception.evaluate value)
