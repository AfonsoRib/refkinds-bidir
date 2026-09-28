{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}

module Suites.LocallyNamelessSpec (tests) where

import Test.Tasty
import Test.Tasty.HUnit
import Check (checkType)
import Support.Errors (assertError)
import Support.Universal (forallType)
import Context hiding (implicationConstraint)
import Substitution
import Types hiding
  ( abstractKind, abstractType, closeExprType, freeNames, freeTypeVariables
  , instantiateExprType, instantiateKindAt, instantiatePiKind, instantiateType
  , instantiateTypeBody, openExprTerm
  , shiftRefinementIndices, shiftTypeIndices, unabstractKind, unabstractType
  )
import Suites.Common (parseTestKind, parseTestType)
import Support.AstInvariants (validateExprAst, validateKindAst, validateTypeAst)

tests :: TestTree
tests = testGroup "Locally Nameless Semantics"
  [ testCase "outer-binder substitution covers every core category" $ do
      substitute TInt (TBound 0) @?= TInt
      substitute TInt
        (KBase BKType (Refined "v"
          ((binaryPredOp BEq) (PBound 0) (PTypeBound 0)))) @?=
        KBase BKType (Refined "v"
          ((binaryPredOp BEq) (PBound 0) PInt))
      substitute PInt
        ((binaryPredOp BEq) (PBound 0) PBool) @?=
        (binaryPredOp BEq) PInt PBool
      substitute (EInteger 7) (EBound 0) @?= EInteger 7
      substitute TInt (EAnn EUnit (TBound 0)) @?= EAnn EUnit TInt

  , testCase "alpha-equivalent type lambdas" $ do
      let lamX = parseTestType "fun x -> x"
          lamY = parseTestType "fun y -> y"
      assertBool "lam x -> x == lam y -> y" (alphaEq lamX lamY)

  , testCase "nested alpha-equivalent binders" $ do
      let body1 = parseTestType "fun x -> fun y -> x y"
          body2 = parseTestType "fun u -> fun v -> u v"
      assertBool "nested lambdas are alpha-equivalent" (alphaEq body1 body2)

  , testCase "free variables remain name-sensitive" $ do
      let tyX = parseTestType "x"
          tyY = parseTestType "y"
      assertBool "free x /= free y" (not (alphaEq tyX tyY))

  , testCase "named and indexed bound variables agree" $ do
      let closed = abstractType "x" (TVar "x")
      assertEqual "abstractType x (TVar x) is TBound 0" (TBound 0) closed
      let opened = unabstractType "y" closed
      assertEqual "unabstractType y (TBound 0) is TVar y" (TVar "y") opened

  , testCase "kind and refinement binders are alpha-equivalent" $ do
      let k1 = parseTestKind "{ v1 :: KType | v1 == TInt }"
          k2 = parseTestKind "{ v2 :: KType | v2 == TInt }"
      assertBool "refinement kinds are alpha-equivalent" (alphaEqKind k1 k2)

  , testCase "different bound indices are not alpha-equivalent" $ do
      assertBool "bvar 0 /= bvar 1" (not (alphaEq (TBound 0) (TBound 1)))

  , testCase "free variable set calculation" $ do
      let ty = parseTestType "x (fun y -> x y)"
          fvs = freeTypeVariables ty
      assertEqual "free vars of ty is [x]" ["x"] fvs
  , testCase "core display hints do not bind free type variables" $ do
      let free = TLambda "x" (TVar "x")
      freeTypeVariables free @?= ["x"]
      alphaEq free (TLambda "y" (TVar "y")) @?= False
      alphaEq free (TLambda "y" (TVar "x")) @?= True
      alphaEq (TLambda "x" (TBound 0)) (TLambda "y" (TBound 0)) @?= True

  , testCase "core display hints do not bind free term variables" $ do
      let free = ELambda "x" (EVar "x")
      alphaEqExpr free (ELambda "y" (EVar "y")) @?= False
      alphaEqExpr free (ELambda "y" (EVar "x")) @?= True
      alphaEqExpr (ELambda "x" (EBound 0)) (ELambda "y" (EBound 0)) @?= True

  , testCase "type opening lifts captures under nested binders" $ do
      instantiateType (TBound 0) (TLambda "inner" (TBound 1))
        @?= Right (TLambda "inner" (TBound 1))
      let original = forallType "inner" (KPi "a" (bTrue BKType)
            (KBase BKType (refinement "v"
              ((binaryPredOp BEq (PBound 0) (PVar "outer"))))))
            (TArrow (TVar "outer") (TBound 0))
      unabstractType "outer" (abstractType "outer" original) @?= original

  , testCase "type shifts preserve refinement indices and visit annotations" $ do
      let k = KBase BKType (refinement "v"
            ((binaryPredOp BEq (PBound 0) (PTypeBound 0))))
      shiftTypeIndices 0 1 (TAnn TInt k) @?=
        TAnn TInt (KBase BKType (refinement "v"
          ((binaryPredOp BEq (PBound 0) (PTypeBound 1)))))
      shiftRefinementIndices 0 1 (TBound 0) @?= TBound 0

  , testCase "free names cross recursive and dependent hints" $ do
      let body = TRec "x" (TVar "x") (TLambda "x" (TVar "x"))
      freeTypeVariables body @?= ["x"]
  , testCase "free refinement names cannot be captured by type hints" $ do
      let k = KBase BKType (Refined "v"
            ((binaryPredOp BEq (PVar "x") (PRefVar "x"))))
      freeNames k @?= [TypeSymbol "x", RefSymbol "x"]

  , testCase "opening never substitutes a core binder hint" $ do
      openExprTerm EUnit (EVar "x") @?= EVar "x"
      instantiateExprType TInt (EAnn EUnit (TVar "A")) @?=
        Right (EAnn EUnit (TVar "A"))

  , testCase "refinement hints do not bind free type names" $ do
      let k = KBase BKType (refinement "x"
            ((binaryPredOp BEq (PBound 0) (PVar "x"))))
      freeNames k @?= [TypeSymbol "x"]

  , testCase "term opening lifts indices" $ do
      let replacement = EAnn (EBound 0) (TBound 0)
      openExprTerm replacement (ELambda "term" (ETLambda "type" (EBound 1))) @?=
        ELambda "term" (ETLambda "type" (EAnn (EBound 1) (TBound 1)))

  , testCase "type opening crosses term annotations safely" $ do
      instantiateExprType (TBound 0)
        (ETLambda "inner" (EAnn EUnit (TBound 1))) @?=
        Right (ETLambda "inner" (EAnn EUnit (TBound 1)))
      let original = ETLambda "A" (EAnn EUnit
            (forallType "B" (KBase BKType (refinement "r"
              ((binaryPredOp BEq (PBound 0) (PVar "free"))))) (TVar "free")))
      instantiateExprType (TVar "free") (closeExprType "free" original) @?= Right original

  , testCase "test instrumentation rejects exposed indices" $ do
      mapM_ (assertRejected . validateTypeAst) [TBound 0, TBound (-1)]
      assertRejected (validateExprAst (EBound 0))
      assertRejected (validateKindAst
        (KBase BKType (refinement "r"
          ((binaryPredOp BEq (PBound 1) PInt)))))

  , testCase "Pi instantiation with a variable equals named opening" $ do
      let codomain = KBase BKType
            (refinement "v" ((binaryPredOp BEq (PBound 0) (PTypeBound 0))))
          piKind = KPi "parameter" (bTrue BKType) codomain
      instantiatePiKind (TVar "Argument") piKind @?=
        Right (unabstractKind "Argument" codomain)

  , testCase "simultaneous opening preserves order and avoids capture" $ do
      instantiateTypeBody [TInt, TBool]
        (TLambda "z" (TArrow (TBound 2) (TArrow (TBound 1) (TBound 0)))) @?=
        Right (TLambda "z" (TArrow TInt (TArrow TBool (TBound 0))))
      instantiateType (TBound 0) (TLambda "z" (TBound 1)) @?=
        Right (TLambda "z" (TBound 1))

  , testCase "actual type instantiation remains lazy and fallible" $ do
      let computation = TLambda "a" (TBound 0)
          indexed = KBase BKType
            (refinement "v" ((binaryPredOp BEq (PBound 0) (PTypeBound 0))))
      case instantiateKindAt 0 computation indexed of
        Left _ -> pure ()
        Right _ -> assertFailure "unsupported replacement accepted"
      instantiateType computation
        (TAnn TInt (KBase BKType
          (refinement "v" ((binaryPredOp BEq (PBound 0) PInt))))) @?=
        Right (TAnn TInt (KBase BKType
          (refinement "v" ((binaryPredOp BEq (PBound 0) PInt)))))

  , testCase "raw annotations reject unbound names and non-Boolean predicates" $ do
      mapM_ assertError
        [ checkType emptyContext
            (EAnn EUnit (TArrow (TVar "Missing") (TVar "Missing"))) TUnit
        , checkType emptyContext
            (EAnn EUnit
              (TAnn TUnit (KBase BKType (refinement "v" PInt)))) TUnit
        ]

  ]
  where
    assertRejected result = case result of
      Left _ -> pure ()
      Right () -> assertFailure "expected malformed AST rejection"
