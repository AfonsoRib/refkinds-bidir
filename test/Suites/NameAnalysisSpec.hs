{-# LANGUAGE OverloadedStrings #-}
module Suites.NameAnalysisSpec (tests) where

import Constraint
import Substitution
import Test.Tasty
import Test.Tasty.HUnit
import Types hiding
  ( allExprNames, allKindNames, allTypeNames, freeNames, freeTypeVariables
  , freshName
  )

tests :: TestTree
tests = testGroup "Name analysis"
  [ testCase "free logical namespaces remain distinct" $ do
      let predicate = (binaryPredOp BEq (PVar "same") (PRefVar "same"))
      freeNames predicate @?= [TypeSymbol "same", RefSymbol "same"]

  , testCase "bound indices and display hints are not free names" $ do
      let ty = TLambda "hint" (TArrow (TBound 0) (TVar "Free"))
      freeTypeVariables ty @?= ["Free"]
      freeNames (KBase BKType
        (Refined "witness" ((binaryPredOp BEq (PBound 0) (PVar "Free"))))) @?=
        [TypeSymbol "Free"]

  , testCase "occupied type names preserve traversal order" $ do
      let ty = TForall "A"
            (KBase BKType (Refined "v" (PVar "Outer")))
            (TLet (Decl "B" (TVar "Definition")) (TVar "Body"))
      allTypeNames ty @?= ["v", "Outer", "A", "Definition", "B", "Body"]

  , testCase "occupied names cover every type and kind binder" $ do
      let ty = TLambda "lambda"
            (TRec "recursive" (TVar "definition")
              (TLet (Decl "local" (TVar "tested")) (TVar "success")))
          kind = KPi "pi"
            (KBase BKType (Refined "domain" (PVar "DomainFree")))
            (KGen "generalized"
              (KBase BKType (Refined "parameter" PTrue))
              (KBase BKType (Refined "result"
                ((binaryPredOp BEq (PVar "Definition") (PVar "Body"))))))
      allTypeNames ty @?=
        ["lambda", "recursive", "definition", "tested", "local", "success"]
      allKindNames kind @?=
        [ "domain", "DomainFree", "pi", "parameter", "generalized"
        , "result", "Definition", "Body"
        ]

  , testCase "expression names include embedded types and term binders" $ do
      let expression = ELetRec "f" (TVar "A") (EVar "definition")
            (ETLambda "T" (ETApp (EVar "body") (TVar "B")))
      allExprNames expression @?=
        ["A", "f", "definition", "T", "body", "B"]
      freeNames expression @?= [TypeSymbol "A", TypeSymbol "B"]

  , testCase "expression name analysis covers remaining binders and type fields" $ do
      let scoped = ELambda "lambda"
            (ELet "let" (EVar "definition") (EVar "body"))
      allExprNames scoped @?= ["lambda", "definition", "let", "body"]
      let restored = ERecordCons "field" (EHeadLabel (EVar "row"))
            (ELabel "field")
      allExprNames restored @?= ["row"]
      freeNames restored @?= []

  , testCase "fresh names are deterministic" $ do
      freshName ["x", "x0"] @?= "x1"
      freshName ["x", "x0"] @?= freshName ["x", "x0"]

  , testCase "CAll removes only its matching logical name" $ do
      let constraint = CAll
            (Bind (TypeSymbol "same") BKType
              ((binaryPredOp BEq (PVar "same") (PRefVar "same"))))
            (CPred ((binaryPredOp BEq (PVar "same") (PVar "outside"))))
      freeNames constraint @?=
        [RefSymbol "same", TypeSymbol "outside"]
  ]
