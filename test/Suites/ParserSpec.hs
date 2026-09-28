{-# LANGUAGE OverloadedStrings #-}

module Suites.ParserSpec (tests) where

import Test.Tasty
import Parser (parseType, parseExpr, parsePred)
import Test.Tasty.HUnit
import Types
import Suites.Common

tests :: TestTree
tests = testGroup "Parser and Lexer"
  [ testCase "parse term annotation" $ do
      let term = parseTestTerm "(42 : TInt)"
      case term of
        EAnn (EInteger 42) TInt -> pure ()
        other -> assertFailure ("Unexpected term: " ++ show other)

  , testCase "parse type kind annotation" $ do
      let ty = parseTestType "(TInt :: KType)"
      case ty of
        TAnn TInt (KBase BKType _) -> pure ()
        other -> assertFailure ("Unexpected type: " ++ show other)

  , testCase "parse unannotated lambda" $ do
      let tm = parseTestTerm "fun x -> x"
      case tm of
        ELambda "x" (EBound 0) -> pure ()
        other -> assertFailure ("Unexpected term: " ++ show other)

  , testCase "parse record type" $ do
      let ty = parseTestType "[| `p : TInt, `q : TBool |]"
      case ty of
        TRecCons (TLabel "p") TInt (TRecCons (TLabel "q") TBool TRecNil) -> pure ()
        other -> assertFailure ("Unexpected type: " ++ show other)

  , testCase "parse label term syntax" $ do
      parseExpr "`field" @?= Right (ELabel "field")
      parseExpr "headLabel [field = 1]" @?=
        Right (EHeadLabel (ERecordCons "field" (EInteger 1) ERecordNil))

  , testCase "record fields require static labels" $ do
      mapM_ (assertRejected . parseExpr)
        [ "[(`field) = 1]"
        , "[(let L = `field in L) = 1]"
        ]

  , testCase "former collection words are ordinary identifiers" $ do
      parseExpr "nil" @?= Right (EVar "nil")
      parseExpr "cons 1 nil" @?=
        Right (EApp (EApp (EVar "cons") (EInteger 1)) (EVar "nil"))

  , testCase "iftype is an ordinary identifier" $ do
      parseExpr "iftype" @?= Right (EVar "iftype")
      parseExpr "iftype 1" @?= Right (EApp (EVar "iftype") (EInteger 1))

  , testCase "former connective words are ordinary identifiers" $ do
      parseExpr "implies" @?= Right (EVar "implies")
      parseExpr "iff" @?= Right (EVar "iff")
      parseExpr "as" @?= Right (EVar "as")

  , testCase "retired kind-case syntax is rejected" $ do
      mapM_ (assertRejected . parseType)
        [ "if TInt :: KType as A then A else TBool"
        , "if TInt :: {a :: KType | a == TInt} as A then A else TBool"
        ]
      assertRejected (parseExpr "if TInt :: KType as A then 1 else 0")

  , testCase "parse refinement kind" $ do
      let kd = parseTestKind "{ r :: KRec | not empty(r) }"
      case kd of
        KBase BKRec (Refined "r"
          (PInterp1 BNot (PInterp1 BEmpty (PBound 0)))) -> pure ()
        other -> assertFailure ("Unexpected kind: " ++ show other)

  , testCase "kind arrows associate right and Pi bodies extend right" $ do
      parseTestKind "KType -> KBool -> KLabel" @?=
        KPi "_" (bTrue BKType) (KPi "_" (bTrue BKBool) (bTrue BKLabel))
      parseTestKind "Pi A :: KType. KBool -> KLabel" @?=
        KPi "A" (bTrue BKType) (KPi "_" (bTrue BKBool) (bTrue BKLabel))

  , testCase "an annotated type needs parentheses before a type arrow" $ do
      parseTestType "(TInt :: KType) -> TBool" @?=
        TArrow (TAnn TInt (bTrue BKType)) TBool
      case parseType "TInt :: KType -> TBool" of
        Left _ -> pure ()
        Right parsed -> assertFailure ("ambiguous annotation parsed as " ++ show parsed)

  , testCase "parentheses, not record brackets, group concatenation" $ do
      case parseExpr "([a = 1] @ [b = 2])" of
        Left err -> assertFailure err
        Right _ -> pure ()
      case parseExpr "[[a = 1] @ [b = 2]]" of
        Left _ -> pure ()
        Right parsed -> assertFailure ("bracketed concatenation parsed as " ++ show parsed)

  , testCase "record concatenation has separate type and predicate syntax" $ do
      parseType "[| `a : TInt |] @ [| `b : TBool |]" @?=
        Right ((binaryTypeOp BConcat)
          (TRecCons (TLabel "a") TInt TRecNil)
          (TRecCons (TLabel "b") TBool TRecNil))
      parsePred "[| `a : TInt |] @ [| `b : TBool |]" @?=
        Right ((binaryPredOp BConcat
          (PRecCons (PLabel "a") PInt PRecNil)
          (PRecCons (PLabel "b") PBool PRecNil)))

  , testCase "type lets stay inside term annotations" $ do
      let term = parseTestTerm "let x : (let Id :: Pi X :: KType. KType = fun X -> X in Id TInt) = 3 in x"
      case term of
        ELet "x" (EAnn (EInteger 3) (TLet (Decl "Id" _) (TApp (TBound 0) TInt))) (EBound 0) -> pure ()
        other -> assertFailure ("Unexpected term: " ++ show other)
  , testCase "type lets cannot scope over terms" $
      mapM_ (\source -> case parseExpr source of
        Left _ -> pure ()
        Right parsed -> assertFailure ("type binding parsed as " ++ show parsed))
        [ "let Id :: Pi X :: KType. KType = fun X -> X in 3"
        , "letrec Id :: Pi X :: KType. KType = fun X -> X in 3"
        ]
  , testCase "obsolete arrow spelling of kind cases is rejected" $ do
      let source = "if TInt :: KType as a => TInt else TBool"
      case parseType source of
        Left _ -> pure ()
        Right _ -> assertFailure "type kind case parsed"
      case parseExpr "if TInt :: KType as a => 1 else 2" of
        Left _ -> pure ()
        Right _ -> assertFailure "term kind case parsed"

  , testCase "top-level declaration syntax is removed" $ do
      mapM_ (\source -> case parseExpr source of
        Left _ -> pure ()
        Right parsed -> assertFailure ("declaration syntax parsed as " ++ show parsed))
        [ "main : TUnit; main = ()"
        , "type Alias :: KType = TInt; 1"
        , "rec loop : TInt; loop = 1; loop"
        ]

  , testCase "former declaration keywords are ordinary identifiers" $ do
      parseExpr "let type = 1 in type" @?=
        Right (ELet "type" (EInteger 1) (EBound 0))
      parseType "let rec = TInt in rec" @?=
        Right (TLet (Decl "rec" TInt) (TBound 0))
  ]
  where
    assertRejected result = case result of
      Left _ -> pure ()
      Right value -> assertFailure ("retired syntax parsed as " ++ show value)
