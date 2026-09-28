{-# LANGUAGE OverloadedStrings #-}
module Suites.GeneralizedKindSpec (tests) where

import ANF (elaborate)
import Check
import Constraint
import Context hiding (implicationConstraint)
import Parser
import Support.AstInvariants
import Test.Tasty
import Test.Tasty.HUnit
import Support.Universal (forallType)
import Suites.Common (checkExpr, synthExpr, universalDomainConstraint)
import Types
import qualified Control.Exception as Exception
import Support.Errors (assertError, assertPureError)

kind :: String -> Rkind
kind = either error id . parseKind

ty :: String -> Type
ty = either error id . parseType

valid :: Cstr -> Assertion
valid c = checkValid c >>= (@?= Valid)

invalid :: Cstr -> Assertion
invalid c = assertError (Exception.evaluate c >>= checkValid)

checkSource :: String -> String -> Cstr
checkSource source target = checkRaw emptyContext (ty source) (kind target)

nestedSignature :: String
nestedSignature =
  "forall s :: KType. " ++
  "forall t :: { f :: KFun | dom f == s && img f == TBool }. " ++
  "t -> s -> TBool"

nestedGeneralizedKind :: String
nestedGeneralizedKind =
  "KGen s :: KType. " ++
  "KGen t :: { f :: KFun | dom f == s && img f == TBool }. " ++
  "{ v :: KFun | dom v == t && img v == (s -> TBool) }"

nestedPolymorphicTerm :: String
nestedPolymorphicTerm =
  "((tfun s -> tfun t -> fun x -> fun y -> x y) : " ++
  "((" ++ nestedSignature ++ ") :: " ++ nestedGeneralizedKind ++ "))"

nestedConstantTerm :: String
nestedConstantTerm =
  "((tfun s -> tfun t -> fun x -> fun y -> True) : " ++
  "((" ++ nestedSignature ++ ") :: " ++ nestedGeneralizedKind ++ "))"

tests :: TestTree
tests = testGroup "Dependent generalized kinds"
  [ testCase "surface binder scopes only the body classifier" $ do
      let source = "Pi Outer :: KType. KGen A :: { v :: KType | v == Outer }. { v :: KType | v == A }"
          expected = KPi "Outer" (bTrue BKType)
            (KGen "A" (KBase BKType (refinement "v"
              ((binaryPredOp BEq (PBound 0) (PTypeBound 0)))))
              (KBase BKType (refinement "v"
                ((binaryPredOp BEq (PBound 0) (PTypeBound 0))))))
      parseKind source @?= Right expected
      validateTypeAst (forallType "F" expected TInt) @?= Right ()
  , testCase "old syntax and enclosing generalized refinements are rejected" $
      mapM_ (\source -> case parseKind source of
        Left _ -> pure (); Right k -> assertFailure (show k))
        ["KGen KType", "{ p :: KGen A :: KType. KType | true }"]
  , testCase "universals synthesize their dependent body kind" $ do
      case synthRaw emptyContext (ty "forall A :: KType. A") of
        (c, result) -> do
          valid c
          assertBool "dependent singleton result" (alphaEqKind result
            (kind "KGen A :: KType. { v :: KType | KTrue && v == A }"))
      valid (checkSource "forall A :: KType. A" "KType")
      case parseType "forall A. A" of
        Left _ -> pure (); Right result -> assertFailure (show result)
  , testCase "checking accepts an exact dependent body and rejects a wrong one" $ do
      valid (checkSource "forall A :: KType. A" "KGen A :: KType. { v :: KType | v == A }")
      invalid (checkSource "forall A :: KType. TInt" "KGen A :: KType. { v :: KType | v == A }")
  , testCase "PolyId restricts its function codomain to Bool or Int" $ do
      let domain = "{ a :: KType | a == TBool || a == TInt }"
          signature = "forall a :: " ++ domain ++ ". a -> a"
          expected = "KGen a :: " ++ domain ++ ". " ++
            "{ v :: KFun | v == (a -> a) && (img v == TBool || img v == TInt) }"
      valid (checkSource signature expected)
      valid (checkSource signature
        ("KGen a :: " ++ domain ++ ". { v :: KFun | v == (a -> a) }"))
      invalid (checkSource "forall a :: KType. a -> a"
        "KGen a :: KType. { v :: KFun | v == (a -> a) && (img v == TBool || img v == TInt) }")
  , testCase "codomain refinements cannot narrow an unrestricted forall" $ do
      invalid (checkSource "forall a :: KType. TInt -> a"
        "KGen a :: KType. { v :: KFun | v == (TInt -> a) && (a == TInt || a == TBool) }")
      let domain = "{ a :: KType | a == TBool || a == TInt }"
          source = "forall a :: " ++ domain ++ ". TInt -> a"
          target = "KGen a :: " ++ domain ++ ". " ++
            "{ v :: KFun | v == (TInt -> a) && (a == TInt || a == TBool) }"
      valid (checkSource source target)
  , testCase "synthesis emits the binder constraint and checks the body's first-order kind" $ do
      mapM_ (\source -> invalid (fst (synthRaw emptyContext (ty source))))
        ["forall A :: {r :: KType | head r == TInt}. TInt",
         "forall A :: {r :: KType | r == Missing}. TInt",
         "forall A :: KType. ((fun X -> X) :: Pi X :: KType. KType)"]
      case synthRaw emptyContext (ty "forall R :: {r :: KRec | not (empty r)}. head R") of
        (c, inferred) -> do
          valid c
          assertBool "selector singleton is inferred" (alphaEqKind inferred
            (kind "KGen R :: {r :: KRec | not (empty r)}. {v :: KType | v == head R}"))
  , testCase "forall binds only its body and nested domains retain outer scope" $ do
      let source = ty "forall A :: KType. forall A :: {v :: KType | v == A}. A"
          expected = TForall "A" (bTrue BKType)
            (TForall "A" (KBase BKType (refinement "v"
              ((binaryPredOp BEq (PBound 0) (PTypeBound 0))))) (TBound 0))
      source @?= expected
      validateAnfType (elaborate source) @?= Right ()
      valid (fst (synthRaw emptyContext source))
      invalid (checkSource "forall A :: {v :: KType | v == A}. A" "KType")
  , testCase "forall domains participate in opening and alpha equivalence" $ do
      let source = ty "forall A :: {v :: KType | v == Outside}. A"
          renamed = ty "forall B :: {w :: KType | w == Outside}. B"
      assertBool "binder hints are ignored" (alphaEq source renamed)
      assertBool "domains distinguish types" (not (alphaEq source (ty "forall A :: KType. A")))
      freeNames source @?= [TypeSymbol "Outside"]
      let closed = abstractType "Outside" source
      instantiateType TInt closed @?=
        Right (ty "forall A :: {v :: KType | v == TInt}. A")
      (either (Left . renderSubstitutionError) validateTypeAst
        (instantiateType TInt closed)) @?= Right ()
  , testCase "term polymorphism works with directly annotated forall binders" $ do
      let signature = "forall A :: KLabel. TInt -> TInt"
          function = "((tfun A -> fun x -> x) : (" ++ signature ++ "))"
      good <- either assertFailure pure (parseExpr (function ++ " [`tag]"))
      checkExpr emptyContext good (TArrow TInt TInt) >>= (@?= ())
      bad <- either assertFailure pure (parseExpr (function ++ " [TInt]"))
      assertError (checkExpr emptyContext bad (TArrow TInt TInt))
  , testCase "universal bodies synthesize before generalized subkinding" $ do
      assertPureError (checkSource "forall A :: KType. if KTrue then A else A"
        "KGen A :: KType. { v :: KType | v == A }")
      valid (checkSource "forall A :: KType. ((if KTrue then A else A) :: {v :: KType | v == A})"
        "KGen A :: KType. { v :: KType | v == A }")
      assertPureError (checkSource "forall A :: KType. if KTrue then TInt else A"
        "KGen A :: KType. { v :: KType | v == A }")
      invalid (checkSource "forall A :: KType. ((if KTrue then TInt else A) :: {v :: KType | v == A})"
        "KGen A :: KType. { v :: KType | v == A }")
      invalid (checkSource "forall A :: KType. A"
        "KGen A :: KType. Pi B :: KType. KType")
  , testCase "an outer annotation exposes exactly its declared kind" $ do
      let expected = kind "KGen A :: KType. KType"
          source = TAnn (TForall "A" (bTrue BKType) (TBound 0)) expected
      case synthRaw emptyContext source of
        (c, inferred) -> do
          valid c
          inferred @?= expected
  , testCase "unused higher-order domains are not eagerly validated" $
      mapM_ (valid . universalDomainConstraint emptyContext . kind)
        [ "KGen A :: KType. { v :: KType | v == A }"
        , "KGen A :: KType. { v :: KType | head A == v }"
        , "KGen A :: KType. Pi B :: KType. KType"
        ]
  , testCase "subkinding reverses domains and preserves body covariance" $ do
      let broad = kind "KGen A :: KType. KRec"
          narrow = kind "KGen B :: KRec. KType"
      valid (sub emptyContext broad narrow)
      invalid (sub emptyContext narrow broad)
  , testCase "dependent subkinding aligns binders under the expected domain" $ do
      let left = kind "KGen A :: KType. { v :: KType | v == A }"
          right = kind "KGen B :: { b :: KType | b == TInt }. { v :: KType | v == TInt }"
      valid (sub emptyContext left right)
      invalid (sub emptyContext right left)
      invalid (sub emptyContext left (kind "KGen B :: KType. { v :: KType | v == TInt }"))
  , testCase "the universal's declared domain supplies its body assumptions" $ do
      valid (checkSource "forall A :: {r :: KRec | not (empty r)}. head A"
        "KGen A :: { r :: KRec | not (empty r) }. KType")
      assertPureError (checkSource "forall A :: KType. head A"
        "KGen A :: { r :: KRec | not (empty r) }. KType")
      invalid (checkSource "forall A :: KType. head A" "KGen A :: KType. KType")
      invalid (checkSource "forall A :: KRec. A"
        "KGen A :: KType. KType")
  , testCase "generalized kinds are below Type but outside Pi and records" $ do
      let gen = kind "KGen A :: KType. KType"
      valid (sub emptyContext gen (bTrue BKType))
      invalid (sub emptyContext (bTrue BKType) gen)
      invalid (sub emptyContext gen (bTrue BKRec))
      invalid (sub emptyContext gen (kind "Pi A :: KType. KType"))
      invalid (sub emptyContext (kind "Pi A :: KType. KType") gen)
  , testCase "generalized variables do not become executable type functions" $ do
      let ctx = addTypeVar "P" (kind "KGen A :: KType. KType") emptyContext
      invalid (checkRaw ctx (ty "P TInt") (bTrue BKType))
  , testCase "opening preserves nested type and refinement binders" $ do
      let original = kind "KGen A :: { v :: KType | v == Free }. KGen B :: KType. { v :: KType | v == A }"
      let closed = abstractKind "Free" original
      instantiateKindAt 0 TInt closed @?=
        Right (kind "KGen A :: { v :: KType | v == TInt }. KGen B :: KType. { v :: KType | v == A }")
      assertBool "alpha equivalence ignores binder hints" (alphaEqKind original
        (kind "KGen X :: { p :: KType | p == Free }. KGen Y :: KType. { p :: KType | p == X }"))
      assertBool "different bound occurrences stay different" (not (alphaEqKind original
        (kind "KGen X :: { p :: KType | p == Free }. KGen Y :: KType. { p :: KType | p == Y }")))
  , testCase "ANF preserves dependent kind annotations and their scope" $ do
      let source = ty "(forall A :: KType. A) :: KGen A :: KType. { v :: KType | v == A }"
          core = elaborate source
      validateAnfType core @?= Right ()
      elaborate core @?= core
      valid (fst (synthRaw emptyContext source))
  , testCase "generalized body dependencies stay open in obligations" $ do
      let ctx = addTypeVar "Ambient" (bTrue BKType) emptyContext
      case checkRaw ctx (ty "forall A :: KType. A")
        (kind "KGen A :: KType. { v :: KType | v == Ambient }") of
        c -> do
          assertBool "ambient name retained" (TypeSymbol "Ambient" `elem` freeNames c)
          assertError (checkValid c)
  , testCase "polymorphic getter rejects an abstract record projection" $ do
      source <- readFile "examples/dependent-generalized-kind.rk"
      program <- either assertFailure pure (parseExpr source)
      assertError (synthExpr emptyContext program)
  , testCase "semantic conversion retains the domain while reducing a universal body" $ do
      let input = ty "(forall A :: KType. ((refOf (TRef A)) :: KType)) :: KGen A :: KType. KType"
          expected = ty "forall A :: KType. A"
      checkTypeEquality emptyContext (kind "KGen A :: KType. KType") input expected
        >>= (@?= ())
      valid (fst (synthRaw emptyContext expected))
  , testCase "type application preserves the universal's own domain" $ do
      let source = "let Make :: Pi A :: KType. KGen B :: KLabel. KFun = " ++
            "fun A -> forall B :: KLabel. A -> A in Make TInt"
          expected = ty "forall B :: KLabel. TInt -> TInt"
      valid (checkRaw emptyContext (ty source) (kind "KGen B :: KLabel. KFun"))
      checkTypeEquality emptyContext (kind "KGen B :: KLabel. KFun")
        (elaborate (ty source)) expected >>= (@?= ())
  , testCase "nested dependent universals synthesize nested generalized kinds" $ do
      let signature = ty nestedSignature
          expected = kind nestedGeneralizedKind
          (constraint, inferred) = synthRaw emptyContext signature
      freeVariables constraint @?= []
      valid constraint
      assertBool "nested generalized result" (alphaEqKind inferred expected)
  , testCase "nested type lambdas check against the dependent signature" $ do
      program <- either assertFailure pure (parseExpr nestedConstantTerm)
      inferred <- synthExpr emptyContext program
      assertBool "annotation retains the written nested signature"
        (alphaEq (stripAnnotations inferred) (ty nestedSignature))
  , testCase "nested dependent universals instantiate both binders" $ do
      let ctx = addTermVar "poly" (ty nestedSignature) emptyContext
          cases =
            [ (" [TInt] [(TInt -> TBool)]",
                ty "(TInt -> TBool) -> TInt -> TBool")
            , (" [TBool] [(TBool -> TBool)]",
                ty "(TBool -> TBool) -> TBool -> TBool")
            ]
      mapM_ (\(arguments, expected) -> do
        program <- either assertFailure pure
          (parseExpr ("poly" ++ arguments))
        checkExpr ctx program expected >>= (@?= ())) cases
  , testCase "nested dependent instantiation rejects the wrong inner domain" $ do
      let ctx = addTermVar "poly" (ty nestedSignature) emptyContext
      program <- either assertFailure pure
        (parseExpr "poly [TInt] [(TBool -> TBool)]")
      assertError (checkExpr ctx program
        (ty "(TBool -> TBool) -> TInt -> TBool"))
  , testCase "nested dependent instantiation rejects the wrong inner image" $ do
      let ctx = addTermVar "poly" (ty nestedSignature) emptyContext
      program <- either assertFailure pure
        (parseExpr "poly [TInt] [(TInt -> TInt)]")
      assertError (checkExpr ctx program
        (ty "(TInt -> TInt) -> TInt -> TBool"))
  , testCase "abstract function application remains a separate restriction" $ do
      program <- either assertFailure pure (parseExpr nestedPolymorphicTerm)
      assertError (synthExpr emptyContext program)
  , testCase "nested universals still reject higher-order result kinds" $ do
      assertPureError (fst (synthRaw emptyContext (ty
        ("forall A :: KType. forall B :: KType. " ++
          "((fun X -> X) :: Pi X :: KType. KType)"))))
      let ctx = addTypeVar "Higher"
            (kind "KGen B :: KType. Pi X :: KType. KType") emptyContext
      assertPureError (fst (synthRaw ctx (ty "forall A :: KType. Higher")))
  , testCase "a declared alias retains its parameter domain for term application" $ do
      let prefix = "(let f : ((let P :: KGen A :: KLabel. KFun = forall A :: KLabel. TInt -> TInt in P) :: KGen A :: KLabel. KFun) " ++
            "= tfun A -> fun x -> x in "
      good <- either assertFailure pure (parseExpr (prefix ++ "f [`tag] 7) : TInt"))
      synthExpr emptyContext good >>= (@?= TInt)
      bad <- either assertFailure pure (parseExpr (prefix ++ "f [TInt] 7) : TInt"))
      assertError (synthExpr emptyContext bad)
  , testCase "a type-function result can classify a polymorphic term" $ do
      let prefix = "(let f : ((let Make :: Pi A :: KType. KGen B :: KLabel. KFun = " ++
            "fun A -> forall B :: KLabel. A -> A in " ++
            "let P :: KGen B :: KLabel. KFun = Make TInt in " ++
            "P) :: KGen B :: KLabel. KFun) = tfun B -> fun x -> x in "
      good <- either assertFailure pure (parseExpr (prefix ++ "f [`tag] 7) : TInt"))
      synthExpr emptyContext good >>= (@?= TInt)
      bad <- either assertFailure pure (parseExpr (prefix ++ "f [TInt] 7) : TInt"))
      assertError (synthExpr emptyContext bad)
  , testCase "universal values never encode, with or without an annotation" $ do
      let rejectConversion t = assertError (Exception.evaluate (typeToPred t))
      rejectConversion (TForall "A" (bTrue BKType) TInt)
      let classified = ty "forall A :: KType. A"
      rejectConversion classified
      let other = ty "forall A :: KRec. A"
      rejectConversion other
  ]
