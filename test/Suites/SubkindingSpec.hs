{-# LANGUAGE OverloadedStrings #-}

module Suites.SubkindingSpec (tests) where

import Test.Tasty
import Check (checkTypeEquality)
import Test.Tasty.HUnit
import Support.Universal (forallType)
import Context
import Types
import Check (checkRaw, synthRaw)
import Constraint
import Suites.Common
import qualified Control.Exception as Exception
import Support.Errors (assertError, assertPureError)

tests :: TestTree
tests = testGroup "Subkinding and Selfification"
  [ testCase "all base kinds are subtype of Type" $ do
      assertBool "Rec <= Type" (baseSubkind BKRec BKType)
      assertBool "Lab <= Type" (baseSubkind BKLabel BKType)
      assertBool "Ref <= Type" (baseSubkind BKRef BKType)
      assertBool "Col <= Type" (baseSubkind BKCol BKType)
      assertBool "Fun <= Type" (baseSubkind BKFun BKType)
      assertBool "Bool <= Type" (baseSubkind BKBool BKType)

  , testCase "identical base kinds are subtypes" $ do
      assertBool "Rec <= Rec" (baseSubkind BKRec BKRec)
      assertBool "Lab <= Lab" (baseSubkind BKLabel BKLabel)

  , testCase "an unrefined compatible target needs no logical obligation" $ do
      let source = parseTestKind "{ v :: KType | v == Ambient }"
      sub emptyContext source (bTrue BKType) @?= CTrue

  , testCase "base subkinding generates one refinement implication" $ do
      let source = parseTestKind "{ left :: KType | left == TInt }"
          target = parseTestKind "{ right :: KType | right == TBool }"
      case sub emptyContext source target of
        CAll (Bind (TypeSymbol witness) BKType guard) (CPred conclusion) -> do
          witness @?= "left"
          guard @?= (binaryPredOp BEq (PVar witness) PInt)
          conclusion @?= (binaryPredOp BEq (PVar witness) PBool)
        other -> assertFailure ("expected one guarded implication, got " ++ show other)

  , testCase "base subkinding alpha-renames a capturing source hint" $ do
      let source = KBase BKType
            (Refined "x" ((binaryPredOp BEq (PBound 0) PInt)))
          target = KBase BKType
            (Refined "value" ((binaryPredOp BEq (PBound 0) (PVar "x"))))
      let vc = sub emptyContext source target
      assertBool "ambient x remains free" (TypeSymbol "x" `elem` freeNames vc)
      case vc of
        CAll (Bind (TypeSymbol witness) BKType _) _ ->
          assertBool "the introduced witness is alpha-renamed" (witness /= "x")
        other -> assertFailure ("expected one guarded implication, got " ++ show other)
      assertClosedInvalid
        (cAll (bind "x" BKType ((binaryPredOp BEq (PVar "x") PBool))) vc)

  , testCase "incompatible base kinds reject" $ do
      assertBool "Rec not <= Lab" (not (baseSubkind BKRec BKLabel))
      assertBool "Lab not <= Rec" (not (baseSubkind BKLabel BKRec))

  , testCase "unrefined targets do not erase incompatible base kinds" $ do
      assertLeft (sub emptyContext (bTrue BKRec) (bTrue BKLabel))
      assertLeft (sub emptyContext (bTrue BKType) (bTrue BKBool))

  , testCase "vacuous refinements do not cross incompatible base kinds" $ do
      let source = KBase BKRec (refinement "row" PFalse)
          target = KBase BKLabel (refinement "label" PFalse)
      assertLeft (sub emptyContext source target)

      -- This is the obligation the refinement-only version of the base rule
      -- would generate. It is valid by vacuity, so the solver cannot recover
      -- the missing structural base-kind check.
      let constraint = implicationConstraint "row" source (cPred PFalse)
      assertClosedValid constraint

  , testCase "refined subkinding generates valid VC for identical formulas" $ do
      let k = parseTestKind "{ v :: KType | v == TInt }"
      case sub emptyContext k k of
        c -> do
          valid <- assertVCValid c
          assertBool "identical refinement kind is valid" valid

  , testCase "generalized binder refinements compare by mutual implication" $ do
      let left = parseTestKind "{ t :: KType | t == TInt }"
          right = parseTestKind "{ t :: KType | TInt == t }"
      assertClosedValid
        (sub emptyContext (KGen "A" left (bTrue BKType)) (KGen "B" right (bTrue BKType)))
      assertClosedValid (sub emptyContext left (bTrue BKType))
      assertClosedInvalid (sub emptyContext (bTrue BKType) left)

  , testCase "generalized kinds generate a scoped Type constraint" $ do
      let source = parseTestKind "KGen A :: KType. KType"
      case sub emptyContext source (bTrue BKType) of
        constraint@(CAll (Bind (TypeSymbol witness) BKType PTrue) CTrue) -> do
          assertBool "generalized binder is fresh" (witness /= "A")
          assertClosedValid constraint
        other -> assertFailure ("expected a scoped generalized constraint, got " ++ show other)

  , testCase "generalized-to-Type opens dependent codomains" $ do
      let source = parseTestKind
            "KGen A :: KType. KGen B :: { t :: KType | t == A }. KType"
      case sub emptyContext source (bTrue BKType) of
        constraint@(CAll (Bind (TypeSymbol outer) BKType PTrue)
            (CAll (Bind (TypeSymbol inner) BKType guard) CTrue)) -> do
          assertBool "nested generalized witnesses differ" (outer /= inner)
          guard @?= (binaryPredOp BEq (PVar inner) (PVar outer))
          assertClosedValid constraint
        other -> assertFailure ("expected nested scoped constraints, got " ++ show other)

  , testCase "generalized-to-Type validates its dependent domain" $ do
      let malformed = parseTestKind
            "KGen A :: { r :: KType | head r == TInt }. KType"
      case sub emptyContext malformed (bTrue BKType) of
        constraint -> assertClosedInvalid constraint

  , testCase "generalized-to-Type preserves incompatible boundaries" $ do
      let gen = parseTestKind "KGen A :: KType. KType"
          higher = parseTestKind "KGen A :: KType. Pi B :: KType. KType"
      assertLeft (sub emptyContext (bTrue BKType) gen)
      assertLeft (sub emptyContext gen (bTrue BKRec))
      assertLeft (sub emptyContext gen
        (parseTestKind "{ t :: KType | t == TInt }"))
      assertLeft (sub emptyContext higher (bTrue BKType))

  , testCase "universal body refinements do not replace alpha-equivalence" $ do
      let k = parseTestKind "{t :: KType | t == TBool}"
          poly = forallType "X" k
          gen = KGen "X" k (bTrue BKType)
      mapM_ (\wrap -> do
        assertError (checkTypeEquality emptyContext gen
          (poly (wrap (TBound 0))) (poly (wrap TBool)))
        assertError (checkTypeEquality emptyContext gen
          (poly (wrap (TBound 0))) (poly (wrap TInt))))
        [id,TRef,TCol,\t -> TArrow t t,\t -> TRecCons (TLabel "field") t TRecNil]
  , testCase "native Type constructors reject unquotable universal components" $ do
      let u = forallType "X" (bTrue BKType) (TBound 0)
      checkTypeEquality emptyContext (bTrue BKType) u u >>= (@?= ())
      mapM_ (\wrap -> assertError (checkTypeEquality emptyContext (bTrue BKType)
        (wrap u) (wrap u)))
        [TRef,TCol,\t -> TArrow t TInt,
          \t -> TRecCons (TLabel "f") t TRecNil]
  , testCase "abstract function refinements do not rewrite universal bodies" $ do
      let k = parseTestKind "{f :: KFun | dom f == TBool && img f == TInt}"
          poly = forallType "F" k
          gen = KGen "F" k (bTrue BKType)
      mapM_ (\(left, right) -> assertError (checkTypeEquality emptyContext gen
        (poly left) (poly right)))
        [ ((unaryTypeOp BDom) (TBound 0), TBool)
        , (TBound 0, TArrow TBool TInt)
        , ((unaryTypeOp BImg) (TBound 0), TBool)
        ]
  , testCase "lexical refinement contracts do not replace alpha-equivalence" $ do
      let kind = KBase BKType (Refined "v"
            ((binaryPredOp BEq (PBound 0) PBool)))
          ctx = addTypeVar "A" kind emptyContext
          poly = forallType "X" (bTrue BKType)
          gen = KGen "X" (bTrue BKType) (bTrue BKType)
      assertError (checkTypeEquality ctx gen (poly (TVar "A")) (poly TBool))
      assertError (checkTypeEquality (addLocalTypeVar "A" kind ctx) gen
        (poly (TVar "A")) (poly TBool))
  , testCase "Pi witnesses cannot capture free domain dependencies" $ do
      let domain = KBase BKType (refinement "u"
            ((unaryPredOp BNot) ((binaryPredOp BEq (PBound 0) (PVar "x0")))))
          codomain t = KBase BKType (refinement "v"
            ((binaryPredOp BEq (PBound 0) t)))
          left = KPi "A" domain (codomain (PTypeBound 0))
          right = KPi "B" domain (codomain PInt)
      let forward = sub emptyContext left right
          backward = sub emptyContext right left
      let vc = cAnd [forward, backward]
      assertBool "dependency remains free" (TypeSymbol "x0" `elem` freeNames vc)
      assertClosedInvalid (cAll (bind "x0" BKType PTrue) vc)
  , testCase "non-alpha dependent Pi domains make universals unequal" $ do
      let k = parseTestKind "Pi X :: KType. {v :: KType | v == X}"
          k' = parseTestKind "Pi Y :: KType. {v :: KType | Y == v}"
          universal domain = forallType "F" domain TInt
          gen = KGen "F" k (bTrue BKType)
      assertError (checkTypeEquality emptyContext gen (universal k) (universal k'))
      assertError (checkTypeEquality emptyContext gen (universal k)
        (universal (parseTestKind "Pi Y :: KType. KType")))
  , testCase "universal witnesses avoid free context dependencies" $ do
      let ctx = addTermVar "unused" (TVar "x0") emptyContext
          gen = KGen "X" (bTrue BKType) (bTrue BKType)
      assertError (checkTypeEquality ctx gen
        (forallType "X" (bTrue BKType) (TBound 0))
        (forallType "Y" (bTrue BKType) TInt))

  , testCase "contradictory refinement kind is invalid in solver" $ do
      let k1 = parseTestKind "{ v :: KType | KTrue }"
          k2 = parseTestKind "{ v :: KType | KFalse }"
      case sub emptyContext k1 k2 of
        c -> do
          invalid <- assertVCInvalid c
          assertBool "Type <= {v::Type | false} rejected by solver" invalid
  , testCase "Pi kinds are never subkinds of Type" $ do
      let source = parseTestKind "Pi X :: KType. { r :: KType | r == X }"
      assertLeft (sub emptyContext source (bTrue BKType))
      assertLeft (sub emptyContext source (parseTestKind "{ t :: KType | KFalse }"))
      assertLeft (sub emptyContext source (parseTestKind "{ t :: KType | KTrue && KTrue }"))
      assertLeft (sub emptyContext source (bTrue BKFun))
      let annotated = parseTestType "(fun X -> X) :: Pi X :: KType. KType"
      assertLeft (checkRaw emptyContext annotated (bTrue BKType))
      assertLeft (synthRaw emptyContext (TLambda "X" (TBound 0)))
      assertLeft (checkRaw emptyContext (TLambda "X" (TBound 0)) (bTrue BKType))
      assertLeft (synthRaw emptyContext ((unaryTypeOp BDom) annotated))

  , testCase "Pi implication omits unused higher-order parameters" $ do
      let piKind = parseTestKind "Pi X :: KType. KType"
      implicationConstraint "f" piKind CTrue @?= CTrue
      assertLeft (implicationConstraint "f" piKind
        (cPred ((binaryPredOp BEq (PVar "f") (PVar "f")))))

  , testCase "first-order obligations reject Pi and Gen solver binders" $ do
      let recordKind = parseTestKind
            "{ r :: KRec | not (empty r) }"
          piKind = parseTestKind "Pi X :: KType. KType"
          genKind = parseTestKind "KGen X :: KType. KType"
          recordObligation = implicationConstraint "r" recordKind
            (cPred ((binaryPredOp BEq (PVar "r") (PVar "r"))))
          higherOrderObligation kind = implicationConstraint "f" kind
            (cPred ((binaryPredOp BEq (PVar "f") (PVar "f"))))
      assertClosedValid recordObligation
      assertLeft (higherOrderObligation piKind)
      assertLeft (higherOrderObligation genKind)
      implicationConstraint "f" piKind CTrue @?= CTrue
      implicationConstraint "f" genKind CTrue @?= CTrue

  , testCase "Pi subkinding opens dependent codomains with a shared witness" $ do
      let left = parseTestKind "Pi Left :: KType. { out :: KType | out == Left }"
          renamed = parseTestKind "Pi Right :: KType. { value :: KType | value == Right }"
      let vc = sub emptyContext left renamed
      assertClosedValid vc
      assertLeft (sub emptyContext (parseTestKind "Pi r :: KRec. KRec")
        (parseTestKind "Pi t :: KType. KRec"))
  ]

assertLeft :: Show a => a -> Assertion
assertLeft = assertPureError
