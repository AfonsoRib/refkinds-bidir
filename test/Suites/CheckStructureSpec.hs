{-# LANGUAGE OverloadedStrings #-}
module Suites.CheckStructureSpec (tests) where

import Check (checkKind, checkRaw, synthKind)
import Constraint
import Context
import Suites.Common (parseTestType, parseTestKind, assertClosedValid, assertClosedInvalid)
import Types
import Test.Tasty
import Test.Tasty.HUnit
import qualified Control.Exception as Exception
import Support.Errors (assertError, assertPureError)

tests :: TestTree
tests = testGroup "Checker rule structure"
  [ testCase "predicate names preserve syntax and separate namespaces" $ do
      let p = (binaryPredOp BAnd) (id (PVar "same")) (eqP (PRefVar "same") PInt)
      freeNames p @?= [TypeSymbol "same", RefSymbol "same"]
      assertBool "Boolean spelling keeps its previous alpha comparison"
        (alphaEqPredicate (id PTrue) PTrue)
      assertBool "different operands remain distinct"
        (not (alphaEqPredicate (id PFalse) PTrue))
  , testCase "predicate opening traverses interpreted operations" $ do
      let nested = eqP (PBound 0) (PTypeBound 0)
          replacement = PArrow (PTypeBound 0) (PBound 0)
          result = eqP replacement (PTypeBound 0)
      assertBool "interpreted operands are opened"
        (alphaEqPredicate (openPredicate replacement nested) result)
  , testCase "predicate guard binding avoids free refinement and type names" $ do
      let p = eqP (PVar "guard") (PRefVar "guard0")
          body = CPred (eqP (PVar "guard1") PInt)
      freeNames (cGuard [] p body) @?=
        [TypeSymbol "guard", RefSymbol "guard0", TypeSymbol "guard1"]
  , testCase "fresh context names include declared free dependencies without validating them" $ do
      let ctx = addTypeVar "alias"
                (KBase BKType (Refined "v" (id (PVar "x0"))))
              $ addTypeVar "contract" (KBase BKType (Refined "v" (id (PVar "x1"))))
              $ addTermVar "term" (TVar "x2")
              $ addLocalTypeVar "local" (KBase BKType (Refined "v" (id (PVar "x6")))) emptyContext
      mapM_ (\n -> assertBool ("missing " ++ n) (n `elem` contextFreshNames ctx))
        ["alias", "contract", "term", "local", "x0", "x1", "x2", "x6"]
      assertBool "display hints are not free dependencies" ("v" `notElem` contextFreshNames ctx)
      assertBool "freshness is not classifier validation"
        (checkKind ctx TInt (bTrue BKType) `seq` True)
  , testCase "lambda written names shadow context bindings" $ do
      let ctx = addTypeVar "A" (bTrue BKType)
              (addTermVar "term" (TVar "x0") emptyContext)
          goal = KPi "X" (bTrue BKType) (bTrue BKType)
      c <- get (checkKind ctx (TLambda "A" (TBound 0)) goal)
      assertBool "the written lambda name is used for its scoped binder"
        (TypeSymbol "A" `elem` [n | Bind n _ _ <- binders c])
      assertClosedValid c
  , testCase "checking uses written names for ordinary type binders" $ do
      let binderNames constraint = [n | Bind n _ _ <- binders constraint]
      letConstraint <- get (checkKind emptyContext
        (TLet (Decl "Alias" TInt) (TBound 0)) (bTrue BKType))
      recursiveConstraint <- get (checkKind emptyContext
        (TRec "Loop" (TAnn (TBound 0) (bTrue BKType)) TInt) (bTrue BKType))
      assertBool "let binder" (TypeSymbol "Alias" `elem` binderNames letConstraint)
      assertBool "recursive binder" (TypeSymbol "Loop" `elem` binderNames recursiveConstraint)
  , testCase "base binders open only the refinement witness" $ do
      let k = KBase BKType (Refined "same" (eqP (PBound 0) (PVar "same")))
      implicationConstraint "value" k CTrue @?=
        CAll (Bind (TypeSymbol "value") BKType
          (eqP (PVar "value") (PVar "same"))) CTrue
  , testCase "record binders retain the solver record invariant" $ do
      scoped <- get (implicationConstraint "row" (bTrue BKRec)
        (CPred ((unaryPredOp BIsRec (PVar "row")))))
      assertClosedValid scoped
      get (implicationConstraint "row" (bTrue BKRec)
        (CPred (eqP (PVar "row") PInt))) >>= assertClosedInvalid
  , testCase "generalized parameters are never first-order proof values" $ do
      let gen = KGen "A" (bTrue BKType) (bTrue BKType)
      implicationConstraint "P" gen CTrue @?= CTrue
      reject (implicationConstraint "P" gen
        (CPred (eqP (PVar "P") (PVar "P"))))
      reject (checkRaw emptyContext (parseTestType
        "forall P :: KGen A :: KType. KType. ((P -> P) :: {v :: KFun | dom v == P})")
        (bTrue BKType))
  , testCase "Pi omits unused parameters and rejects used type names" $ do
      let piKind = KPi "A" (bTrue BKType) (bTrue BKType)
          separate = CPred (eqP (PRefVar "F") PInt)
      implicationConstraint "F" piKind separate @?= separate
      implicationConstraint "F" piKind CTrue @?= CTrue
      reject (implicationConstraint "F" piKind
        (CPred (eqP (PVar "F") PInt)))
  , testCase "selfification strengthens bases and preserves nonbase kinds" $ do
      let base = KBase BKType (Refined "A" (eqP (PBound 0) PInt))
      snd (synthKind (addTypeVar "A" base emptyContext) (TVar "A")) @?=
        KBase BKType (Refined "A" ((binaryPredOp BAnd) (eqP (PBound 0) PInt)
          (eqP (PBound 0) (PVar "A"))))
      mapM_ (\k -> snd (synthKind (addTypeVar "A" k emptyContext) (TVar "A")) @?= k)
        [KPi "A" base (bTrue BKType), KGen "A" base (bTrue BKType)]
  , testCase "Pi application opens its codomain with an ANF variable" $ do
      let domain = bTrue BKType
          codomain = KBase BKType
            (Refined "v" (eqP (PBound 0) (PTypeBound 0)))
          ctx = addTypeVar "A" domain
              (addTypeVar "F" (KPi "parameter" domain codomain) emptyContext)
          expected = KBase BKType
            (Refined "v" (eqP (PBound 0) (PVar "A")))
          expectedInt = KBase BKType
            (Refined "v" (eqP (PBound 0) PInt))
      snd (synthKind ctx (TApp (TVar "F") (TVar "A"))) @?= expected
      snd (synthKind ctx (TApp (TVar "F") TInt)) @?= expectedInt
      Exception.evaluate (checkRaw ctx (TApp (TVar "F") TInt)
        (bTrue BKType)) >> pure ()
  , testCase "Pi application does not capture an argument at a nested Pi hint" $ do
      let domain = bTrue BKType
          nestedDomain = KBase BKType
            (Refined "d" (eqP (PBound 0) (PTypeBound 0)))
          nestedCodomain = KBase BKType
            (Refined "v" ((binaryPredOp BAnd)
              (eqP (PBound 0) (PTypeBound 1))
              (eqP (PTypeBound 0) (PTypeBound 0))))
          functionKind = KPi "outer" domain
            (KPi "Argument" nestedDomain nestedCodomain)
          ctx = addTypeVar "Argument" domain
              (addTypeVar "F" functionKind emptyContext)
          expected = KPi "Argument"
            (KBase BKType (Refined "d" (eqP (PBound 0) (PVar "Argument"))))
            (KBase BKType (Refined "v" ((binaryPredOp BAnd)
              (eqP (PBound 0) (PVar "Argument"))
              (eqP (PTypeBound 0) (PTypeBound 0)))))
          captured = KPi "Argument"
            (KBase BKType (Refined "d" (eqP (PBound 0) (PVar "Argument"))))
            (KBase BKType (Refined "v" ((binaryPredOp BAnd)
              (eqP (PBound 0) (PTypeBound 0))
              (eqP (PTypeBound 0) (PTypeBound 0)))))
          inferred = snd
            (synthKind ctx (TApp (TVar "F") (TVar "Argument")))
      inferred @?= expected
      assertBool "outer argument was captured by the nested Pi"
        (not (alphaEqKind inferred captured))
  , testCase "conditional witnesses cannot capture condition or branch dependencies" $ do
      let ctx = addTypeVar "x0" (bTrue BKBool)
              (addTypeVar "x1" (bTrue BKType) (addTypeVar "x2" (bTrue BKType) emptyContext))
          goal = KBase BKType (Refined "v" (eqP (PBound 0) (PVar "x1")))
      c <- get (checkKind ctx (TIf (TVar "x0") TInt (TVar "x2")) goal)
      let guards = [(n,p) | Bind n BKType p <- binders c,
                     p == id (PVar "x0") || p == (unaryPredOp BNot) (id (PVar "x0"))]
      length guards @?= 2
      assertBool "fresh witnesses" (all (\(n,_) -> n `notElem` map TypeSymbol ["x0","x1","x2"]) guards)
      assertBool "dependencies remain free" (all (`elem` freeNames c) (map TypeSymbol ["x0","x1","x2"]))
  , testCase "conditional guards preserve selector preconditions" $ do
      let goal = parseTestKind "Pi R :: KRec. KType"
      get (checkRaw emptyContext (parseTestType "fun R -> if empty R then TInt else head R") goal)
        >>= assertClosedValid
      get (checkRaw emptyContext (parseTestType "fun R -> if empty R then head R else TInt") goal)
        >>= assertClosedInvalid
      reject (checkKind emptyContext (TIf TInt TInt TInt) (bTrue BKType))
      reject (checkKind emptyContext (TIf TTrue TInt (TLambda "A" TInt)) (bTrue BKType))
  , testCase "fallback admits universal Type and rejects false refinements" $ do
      let u = parseTestType "forall A :: KType. A"
          good = bTrue BKType
          bad = KBase BKType (Refined "v" PFalse)
      mapM_ (\t -> do
        get (checkKind emptyContext t good) >>= assertClosedValid
        reject (checkKind emptyContext t bad))
        [u, TAnn u (parseTestKind "KGen A :: KType. KType")]
      let (_, inferred) = synthKind emptyContext u
      assertBool "dependent KGen is preserved" (alphaEqKind inferred
        (parseTestKind "KGen A :: KType. {v :: KType | KTrue && v == A}"))
  ]
  where
    binders (CAll b c) = b : binders c
    binders (CAnd cs) = concatMap binders cs
    binders _ = []

    eqP left right = (binaryPredOp BEq left right)

get :: a -> IO a
get = pure

reject :: Show a => a -> Assertion
reject = assertPureError
