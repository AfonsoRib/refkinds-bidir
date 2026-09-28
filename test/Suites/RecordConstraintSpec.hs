{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}

module Suites.RecordConstraintSpec (tests) where

import Test.Tasty
import Test.Tasty.HUnit
import qualified Data.Text as T

import ANF (elaborate)
import Parser (parsePred, parseType)
import Check hiding (sub)
import Constraint
import Context hiding (implicationConstraint)
import Support.AstInvariants (validateAnfType)
import Support.Universal (forallType)
import Support.Expected
import Types
import Suites.Common (synth, synthExpr, parseTestTerm, parseTestType)
import qualified Control.Exception as Exception
import Support.Errors (assertError, assertErrorContaining)

tests :: TestTree
tests = testGroup "Constraint-producing record rules"
  [ testCase "fresh record labels are valid" $ do
      constraint <- synthConstraint
        (parseTestType "[| `x : TInt, `y : TBool |]")
      validateConstraint constraint >>= (@?= ())

  , testCase "duplicate record labels are rejected" $ do
      constraint <- synthConstraint
        (parseTestType "[| `x : TInt, `x : TBool |]")
      assertInvalid constraint

  , testCase "predicate concatenation encodes record and apartness guards" $ do
      let x = PRecCons (PLabel "x") PInt PRecNil
          y = PRecCons (PLabel "y") PBool PRecNil
          expected = PRecCons (PLabel "x") PInt y
      checkValid (cPred (eqP (concatP x y) expected)) >>= (@?= Valid)
      let script = toSmt (cPred (eqP (concatP x y) expected))
      assertBool "interpreted concatenation lost its SMT record guards"
        ("recConcat" `T.isInfixOf` script && "set.inter" `T.isInfixOf` script)

  , testCase "term-derived records retain freshness obligations" $ do
      let duplicate = parseTestTerm "[x = 1, x = True]"
      assertError (synthExpr emptyContext duplicate)

  , testCase "term-derived concatenation rejects duplicate labels structurally" $ do
      let left = TRecCons (TLabel "x") TInt TRecNil
          right = TRecCons (TLabel "x") TBool TRecNil
          context = addTermVar "left" left
            (addTermVar "right" right emptyContext)
      assertErrorContaining "duplicate record label: x"
        (synthExpr context (EConcat (EVar "left") (EVar "right")))

  , testCase "empty record destructors are rejected by VCs" $ do
      mapM_ rejectDestructor
        [ parseTestType "head [||]"
        , parseTestType "headLabel [||]"
        , parseTestType "tail [||]"
        ]

  , testCase "term destructors reject symbolic record shapes" $ do
      let context kind = addTermVar "record" (TVar "R")
            (addTypeVar "R" kind emptyContext)
          nonEmpty = KBase BKRec
            (refinement "r" ((unaryPredOp BNot) (emptyP (PBound 0))))
      assertErrorContaining "concrete nonempty record"
        (synthExpr (context nonEmpty) (parseTestTerm "head record"))
      assertError (synthExpr (context (bTrue BKRec))
        (parseTestTerm "head record"))

  , testCase "open record obligations reach CVC5 and fail there" $ do
      let obligation = cPred ((unaryPredOp BNot) (emptyP (PVar "R")))
      let script = toSmt obligation
      assertBool "open variable is emitted without a declaration"
        ("var_82" `T.isInfixOf` script && not ("declare-const var_82" `T.isInfixOf` script))
      assertErrorContaining "solver error:" (checkValid obligation)
  , testCase "formulas and Boolean type representations have distinct sorts" $ do
      checkValid (cPred (eqP PTrue PTrue)) >>= (@?= Valid)
      assertError (checkValid (cPred (eqP PTrue PBool)))
      checkValid (cAll (bind "b" BKBool PTrue)
        (cPred (eqP (PVar "b") ((unaryPredOp BNot) ((unaryPredOp BNot) (PVar "b")))))) >>= (@?= Valid)
      assertError (checkValid (cAll (bind "b" BKBool PTrue)
        (cPred (PVar "b"))))
      checkValid (cAll (bind "b" BKBool (PVar "b")) (cPred (PVar "b"))) >>= (@?= Valid)

  , testCase "checked SMT boundary rejects malformed core formulas" $ do
      mapM_ (\t -> assertError (Exception.evaluate (typeToPred t)))
        [TLambda "x" (TBound 0), TApp TInt TInt]
      mapM_ (assertRejected . cPred)
        [PTypeBound 0, PBound 0, eqP (labelSetP PRecNil) PInt]
      assertInvalid (cAll (bind "b" BKType PTrue) (cPred (PVar "b")))
      assertInvalid (cPred (memberP PInt (labelSetP PRecNil)))
      assertInvalid (cPred (emptyP PTrue))
      assertInvalid (cPred PInt)
      assertInvalid (cAnd [cPred PFalse, cPred PInt])

  , testCase "label-set equality validates both operands" $ do
      let row = PRecCons (PLabel "x") PInt PRecNil
      checkValid (cPred (eqP (labelSetP row) (labelSetP row))) >>= (@?= Valid)
      assertError (checkValid
        (cPred (eqP (labelSetP row) (labelSetP PRecNil))))

  , testCase "SMT rejects universal operands before considering classifiers" $ do
      let a = forallType "a" (bTrue BKType) (TBound 0)
          b = forallType "b" (bTrue BKRec) (TBound 0)
      mapM_ (\t -> assertError (Exception.evaluate (typeToPred t)))
        [(binaryTypeOp BEq) a a,(binaryTypeOp BEq) a b,
         (unaryTypeOp BNot) ((binaryTypeOp BEq) a b)]

  , testCase "SMT identifiers cannot collide after escaping" $ do
      let goal = cAll (bind "a-b" BKType (eqP (PVar "a-b") PInt))
            (cAll (bind "a_b" BKType (eqP (PVar "a_b") PBool))
              (cPred (eqP (PVar "a-b") (PVar "a_b"))))
      assertError (checkValid goal)

  , testCase "refinements and constraints store predicate constructors" $ do
      refinement "p" (eqP PInt PString) @?= Refined "p" (eqP PInt PString)
      cPred ((unaryPredOp BNot) PFalse) @?= CPred ((unaryPredOp BNot) PFalse)
  , testCase "propositional connectives agree with every truth-table row" $ do
      let bool True = TTrue
          bool False = TFalse
          ops = [((binaryTypeOp BAnd), (&&)), ((binaryTypeOp BOr), (||))]
      mapM_ (\(constructor, operation) -> mapM_ (\(a,b) -> do
        let expression = constructor (bool a) (bool b)
            result = bool (operation a b)
        validateAnfType (elaborate expression) @?= Right ()
        checkValid (cPred (eqP (predicateOf expression) (predicateOf result))) >>= (@?= Valid)
        assertError (checkValid (cPred (eqP (predicateOf expression)
          ((unaryPredOp BNot) (predicateOf result)))))
        let vc = checkRaw emptyContext expression (bTrue BKBool)
        validateConstraint vc >>= (@?= ())) [(a,b) | a <- [False,True], b <- [False,True]]) ops

  , testCase "symbolic propositional laws are solver checked" $ do
      let p = PVar "p"
          q = PVar "q"
          close = cAll (bind "p" BKBool PTrue) . cAll (bind "q" BKBool PTrue) . cPred
      checkValid (close (eqP ((binaryPredOp BOr) ((unaryPredOp BNot) p) q)
        ((unaryPredOp BNot) ((binaryPredOp BAnd) p ((unaryPredOp BNot) q))))) >>= (@?= Valid)
      assertError (checkValid
        (close (eqP ((binaryPredOp BAnd) p q) ((binaryPredOp BOr) p q))))
      -- Structural classification is independent of Boolean reachability.
      mapM_ (\left -> assertError (Exception.evaluate
        (checkRaw emptyContext ((binaryTypeOp BOr) left TInt)
          (bTrue BKBool)))) [TTrue, TFalse]

  , testCase "logical parsing has defined precedence and associativity" $ do
      parseTestType "KTrue || KFalse && KTrue" @?=
        (binaryTypeOp BOr) TTrue ((binaryTypeOp BAnd) TFalse TTrue)
      parseTestType "TInt == TInt && TString == TString" @?=
        (binaryTypeOp BAnd) ((binaryTypeOp BEq) TInt TInt) ((binaryTypeOp BEq) TString TString)
      parsePred "KTrue || KFalse && KTrue" @?=
        Right ((binaryPredOp BOr) PTrue ((binaryPredOp BAnd) PFalse PTrue))
      parsePred "implies" @?= Right (PVar "implies")
      parsePred "iff" @?= Right (PVar "iff")
  , testCase "source refinements preserve id and operand sorts" $ do
      mapM_ (\kind -> assertError (Exception.evaluate
        (checkRaw emptyContext TInt kind) >>= checkValid))
        [ KBase BKType (refinement "v" PInt)
        , KBase BKType (refinement "v" (eqP (labelSetP PRecNil) PInt))
        ]
      let source = "labels [| `x : TInt |] == labels [| `x : TBool |]"
      predicate <- either assertFailure pure (parsePred source)
      checkValid (CPred predicate) >>= (@?= Valid)
      case parseType source of
        Left _ -> pure (); Right _ -> assertFailure "label sets accepted as types"
  ]

eqP :: Pred -> Pred -> Pred
eqP left right = (binaryPredOp BEq left right)

concatP :: Pred -> Pred -> Pred
concatP left right = (binaryPredOp BConcat left right)

emptyP :: Pred -> Pred
emptyP = unaryPredOp BEmpty

labelSetP :: Pred -> Pred
labelSetP = PLabSet

memberP :: Pred -> Pred -> Pred
memberP left right = (PMember left right)

synthConstraint :: Type -> IO Cstr
synthConstraint ty = pure (fst (synth emptyContext ty))

assertInvalid :: Cstr -> IO ()
assertInvalid = assertError . checkValid

rejectDestructor :: Type -> IO ()
rejectDestructor destructor = synthConstraint destructor >>= assertInvalid

assertRejected :: Cstr -> Assertion
assertRejected constraint = assertError (Exception.evaluate (toSmt constraint))

isPrefixOf :: String -> String -> Bool
isPrefixOf prefix value = take (length prefix) value == prefix
