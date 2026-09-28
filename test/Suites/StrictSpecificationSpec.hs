{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE LambdaCase #-}
module Suites.StrictSpecificationSpec
  ( tests, normalizationProbe, exposureProbe, typeApplicationProbe
  , equalityProbe, kindFailureProbe, quotationProbe
  ) where

import ANF
import Check
import Context hiding (implicationConstraint)
import Control.Exception (evaluate)
import Suites.Common
  ( assertClosedInvalid, assertClosedValid, checkExpr, parseTestKind
  , parseTestTerm, parseTestType, synthExpr
  )
import System.Environment (getExecutablePath)
import System.Exit (ExitCode(..))
import Data.List (isInfixOf)
import System.Process (readProcessWithExitCode)
import System.Timeout (timeout)
import Test.Tasty
import Test.Tasty.HUnit
import Support.AstInvariants (validateAnfExpr, validateAnfType)
import Support.Universal (forallType)
import Suites.Common (universalDomainConstraint)
import Types
import Support.Errors (assertError, captureError)

tests :: TestTree
tests = testGroup "Strict interview specification"
  [ testCase "kind checking-only families need explicit annotations" $ do
      mapM_ (\ty -> do
        rejectPure (synthRaw emptyContext ty)
        get (checkRaw emptyContext ty (bTrue BKType)) >>= assertClosedValid
        (vc,k) <- get (synthRaw emptyContext (TAnn ty (bTrue BKType)))
        k @?= bTrue BKType
        assertClosedValid vc)
        [parseTestType "let X = TInt in X", TIf TTrue TInt TBool,
         parseTestType "letrec X :: KType = TInt in X"]
      rejectPure (checkRaw emptyContext (TRec "x" TInt TInt) (bTrue BKType))
  , testCase "term checking-only families need explicit annotations" $ do
      mapM_ (\e -> do
        rejectIO (synthExpr emptyContext e)
        checkExpr emptyContext e TInt >>= (@?= ())
        synthExpr emptyContext (EAnn e TInt) >>= (@?= TInt))
        [parseTestTerm "let x = 1 in x", parseTestTerm "if True then 1 else 2",
         parseTestTerm "letrec f : TInt -> TInt = fun x -> x in 1"]
  , testCase "recursive declaration and continuation have different classifiers" $ do
      get (checkRaw emptyContext
        (parseTestType "letrec F :: Pi X :: KType. KType = fun X -> X in TInt")
        (bTrue BKType)) >>= assertClosedValid
      checkExpr emptyContext (parseTestTerm "letrec f : TInt -> TInt = fun x -> x in True") TBool
        >>= (@?= ())
      rejectIO (checkExpr emptyContext
        (parseTestTerm "letrec f : TInt -> TInt = fun x -> True in True") TBool)
  , testCase "ANF names literal arguments at both levels" $ do
      case elaborate (TApp (TVar "F") TInt) of
        TLet (Decl _ TInt) (TApp (TVar "F") (TBound 0)) -> pure ()
        other -> assertFailure (show other)
      case elaborateExpr (EApp (EVar "f") (EInteger 1)) of
        ELet _ (EInteger 1) (EApp (EVar "f") (EBound 0)) -> pure ()
        other -> assertFailure (show other)
      validateAnfType (TApp (TVar "F") TInt) @?= Left "type is not in ANF"
      validateAnfExpr (EApp (EVar "f") (EInteger 1)) @?= Left "expression is not in ANF"
  , testCase "ANF is idempotent for nested term and type lets" $ do
      let term = parseTestTerm "let a = f (g x) in f a"
          ty = parseTestType "let A = F (G X) in F A"
      elaborateExpr (elaborateExpr term) @?= elaborateExpr term
      elaborate (elaborate ty) @?= elaborate ty
  , testCase "nested applications use the surrounding checking boundary" $ do
      let ctx = addTermVar "x" TInt (addTermVar "f" (TArrow TInt TInt)
            (addTermVar "g" (TArrow TInt TInt) emptyContext))
          e = parseTestTerm "f (g x)"
      rejectIO (synthExpr ctx e)
      checkExpr ctx e TInt >>= (@?= ())
      synthExpr ctx (EAnn e TInt) >>= (@?= TInt)
  , testCase "polymorphic application returns its evaluated declared result" $ do
      let identityKind = KPi "x" (bTrue BKType) (bTrue BKType)
          identity = TAnn (TLambda "x" (TBound 0)) identityKind
          polymorphic = forallType "X" (bTrue BKType)
            (TLet (Decl "Id" identity)
              (TAnn (TArrow (TBound 1) (TApp (TBound 0) (TBound 1)))
                (bTrue BKType)))
          ctx = addTermVar "f" polymorphic
            (addTypeVar "A" (bTrue BKType) emptyContext)
      synthExpr ctx (ETApp (EVar "f") (TVar "A"))
        >>= (@?= (TArrow (TVar "A") (TVar "A")))
      rejectIO (checkExpr ctx (ETApp (EVar "f") (TVar "A")) TInt)

  , testCase "hoisted conditionals require source annotations" $ do
      rejectPure (checkRaw emptyContext
        (parseTestType "((forall R :: KRec. R -> (if empty R then TInt else TBool)) :: KGen R :: KRec. KType)") (bTrue BKType))
      get (checkRaw emptyContext
        (parseTestType "forall R :: KRec. ((R -> ((if empty R then TInt else TBool) :: KType)) :: KType)") (parseTestKind "KGen R :: KRec. KType"))
        >>= assertClosedValid
  , testCase "ordered refinement guards establish selector preconditions" $ do
      get (universalDomainConstraint emptyContext (parseTestKind "{ r :: KRec | not (empty r) && head r == TInt }"))
        >>= assertClosedValid
      get (universalDomainConstraint emptyContext (parseTestKind "{ r :: KRec | head r == TInt && not (empty r) }"))
        >>= assertClosedInvalid
      get (universalDomainConstraint emptyContext (parseTestKind "{ r :: KRec | empty r || head r == TInt }"))
        >>= assertClosedValid
      get (universalDomainConstraint emptyContext (parseTestKind
        "{ r :: KRec | not (not (empty r) && not (head r == TInt)) }"))
        >>= assertClosedValid
  , testCase "Boolean guards preserve skipped checker obligations" $ do
      let invalid = (binaryTypeOp BEq) ((unaryTypeOp BHead) TRecNil) TInt
      get (checkRaw emptyContext ((binaryTypeOp BAnd) TFalse invalid) (bTrue BKBool)) >>= assertClosedInvalid
      get (checkRaw emptyContext ((binaryTypeOp BAnd) TTrue invalid) (bTrue BKBool)) >>= assertClosedInvalid
  , testCase "structural universals enforce their domain classifiers" $ do
      get (checkRaw emptyContext (forallType "l" (bTrue BKLabel)
        (TRecCons (TBound 0) TInt TRecNil)) (parseTestKind "KGen l :: KLabel. KType")) >>= assertClosedValid
      rejectPure (checkRaw emptyContext (forallType "t" (bTrue BKType)
        (TRecCons (TBound 0) TInt TRecNil)) (bTrue BKType))
  , testCase "term conversion normalizes validated selectors" $ do
      checkExpr emptyContext (EInteger 1) ((unaryTypeOp BRefOf) (TRef TInt)) >>= (@?= ())
      rejectIO (checkExpr emptyContext (EBoolean True)
        ((unaryTypeOp BRefOf) (TRef TInt)))
  , testCase "reflexive conversion succeeds but ambient-only nontrivial proofs stay open" $ do
      let ctx = addTermVar "x" (TVar "A")
            (addTypeVar "B" (KBase BKType (refinement "v"
              ((binaryPredOp BEq (PBound 0) (PVar "A")))))
              (addTypeVar "A" (bTrue BKType) emptyContext))
      checkExpr ctx (EVar "x") (TVar "A") >>= (@?= ())
      rejectIO (checkExpr ctx (EVar "x") (TVar "B"))
  , testCase "neutral selectors with open proofs fail at CVC5" $ do
      let ctx = addTermVar "r" (TVar "R") (addTypeVar "R"
            (parseTestKind "{ r :: KRec | not (empty r) && head r == TInt }") emptyContext)
      rejectIO (synthExpr ctx (EHead (EVar "r")))
      rejectIO (checkExpr ctx (EHead (EVar "r")) TInt)
  , testCase "invalid kind obligation fails before divergent normalization" $ do
      let impossible = parseTestType "let Bad = head [||] in letrec F :: Pi X :: KType. KType = fun X -> F X in F TInt"
      result <- timeout 2000000
        (captureError
          (checkType emptyContext (EAnn EUnit impossible) TUnit))
      case result of
        Just (Left _) -> pure ()
        other -> assertFailure ("kind failure must precede normalization: " ++ show other)
  , testCase "unknown kind proof never permits normalization" $ do
      executable <- getExecutablePath
      let script = unlines
            [ "mock_dir=$(mktemp -d)"
            , "trap 'rm -rf \"$mock_dir\"' EXIT"
            , "cat > \"$mock_dir/cvc5\" <<'MOCK'"
            , "#!/bin/sh"
            , "printf 'unknown\\n'"
            , "MOCK"
            , "chmod +x \"$mock_dir/cvc5\""
            , "PATH=\"$mock_dir:$PATH\" \"$1\" --kind-failure-probe"
            ]
      result <- timeout 3000000 (readProcessWithExitCode "sh" ["-c", script, "refk-test", executable] "")
      case result of
        Just (ExitFailure _, _, errors) -> assertBool errors
          ("unknown" `isInfixOf` errors)
        other -> assertFailure (show other)
  , testCase "validated divergence has no hidden conversion budget" $ do
      executable <- getExecutablePath
      result <- timeout 1500000 (readProcessWithExitCode executable ["--normalization-probe"] "")
      case result of
        Nothing -> pure ()
        Just observed -> assertFailure ("normalization unexpectedly returned: " ++ show observed)
  , testCase "CBV constructor normalization remains unbounded when evaluation diverges" $ do
      executable <- getExecutablePath
      result <- timeout 1500000
        (readProcessWithExitCode executable ["--exposure-probe"] "")
      case result of
        Nothing -> pure ()
        Just observed -> assertFailure
          ("CBV normalization unexpectedly returned: " ++ show observed)
  , testCase "construction normalization remains unbounded" $ do
      executable <- getExecutablePath
      result <- timeout 1500000
        (readProcessWithExitCode executable ["--quotation-probe"] "")
      case result of
        Nothing -> pure ()
        Just observed -> assertFailure
          ("construction normalization unexpectedly returned: " ++ show observed)
  , testCase "type application retains strict argument evaluation" $ do
      executable <- getExecutablePath
      result <- timeout 1500000
        (readProcessWithExitCode executable ["--type-application-probe"] "")
      case result of
        Nothing -> pure ()
        Just observed -> assertFailure
          ("type application skipped argument evaluation: " ++ show observed)
  , testCase "semantic equality retains full normalization" $ do
      executable <- getExecutablePath
      result <- timeout 1500000
        (readProcessWithExitCode executable ["--equality-probe"] "")
      case result of
        Nothing -> pure ()
        Just observed -> assertFailure
          ("semantic equality skipped normalization: " ++ show observed)
  , testCase "universal predicates reject opaque identities and quoted computations" $ do
      let poly body = forallType "X" (bTrue BKType) body
      mapM_ (\body -> mapM_ (rejectPure . typeToPred)
        [(binaryTypeOp BEq) (poly body) (poly body), (unaryTypeOp BNot) ((binaryTypeOp BEq) (poly body) (poly TInt))])
        [TBound 0, TVar "A", TRef TInt,
         TLet (Decl "x" TInt) (TBound 0), TIf TTrue TInt TBool,
         TApp (TLambda "x" (TBound 0)) TInt,
         forallType "Y" (bTrue BKType) (TBound 1)]

  ]
  where
    get :: a -> IO a
    get = pure

    rejectPure :: Show a => a -> Assertion
    rejectPure value = assertError (evaluate value)

    rejectIO :: Show a => IO a -> Assertion
    rejectIO = assertError

-- Executed in an isolated process with a harness deadline. The implementation
-- remains unbounded; an error or successful return makes the parent test fail.
normalizationProbe :: IO ()
normalizationProbe = do
  let loop = parseTestType "letrec F :: Pi X :: KType. KType = fun X -> F X in F TInt"
  result <- checkExpr emptyContext EUnit loop
  _ <- evaluate (length (show result))
  print result

exposureProbe :: IO ()
exposureProbe = do
  let loop = parseTestType
        "letrec F :: Pi X :: KType. KType = fun X -> F X in F TInt"
      context = addTermVar "f" loop
        (addTermVar "argument" TInt emptyContext)
  result <- synthType context (EApp (EVar "f") (EVar "argument"))
  _ <- evaluate (length (show result))
  print result

quotationProbe :: IO ()
quotationProbe = do
  let loop = parseTestType
        "letrec F :: Pi X :: KType. KType = fun X -> F X in F TInt"
      context = addTermVar "value" loop emptyContext
  result <- synthType context (ERef (EVar "value"))
  _ <- evaluate (length (show result))
  print result

typeApplicationProbe :: IO ()
typeApplicationProbe = do
  let loop = parseTestType
        "letrec F :: Pi X :: KType. KType = fun X -> F X in F TInt"
      universal = forallType "A" (bTrue BKType) TInt
      context = addTermVar "poly" universal emptyContext
  result <- synthType context (ETApp (EVar "poly") loop)
  _ <- evaluate (length (show result))
  print result

equalityProbe :: IO ()
equalityProbe = do
  let loop = parseTestType
        "letrec F :: Pi X :: KType. KType = fun X -> F X in F TInt"
  result <- checkTypeEquality emptyContext (bTrue BKType) loop loop
  _ <- evaluate (length (show result))
  print result

kindFailureProbe :: IO ()
kindFailureProbe = do
  let impossible = parseTestType "let Bad = head [||] in letrec F :: Pi X :: KType. KType = fun X -> F X in F TInt"
  checkType emptyContext (EAnn EUnit impossible) TUnit >>= print
