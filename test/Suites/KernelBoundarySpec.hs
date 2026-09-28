{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
module Suites.KernelBoundarySpec (tests) where

import qualified Check
import Constraint
import Context hiding (implicationConstraint)
import qualified Data.Text as Text
import Parser (parseExpr, parseType)
import Suites.Common (assertClosedValid, assertClosedInvalid, checkExpr, synthExpr)
import Suites.Common (parseTestType, parseTestKind)
import Support.AstInvariants (validateTypeAst)
import Support.Universal (forallType)
import Suites.Common (universalDomainConstraint)
import Types
import Test.Tasty
import Test.Tasty.HUnit
import qualified Control.Exception as Exception
import Support.Errors (assertError, assertPureError)

tests :: TestTree
tests = testGroup "Validated checker protocol"
  [ testCase "term judgments require a well-formed caller context" $ do
      let ctx = addTermVar "x" TInt
              (addTypeVar "A" (bTrue BKType) emptyContext)
      synthExpr ctx EUnit >>= (@?= TUnit)
  , testCase "normalization cannot erase an ill-formed predicate" $ do
      let lambda = TLambda "x" (TBound 0)
      rejectDirect (typeToPred lambda)
      get (universalDomainConstraint emptyContext (KBase BKType
        (refinement "v" (eqP PInt PInt)))) >>= assertClosedValid
  , testCase "removed syntax and invalid characters return parse errors" $ do
      rejectEither (parseType "if TInt :: KType as X => X else TInt")
      rejectEither (parseExpr "if TInt :: KType as X => () else ()")
      rejectEither (parseExpr "~")
  , testCase "polymorphic arrow fields are rejected at KType" $
      rejectDirect (Check.checkRaw emptyContext
        (parseTestType "TInt -> ((forall l :: KLabel. [| l : TInt |]) :: KGen l :: KLabel. KType)") (bTrue BKType))
  , testCase "ANF requires source checking information in arrow fields" $ do
      c <- get (Check.checkRaw emptyContext
        (parseTestType "forall R :: KRec. ((R -> ((if empty R then TInt else TBool) :: KType)) :: KType)")
        (parseTestKind "KGen R :: KRec. KType"))
      assertClosedValid c
  , testCase "domain assumptions do not require inhabitation" $ do
      get (universalDomainConstraint emptyContext (KBase BKType (refinement "v" PFalse)))
        >>= assertClosedValid
  , testCase "public rules accept ordinary context and classifier syntax" $ do
      get (Check.checkKind emptyContext TInt (bTrue BKType)) >>= assertClosedValid
      checkExpr emptyContext EUnit TUnit >>= (@?= ())
  , testCase "SMT encoding preserves generated Boolean structure" $ do
      let p = eqP (PVar "A") PInt
          close = cAll (bind "A" BKType PTrue)
          raw = close (cPred ((binaryPredOp BAnd) PTrue ((binaryPredOp BOr) PTrue p)))
      let script = toSmt raw
      assertBool "true conjunction was folded"
        ("(and true (or true" `Text.isInfixOf` script)
      assertBool "literal negation was folded"
        ("(not false)" `Text.isInfixOf` toSmt (cPred ((unaryPredOp BNot) PFalse)))
      checkValid raw >>= (@?= Valid)
  , testCase "cleanup does not normalize universal binder predicates" $ do
      let u = forallType "X" (KBase BKType (Refined "v" ((binaryPredOp BAnd) PTrue PTrue))) TInt
      rejectDirect (typeToPred u)
  , testCase "test-only AST validation catches malformed conversion input" $
      case validateTypeAst ((binaryTypeOp BEq) (TBound 0) (TBound 0)) of
        Left _ -> pure ()
        Right () -> assertFailure "expected malformed AST rejection"
  , testCase "unconstrained application contracts do not justify conversion" $ do
      let ctx = addTypeVar "F" (KPi "a" (bTrue BKType) (bTrue BKType)) emptyContext
          expression = EVar "value"
          withValue = addTermVar "value" (TApp (TVar "F") TInt) ctx
      assertError (checkExpr withValue expression TBool)
  , testCase "closing a let cannot weaken a function domain" $ do
      let ctx = addTypeVar "F"
            (parseTestKind "Pi a :: KType. Pi y :: { v :: KType | v == a }. KType")
            (addTypeVar "G" (KPi "a" (bTrue BKType) (bTrue BKType)) emptyContext)
          program = parseTestType "let X = G TInt in F X"
      rejectDirect (Check.synthRaw ctx program)
  , testCase "ordinary constructors cannot consume refinement variables" $ do
      mapM_ (rejectDirect . Check.synthKind emptyContext)
        [(unaryTypeOp BHead) (TVar "r"), TArrow (TVar "r") TInt, (unaryTypeOp BEmpty) (TVar "r")]
  , testCase "predicate witnesses and type names remain distinct" $ do
      let ctx = addTypeVar "r" (bTrue BKLabel) emptyContext
          k = KBase BKType (Refined "v"
            ((binaryPredOp BAnd) ((unaryPredOp BNot) (emptyP (PRefVar "r")))
              (eqP ((unaryPredOp BHeadLabel (PRefVar "r"))) (PVar "r"))))
          scope = cAll (bind (TypeSymbol "r") BKLabel PTrue)
                . cAll (bind (RefSymbol "r") BKRec PTrue)
      get (universalDomainConstraint ctx k) >>= assertClosedValid . scope
      assertError (checkValid (universalDomainConstraint emptyContext k))
  , testCase "nested refinements shadow their display hints without capture" $ do
      let nested = parseTestType "forall r :: KRec. forall A :: { r :: KType | r == TInt }. A"
      validateTypeAst nested @?= Right ()
      let (constraint, _) = Check.synthRaw emptyContext nested
      assertClosedValid constraint
  , testCase "core checks reject malformed goals and annotations" $ do
      let malformed = KBase BKType (Refined "v" (id PInt))
      invalidConstraint (Check.checkKind emptyContext TInt malformed)
      invalidConstraint (fst (Check.synthKind emptyContext (TAnn TInt malformed)))
      invalidConstraint (Check.checkKind emptyContext (TLambda "a" TInt)
        (KPi "a" malformed (bTrue BKType)))
      invalidConstraint (Check.checkKind emptyContext (TRec "bad" (TAnn TInt malformed) TInt) (bTrue BKType))
  , testCase "a recursive classifier cannot justify its own selector" $ do
      let k = parseTestKind "{ r :: KRec | head r == TInt }"
      get (Check.checkKind emptyContext
        (TRec "bad" (TAnn (TBound 0) k) TInt) (bTrue BKType)) >>= assertClosedInvalid
  , testCase "refinement names remain separate and require explicit logical scope" $ do
      let scoped = cAll (bind (RefSymbol "r") BKRec PTrue)
      rejectDirect (Check.synthKind emptyContext (TVar "r"))
      rejectDirect (Check.checkKind emptyContext (TVar "r") (bTrue BKRec))
      get (universalDomainConstraint emptyContext
        (KBase BKType (Refined "v" (emptyP (PRefVar "r")))))
        >>= assertClosedValid . scoped
  ]
  where
    get = pure
    rejectEither result = case result of
      Left _ -> pure ()
      Right _ -> assertFailure "expected a validation error"
    rejectDirect value = assertPureError value
    eqP left right = (binaryPredOp BEq left right)
    emptyP = unaryPredOp BEmpty

invalidConstraint :: Cstr -> Assertion
invalidConstraint c = assertError (Exception.evaluate c >>= checkValid)
