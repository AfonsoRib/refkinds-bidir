{-# LANGUAGE OverloadedStrings #-}
module Suites.EqualityBoundarySpec (tests) where

import Check (synthRaw)
import Constraint
import Context hiding (implicationConstraint)
import Check (checkTypeEquality)
import Parser
import qualified Data.Text as Text
import qualified Control.Exception as Exception
import Support.Errors (assertError, assertPureError)
import Test.Tasty
import Test.Tasty.HUnit
import Types

kind :: String -> Rkind
kind = either error id . parseKind
ty :: String -> Type
ty = either error id . parseType
rejectEither :: Show a => Either a b -> Assertion
rejectEither (Left _) = pure ()
rejectEither (Right _) = assertFailure "unsupported universal boundary accepted"
convert :: String -> String -> String -> IO ()
convert k a b = checkTypeEquality emptyContext (kind k) (ty a) (ty b)

tests :: TestTree
tests = testGroup "Universal equality boundary"
  [ testCase "alpha-renamed universals compare structurally at KGen" $
      convert "KGen X :: KType. KType" "forall A :: KType. A" "forall B :: KType. B" >>= (@?= ())
  , testCase "refinement-assisted universal body equality is rejected" $
      assertError (convert "KGen X :: {v :: KType | v == TInt}. KType"
        "forall A :: {v :: KType | v == TInt}. A"
        "forall B :: {v :: KType | TInt == v}. TInt")
  , testCase "opened bodies are normalized before alpha comparison" $
      convert "KGen X :: KType. KType"
        "forall A :: KType. ((refOf (TRef A)) :: KType)" "forall B :: KType. B" >>= (@?= ())
  , testCase "unequal unrestricted bodies fail without an SMT universal fallback" $
      assertError (convert "KGen X :: KType. KType"
        "forall A :: KType. A" "forall B :: KType. TInt")
  , testCase "one-way domain inclusion is insufficient" $
      assertError (convert "KGen X :: {v :: KType | v == TInt}. KType"
        "forall A :: KType. TInt" "forall B :: {v :: KType | v == TInt}. TInt")
  , testCase "empty domains do not make distinct bodies alpha-equivalent" $
      assertError (convert "KGen X :: {v :: KType | KFalse}. KType"
        "forall A :: {v :: KType | KFalse}. TInt"
        "forall B :: {v :: KType | KFalse}. TBool")
  , testCase "record refinements do not rewrite universal bodies" $
      assertError (convert "KGen X :: {r :: KRec | not (empty r) && head r == TInt}. KType"
        "forall A :: {r :: KRec | not (empty r) && head r == TInt}. head A"
        "forall B :: {r :: KRec | not (empty r) && head r == TInt}. TInt")
  , testCase "universal singleton syntax is rejected during parsing" $
      rejectEither (parseKind "{v :: KType | v == (forall A :: KType. A)}")
  , testCase "abstract KType values cannot equal a concrete universal" $ do
      let u = ty "forall A :: KType. A"
      assertPureError (synthRaw
        (addTypeVar "P" (bTrue BKType) emptyContext)
        ((binaryTypeOp BEq) (TVar "P") u))
  , testCase "SMT rejects universals at every quoted operand depth" $ do
      let u = ty "forall A :: KType. A"
      mapM_ (\v -> assertError (Exception.evaluate (typeToPred v)))
        [u,TRef u,TCol u,TArrow TInt u,TRecCons (TLabel "u") u TRecNil,
         TAnn u (kind "KGen A :: KType. KType")]
  , testCase "unreachable predicates do not admit executable syntax" $ do
      rejectEither (parseKind "{v :: KType | KTrue || (forall A :: KType. A) == TInt}")
      rejectEither (parseKind "{v :: KType | KTrue || (fun A -> A) == TInt}")
  , testCase "first-order scripts declare no polymorphic machinery" $ do
      let script = toSmt
            (CPred ((binaryPredOp BEq (PRef PInt)
              (PRef PInt))))
      mapM_ (\symbol -> assertBool (Text.unpack symbol) (not (symbol `Text.isInfixOf` script)))
        ["TypePoly","polyMap","poly_","appTyp","KindSyntax","declare-fun"]
  , testCase "ambient dependencies remain distinct after evaluation" $ do
      let ctx = addTypeVar "Ambient" (bTrue BKType) emptyContext
      assertError (checkTypeEquality ctx (kind "KGen A :: KType. KType")
        (ty "forall A :: KType. Ambient") (ty "forall B :: KType. TInt")
        )
  , testCase "nested universal equality validates before reflexivity" $
      convert "KGen A :: KType. KGen B :: KType. KType"
        "forall A :: KType. forall B :: KType. A"
        "forall A :: KType. forall B :: KType. A"
  ]
