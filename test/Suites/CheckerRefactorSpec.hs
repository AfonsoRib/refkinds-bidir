{-# LANGUAGE OverloadedStrings #-}
module Suites.CheckerRefactorSpec (tests) where

import Check
import Constraint
import Context
import Parser
import Suites.Common (checkExpr)
import qualified Data.Text as Text
import Test.Tasty
import Test.Tasty.HUnit
import Support.Expected
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

poly :: Type
poly = ty "forall A :: KType. A"
tests :: TestTree
tests = testGroup "Accepted checker refactor"
  [ testCase "top-level forall synthesizes KGen" $ case synthRaw emptyContext poly of
      (c,KGen {}) -> valid c
      other -> assertFailure (show other)
  , testCase "KGen is below plain KType" $
      valid (sub emptyContext (kind "KGen A :: KType. KType") (bTrue BKType))
  , testCase "forall accepts plain and rejects refined KType goals" $ do
      valid (checkRaw emptyContext poly (bTrue BKType))
      invalid (checkRaw emptyContext poly (kind "{v :: KType | v == TInt}"))
  , testCase "nested forall synthesizes recursively" $
      valid (fst (synthRaw emptyContext
        (ty "forall A :: KType. forall B :: KType. B")))
  , testCase "KType constructors reject universal components" $
      mapM_ (assertPureError . synthConstraint)
        [TArrow poly TInt,TArrow TInt poly,TRef poly,TCol poly,TRecCons (TLabel "p") poly TRecNil]
  , testCase "quoted universal predicates are rejected" $
      mapM_ (\operand -> assertError (Exception.evaluate (typeToPred operand)))
        [poly,TRef poly,TArrow TInt poly,TRecCons (TLabel "p") poly TRecNil]
  , testCase "rank-1 term abstraction and instantiation work" $ do
      e <- either assertFailure pure (parseExpr
        "((tfun A -> fun x -> x) : forall A :: KType. A -> A) [TInt]")
      checkExpr emptyContext e (TArrow TInt TInt) >>= (@?= ())
  , testCase "empty is total and recognizes exactly the empty record" $ do
      mapM_ (\t -> do
        valid (checkRaw emptyContext ((unaryTypeOp BEmpty) t) (bTrue BKBool))
        let p = (unaryPredOp BEmpty (predicateOf t))
        if t == TRecNil
          then do
            checkValid (CPred p) >>= (@?= Valid)
            assertError (checkValid (CPred ((unaryPredOp BNot) p)))
          else do
            assertError (checkValid (CPred p))
            checkValid (CPred ((unaryPredOp BNot) p)) >>= (@?= Valid))
        [TRecNil,TRecCons (TLabel "x") TInt TRecNil,TInt,TTrue,TLabel "x",TRef TInt]
  , testCase "KType binders include the record validity theory" $ do
      let script = toSmt (CAll (Bind (TypeSymbol "t") BKType PTrue) CTrue)
      assertBool "record theory emitted for KType alone" ("define-fun-rec isRec" `Text.isInfixOf` script)
  , testCase "value membership does not cross incompatible base kinds" $ do
      let refKind = KBase BKType (Refined "v" (eqP (PBound 0) (PRef PInt)))
          ctx = addTypeVar "T" refKind emptyContext
      assertPureError (implicationConstraint "T" refKind
        (checkRaw ctx ((unaryTypeOp BRefOf) (TVar "T")) (bTrue BKType)))
      assertPureError (sub emptyContext (bTrue BKType) (bTrue BKRef))
      assertPureError
        (checkRaw emptyContext ((unaryTypeOp BRefOf) TInt) (bTrue BKType))
  , testCase "empty encoding uses no label-set theory" $ do
      let script = toSmt (CPred ((unaryPredOp BEmpty PInt)))
      assertBool "empty-record recognizer" ("is-TypeRecEmpty TypeInt" `Text.isInfixOf` script)
      mapM_ (\symbol -> assertBool (Text.unpack symbol) (not (symbol `Text.isInfixOf` script)))
        ["labSet","set.empty","isRec"]
  , testCase "open operands survive SMT tautologies and definedness translation" $ do
      let atom = eqP (PVar "open") PInt
          predicates = [(binaryPredOp BOr) atom PTrue,(binaryPredOp BOr) ((unaryPredOp BNot) atom) PTrue,
            (unaryPredOp BNot) ((binaryPredOp BAnd) atom PFalse)]
          scope = CAll (Bind (TypeSymbol "open") BKType PTrue)
      mapM_ (\p -> mapM_ (\construct -> do
        assertError (checkValid (construct p))
        checkValid (scope (construct p)) >>= (@?= Valid))
        [CPred,defined]) predicates
  , testCase "split proofs retain their binder assumptions and definedness" $ do
      let row = PRecCons (PLabel "x") PInt PRecNil
          scope = CAll (Bind (TypeSymbol "r") BKRec (eqP (PVar "r") row))
          selected = eqP ((unaryPredOp BHead (PVar "r"))) PInt
      checkValid (scope (CAnd [defined selected,CPred selected,CPred selected])) >>= (@?= Valid)
      assertError (checkValid (scope (CAnd [CPred selected,
        CPred (eqP ((unaryPredOp BHead (PVar "r"))) PBool)])))
  , testCase "selectors require constructor recognition even under negation" $
      mapM_ (\selector -> do
        let atom = eqP (selector PInt) PInt
        assertError (checkValid (CPred atom))
        assertError (checkValid (CPred ((unaryPredOp BNot) atom))))
        [ unaryPredOp BHead, unaryPredOp BTail, unaryPredOp BHeadLabel
        , unaryPredOp BDom, unaryPredOp BImg
        , unaryPredOp BRefOf, unaryPredOp BColOf
        ]
  , testCase "equality guards establish each selector's constructor" $ do
      let record = PRecCons (PLabel "x") PInt PRecNil
          operations =
            [ (unaryPredOp BHead,record,PInt)
            , (unaryPredOp BTail,record,PRecNil)
            , (unaryPredOp BHeadLabel,record,PLabel "x")
            , (unaryPredOp BDom,PArrow PInt PBool,PInt)
            , (unaryPredOp BImg,PArrow PInt PBool,PBool)
            , (unaryPredOp BRefOf,PRef PInt,PInt)
            , (unaryPredOp BColOf,PCol PInt,PInt)
            ]
      mapM_ (\(selector,value,result) -> do
        let premise = eqP (PBound 0) value
            selected = eqP (selector (PBound 0)) result
            declaration p = fst (synthRaw emptyContext
              (TForall "A" (KBase BKType (Refined "v" p)) TInt))
        valid (declaration ((binaryPredOp BAnd) premise selected))
        invalid (declaration ((binaryPredOp BAnd) selected premise))) operations
  , testCase "unused generalized parameters need no SMT value binder" $
      valid (fst (synthRaw emptyContext (ty "forall P :: KGen A :: KType. KType. TInt")))
  , testCase "record selectors also require valid unique-label records" $ do
      let malformed = [PRecCons (PLabel "x") PInt (PRecCons (PLabel "x") PBool PRecNil),
                       PRecCons (PLabel "x") PInt PInt]
      mapM_ (\bad -> mapM_ (\selector ->
        assertError (checkValid (defined (eqP (selector bad) PInt))))
        [unaryPredOp BHead,unaryPredOp BTail,unaryPredOp BHeadLabel]) malformed
  , testCase "ordered guards permit unreachable undefined selectors" $ do
      let bad = eqP ((unaryPredOp BHead PInt)) PInt
      mapM_ (\p -> checkValid (defined p) >>= (@?= Valid))
        [(binaryPredOp BAnd) PFalse bad,(binaryPredOp BOr) PTrue bad,(binaryPredOp BOr) ((unaryPredOp BNot) PFalse) bad]
      mapM_ (\p -> assertError (checkValid (defined p)))
        [(binaryPredOp BAnd) PTrue bad,(binaryPredOp BOr) PFalse bad,(binaryPredOp BOr) ((unaryPredOp BNot) PTrue) bad,eqP PFalse bad]
  , testCase "Boolean operands must be defined" $ do
      assertError (checkValid (defined (id PInt)))
      assertError (checkValid (defined ((unaryPredOp BNot) (id PInt))))
  , testCase "literal cleanup cannot erase an undefined left operand" $ do
      let bad = eqP ((unaryPredOp BHead PInt)) PInt
      mapM_ (\p -> assertError (checkValid (CPred p)))
        [(unaryPredOp BNot) bad,(binaryPredOp BOr) bad PTrue,(binaryPredOp BOr) ((unaryPredOp BNot) bad) PTrue,(unaryPredOp BNot) ((binaryPredOp BAnd) bad PFalse)]
  , testCase "guarded refinements establish selector definedness through CVC5" $ do
      mapM_ (\k -> valid (fst (synthRaw emptyContext (TForall "R" (kind k) TInt))))
        ["{r :: KRec | not (empty r) && head r == TInt}",
         "{r :: KRec | empty r || head r == TInt}",
         "{r :: KRec | not (not (empty r) && not (head r == TInt))}"]
      invalid (fst (synthRaw emptyContext
        (TForall "R" (kind "{r :: KRec | head r == TInt}") TInt)))

  ]
  where
    defined predicate = cGuard [] predicate CTrue
    synthConstraint t = fst (synthRaw emptyContext t)
    eqP left right = (binaryPredOp BEq left right)
