{-# LANGUAGE OverloadedStrings #-}
module Suites.EmbeddedTypeSpec (tests) where

import ANF (elaborateExpr)
import qualified Data.Text as Text
import qualified Check
import Context hiding (implicationConstraint)
import Parser (parseExpr, parseType)
import Suites.Common (checkExpr, synthExpr)
import Support.AstInvariants (validateAnfExpr)
import Test.Tasty
import Test.Tasty.HUnit
import Types
import Support.Errors (assertError, assertErrorContaining)

tests :: TestTree
tests = testGroup "Embedded type bindings"
  [ testCase "nested type lets check inside a term annotation" $
      accepted "3 : (let A = TInt in let B = A in B)" TInt
  , testCase "recursive type definitions check their annotation and continuation" $
      accepted "3 : (letrec Id :: Pi A :: KType. KType = fun A -> A in Id TInt)"
        TInt
  , testCase "wrong values and invalid unused type definitions are rejected" $
      mapM_ rejected
        [ "let x : (let A = TBool in A) = 3 in x"
        , "let x : (letrec Bad :: Pi A :: KType. KRec = fun A -> TInt in TInt) = 3 in x"
        , "let x : (let Bad = head [||] in TInt) = 3 in x"
        ]
  , testCase "an annotation cannot export its local type name" $
      rejected "let x : (let A = TInt in A) = 3 in (x : A)"
  , testCase "type argument bindings remain inside ETApp through ANF" $ do
      source <- parsed "f [let A = TInt in A]"
      let core = elaborateExpr source
      core @?= ETApp (EVar "f") (TLet (Decl "A" TInt) (TBound 0))
      validateAnfExpr core @?= Right ()
      elaborateExpr core @?= core
  , testCase "computed polymorphic arguments are checked and instantiated" $
      accepted (identity ++ " [let A = TInt in A]") (TArrow TInt TInt)
  , testCase "recursive polymorphic arguments are checked and instantiated" $
      accepted (identity ++ " [letrec Id :: Pi A :: KType. KType = fun A -> A in Id TInt]")
        (TArrow TInt TInt)
  , testCase "a computed polymorphic argument still enforces its kind" $ do
      expression <- parsed
        ("((tfun A -> fun x -> x) : (forall A :: KLabel. TInt -> TInt)) " ++
          "[let A = TInt in A] 7")
      assertErrorContaining "incompatible basic kinds"
        (checkExpr emptyContext expression TInt)
  , testCase "embedded lets respect separate term and type scopes" $ do
      source <- parsed "tfun A -> fun x -> (x : (let B = A in B))"
      source @?= ETLambda "A" (ELambda "x"
        (EAnn (EBound 0) (TLet (Decl "B" (TBound 0)) (TBound 0))))
      case source of
        ETLambda _ body -> instantiateExprType TInt body @?=
          Right (ELambda "x" (EAnn (EBound 0) (TLet (Decl "B" TInt) (TBound 0))))
        other -> assertFailure (show other)
      validateAnfExpr (elaborateExpr source) @?= Right ()
  , testCase "term ANF inspects the embedded type computation" $ do
      let badType = TApp (TVar "F") (TApp (TVar "G") (TVar "A"))
      mapM_ (\source -> do
        validateAnfExpr source @?= Left "expression is not in ANF"
        let core = elaborateExpr source
        validateAnfExpr core @?= Right ()
        elaborateExpr core @?= core)
        [ EAnn EUnit badType, ETApp (EVar "f") badType
        ]
  , testCase "published Map annotation computes all fields and preserves labels" $ do
      source <- readFile "examples/map-annotation.rk"
      accepted source TBool
  , testCase "refined generalized identity accepts Bool and Int only" $ do
      restrictedForall <- either assertFailure pure (parseType
        ("((forall a :: { a :: KType | a == TBool || a == TInt }. a -> a) :: " ++
         "KGen a :: { a :: KType | a == TBool || a == TInt }. " ++
         "{ v :: KFun | v == (a -> a) && (img v == TBool || img v == TInt) })"))
      _ <- Check.validateTypeKind emptyContext restrictedForall (bTrue BKType)
      source <- readFile "examples/poly-id-refined.rk"
      accepted source TInt
      let boolSource = Text.unpack
            (Text.replace "[TInt]) 42" "[TBool]) True" (Text.pack source))
      accepted boolSource TBool
      let unitSource = Text.unpack
            (Text.replace "[TInt]) 42" "[TUnit]) ()" (Text.pack source))
      expression <- parsed unitSource
      assertError (synthExpr emptyContext expression)
  , testCase "Map annotation rejects a wrong field type or label" $ do
      source <- Text.pack <$> readFile "examples/map-annotation.rk"
      accepted (Text.unpack source) TBool
      mapM_ (\(from, to) -> do
        expression <- parsed (Text.unpack (Text.replace from to source))
        assertError (synthExpr emptyContext expression))
        [("first = True", "first = 7"), ("first = True", "wrong = True")]
  ]

identity :: String
identity = "((tfun A -> fun x -> x) : (forall A :: KType. A -> A))"

parsed :: String -> IO Expr
parsed = either assertFailure pure . parseExpr

accepted :: String -> Type -> Assertion
accepted source expected = do
  expression <- parsed source
  let core = elaborateExpr expression
  validateAnfExpr core @?= Right ()
  checkExpr emptyContext expression expected >>= (@?= ())
  checkExpr emptyContext core expected >>= (@?= ())

rejected :: String -> Assertion
rejected source = do
  expression <- parsed source
  assertError (checkExpr emptyContext expression TInt)
