{-# LANGUAGE OverloadedStrings #-}
module Suites.PredicateSyntaxSpec (tests) where

import ANF (elaborate)
import Check (synthKind, checkRaw)
import Constraint
import Check (checkTypeEquality)
import Context hiding (implicationConstraint)
import Parser
import qualified Prims
import Suites.Common (checkExpr)
import Support.AstInvariants (validateAnfType)
import qualified Support.Errors as Errors
import Types
import Test.Tasty
import Test.Tasty.HUnit
import qualified Control.Exception as Exception
import Support.Errors (assertError)

tests :: TestTree
tests = testGroup "Separate predicate syntax"
  [ testCase "TypeOp inventory and arities are complete" $
      map (\operation -> (operation, typeOpArity operation)) typeOperations @?=
        zip typeOperations [2,1,1,1,1,1,1,1,1,2,1,2,2,1]

  , testCase "bare primitives expose their complete dependent kinds" $
      mapM_ (\operation -> synthKind emptyContext (PBIn operation) @?=
        (CTrue, Prims.typeOpKind operation)) typeOperations

  , testCase "declared primitive kinds have the advertised arities" $
      map (piArity . Prims.typeOpKind) typeOperations @?=
        map typeOpArity typeOperations

  , testCase "saturated primitive spines synthesize their result base kinds" $
      mapM_ assertPrimitiveResult primitiveApplications

  , testCase "partial binary applications retain one dependent argument" $
      mapM_ (\(operation, operand) -> case synthKind emptyContext
          (TApp (PBIn operation) operand) of
        (_, KPi {}) -> pure ()
        result -> assertFailure ("expected remaining Pi kind, got " ++ show result))
        [(BEq, TInt), (BConcat, TRecNil), (BOr, TTrue), (BAnd, TFalse)]

  , testCase "over-applied primitives fail kind synthesis" $
      Errors.assertPureError
        (synthKind emptyContext (TApp ((unaryTypeOp BNot) TTrue) TInt))

  , testCase "malformed predicate interpretations report their arity" $ do
      Errors.assertErrorContaining "operator BEq expects 2 operands, got 1"
        (pure (toSmt (CPred (PInterp1 BEq PInt))))
      Errors.assertErrorContaining "operator BNot expects 1 operands, got 2"
        (pure (toSmt (CPred (PInterp2 BNot PTrue PFalse))))

  , testCase "matching first-order operations convert structurally" $ do
      mapM_ (\(t,p) -> typeToPred t @?= p)
        [ (TArrow TInt TBool,PArrow PInt PBool)
        , (TRef TInt,PRef PInt)
        , (TCol TInt,PCol PInt)
        , ((binaryTypeOp BAnd) TTrue TFalse,(binaryPredOp BAnd) PTrue PFalse)
        , ((binaryTypeOp BOr) TTrue TFalse,(binaryPredOp BOr) PTrue PFalse)
        , ((unaryTypeOp BNot) TTrue,(unaryPredOp BNot) PTrue)
        , ((binaryTypeOp BEq) TInt TBool,(binaryPredOp BEq PInt PBool))
        , ((unaryTypeOp BHead) TRecNil,(unaryPredOp BHead PRecNil))
        , ((unaryTypeOp BHeadLabel) TRecNil,(unaryPredOp BHeadLabel PRecNil))
        , ((unaryTypeOp BTail) TRecNil,(unaryPredOp BTail PRecNil))
        , ((unaryTypeOp BDom) (TArrow TInt TBool),(unaryPredOp BDom (PArrow PInt PBool)))
        , ((unaryTypeOp BImg) (TArrow TInt TBool),(unaryPredOp BImg (PArrow PInt PBool)))
        , ((unaryTypeOp BRefOf) (TRef TInt),(unaryPredOp BRefOf) (PRef PInt))
        , ((unaryTypeOp BColOf) (TCol TInt),(unaryPredOp BColOf) (PCol PInt))
        , ((binaryTypeOp BConcat) TRecNil TRecNil,(binaryPredOp BConcat PRecNil PRecNil))
        , ((unaryTypeOp BEmpty) TRecNil,(unaryPredOp BEmpty PRecNil))
        , ((unaryTypeOp BIsRec) TRecNil,(unaryPredOp BIsRec PRecNil))
        , (TBound 2,PTypeBound 2)
        , (TAnn TInt (bTrue BKType),PInt)
        ]
  , testCase "type record recognition retains ANF support" $
      validateAnfType (elaborate ((unaryTypeOp BIsRec) TRecNil)) @?= Right ()
  , testCase "conversion rejects computation without evaluating it" $
      mapM_ (\value -> assertError (Exception.evaluate (typeToPred value)))
        [TLambda "x" (TBound 0), TApp (TLambda "x" (TBound 0)) TInt,
         TRec "x" (TBound 0) (TBound 0), TForall "x" (bTrue BKType) TInt,
         TIf TTrue TInt TBool]
  , testCase "refinements parse directly into predicate syntax" $ do
      parsePred "dom (TInt -> TBool) == TInt && not KFalse" @?=
        Right ((binaryPredOp BAnd)
          ((binaryPredOp BEq ((unaryPredOp BDom (PArrow PInt PBool))) PInt))
          ((unaryPredOp BNot) PFalse))
      parseKind "Pi A :: KType. {v :: KType | v == A}" @?=
        Right (KPi "A" (bTrue BKType)
          (KBase BKType (Refined "v"
            ((binaryPredOp BEq (PBound 0) (PTypeBound 0))))))
  , testGroup "executable syntax excluded from source predicates"
      [testCase source (reject (parsePred source)) | source <-
        ["fun A -> A", "F TInt", "forall A :: KType. A", "TInt :: KType",
         "let A = TInt in A", "rec A = A in A", "if KTrue then TInt else TBool"]]
  , testGroup "label sets occur only in predicates"
      [testCase source $ do
        p <- either assertFailure pure (parsePred source)
        checkValid (CPred p) >>= (@?= Valid)
        reject (parseType source)
        reject (parseType ("if " ++ source ++ " then TInt else TBool"))
      | source <- ["labels [| `a : TInt |] == labels [| `a : TBool |]",
                   "member `a [| `a : TInt |]", "subset [||] [| `a : TInt |]",
                   "[| `a : TInt |] # [| `b : TInt |]"]]
  , testCase "surface interpreted operations use the mirrored wrapper" $ do
      parseSurfacePred "not KFalse" @?=
        Right (SPInterp1 BNot SPFalse)
      parseSurfacePred "KTrue && KFalse" @?=
        Right (SPInterp2 BAnd SPTrue SPFalse)
      parseSurfacePred "labels R" @?=
        Right (SPLabSet (SPVar "R"))
      parseSurfacePred "member `a R" @?=
        Right (SPMember (SPLabel "a")
          (SPLabSet (SPVar "R")))
      parseSurfacePred "subset R S" @?=
        Right (SPSubset
          (SPLabSet (SPVar "R"))
          (SPLabSet (SPVar "S")))
      parseSurfacePred "R # S" @?=
        Right (SPApart
          (SPLabSet (SPVar "R"))
          (SPLabSet (SPVar "S")))
  , testCase "ordinary type guards and term conditionals remain" $ do
      case parseType "if TInt == TInt && KTrue then TInt else TBool" of
        Left e -> assertFailure e
        Right t -> checkTypeEquality emptyContext (bTrue BKType) t TInt >>= (@?= ())
      case parseExpr "if True then 1 else 2" of
        Left e -> assertFailure e
        Right e -> checkExpr emptyContext e TInt >>= (@?= ())
  , testCase "arrow refinement names domain and image directly" $ do
      snd (synthKind emptyContext (TArrow TInt TBool)) @?=
        KBase BKFun (Refined "v" ((binaryPredOp BAnd)
          ((binaryPredOp BEq ((unaryPredOp BDom (PBound 0))) PInt))
          ((binaryPredOp BEq ((unaryPredOp BImg (PBound 0))) PBool))))
  , testCase "empty record refinement includes exact equality" $
      snd (synthKind emptyContext TRecNil) @?=
        KBase BKRec (Refined "r" ((binaryPredOp BAnd)
          ((binaryPredOp BEq (PBound 0) PRecNil))
          ((unaryPredOp BEmpty (PBound 0)))))
  , testCase "logical conversion rejects residual type lets" $ do
      let t = TLet (Decl "v" TInt) ((binaryTypeOp BEq) (TBound 0) TInt)
      assertError (Exception.evaluate (typeToPred t))
  , testCase "substitution errors propagate through term type arguments" $ do
      let kind = KBase BKType (Refined "v"
            ((binaryPredOp BEq (PBound 0) (PTypeBound 0))))
          body = EAnn EUnit (TAnn TUnit kind)
          arg = TLambda "A" (TBound 0)
      reject (instantiateExprType arg body)
      assertError (checkTypeEquality emptyContext (bTrue BKType)
        (TApp (TLambda "A" (TAnn TInt kind)) arg) TInt)
  , testCase "ANF condition lets preserve logical guards" $ do
      t <- either assertFailure pure (parseType "fun R -> if not (empty R) && head R == TInt then TInt else TBool")
      k <- either assertFailure pure (parseKind "Pi R :: KRec. KType")
      let c = checkRaw emptyContext (elaborate t) k
      assertError (checkValid c)
  ]

reject :: Show a => Either e a -> Assertion
reject (Left _) = pure ()
reject (Right a) = assertFailure ("unexpected success: " ++ show a)

typeOperations :: [TypeOp]
typeOperations =
  [ BEq, BNot, BHead, BHeadLabel, BTail, BDom, BImg
  , BRefOf, BColOf, BConcat, BEmpty, BOr, BAnd, BIsRec
  ]

piArity :: Rkind -> Int
piArity (KPi _ _ codomain) = 1 + piArity codomain
piArity _ = 0

primitiveApplications :: [(Type, BaseKind)]
primitiveApplications =
  let record = TRecCons (TLabel "field") TInt TRecNil
      arrow = TArrow TInt TBool
  in [ ((binaryTypeOp BEq) TInt TBool, BKBool)
     , ((unaryTypeOp BNot) TTrue, BKBool)
     , ((unaryTypeOp BHead) record, BKType)
     , ((unaryTypeOp BHeadLabel) record, BKLabel)
     , ((unaryTypeOp BTail) record, BKRec)
     , ((unaryTypeOp BDom) arrow, BKType)
     , ((unaryTypeOp BImg) arrow, BKType)
     , ((unaryTypeOp BRefOf) (TRef TInt), BKType)
     , ((unaryTypeOp BColOf) (TCol TInt), BKType)
     , ((binaryTypeOp BConcat) TRecNil record, BKRec)
     , ((unaryTypeOp BEmpty) TRecNil, BKBool)
     , ((binaryTypeOp BOr) TTrue TFalse, BKBool)
     , ((binaryTypeOp BAnd) TTrue TFalse, BKBool)
     , ((unaryTypeOp BIsRec) record, BKBool)
     ]

assertPrimitiveResult :: (Type, BaseKind) -> Assertion
assertPrimitiveResult (application, expectedBase) =
  case synthKind emptyContext application of
    (_, KBase actualBase _) -> actualBase @?= expectedBase
    result -> assertFailure ("expected primitive base kind, got " ++ show result)
