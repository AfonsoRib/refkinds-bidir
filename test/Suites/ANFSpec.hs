{-# LANGUAGE OverloadedStrings #-}

module Suites.ANFSpec (tests) where

import ANF (elaborate, elaborateExpr)
import Suites.Common (parseTestTerm, parseTestType)
import Support.AstInvariants (validateAnfExpr, validateAnfType)
import Test.Tasty
import Test.Tasty.HUnit
import Types

tests :: TestTree
tests = testGroup "ANF elaboration"
  [ testCase "atomic values remain unchanged and valid" $ do
      let ty = parseTestType "TInt"
          expression = parseTestTerm "\"value\""
      elaborate ty @?= ty
      elaborateExpr expression @?= expression
      validateAnfType ty @?= Right ()
      validateAnfExpr expression @?= Right ()

  , testCase "test oracle rejects non-ANF applications" $ do
      validateAnfType (TApp (TVar "F") TInt) @?= Left "type is not in ANF"
      validateAnfType ((unaryTypeOp BNot) TTrue) @?= Left "type is not in ANF"
      validateAnfExpr (parseTestTerm "f (g 1)") @?= Left "expression is not in ANF"

  , testCase "every type constructor elaborates to stable ANF" $
      mapM_ assertTypeCase typeCases

  , testCase "every expression constructor elaborates to stable ANF" $
      mapM_ assertExprCase exprCases

  , testCase "strict operands are named from left to right" $ do
      let left = EApp (EVar "f") (EVar "x")
          right = EApp (EVar "g") (EVar "y")
      elaborateExpr (EStringConcat left right) @?=
        ELet "x0" left
          (ELet "x1" right
            (EStringConcat (EBound 1) (EBound 0)))

  , testCase "generated type lets shift surrounding binders" $ do
      let source = TLambda "row"
            (TApp (TBound 1) ((unaryTypeOp BTail) (TBound 0)))
      elaborate source @?=
        TLambda "row"
          (TLet (Decl "x0" ((unaryTypeOp BTail) (TBound 0)))
            (TApp (TBound 2) (TBound 0)))

  , testCase "native reference types remain constructors inside primitive applications" $ do
      let source = (unaryTypeOp BNot)
            ((unaryTypeOp BRefOf) (TRef TInt))
          anf = elaborate source
      validateAnfType anf @?= Right ()
      anf @?=
        TLet (Decl "x1" (TRef TInt))
          (TLet (Decl "x2" ((unaryTypeOp BRefOf) (TBound 0)))
            ((unaryTypeOp BNot) (TBound 0)))
  ]

assertTypeCase :: (String, Type) -> Assertion
assertTypeCase (label, source) = do
  let anf = elaborate source
  assertEqual (label ++ " is valid ANF: " ++ show anf)
    (Right ()) (validateAnfType anf)
  assertEqual (label ++ " is idempotent") anf (elaborate anf)

assertExprCase :: (String, Expr) -> Assertion
assertExprCase (label, source) = do
  let anf = elaborateExpr source
  assertEqual (label ++ " is valid ANF") (Right ()) (validateAnfExpr anf)
  assertEqual (label ++ " is idempotent") anf (elaborateExpr anf)

typeCases :: [(String, Type)]
typeCases =
  [ ("record", TRecCons computedType computedType computedType)
  , ("arrow", TArrow computedType computedType)
  , ("lambda", TLambda "A" computedType)
  , ("application", TApp computedType computedType)
  , ("annotation", TAnn computedType typeKind)
  , ("forall", TForall "A" typeKind computedType)
  , ("let", TLet (Decl "A" computedType) computedType)
  , ("recursion", TRec "A" computedType computedType)
  , ("conditional", TIf computedType computedType computedType)
  , ("equality", (binaryTypeOp BEq) computedType computedType)
  , ("conjunction", (binaryTypeOp BAnd) computedType computedType)
  , ("disjunction", (binaryTypeOp BOr) computedType computedType)
  , ("negation", (unaryTypeOp BNot) computedType)
  , ("record predicate", (unaryTypeOp BIsRec) computedType)
  , ("head", (unaryTypeOp BHead) computedType)
  , ("head label", (unaryTypeOp BHeadLabel) computedType)
  , ("tail", (unaryTypeOp BTail) computedType)
  , ("domain", (unaryTypeOp BDom) computedType)
  , ("image", (unaryTypeOp BImg) computedType)
  , ("reference", TRef computedType)
  , ("dereference", (unaryTypeOp BRefOf) computedType)
  , ("collection", TCol computedType)
  , ("collection element", (unaryTypeOp BColOf) computedType)
  , ("concatenation", (binaryTypeOp BConcat) computedType computedType)
  , ("empty", (unaryTypeOp BEmpty) computedType)
  ]

exprCases :: [(String, Expr)]
exprCases =
  [ ("lambda", ELambda "x" computedExpr)
  , ("type lambda", ETLambda "A" computedExpr)
  , ("application", EApp computedExpr computedExpr)
  , ("negation", ENot computedExpr)
  , ("string concatenation", EStringConcat computedExpr computedExpr)
  , ("type application", ETApp computedExpr computedType)
  , ("let", ELet "x" computedExpr computedExpr)
  , ("recursion", ELetRec "f" TInt computedExpr computedExpr)
  , ("record", ERecordCons "field" computedExpr computedExpr)
  , ("record concatenation", EConcat computedExpr computedExpr)
  , ("head", EHead computedExpr)
  , ("term head label", EHeadLabel computedExpr)
  , ("tail", ETail computedExpr)
  , ("reference", ERef computedExpr)
  , ("dereference", ERefOf computedExpr)
  , ("assignment", EAssign computedExpr computedExpr)
  , ("conditional", EIf computedExpr computedExpr computedExpr)
  , ("annotation", EAnn computedExpr computedType)
  , ("term label", ELabel "field")
  ]

computedType :: Type
computedType = TApp (TVar "F") (TApp (TVar "G") (TVar "A"))

computedExpr :: Expr
computedExpr = EApp (EVar "f") (EApp (EVar "g") (EVar "x"))

typeKind :: Rkind
typeKind = bTrue BKType
