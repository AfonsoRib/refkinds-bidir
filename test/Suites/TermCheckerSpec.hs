{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}

module Suites.TermCheckerSpec (tests, strictVisibleProbe) where

import ANF (elaborate)
import Check (checkType, synthType, validateTypeKind)
import Context hiding (implicationConstraint)
import Control.Exception (evaluate)
import Data.List (isInfixOf)
import Suites.Common
import Support.Universal (forallType)
import System.Environment (getExecutablePath)
import System.Process (readProcessWithExitCode)
import System.Timeout (timeout)
import Test.Tasty
import Test.Tasty.HUnit
import Types
import Support.Errors (assertError, assertErrorContaining, captureError)

tests :: TestTree
tests = testGroup "Complete static term checker"
  [ testCase "constants and trusted variables synthesize directly" $ do
      let cases =
            [ (EUnit, TUnit)
            , (EInteger 1, TInt)
            , (EBoolean True, TBool)
            , (EString "value", TString)
            ]
      mapM_ (\(expression, expected) ->
        synthType emptyContext expression >>= (@?= expected)) cases
      let ctx = addTermVar "value" ((unaryTypeOp BRefOf) (TRef TInt)) emptyContext
      synthType ctx (EVar "value") >>= (@?= ((unaryTypeOp BRefOf) (TRef TInt)))

  , testCase "unbound and escaped bound variables retain precise errors" $ do
      assertErrorContaining "unbound term variable"
        (synthType emptyContext (EVar "missing"))
      assertErrorContaining "unopened term index 0"
        (synthType emptyContext (EBound 0))

  , testCase "term lambdas check only against evaluated arrows" $ do
      let identity = ELambda "x" (EBound 0)
      checkExpr emptyContext identity ((unaryTypeOp BRefOf) (TRef (TArrow TInt TInt)))
        >>= (@?= ())
      assertErrorContaining "checking-only"
        (synthType emptyContext identity)
      assertError (checkExpr emptyContext identity TInt)

  , testCase "type lambdas check only against evaluated rank-1 universals" $ do
      let identity = ETLambda "A" (ELambda "x" (EBound 0))
          expected = forallType "A" (bTrue BKType)
            (TArrow (TBound 0) (TBound 0))
      checkExpr emptyContext identity expected >>= (@?= ())
      assertErrorContaining "checking-only"
        (synthType emptyContext identity)
      assertError (checkExpr emptyContext identity (TArrow TInt TInt))

  , testCase "annotations validate kind formation and retain their ANF result" $ do
      let written = (unaryTypeOp BRefOf) (TRef TInt)
          value = EAnn (EInteger 1) written
      inferred <- synthType emptyContext value
      inferred @?= elaborate written
      synthExpr emptyContext value >>= (@?= elaborate written)
      assertError (synthExpr emptyContext (EAnn EUnit (TVar "Missing")))
      let functionKind = KPi "A" (bTrue BKType) (bTrue BKType)
          typeFunction = TAnn (TLambda "A" (TBound 0)) functionKind
      assertError (synthExpr emptyContext (EAnn EUnit typeFunction))

  , testCase "term application synthesizes, evaluates, and checks its argument" $ do
      let ctx = addTermVar "f" ((unaryTypeOp BRefOf) (TRef (TArrow TInt TBool)))
              (addTermVar "x" TInt (addTermVar "u" TUnit emptyContext))
      inferred <- synthType ctx (EApp (EVar "f") (EVar "x"))
      inferred @?= TBool
      synthExpr ctx (EApp (EVar "f") (EVar "x")) >>= (@?= TBool)
      assertErrorContaining "subtype error"
        (synthExpr ctx (EApp (EVar "f") (EVar "u")))
      assertError (synthExpr ctx (EApp (EVar "x") (EVar "x")))

  , testCase "an annotated closed lambda can be applied to an ANF variable" $ do
      let function = EAnn (ELambda "x" (EBound 0)) (TArrow TInt TInt)
          ctx = addTermVar "argument" TInt emptyContext
      synthExpr ctx (EApp function (EVar "argument")) >>= (@?= TInt)

  , testCase "eliminators fully normalize visible constructor components" $ do
      let computed = (unaryTypeOp BRefOf) (TRef TInt)
          tailType = (unaryTypeOp BRefOf) (TRef TRecNil)
          row = TRecCons (TLabel "a") computed tailType
          ctx = addTermVar "f" (TArrow TInt computed)
              (addTermVar "cell" (TRef computed)
              (addTermVar "row" row
              (addTermVar "value" computed
              (addTermVar "argument" TInt emptyContext))))
          cases =
            [ (EApp (EVar "f") (EVar "argument"), TInt)
            , (ERefOf (EVar "cell"), TInt)
            , (EHead (EVar "row"), TInt)
            , (ETail (EVar "row"), TRecNil)
            , (EHeadLabel (EVar "row"), TLabel "a")
            ]
      mapM_ (\(expression, expected) ->
        synthType ctx expression >>= (@?= expected)) cases
      synthType ctx (ERef (EVar "value"))
        >>= (@?= (TRef computed))

  , testCase "record and reference construction normalize only for quotation" $ do
      let loop = parseTestType
            "letrec F :: Pi X :: KType. KType = fun X -> F X in F TInt"
          computed =
            [ ("conditional", TIf TTrue TInt loop, TInt)
            , ("recursion", parseTestType
                "letrec A :: KType = TInt in A", TInt)
            , ("first-order selector", (unaryTypeOp BRefOf) (TRef TInt),
                (unaryTypeOp BRefOf) (TRef TInt))
            ]
      mapM_ (\(label, written, quoted) -> do
        let ctx = addTermVar "value" written emptyContext
            cases =
              [ (ERef (EVar "value"), TRef quoted)
              , (ERecordCons "field" (EVar "value") ERecordNil,
                  TRecCons (TLabel "field") quoted TRecNil)
              ]
        mapM_ (\(expression, expected) -> do
          result <- timeout 2000000 (synthType ctx expression)
          assertEqual (label ++ ": " ++ show expression)
            (Just expected) result
          _ <- validateTypeKind ctx expected (bTrue BKType)
          pure ()) cases) computed

  , testCase "quotation cannot hide irreducible universal components" $ do
      let universal = forallType "A" (bTrue BKType) TUnit
          ctx = addTermVar "poly" universal emptyContext
          cases =
            [ ERef (EVar "poly")
            , ERecordCons "poly" (EVar "poly") ERecordNil
            ]
      mapM_ (assertError . synthType ctx) cases

  , testCase "full normalization demands divergent visible components" $ do
      executable <- getExecutablePath
      mapM_ (\mode -> do
        result <- timeout 1500000
          (readProcessWithExitCode executable ["--strict-visible-probe", mode] "")
        case result of
          Nothing -> pure ()
          Just observed -> assertFailure
            (mode ++ " skipped full normalization: " ++ show observed))
        ["app", "deref", "head", "head-label", "tail", "concat", "record-cons"]

  , testCase "CBV normalization evaluates application and let inputs" $ do
      let loop = parseTestType
            "letrec F :: Pi X :: KType. KType = fun X -> F X in F TInt"
          computedApplication = TApp
            (TLambda "Ignored" (TArrow TInt TBool)) loop
          computedLet = TLet (Decl "Ignored" loop) (TArrow TInt TBool)
          ctx = addTermVar "byApplication" computedApplication
              (addTermVar "byLet" computedLet
              (addTermVar "argument" TInt emptyContext))
          applications =
            [ EApp (EVar "byApplication") (EVar "argument")
            , EApp (EVar "byLet") (EVar "argument")
            ]
      mapM_ (\expression -> do
        result <- timeout 500000 (synthType ctx expression)
        result @?= Nothing) applications

  , testCase "CBV normalization unfolds type lets and normalizes their components" $ do
      let computed = (unaryTypeOp BRefOf) (TRef TInt)
          row = TRecCons (TLabel "a") computed TRecNil
          alias hint definition = TLet (Decl hint definition) (TBound 0)
          ctx = addTermVar "f" (alias "FunctionAlias" (TArrow TInt computed))
              (addTermVar "cell" (alias "ReferenceAlias" (TRef computed))
              (addTermVar "row" (alias "RecordAlias" row)
              (addTermVar "argument" TInt emptyContext)))
          synthesisCases =
            [ (EApp (EVar "f") (EVar "argument"), TInt)
            , (ERefOf (EVar "cell"), TInt)
            , (EHead (EVar "row"), TInt)
            , (EHeadLabel (EVar "row"), TLabel "a")
            , (ETail (EVar "row"), TRecNil)
            , (EConcat (EVar "row") ERecordNil,
                TRecCons (TLabel "a") TInt TRecNil)
            ]
      mapM_ (\(expression, expected) -> do
        result <- timeout 2000000 (synthType ctx expression)
        result @?= Just expected) synthesisCases

  , testCase "CBV conditionals evaluate only the selected branch" $ do
      let loop = parseTestType
            "letrec F :: Pi X :: KType. KType = fun X -> F X in F TInt"
          expected = TIf TTrue (TArrow TInt TInt) loop
      result <- timeout 2000000
        (checkType emptyContext (ELambda "x" (EBound 0)) expected)
      result @?= Just ()

  , testCase "type application checks and evaluates its written argument" $ do
      let universal = forallType "A" (bTrue BKType) (TBound 0)
          ctx = addTermVar "poly" universal emptyContext
      inferred <- synthType ctx
        (ETApp (EVar "poly") ((unaryTypeOp BRefOf) (TRef TInt)))
      inferred @?= TInt
      assertError (synthExpr ctx (ETApp (EVar "poly") (TVar "Missing")))
      assertError (synthExpr (addTermVar "mono" TInt ctx)
        (ETApp (EVar "mono") TInt))

  , testCase "type application evaluates redexes created by substitution" $ do
      let domain = KPi "A" (bTrue BKType) (bTrue BKType)
          universal = forallType "F" domain (TApp (TBound 0) TInt)
          argument = TAnn (TLambda "A" (TBound 0)) domain
          ctx = addTermVar "poly" universal emptyContext
      synthType ctx (ETApp (EVar "poly") argument) >>= (@?= TInt)

  , testCase "type application validates even unused arguments before evaluation" $ do
      let universal = forallType "A" (bTrue BKType) TInt
          ctx = addTermVar "poly" universal emptyContext
          malformed = parseTestType
            "let Bad = head [||] in letrec F :: Pi X :: KType. KType = fun X -> F X in F TInt"
      result <- timeout 2000000
        (captureError (synthType ctx (ETApp (EVar "poly") malformed)))
      case result of
        Just (Left _) -> pure ()
        other -> assertFailure ("expected prompt kind failure, got " ++ show other)

  , testCase "fallback compares evaluated types before structural subtyping" $ do
      let ctx = addTermVar "value" ((unaryTypeOp BRefOf) (TRef TInt)) emptyContext
      checkExpr ctx (EVar "value") TInt >>= (@?= ())
      checkType ctx (EVar "value") TInt
      assertErrorContaining "subtype error" (checkExpr ctx (EVar "value") TBool)

  , testCase "computed annotations validate before checking" $ do
      let identity = TAnn (TLambda "A" (TBound 0))
            (KPi "A" (bTrue BKType) (bTrue BKType))
          computed = TApp identity TInt
      checkType emptyContext (EAnn (EInteger 1) computed) TInt >>= (@?= ())
      let malformed = TLet (Decl "Bad" ((unaryTypeOp BHead) TRecNil)) TInt
      assertError (checkType emptyContext (EAnn EUnit malformed) TUnit)

  , testCase "arrow subtyping equation is contravariant then covariant" $ do
      checker <- readFile "src/Check.hs"
      assertBool "arrow domain comparison is not reversed"
        ("compareTypes environment c a" `isInfixOf` checker)
      assertBool "arrow result comparison is not covariant"
        ("compareTypes environment b d" `isInfixOf` checker)

  , testCase "structural subtyping visits late mismatches once" $ do
      let depth = 8000 :: Int
          arrow leaf = foldr (const (TArrow TInt)) leaf [1 .. depth]
          row lastField = foldr field TRecNil [1 .. depth]
            where
              field index rest = TRecCons (TLabel ("f" ++ show index))
                (if index == depth then lastField else TInt) rest
          actualArrow = arrow TInt
          expectedArrow = arrow TBool
          actualRow = row TInt
          expectedRow = row TBool
      completed <- timeout 3000000 $ do
        assertError (checkType (addTermVar "arrow" actualArrow emptyContext)
          (EVar "arrow") expectedArrow)
        assertError (checkType (addTermVar "row" actualRow emptyContext)
          (EVar "row") expectedRow)
      completed @?= Just ()

  , testCase "universal subtyping computes contravariant domain subkinding" $ do
      let singleton = parseTestKind "{ t :: KType | t == TInt }"
          actual = forallType "X" singleton (TBound 0)
          equivalent = forallType "Y"
            (parseTestKind "{ t :: KType | TInt == t }") (TBound 0)
          unrestricted = forallType "Y" (bTrue BKType) (TBound 0)
          ctx = addTermVar "poly" actual emptyContext
      checkExpr ctx (EVar "poly") equivalent >>= (@?= ())
      assertError (checkExpr ctx (EVar "poly") unrestricted)

  , testCase "record spines and mutable references remain structural type relations" $ do
      let row = TRecCons (TLabel "a") TInt TRecNil
          ctx = addTermVar "row" row
              (addTermVar "cell" (TRef TInt) emptyContext)
      checkExpr ctx (EVar "row") row >>= (@?= ())
      assertError (checkExpr ctx (EVar "row") TRecNil)
      checkExpr ctx (EVar "cell") (TRef TInt) >>= (@?= ())
      assertError (checkExpr ctx (EVar "cell") (TRef TBool))

  , testCase "record eliminators expose computed aliases" $ do
      let row = TRecCons (TLabel "a") TInt TRecNil
          ctx = addTermVar "row" ((unaryTypeOp BRefOf) (TRef row)) emptyContext
      synthExpr ctx (EHead (EVar "row")) >>= (@?= TInt)

  , testCase "reference eliminators expose computed aliases" $ do
      let ctx = addTermVar "cell"
            ((unaryTypeOp BRefOf) (TRef (TRef TInt))) emptyContext
      synthExpr ctx (ERefOf (EVar "cell")) >>= (@?= TInt)

  , testCase "all record and reference eliminators expose computed aliases" $ do
      let row = TRecCons (TLabel "a") TInt TRecNil
          ctx = addTermVar "row" ((unaryTypeOp BRefOf) (TRef row))
              (addTermVar "cell" ((unaryTypeOp BRefOf) (TRef (TRef TInt))) emptyContext)
      synthType ctx (EHeadLabel (EVar "row")) >>= (@?= (TLabel "a"))
      synthType ctx (ETail (EVar "row")) >>= (@?= TRecNil)
      synthType ctx (EAssign (EVar "cell") (EInteger 1)) >>= (@?= TUnit)
      assertErrorContaining "subtype error"
        (synthType ctx (EAssign (EVar "cell") (EBoolean True)))

  , testCase "record construction and concatenation fully normalize spines" $ do
      let computedField = (unaryTypeOp BRefOf) (TRef TInt)
          tailRow = TRecCons (TLabel "b") TBool TRecNil
          computedTail = (unaryTypeOp BRefOf) (TRef tailRow)
          row = TRecCons (TLabel "a") computedField computedTail
          normalizedRow = TRecCons (TLabel "a") TInt tailRow
          ctx = addTermVar "row" row
              (addTermVar "tail" computedTail emptyContext)
      synthType ctx (EConcat (EVar "row") ERecordNil)
        >>= (@?= normalizedRow)
      synthType ctx (EConcat ERecordNil (EVar "tail"))
        >>= (@?= tailRow)
      let computedConcat = binaryTypeOp BConcat
            (TRecCons (TLabel "x") TInt TRecNil)
            (TRecCons (TLabel "y") TBool TRecNil)
          concatContext = addTermVar "computedConcat" computedConcat emptyContext
          concreteConcat = TRecCons (TLabel "x") TInt
            (TRecCons (TLabel "y") TBool TRecNil)
      synthType concatContext (EConcat (EVar "computedConcat") ERecordNil)
        >>= (@?= concreteConcat)
      synthType ctx (ERecordCons "c" EUnit (EVar "row"))
        >>= (@?= (TRecCons (TLabel "c") TUnit normalizedRow))
      assertErrorContaining "duplicate record label: b"
        (synthType ctx (EConcat (EVar "row") (EVar "tail")))
      assertErrorContaining "duplicate record label: b"
        (synthType ctx (ERecordCons "b" EUnit (EVar "row")))

  , testCase "operations, bindings, conditionals, records, and references are restored" $ do
      synthExpr emptyContext (ENot (EBoolean True)) >>= (@?= TBool)
      synthExpr emptyContext (EStringConcat (EString "a") (EString "b"))
        >>= (@?= TString)
      checkExpr emptyContext (ELet "x" (EInteger 1) (EBound 0)) TInt
        >>= (@?= ())
      checkExpr emptyContext
        (ELetRec "f" (TArrow TInt TInt) (ELambda "x" (EBound 0)) EUnit)
        TUnit >>= (@?= ())
      checkExpr emptyContext (EIf (EBoolean True) EUnit EUnit) TUnit
        >>= (@?= ())
      let row = ERecordCons "a" (EInteger 1) ERecordNil
          rowType = TRecCons (TLabel "a") TInt TRecNil
      synthExpr emptyContext row >>= (@?= rowType)
      let otherType = TRecCons (TLabel "b") TBool TRecNil
          concatenatedType = TRecCons (TLabel "a") TInt otherType
          rowContext = addTermVar "row" rowType
            (addTermVar "other" otherType emptyContext)
      synthExpr rowContext (EHead (EVar "row")) >>= (@?= TInt)
      synthExpr rowContext (ETail (EVar "row")) >>= (@?= TRecNil)
      synthExpr rowContext (EConcat (EVar "row") (EVar "other"))
        >>= (@?= concatenatedType)
      synthExpr emptyContext (ERef (EInteger 1)) >>= (@?= (TRef TInt))
      let refContext = addTermVar "cell" (TRef TInt) emptyContext
      synthExpr refContext (ERefOf (EVar "cell")) >>= (@?= TInt)
      synthExpr refContext (EAssign (EVar "cell") (EInteger 2))
        >>= (@?= TUnit)

  , testCase "labels and record head labels synthesize singleton label types" $ do
      synthExpr emptyContext (ELabel "field") >>= (@?= (TLabel "field"))
      let rowType = TRecCons (TLabel "field") TUnit TRecNil
          rowContext = addTermVar "row" rowType emptyContext
      synthExpr rowContext (EHeadLabel (EVar "row"))
        >>= (@?= (TLabel "field"))
      checkExpr emptyContext (ELabel "field") (TLabel "field")
        >>= (@?= ())
      assertError (synthExpr emptyContext (EHeadLabel ERecordNil))

  , testCase "record concatenation requires two concrete disjoint spines" $ do
      let expression = ETLambda "R"
            (ELambda "row" (ELet "merged"
              (EConcat (EBound 0) ERecordNil) EUnit))
          expected = forallType "R" (bTrue BKRec)
            (TArrow (TBound 0) TUnit)
      assertErrorContaining "concrete left record"
        (checkExpr emptyContext expression expected)
      let concrete = TRecCons (TLabel "a") TInt TRecNil
          context = addTermVar "left" concrete
            (addTermVar "right" (TVar "R") emptyContext)
      assertErrorContaining "concrete right record"
        (synthExpr context (EConcat (EVar "left") (EVar "right")))
      let duplicateContext = addTermVar "left" concrete
            (addTermVar "right" concrete emptyContext)
      assertErrorContaining "duplicate record label: a" (synthExpr duplicateContext
        (EConcat (EVar "left") (EVar "right")))
  ]

strictVisibleProbe :: String -> IO ()
strictVisibleProbe mode = do
  let loop = parseTestType
        "letrec F :: Pi X :: KType. KType = fun X -> F X in F TInt"
      row = TRecCons (TLabel "a") loop TRecNil
      context = addTermVar "f" (TArrow TInt loop)
          (addTermVar "cell" (TRef loop)
          (addTermVar "row" row
          (addTermVar "argument" TInt emptyContext)))
      run expression = observe (synthType context expression)
  case mode of
    "app" -> run (EApp (EVar "f") (EVar "argument"))
    "deref" -> run (ERefOf (EVar "cell"))
    "head" -> run (EHead (EVar "row"))
    "head-label" -> run (EHeadLabel (EVar "row"))
    "tail" -> run (ETail (EVar "row"))
    "concat" -> run (EConcat (EVar "row") ERecordNil)
    "record-cons" -> run (ERecordCons "b" EUnit (EVar "row"))
    _ -> fail ("unknown strict visible probe: " ++ mode)

observe :: Show a => IO a -> IO ()
observe action = do
  result <- action
  _ <- evaluate (length (show result))
  print result
