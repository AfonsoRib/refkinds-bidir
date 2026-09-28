{-# LANGUAGE OverloadedStrings #-}

module Suites.CheckerOnlySpec (tests) where

import Check (validateInferredKind)
import Context hiding (implicationConstraint)
import Data.List (isInfixOf, isPrefixOf, isSuffixOf, sort, tails)
import Parser (parseExpr)
import System.Directory (doesFileExist, listDirectory)
import Suites.Common (checkExpr, synthExpr)
import Test.Tasty
import Test.Tasty.HUnit
import Types

tests :: TestTree
tests = testGroup "Checker-only interfaces"
  [ testCase "caller contexts supply term and type assumptions" $ do
      let ctx = addTermVar "value" (TVar "A")
              (addTypeVar "A" (bTrue BKType) emptyContext)
      synthExpr ctx (EVar "value") >>= (@?= (TVar "A"))
      validateInferredKind ctx (TVar "A") >>= \result -> case result of
        KBase BKType _ -> pure ()
        other -> assertFailure (show other)

  , testCase "lexical type lets expose computed arrow aliases" $ do
      let alias = TLet (Decl "Alias" (TArrow TInt TBool)) (TBound 0)
      let ctx = addTermVar "argument" TInt
              (addTermVar "function" alias emptyContext)
      synthExpr ctx (EApp (EVar "function") (EVar "argument"))
        >>= (@?= TBool)

  , testCase "lexical type lets expose computed universal aliases" $ do
      let universal = TForall "A" (bTrue BKType)
            (TArrow (TBound 0) (TBound 0))
          alias = TLet (Decl "Poly" universal) (TBound 0)
          ctx = addTermVar "identity" alias emptyContext
      checkExpr ctx (ETApp (EVar "identity") TInt) (TArrow TInt TInt)
        >>= (@?= ())

  , testCase "explicit contexts support record extension" $ do
      let rowType = TRecCons (TLabel "p") TInt TRecNil
          expected = TRecCons (TLabel "q") TBool rowType
          ctx = addTermVar "row" rowType emptyContext
      synthExpr ctx (ERecordCons "q" (EBoolean True) (EVar "row"))
        >>= (@?= expected)

  , testCase "explicit contexts support projection and table-cell typing" $ do
      let cellType = TRecCons (TLabel "tag") TString
            (TRecCons (TLabel "render") (TArrow TInt TString) TRecNil)
          ctx = addTermVar "value" TInt
              (addTermVar "cell" cellType emptyContext)
          render = EHead (ETail (EVar "cell"))
      synthExpr ctx (EHead (EVar "cell")) >>= (@?= TString)
      checkExpr ctx (EApp render (EVar "value")) TString >>= (@?= ())

  , testCase "validated kind inference applies ANF to ordinary types" $ do
      let identity = TAnn (TLambda "A" (TBound 0))
            (KPi "A" (bTrue BKType) (bTrue BKType))
          source = TAnn (TApp identity TInt) (bTrue BKType)
      validateInferredKind emptyContext source
        >>= (@?= (bTrue BKType))

  , testCase "local bindings and recursion remain surface syntax" $ do
      mapM_ (either assertFailure (const (pure ())) . parseExpr)
        [ "let value = 1 in value"
        , "letrec loop : TInt -> TInt = fun x -> loop x in loop"
        ]

  , testCase "removed public modules and program parser names stay absent" $ do
      mapM_ (doesFileExist >=> (@?= False))
        [ "src/Program.hs", "src/ProgramCheck.hs", "src/ExprEval.hs", "src/Equal.hs" ]
      parser <- readFile "src/Parser.y"
      mapM_ (\obsolete -> assertBool obsolete (not (obsolete `isInfixOf` parser)))
        [ "parseProgram", "parseTermProgram", "parseTypeProgram"
        , "typeDeclaration", "termProgramBody"
        ]

  , testCase "the grammar requires zero conflicts and has no declaration terminals" $ do
      parser <- readFile "src/Parser.y"
      lexer <- readFile "src/Lexer.x"
      assertBool "missing %expect 0" ("%expect 0" `isInfixOf` parser)
      mapM_ (\obsolete -> assertBool obsolete
        (not (obsolete `isInfixOf` (parser ++ lexer))))
        [ "TokenSemicolon", "TokenType", "TokenRec" ]

  , testCase "production source separates named-to-core desugaring" $ do
      sort . filter isProductionSource <$> listDirectory "src" >>= (@?=
        [ "ANF.hs", "Check.hs", "Constraint.hs", "Context.hs", "Desugar.hs"
        , "EvalTy.hs", "Lexer.x", "Parser.y", "Prims.hs", "Substitution.hs"
        , "Types.hs", "WhnfEquality.hs"
        ])
      cabal <- readFile "refinement-kinds-bidir.cabal"
      let exposed = takeWhile (not . isInfixOf "build-depends:")
            (dropWhile (not . isInfixOf "exposed-modules:") (lines cabal))
      assertBool "EvalTy must remain hidden" (all (not . isInfixOf "EvalTy") exposed)
      assertBool "hidden EvalTy module missing" ("other-modules:    EvalTy" `isInfixOf` cabal)
      typesSource <- readFile "src/Types.hs"
      desugarSource <- readFile "src/Desugar.hs"
      mapM_ (\entrypoint -> do
        assertBool (entrypoint ++ " remains in Types")
          (not (entrypoint `isInfixOf` typesSource))
        assertBool (entrypoint ++ " missing from Desugar")
          (entrypoint `isInfixOf` desugarSource))
        [ "lowerType ::", "lowerKind ::", "lowerPredicate ::", "lowerExpr ::" ]
      checkSource <- readFile "src/Check.hs"
      contextSource <- readFile "src/Context.hs"
      constraintSource <- readFile "src/Constraint.hs"
      mapM_ (\obsolete -> assertBool (obsolete ++ " remains in Check")
        (not (obsolete `isInfixOf` checkSource)))
        [ "equalTypes", "equivalentKind", "validateTypeEquality", "EqualityOps" ]
      mapM_ (\obsolete -> assertBool (obsolete ++ " remains in Constraint")
        (not (obsolete `isInfixOf` constraintSource)))
        [ "simplifyConstraint", "simplifyPredicate", "checkConjuncts" ]
      mapM_ (\obsolete -> assertBool (obsolete ++ " remains in Cabal")
        (not (obsolete `isInfixOf` unlines exposed)))
        [ "Preprocess", "TypeReduction", "ExprCheck"
        , "KindValidation", "Equality", "Solver", "Program"
        ]
      assertBool "Substitution must be exposed"
        ("Substitution" `isInfixOf` unlines exposed)
      mapM_ (\obsolete -> assertBool (obsolete ++ " remains in Context")
        (not (obsolete `isInfixOf` contextSource)))
        [ "DefinitionEntry", "addTypeDefinition", "lookupTypeDefinition"
        , "expandDefinitions", "restoreDefinitionNames"
        ]

  , testCase "production and CLI imports are qualified and aliased" $ do
      sourceNames <- filter isProductionSource <$> listDirectory "src"
      let paths = map ("src/" ++) sourceNames ++ ["app/Main.hs"]
      sources <- mapM readFile paths
      let imports =
            [ (path, line)
            | (path, source) <- zip paths sources
            , line <- lines source
            , "import " `isPrefixOf` dropWhile (== ' ') line
            ]
      mapM_ (\(path, line) ->
        assertBool (path ++ ": " ++ line)
          ("import qualified " `isPrefixOf` dropWhile (== ' ') line &&
            " as " `isInfixOf` line)) imports

  , testCase "the two validated term judgments are the public API" $ do
      checker <- readFile "src/Check.hs"
      syntax <- readFile "src/Types.hs"
      lexer <- readFile "src/Lexer.x"
      mapM_ (\name -> assertBool name (name `isInfixOf` checker))
        [ "synthType :: Ctx.Context -> T.Expr"
        , "checkType :: Ctx.Context -> T.Expr -> T.Type"
        ]
      mapM_ (\name -> assertBool name (not (name `isInfixOf` checker)))
        [ "synthTerm", "checkTerm", "inferTerm", "synthRule", "checkRule"
        , "selector ::", "TermTypeMismatch"
        ]
      mapM_ (\name -> assertBool name (name `isInfixOf` syntax))
        ["ELabel", "EHeadLabel"]
      mapM_ (\name -> assertBool name (not (name `isInfixOf` syntax)))
        [ "ECons", "ENil", "SECons", "SENil"
        , "ERecordConsDynamic", "SERecordConsDynamic"
        ]
      assertBool "type and logical record concatenation are present"
        (all (`isInfixOf` syntax)
          ["BConcat", "STConcat", "PInterp1 TypeOp", "PInterp2 TypeOp"
          , "SPInterp1 TypeOp", "SPInterp2 TypeOp"])
      mapM_ (\name -> assertBool name (not (name `isInfixOf` lexer)))
        ["TokenCons", "TokenNil"]
      mapM_ (\name -> assertBool name (not (name `isInfixOf` syntax)))
        ["ETypeIf", "SETypeIf", "EKindCase", "SEKindCase"]
      assertBool "iftype is not reserved"
        (not ("TokenIfType" `isInfixOf` lexer))

  , testCase "universals have no dedicated kind-checking equation" $ do
      checker <- readFile "src/Check.hs"
      mapM_ (\equation -> assertBool equation
        (not (equation `isInfixOf` checker)))
        [ "checkKind ctx (T.TForall"
        , "checkKind _ (T.TForall"
        ]

  , testCase "only conditional checking creates a fresh checking witness" $ do
      checker <- readFile "src/Check.hs"
      guardrails <- readFile "GUARDRAILS.md"
      let kindChecking = takeUntil "-- [K-CHK-SUB]"
            (dropUntil "checkKind ::" checker)
          conditional = takeUntil "-- [K-CHK-LET]"
            (dropUntil "-- [K-CHK-IF]" kindChecking)
          termChecking = takeUntil "-- Structural-alpha term subtyping"
            (dropUntil "checkTypeRaw ::" checker)
      assertEqual "kind-checking freshness count"
        1 (count "S.freshName" kindChecking)
      assertBool "conditional witness is not fresh"
        ("S.freshName" `isInfixOf` conditional)
      assertBool "term checking still freshens syntax binders"
        (not ("freshName" `isInfixOf` termChecking ||
          "freshTerm" `isInfixOf` termChecking))
      assertBool "freshness guardrail is missing"
        ("sole checking" `isInfixOf` guardrails)

  , testCase "term rule premises remain explicit in exactly two judgments" $ do
      checker <- readFile "src/Check.hs"
      mapM_ (\name -> assertBool (name ++ " missing") (name `isInfixOf` checker))
        [ "synthTypeRaw", "checkTypeRaw", "validateTypeKind ctx"
        , "evalType ctx"
        ]
      let termSection = dropUntil "-- Bidirectional term checking" checker
      assertBool "term checking still constructs constraints"
        (not ("C.c" `isInfixOf` termSection || "C.C" `isInfixOf` termSection))
      assertBool "term checking still has a replay boundary"
        (not ("proveTerm" `isInfixOf` checker))
      mapM_ (\helper -> assertBool (helper ++ " hides a term-rule premise")
        (not (helper `isInfixOf` checker)))
        [ "prepareTermType", "prepareKind", "synthTermView", "synthRecordCons"
        , "guardedTerm", "cannotSynthesize", "validateKindCase"
        ]

  , testCase "synthesis equations cover synthesizing terms and use one fallback" $ do
      checker <- readFile "src/Check.hs"
      let synthesis = takeUntil "-- Checking" (dropUntil "-- Synthesis" checker)
          constructors =
            [ "EUnit", "EInteger", "EBoolean", "ENot", "EString"
            , "EStringConcat", "EVar", "EBound", "EAnn", "EApp", "ELabel"
            , "ERecordNil"
            , "ERecordCons", "EHead", "EHeadLabel"
            , "ETail", "EConcat", "ERef", "ERefOf", "EAssign", "ETApp"
            ]
      mapM_ (\constructor -> assertBool (constructor ++ " missing from synthTypeRaw")
        (("T." ++ constructor) `isInfixOf` synthesis)) constructors
      assertBool "checking-only synthesis errors are not handled by one fallback"
        ("synthTypeRaw _ _ = error" `isInfixOf` synthesis)

  , testCase "record overlap indexes right labels once" $ do
      checker <- readFile "src/Check.hs"
      let concatEquation = takeUntil "-- [T-SYN-HEAD]"
            (dropUntil "-- [T-SYN-CONCAT]" checker)
      assertBool "left record is not fully normalized before traversal"
        ("leftValue <- evalType ctx leftType" `isInfixOf` concatEquation)
      assertBool "right record is not fully normalized before traversal"
        ("rightValue <- evalType ctx rightType" `isInfixOf` concatEquation)
      assertEqual "right-label set construction count"
        1 (count "Set.fromList right" checker)
      assertBool "overlap scan does not use the right-label set"
        ("Set.member label rightLabels" `isInfixOf` checker)
      assertBool "quadratic list membership returned"
        (not ("`elem` rightLabels" `isInfixOf` concatEquation))

  , testCase "kind checks occur only in rules with explicit formation premises" $ do
      checker <- readFile "src/Check.hs"
      let termSection = dropUntil "-- Synthesis" checker
          synthesis = takeUntil "-- Checking" termSection
          checking = dropUntil "-- Checking" termSection
      assertEqual "only annotations and type applications check kinds in synthesis"
        2 (count "validateTypeKind ctx" synthesis)
      assertBool "annotation does not check its declaration at KType"
        ("validateTypeKind ctx declared" `isInfixOf` synthesis &&
          "(P.bTrue T.BKType)" `isInfixOf` synthesis)
      assertBool "type application does not check its argument domain"
        ("validateTypeKind ctx argument domain" `isInfixOf` synthesis)
      assertEqual "only recursive declarations check formation while checking"
        1 (count "validateTypeKind ctx" checking)
      assertBool "checkType repeated general expected-type formation"
        (not ("checkRaw ctx expected (P.bTrue T.BKType)" `isInfixOf` checking))
      assertBool "term-level collection checking was reintroduced"
        (not ("checkRaw ctx expected (P.bTrue T.BKCol)" `isInfixOf` checking))

  , testCase "public term entry points elaborate once before raw checking" $ do
      checker <- readFile "src/Check.hs"
      let lambdaEquation = takeUntil "checkTypeRaw ctx (T.ETLambda"
            (dropUntil "checkTypeRaw ctx (T.ELambda" checker)
      assertBool "synthesis entry point does not elaborate before the raw judgment"
        ("synthType ctx = synthTypeRaw ctx . A.elaborateExpr" `isInfixOf` checker)
      assertBool "checking entry point does not elaborate before the raw judgment"
        ("checkTypeRaw ctx (A.elaborateExpr expression) (A.elaborate expected)"
          `isInfixOf` checker)
      assertBool "raw judgments still contain normalization guards"
        (not ("/= normalized" `isInfixOf` checker))
      assertBool "raw lambda checking does not use full CBV normalization"
        ("evalType ctx expected >>= \\case"
          `isInfixOf` lambdaEquation)
      assertBool "obsolete outer-constructor evaluator remains"
        (not ("evalTypeOuter" `isInfixOf` checker))
  ]
  where
    isProductionSource path = not ("." `isPrefixOf` path) &&
      any (`isSuffixOf` path) [".hs", ".x", ".y"]
    count needle = length . filter (isPrefixOf needle) . tails
    dropUntil needle source = case dropWhile (not . isPrefixOf needle) (tails source) of
      match : _ -> match
      [] -> ""
    takeUntil needle source = case break (isPrefixOf needle) (tails source) of
      (prefixes, _) -> map head (filter (not . null) prefixes)

(>=>) :: (a -> IO b) -> (b -> IO c) -> a -> IO c
(>=>) first second value = first value >>= second
