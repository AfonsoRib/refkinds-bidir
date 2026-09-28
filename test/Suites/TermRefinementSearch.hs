{-# LANGUAGE OverloadedStrings #-}

-- Opt-in adversarial search. Expectations describe hypotheses, not new language rules.
module Suites.TermRefinementSearch (search, tests) where

import Check
import Context hiding (implicationConstraint)
import Control.Exception (evaluate)
import Control.Monad (forM, forM_)
import Data.List (intercalate, isPrefixOf)
import Parser
import Suites.Common (checkExpr, synthExpr)
import System.Timeout (timeout)
import Test.Tasty
import Test.Tasty.HUnit
import Types
import Support.Errors (captureError)

data Expectation = Accept | Reject | SolverFails | Observe deriving (Eq, Show)
data Outcome = Accepted | Rejected String | SolverFailure String | SolverUnknown String
  | ParseFailure String | BudgetExpired
  deriving (Eq, Show)
data Operation = Check | InferredFormation | InferredNormal deriving (Eq, Show)
data Probe = Probe
  { identifier :: String
  , expectation :: Expectation
  , assumptions :: [(String, String)]
  , source :: String
  , signature :: String
  , operation :: Operation
  }

probe :: String -> Expectation -> String -> String -> Probe
probe name expected term goal = Probe name expected [] term goal Check

runProbe :: Probe -> IO Outcome
runProbe p = case parsed of
  Left message -> pure (ParseFailure message)
  Right (context, term, goal) -> do
    result <- timeout 6000000 $ do
      checked <- runOperation (operation p) context term goal
      let outcome = either classify (const Accepted) checked
      _ <- evaluate (length (show outcome))
      pure outcome
    pure (maybe BudgetExpired id result)
  where
    parsed = do
      term <- parseExpr (source p)
      goal <- parseType (signature p)
      bindings <- mapM (\(name, ty) -> (,) (termName name) <$> parseType ty) (assumptions p)
      pure (foldr (uncurry addTermVar) emptyContext bindings, term, goal)

runOperation :: Operation -> Context -> Expr -> Type -> IO (Either String ())
runOperation Check context term goal = captureError
  (checkExpr context term goal)

runOperation InferredFormation context term _ = do
  captureError $ do
    raw <- synthType context term
    _ <- validateTypeKind context raw (bTrue BKType)
    pure ()

runOperation InferredNormal context term goal = do
  captureError $ do
    ty <- synthExpr context term
    if alphaEq ty goal
      then pure ()
      else error ("subtype error: " ++ show ty ++
        " is not a subtype of " ++ show goal)

classify :: String -> Outcome
classify message
  | "solver error: unknown" `isPrefixOf` message = SolverUnknown message
  | "solver error:" `isPrefixOf` message = SolverFailure message
  | otherwise = Rejected message

matches :: Expectation -> Outcome -> Bool
matches Accept Accepted = True
matches Reject Rejected {} = True
matches SolverFails SolverFailure {} = True
matches Observe _ = True
matches _ _ = False

search :: [String] -> IO ()
search ("--record" : path : prefixes) = searchInto (Just path) prefixes
search prefixes = searchInto Nothing prefixes

searchInto :: Maybe FilePath -> [String] -> IO ()
searchInto destination prefixes = do
  results <- forM selected $ \p -> do
    result <- runProbe p
    putStrLn (identifier p ++ "\t" ++ show (expectation p) ++ "\t" ++ show result)
    pure (p, result)
  let differences = filter (\(p, r) -> not (matches (expectation p) r)) results
  forM_ destination $ \path -> writeFile path (unlines
    ("id\texpectation\toutcome\toperation\tcontext\tterm\ttype" : map row results))
  putStrLn ("TOTAL " ++ show (length results) ++ "; DISCREPANCIES " ++ show (length differences))
  forM_ differences $ \(p, result) -> do
    putStrLn ("\n" ++ identifier p ++ ": " ++ show (expectation p) ++ " / " ++ show result)
    putStrLn ("context: " ++ show (assumptions p))
    putStrLn ("operation: " ++ show (operation p))
    putStrLn ("term: " ++ source p)
    putStrLn ("type: " ++ signature p)
  where
    selected = filter (\p -> null prefixes || any (`isPrefixOf` identifier p) prefixes) probes
    row (p, r) = intercalate "\t"
      [identifier p, show (expectation p), show r, show (operation p), show (assumptions p),
       show (source p), show (signature p)]

-- This suite is intentionally opt-in: unresolved expectations must stay visible as red tests.
tests :: TestTree
tests = testGroup "Term refinement counterexample search"
  [ testCase (identifier p) $ do
      result <- runProbe p
      assertBool (show result ++ "\n" ++ source p ++ "\n" ++ signature p)
        (matches (expectation p) result)
  | p <- probes, expectation p /= Observe
  ]

probes :: [Probe]
probes = varianceMatrix ++ compositionCases ++ scopeCases ++
  applicationCases ++ limits ++ inferenceCases ++ concatenationCases

concatenationCases :: [Probe]
concatenationCases =
  [ probe ("concat/" ++ name ++ "/" ++ label) expected
      ("tfun R -> fun row -> let merged = [" ++ label ++ " = 1] @ row in ()")
      ("forall R :: " ++ domain ++ ". R -> TUnit")
  | (name, domain, permitsA, permitsB) <-
      [("unknown", "KRec", False, False),
       ("without-a", "{r :: KRec | not (`a member labels r)}", True, False),
       ("exact-a", "{r :: KRec | r == [| `a : TInt |]}", False, True),
       ("bottom", "{r :: KRec | KFalse}", True, True)]
  , (label, permits) <- [("a", permitsA), ("b", permitsB)]
  , let expected = if permits then Accept else Reject
  ]

inferenceCases :: [Probe]
inferenceCases =
  [ (probe ("inference/" ++ name ++ "/" ++ wrapper ++ "/" ++ show op) Accept term goal)
      { operation = op }
  | (name, computed) <-
      [("if", "if KTrue then TInt else TBool"),
       ("rec", "letrec A :: KType = TInt in A"),
       ("let", "let A = TInt in A")]
  , let value = "(1 : (" ++ computed ++ "))"
  , (wrapper, term, goal) <-
      [("annotation", value, "TInt"), ("record", "[a = " ++ value ++ "]", "[| `a : TInt |]"),
       ("reference", "new " ++ value, "TRef TInt")]
  , op <- [InferredFormation, InferredNormal]
  ]

unitPoly :: String -> String
unitPoly kind = "forall R :: " ++ kind ++ ". TUnit"

badRow :: String
badRow = "(let row = [a = 1 | [a = 2]] in ())"

-- The masks enumerate all equivalence classes distinguished by these refinements.
varianceMatrix :: [Probe]
varianceMatrix =
  [ (probe ("variance/" ++ from ++ "/" ++ to) expected "f" (poly target))
      { assumptions = [("f", poly actual)] }
  | (from, actual, acceptsSource) <- domains
  , (to, target, acceptsTarget) <- domains
  , let expected = if and (zipWith (\s t -> not t || s) acceptsSource acceptsTarget)
                      then Accept else Reject
  ]
  where
    poly domain = "forall A :: " ++ domain ++ ". TUnit"
    domains =
      [ ("all", "KRec", [True, True, True, True])
      , ("empty", "{r :: KRec | empty r}", [True, False, False, False])
      , ("nonempty", "{r :: KRec | not (empty r)}", [False, True, True, True])
      , ("bottom", "{r :: KRec | KFalse}", [False, False, False, False])
      , ("row-a", "{r :: KRec | r == [| `a : TInt |]}", [False, True, False, False])
      , ("row-b", "{r :: KRec | r == [| `b : TInt |]}", [False, False, True, False])
      ]

compositionCases :: [Probe]
compositionCases =
  [ probe ("composition/" ++ name ++ "/" ++ wrapper) Accept term goal
  | (name, computed) <-
      [("let", "(let A = TInt in A)"),
       ("beta", "(((fun A -> A) :: Pi A :: KType. KType) TInt)"),
       ("if", "(if KTrue then TInt else TBool)"),
       ("rec", "(letrec A :: KType = TInt in A)")]
  , let one = "(1 : " ++ computed ++ ")"
  , (wrapper, term, goal) <-
      [("annotation", one, "TInt"),
       ("field", "[a = " ++ one ++ "]", "[| `a : TInt |]"),
       ("tail", "let row = [a = " ++ one ++ "] in [b = 2 | row]",
         "[| `b : TInt, `a : TInt |]"),
       ("concat", "let row = [a = " ++ one ++ "] in [] @ row", "[| `a : TInt |]"),
       ("reference", "new " ++ one, "TRef TInt"),
       ("reference-field", "let ref = new " ++ one ++ " in [a = ref]",
         "[| `a : TRef TInt |]"),
       ("reference-reference", "let ref = new " ++ one ++ " in new ref", "TRef (TRef TInt)"),
       ("projection", "let row = [a = " ++ one ++ "] in head row", "TInt")]
  ]

scopeCases :: [Probe]
scopeCases =
  [ probe "scope/unused-free-refinement" SolverFails
      "tfun R -> ()" "forall R :: {r :: KRec | r == Missing}. TUnit"
  , probe "scope/undefined-binder-refinement" Reject
      "tfun R -> ()" "forall R :: {r :: KRec | head r == TInt}. TUnit"
  , probe "scope/short-circuit-binder-refinement" Accept
      "tfun R -> ()" "forall R :: {r :: KRec | empty r || head r == TInt}. TUnit"
  , probe "scope/refinement-guard-name-is-not-an-ambient-name" SolverFails
      "tfun x0 -> ()" "forall x0 :: {x1 :: KRec | x1 == x0}. TUnit"
  , probe "scope/inner-refinement-cannot-close-outer-obligation" Reject
      "tfun R -> let f = ((tfun S -> let g : head R -> head R = fun x -> x in ()) : forall S :: {s :: KRec | not (empty s)}. TUnit) in ()"
      (unitPoly "KRec")
  ]

applicationCases :: [Probe]
applicationCases =
  [ (probe ("application/refined-type-argument/" ++ name) expected
       ("f [" ++ argument ++ "]") "TUnit")
      { assumptions = [("f", "forall R :: {r :: KRec | not (empty r)}. TUnit")] }
  | (name, argument, expected) <-
      [("nonempty", "[| `a : TInt |]", Accept), ("empty", "[||]", Reject),
       ("wrong-base", "TInt", Reject),
       ("computed-nonempty", "if KTrue then [| `a : TInt |] else [||]", Accept),
       ("computed-empty", "if KFalse then [| `a : TInt |] else [||]", Reject)]
  ] ++
  [ probe "application/recursive-signature-does-not-trust-body" Reject
      "letrec f : TInt -> TInt = fun x -> True in ()" "TUnit"
  , probe "application/unrestricted-term-recursion" Accept
      "letrec f : TInt -> TInt = fun x -> f x in ()" "TUnit"
  , probe "application/unused-checking-only-type-argument" Accept
      "let f = ((tfun R -> ()) : forall R :: KType. TUnit) in f [(let A = TInt in A)]"
      "TUnit"
  , probe "application/unused-higher-order-argument" Accept
      "let f = ((tfun F -> ()) : forall F :: Pi A :: KType. KType. TUnit) in f [(fun A -> A)]"
      "TUnit"
  , probe "application/type-argument-invalid-unused-definition" Reject
      "let f = ((tfun R -> ()) : forall R :: KType. TUnit) in f [(let bad = head [||] in TInt)]"
      "TUnit"
  ]

limits :: [Probe]
limits =
  [ probe "limits/runtime-boolean-does-not-guard" Reject
      ("if False then " ++ badRow ++ " else ()") "TUnit"
  , probe "limits/vacuous-refinement-keeps-structural-checks" Reject
      "tfun R -> True" "forall R :: {r :: KRec | KFalse}. TUnit"
  , probe "limits/abstract-record-projection" Reject
      "tfun R -> fun row -> head row"
      "forall R :: {r :: KRec | not (empty r)}. R -> head R"
  , probe "limits/abstract-reference-elimination" Reject
      "tfun R -> fun ref -> !ref" "forall R :: KRef. R -> refOf R"
  , probe "limits/abstract-arrow-elimination" Reject
      "tfun F -> fun f -> fun x -> f x" "forall F :: KFun. F -> dom F -> img F"
  , probe "limits/refinement-equality-is-not-conversion" Reject
      "tfun A -> 1" "forall A :: {a :: KType | a == TInt}. A"
  , probe "limits/mutable-reference-is-invariant" Reject
      "let r = new 1 in r" "TRef TBool"
  , probe "limits/wrong-assignment" Reject
      "let r = new 1 in r := True" "TUnit"
  , probe "limits/row-width" Reject "[a = 1, b = True]" "[| `a : TInt |]"
  , probe "limits/row-order" Reject "[a = 1, b = True]" "[| `b : TBool, `a : TInt |]"
  , probe "limits/computed-universal-signature" Accept "tfun A -> fun x -> x"
      "let F = (forall A :: KType. A -> A) in F"
  , probe "limits/annotated-computed-universal-signature" Accept "tfun A -> fun x -> x"
      "(let F = (forall A :: KType. A -> A) in F) :: KGen A :: KType. KType"
  , probe "limits/invalid-formation-before-divergence" Reject
      "let f : (let bad = head [||] in letrec T :: KType = T in T) = () in ()"
      "TUnit"
  , (probe "limits/invalid-concat-left-before-divergent-right" Observe
       "0 @ slow" "[||]")
      { assumptions = [("slow", "letrec T :: KType = T in T")] }
  , probe "limits/invalid-concat-left-before-concrete-right" Reject "0 @ []" "[||]"
  ]
