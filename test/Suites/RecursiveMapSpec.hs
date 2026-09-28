{-# LANGUAGE OverloadedStrings #-}

module Suites.RecursiveMapSpec (tests) where

import Check (checkRaw, synthRaw)
import ANF (elaborate, elaborateExpr)
import qualified Data.Text as Text
import Constraint (SolverResult(..), checkValid)
import Context hiding (implicationConstraint)
import Check (checkTypeEquality)
import Suites.Common (check, synth, checkExpr, parseTestType)
import Test.Tasty
import Test.Tasty.HUnit
import Types
import qualified Control.Exception as Exception
import Support.Errors (assertError, assertPureError)

tests :: TestTree
tests = testGroup "Recursive refined Map"
  [ testCase "raw and ANF APIs accept unrestricted type recursion" $ do
      let bad = parseTestType "letrec Loop :: Pi r :: KRec. KRec = fun r -> Loop r in [||]"
          unusedCall = parseTestType "letrec Loop :: Pi r :: KRec. KRec = fun r -> let ignored = Loop r in [||] in [||]"
          escape = parseTestType "letrec Loop :: Pi r :: KRec. KRec = Loop in [||]"
      mapM_ (\ty -> do
        assertAccepted (checkRaw emptyContext ty (bTrue BKRec))
        assertPureError (synthRaw emptyContext ty)
        assertAccepted (check emptyContext (elaborate ty) (bTrue BKRec))
        assertPureError (synth emptyContext (elaborate ty))
        let term = EAnn ERecordNil ty
        checkExpr emptyContext term TRecNil
        checkExpr emptyContext (elaborateExpr term) TRecNil)
        [bad, escape, unusedCall]

  , testCase "decreasing type recursion still checks after ANF" $ do
      let ty = parseTestType "letrec Drop :: Pi r :: KRec. KRec = fun r -> if empty r then [||] else Drop (tail r) in [||]"
      mapM_ (\vc -> checkValid vc >>= (@?= Valid))
        [checkRaw emptyContext ty (bTrue BKRec), check emptyContext (elaborate ty) (bTrue BKRec)]

  , testCase "a nonstructural recursive call can terminate" $ do
      let ty = parseTestType "letrec Clear :: Pi r :: KRec. KRec = fun r -> if empty r then [||] else Clear [||] in Clear [| `x : TInt |]"
      let vc = checkRaw emptyContext ty (bTrue BKRec)
      checkValid vc >>= (@?= Valid)
      checkTypeEquality emptyContext (bTrue BKRec) ty TRecNil >>= (@?= ())
  , testCase "unrestricted recursion still checks its declared kind" $ do
      let ty = parseTestType "letrec Bad :: Pi r :: KRec. KRec = fun r -> TInt in [||]"
      assertError (Exception.evaluate (checkRaw emptyContext ty (bTrue BKRec))
        >>= checkValid)
  , testCase "local recursive Map computes every field and the empty base case" $ do
      let mapped = parseTestType (Text.unlines
            [ "letrec Map ::"
            , "  Pi row :: KRec."
            , "  Pi transform :: (Pi field :: KType. KType)."
            , "  { mapped :: KRec | labels mapped == labels row } ="
            , "  fun row -> fun transform ->"
            , "    if not empty row then"
            , "      [| headLabel row : transform (head row) |]"
            , "        @ Map (tail row) transform"
            , "    else [||]"
            , "in Map [| `first : TInt, `second : TString, `third : TUnit |]"
            , "     ((fun field -> TBool) :: Pi field :: KType. KType)"
            ])
          expected = parseTestType
            "[| `first : TBool, `second : TBool, `third : TBool |]"
      checkTypeEquality emptyContext (bTrue BKRec) mapped expected >>= (@?= ())

  , testCase "Map supports identity, arrow, empty, and nested transformations" $ do
      let cases =
            [ ( mapApplication
                  "[| `integer : TInt, `text : TString |]"
                  "(fun field -> field)"
              , "[| `integer : TInt, `text : TString |]"
              )
            , ( mapApplication
                  "[| `integer : TInt, `text : TString |]"
                  "(fun field -> field -> TBool)"
              , "[| `integer : TInt -> TBool, `text : TString -> TBool |]"
              )
            , (mapApplication "[||]" "(fun field -> TBool)", "[||]")
            , ( mapApplication
                  "[| `nested : [| `inside : TInt |], `flag : TBool |]"
                  "(fun field -> field)"
              , "[| `nested : [| `inside : TInt |], `flag : TBool |]"
              )
            ]
      mapM_ (\(actualSource, expectedSource) ->
        checkTypeEquality emptyContext (bTrue BKRec)
          (parseTestType (Text.pack actualSource))
          (parseTestType (Text.pack expectedSource)) >>= (@?= ())) cases

  ]

mapApplication :: String -> String -> String
mapApplication row transform = unlines
  [ "letrec Map ::"
  , "  Pi row :: KRec."
  , "  Pi transform :: (Pi field :: KType. KType)."
  , "  { mapped :: KRec | labels mapped == labels row } ="
  , "  fun row -> fun transform ->"
  , "    if not empty row then"
  , "      [| headLabel row : transform (head row) |]"
  , "        @ Map (tail row) transform"
  , "    else [||]"
  , "in Map " ++ row ++ " (" ++ transform ++ " :: Pi field :: KType. KType)"
  ]

assertAccepted :: a -> Assertion
assertAccepted value = Exception.evaluate value >> pure ()
