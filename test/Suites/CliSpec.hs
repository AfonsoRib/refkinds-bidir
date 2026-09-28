module Suites.CliSpec (tests) where

import Control.Exception (bracket)
import Data.List (isPrefixOf)
import System.Directory (getTemporaryDirectory, removeFile)
import System.Exit (ExitCode(..))
import System.IO (hClose, hPutStr, openTempFile)
import System.Process (readProcessWithExitCode)
import Test.Tasty
import Test.Tasty.HUnit

tests :: TestTree
tests = testGroup "Command-line interface"
  [ testCase "term synthesis preserves success output" $
      withSource "1" $ \path -> do
        (status, out, err) <- run ["term", path]
        status @?= ExitSuccess
        out @?= "Checked :: TInt\n"
        err @?= ""
  , testCase "term checking preserves success output" $
      withSource "1" $ \path -> do
        (status, out, err) <- run ["term", "--check", "TInt", path]
        status @?= ExitSuccess
        out @?= "Checked :: TInt\n"
        err @?= ""
  , testCase "kind inference preserves success output" $
      withSource "TInt" $ \path -> do
        (status, out, err) <- run ["kind", path]
        status @?= ExitSuccess
        out @?= "Checked :: KBase BKType (Refined \"v\" (PInterp2 BEq (PBound 0) PInt))\n"
        err @?= ""
  , testCase "polymorphic selector signatures check through the CLI" $
      withSource "tfun R -> ((fun x -> x) : head R -> head R)" $ \path -> do
        (status, out, err) <- run
          ["term", "--check",
           "forall R :: {r :: KRec | not (empty r)}. ((head R -> head R) :: KType)", path]
        status @?= ExitSuccess
        assertBool out ("Checked :: TForall" `isPrefixOf` out)
        err @?= ""
  , testCase "polymorphic selector signatures require nonemptiness" $
      withSource "tfun R -> ((fun x -> x) : head R -> head R)" $ \path ->
        assertFailurePrefix
          ["term", "--check", "forall R :: KRec. ((head R -> head R) :: KType)", path]
          "invalid-kind error: constraint is not valid"
  , testCase "kind and term errors retain CLI behavior" $ do
      withSource "let r = [a = 1 | [a = 2]] in ()" $ \path ->
        assertFailurePrefix ["term", "--check", "TUnit", path]
          "type error: duplicate record label: a"
      withSource "True" $ \path ->
        assertFailurePrefix ["term", "--check", "TInt", path]
          "subtype error:"
  , testCase "failure categories retain their prefixes" $ do
      withSource "@" $ \path -> assertFailurePrefix ["term", path] "parse error:"
      withSource "1" $ \path -> assertFailurePrefix
        ["term", "--check", "(", path] "type parse error:"
      withSource "fun x -> x" $ \path -> assertFailurePrefix
        ["term", path] "type error:"
      assertFailurePrefix ["kind", "/definitely/missing/refk-input.rk"]
        "/definitely/missing/refk-input.rk:"
      assertFailurePrefix [] "usage error:"
  ]

run :: [String] -> IO (ExitCode, String, String)
run arguments = readProcessWithExitCode "refk" arguments ""

assertFailurePrefix :: [String] -> String -> Assertion
assertFailurePrefix arguments prefix = do
  (status, _, err) <- run arguments
  assertBool "command unexpectedly succeeded" (status /= ExitSuccess)
  let message = dropProgramPrefix err
  assertBool ("missing prefix " ++ show prefix ++ " in " ++ show err)
    (prefix `isPrefixOf` message)

dropProgramPrefix :: String -> String
dropProgramPrefix message = case removePrefix "refk: " message of
  Just rest -> rest
  Nothing -> message

removePrefix :: Eq a => [a] -> [a] -> Maybe [a]
removePrefix [] value = Just value
removePrefix _ [] = Nothing
removePrefix (x:xs) (y:ys)
  | x == y = removePrefix xs ys
  | otherwise = Nothing

withSource :: String -> (FilePath -> IO a) -> IO a
withSource source = bracket create removeFile
  where
    create = do
      directory <- getTemporaryDirectory
      (path, handle) <- openTempFile directory "refk-cli.rk"
      hPutStr handle source
      hClose handle
      pure path
