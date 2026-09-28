module Main where

import qualified Check as C
import qualified Context as Ctx
import qualified Parser as P
import qualified System.Environment as Environment
import qualified Types as T

main :: IO ()
main = do
  args <- Environment.getArgs
  case args of
    ["--help"] -> putStrLn usage
    ["term", file] -> runTerm Nothing file
    ["term", "--check", expected, file] -> runTerm (Just expected) file
    ["kind", file] -> runKind file
    _ -> error ("usage error: " ++ usage)

usage :: String
usage = unlines
  [ "Usage: refk term FILE"
  , "       refk term --check TYPE FILE"
  , "       refk kind FILE"
  ]

runTerm :: Maybe String -> FilePath -> IO ()
runTerm expected path = do
  source <- readFile path
  expression <- either (error . ("parse error: " ++)) pure
    (P.parseExpr source)
  case expected of
    Nothing -> do
      inferred <- C.synthType Ctx.emptyContext expression
      putStrLn ("Checked :: " ++ show inferred)
    Just typeSource -> do
      expectedType <- either (error . ("type parse error: " ++)) pure
        (P.parseType typeSource)
      _ <- C.validateTypeKind Ctx.emptyContext expectedType (T.bTrue T.BKType)
      C.checkType Ctx.emptyContext expression expectedType
      putStrLn ("Checked :: " ++ show expectedType)

runKind :: FilePath -> IO ()
runKind path = do
  source <- readFile path
  ty <- either (error . ("parse error: " ++)) pure (P.parseType source)
  result <- C.validateInferredKind Ctx.emptyContext ty
  putStrLn ("Checked :: " ++ show result)
