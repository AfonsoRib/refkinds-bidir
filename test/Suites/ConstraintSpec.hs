{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
module Suites.ConstraintSpec (tests, solverProbe) where

import Control.Exception (bracket)
import qualified Data.Kind as Kind
import Data.List (isInfixOf)
import Data.Proxy (Proxy(..))
import GHC.Generics
import Constraint
import System.Directory
import System.Environment (getEnvironment, getExecutablePath)
import System.Exit (ExitCode(..))
import System.FilePath ((</>))
import System.IO (hClose, openTempFile)
import System.Process (CreateProcess(..), proc, readCreateProcessWithExitCode)
import Test.Tasty
import Test.Tasty.HUnit
import Types

tests :: TestTree
tests = testGroup "Constraints"
  [ testCase "constructor inventory is closed" $
      constructorNames (Proxy :: Proxy (Rep Cstr)) @?=
        ["CTrue", "CPred", "CAll", "CAnd"]
  , testCase "CTrue is solver-free and conjunctions use one raw query" $
      withSolverDirectory $ \directory -> do
        executable <- getExecutablePath
        environment <- getEnvironment
        let solver = directory </> "cvc5"
            count = directory </> "count"
            process = (proc executable ["--constraint-solver-probe"])
              { env = Just (("PATH", directory) : ("REFK_CVC5_COUNT", count) :
                  filter (\(name, _) -> name /= "PATH" && name /= "REFK_CVC5_COUNT") environment)
              }
        writeFile solver $ unlines
          [ "#!/bin/sh"
          , "printf x >> \"$REFK_CVC5_COUNT\""
          , "printf 'unsat\\n'"
          ]
        permissions <- getPermissions solver
        setPermissions solver permissions { executable = True }
        (status, output, errors) <- readCreateProcessWithExitCode process ""
        status @?= ExitSuccess
        assertBool (output ++ errors) ("(Valid,Valid)" `isInfixOf` output)
        readFile count >>= (@?= "x")
  ]

solverProbe :: IO ()
solverProbe = do
  trivial <- checkValid CTrue
  conjunction <- checkValid (cAnd
    [ cPred ((binaryPredOp BEq PInt PInt))
    , cPred ((binaryPredOp BEq PBool PBool))
    ])
  print (trivial, conjunction)

withSolverDirectory :: (FilePath -> IO a) -> IO a
withSolverDirectory = bracket create removePathForcibly
  where
    create = do
      temporary <- getTemporaryDirectory
      (path, handle) <- openTempFile temporary "refk-constraint-solver"
      hClose handle
      removeFile path
      createDirectory path
      pure path

class ConstructorNames (f :: Kind.Type -> Kind.Type) where
  constructorNames :: proxy f -> [String]

instance ConstructorNames f => ConstructorNames (M1 D metadata f) where
  constructorNames _ = constructorNames (Proxy :: Proxy f)

instance (ConstructorNames left, ConstructorNames right) =>
    ConstructorNames (left :+: right) where
  constructorNames _ = constructorNames (Proxy :: Proxy left)
    ++ constructorNames (Proxy :: Proxy right)

instance Constructor metadata => ConstructorNames (M1 C metadata f) where
  constructorNames _ = [conName (undefined :: M1 C metadata f ())]
