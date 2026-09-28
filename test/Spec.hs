{-# LANGUAGE OverloadedStrings #-}
module Main where

import qualified Suites.PredicateSyntaxSpec as PredicateSyntaxSpec
import qualified Suites.CheckerRefactorSpec as CheckerRefactorSpec
import qualified Suites.CheckerOnlySpec as CheckerOnlySpec
import qualified Suites.CliSpec as CliSpec
import System.Environment (getArgs, withArgs)
import qualified Suites.StrictSpecificationSpec as Strict
import qualified Suites.EqualityBoundarySpec as EqualityBoundarySpec
import qualified Suites.PaperEqualitySpec as PaperEqualitySpec
import qualified Suites.NameAnalysisSpec as NameAnalysisSpec
import qualified Suites.ConstraintSpec as ConstraintSpec
import qualified Suites.ContextSpec as ContextSpec
import Test.Tasty
import qualified Suites.GeneralizedKindSpec as GeneralizedKindSpec
import qualified Suites.UninterpretedSpec as UninterpretedSpec
import qualified Suites.ANFSpec as ANFSpec
import qualified Suites.KernelBoundarySpec as KernelBoundarySpec
import qualified Suites.LocallyNamelessSpec as LocallyNamelessSpec
import qualified Suites.SemanticEqualitySpec as SemanticEqualitySpec
import qualified Suites.WhnfEqualitySpec as WhnfEqualitySpec
import qualified Suites.SubkindingSpec as SubkindingSpec
import qualified Suites.CheckStructureSpec as CheckStructureSpec
import qualified Suites.TypeCheckerSpec as TypeCheckerSpec
import qualified Suites.TermCheckerSpec as TermCheckerSpec
import qualified Suites.TermValidationSpec as TermValidationSpec
import qualified Suites.TermRefinementSearch as TermRefinementSearch
import qualified Suites.ParserSpec as ParserSpec
import qualified Suites.ParsedSyntaxSpec as ParsedSyntaxSpec
import qualified Suites.PaperExamplesSpec as PaperExamplesSpec
import qualified Suites.BehaviorCatalogueSpec as BehaviorCatalogueSpec
import qualified Suites.TypeConstructsSpec as TypeConstructsSpec
import qualified Suites.SurfaceLoweringSpec as SurfaceLoweringSpec
import qualified Suites.RecordConstraintSpec as RecordConstraintSpec
import qualified Suites.RecursiveMapSpec as RecursiveMapSpec
import qualified Suites.EmbeddedTypeSpec as EmbeddedTypeSpec

main :: IO ()
main = do
  args <- getArgs
  case args of
    ["--normalization-probe"] -> Strict.normalizationProbe
    ["--exposure-probe"] -> Strict.exposureProbe
    ["--quotation-probe"] -> Strict.quotationProbe
    ["--type-application-probe"] -> Strict.typeApplicationProbe
    ["--equality-probe"] -> Strict.equalityProbe
    ["--kind-failure-probe"] -> Strict.kindFailureProbe
    ["--constraint-solver-probe"] -> ConstraintSpec.solverProbe
    ["--term-validation-probe", mode] -> TermValidationSpec.solverProbe mode
    ["--strict-visible-probe", mode] -> TermCheckerSpec.strictVisibleProbe mode
    "--term-refinement-search" : prefixes -> TermRefinementSearch.search prefixes
    "--term-refinement-counterexamples" : options ->
      withArgs options (defaultMain TermRefinementSearch.tests)
    _ -> defaultMain tests

tests :: TestTree
tests = testGroup "refinement Kinds Test Suite"
  [ PredicateSyntaxSpec.tests
  , CheckerRefactorSpec.tests
  , CheckerOnlySpec.tests
  , CliSpec.tests
  , NameAnalysisSpec.tests
  , ConstraintSpec.tests
  , ContextSpec.tests
  , GeneralizedKindSpec.tests
  , UninterpretedSpec.tests
  , PaperEqualitySpec.tests
  , EqualityBoundarySpec.tests
  , Strict.tests
  , ANFSpec.tests
  , SurfaceLoweringSpec.tests
  , RecordConstraintSpec.tests
  , RecursiveMapSpec.tests
  , EmbeddedTypeSpec.tests
  , KernelBoundarySpec.tests
  , LocallyNamelessSpec.tests
  , SemanticEqualitySpec.tests
  , WhnfEqualitySpec.tests
  , SubkindingSpec.tests
  , CheckStructureSpec.tests
  , TypeCheckerSpec.tests
  , TermCheckerSpec.tests
  , TermValidationSpec.tests
  , ParserSpec.tests
  , ParsedSyntaxSpec.tests
  , PaperExamplesSpec.tests
  , BehaviorCatalogueSpec.tests
  , TypeConstructsSpec.tests
  ]
