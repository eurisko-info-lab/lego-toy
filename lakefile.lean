import Lake
open Lake DSL

/-!
# Bootstrap Chain

Code generation follows a bootstrap chain with no circular dependency:

    gen(V_n) = tolean_{V_{n-1}}(Bootstrap.lego)

Build stages:
  1. Stage 1: Build tolean using checked-in generated/*.lean (V_{n-1})
  2. Stage 2: Run tolean to regenerate from Bootstrap.lego → V_n
  3. Stage 3: Rebuild with V_n (if different)
  4. Fixpoint check: V_n should produce V_n (self-hosting)

To regenerate: ./scripts/bootstrap.sh
To verify canonical (CI): ./scripts/bootstrap.sh --check
-/

package «lego» where
  version := v!"0.1.0"

lean_lib «Lego» where
  srcDir := "src"

-- Cubical Runtime library (multi-target runtime for generated code)
lean_lib «CubicalRuntime» where
  srcDir := "src"
  roots := #[`Runtime.Cubical.Lean.Runtime]

-- Rosetta code generation pipeline
lean_lib «Rosetta» where
  srcDir := "src"
  roots := #[`Rosetta.Rosetta, `Rosetta.CodeGen]

-- Generated Cubical files (from cubical-pipeline)
-- Uses CubicalGen to avoid module conflicts with examples/Cubical
lean_lib «CubicalGen» where
  srcDir := "generated"
  roots := #[`CubicalGen.Cofibration, `CubicalGen.Conversion, `CubicalGen.Core,
             `CubicalGen.CubicalTT, `CubicalGen.Datatype, `CubicalGen.Domain,
             `CubicalGen.Elaborate, `CubicalGen.ExtType, `CubicalGen.FHCom,
             `CubicalGen.GlobalEnv, `CubicalGen.HIT, `CubicalGen.Kan,
             `CubicalGen.Module, `CubicalGen.Quote, `CubicalGen.Red,
             `CubicalGen.Redtt, `CubicalGen.RefineMonad, `CubicalGen.Semantics,
             `CubicalGen.Signature, `CubicalGen.Splice, `CubicalGen.SubType,
             `CubicalGen.Tactic, `CubicalGen.TermBuilder, `CubicalGen.TypeAttrs,
             `CubicalGen.Unify, `CubicalGen.Visitor, `CubicalGen.VType]

lean_exe «rosetta» where
  root := `RosettaMain

-- Bootstrap code (required to regenerate itself)
-- Regenerate with: ./scripts/bootstrap.sh
lean_lib «LegoGenerated» where
  srcDir := "generated"
  roots := #[`BootstrapGrammar, `BootstrapTokenizer, `BootstrapRules, `MinimalBootstrapTokenizer]

-- Code generation tools and pipelines (tools/)
lean_lib «ToolsLib» where
  srcDir := "tools"
  roots := #[`MultiTargetPipeline, `GrammarDrivenPipeline, `ToLean]

-- Shared test utilities library
lean_lib «TestUtils» where
  srcDir := "test/lean"
  roots := #[`TestUtils]

lean_exe «test-grammar-driven» where
  root := `test.lean.TestGrammarDriven

lean_exe «test-codegen» where
  root := `test.lean.TestCodeGen

@[default_target]
lean_exe «lego» where
  root := `Main

lean_exe «lego-test» where
  root := `test.lean.Test
  -- Ensure proper linking with Init library
  moreLinkArgs := #["-lInit"]

lean_exe «lego-test-cool» where
  root := `test.lean.TestCool
  moreLinkArgs := #["-lInit"]

lean_exe «lego-test-runtime» where
  root := `test.lean.TestRuntime
  moreLinkArgs := #["-lInit"]

lean_exe «lego-test-cubical-gen» where
  root := `test.lean.TestCubicalGen
  moreLinkArgs := #["-lInit"]

lean_exe «lego-test-minimal» where
  root := `test.lean.TestMinimalBootstrap
  moreLinkArgs := #["-lInit"]

-- Parse all files test: verifies all .lego, .rosetta, .lean files parse correctly
lean_exe «lego-test-parse» where
  root := `test.lean.TestParseAll
  moreLinkArgs := #["-lInit"]

-- Tools executables

lean_exe «tolean» where
  root := `tools.ToLean

-- Multi-target pipeline: .lego/.rosetta → Lean/Rust/Haskell/Scala
lean_exe «multi-target» where
  root := `tools.MultiTargetPipeline

-- Grammar interpreter unit tests
lean_exe «lego-test-grammar» where
  root := `test.lean.TestGrammarInterp
  moreLinkArgs := #["-lInit"]

-- Composition unit tests
lean_exe «lego-test-compose» where
  root := `test.lean.TestComposition
  moreLinkArgs := #["-lInit"]

-- Integration pipeline tests
lean_exe «lego-test-pipeline» where
  root := `test.lean.TestIntegration
  moreLinkArgs := #["-lInit"]

-- Code generator comparison tests
lean_exe «lego-test-codegen-compare» where
  root := `test.lean.TestCodeGenComparison
  moreLinkArgs := #["-lInit"]

-- Unified test runner (runs all test suites)
lean_exe «lego-test-all» where
  root := `test.lean.TestAll
  moreLinkArgs := #["-lInit"]

-- Coverage analysis tool
lean_exe «lego-coverage» where
  root := `test.lean.TestCoverage
  moreLinkArgs := #["-lInit"]

-- Algebra module tests (highest dependency priority)
lean_exe «lego-test-algebra» where
  root := `test.lean.TestAlgebra
  moreLinkArgs := #["-lInit"]

-- Loader module tests
lean_exe «lego-test-loader» where
  root := `test.lean.TestLoaderUnit
  moreLinkArgs := #["-lInit"]

-- Interp module tests
lean_exe «lego-test-interp» where
  root := `test.lean.TestInterpUnit
  moreLinkArgs := #["-lInit"]

-- Bootstrap module tests
lean_exe «lego-test-bootstrap» where
  root := `test.lean.TestBootstrapUnit
  moreLinkArgs := #["-lInit"]

-- Attr module tests
lean_exe «lego-test-attr» where
  root := `test.lean.TestAttrUnit
  moreLinkArgs := #["-lInit"]

-- Validation module tests
lean_exe «lego-test-validation» where
  root := `test.lean.TestValidationUnit
  moreLinkArgs := #["-lInit"]

-- Language registry tests
lean_exe «lego-test-language-registry» where
  root := `test.lean.TestLanguageRegistryUnit
  moreLinkArgs := #["-lInit"]

-- Runtime tests
lean_exe «lego-test-runtime-unit» where
  root := `test.lean.TestRuntimeUnit
  moreLinkArgs := #["-lInit"]

-- AttrEval tests
lean_exe «lego-test-attr-eval» where
  root := `test.lean.TestAttrEvalUnit
  moreLinkArgs := #["-lInit"]
