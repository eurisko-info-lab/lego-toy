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

-- Rosetta code generation pipeline
lean_lib «Rosetta» where
  srcDir := "src"
  roots := #[`Rosetta.Rosetta, `Rosetta.CodeGen, `Rosetta.UnifiedCodeGen]

lean_exe «rosetta» where
  root := `RosettaMain

-- Bootstrap code (required to regenerate itself)
-- Regenerate with: ./scripts/bootstrap.sh
lean_lib «LegoGenerated» where
  srcDir := "generated"
  roots := #[`BootstrapGrammar, `BootstrapTokenizer, `BootstrapRules, `MinimalBootstrapTokenizer]

-- Code generation pipelines (pipelines/)
lean_lib «RosettaPipeline» where
  srcDir := "pipelines"
  roots := #[`Pipeline, `RosettaPipeline, `MultiTargetPipeline, `GrammarDrivenPipeline]

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

lean_exe «lego-test-red» where
  root := `test.lean.TestRed
  moreLinkArgs := #["-lInit"]

lean_exe «lego-test-cool» where
  root := `test.lean.TestCool
  moreLinkArgs := #["-lInit"]

lean_exe «lego-test-runtime» where
  root := `test.lean.TestRuntime
  moreLinkArgs := #["-lInit"]

lean_exe «lego-test-minimal» where
  root := `test.lean.TestMinimalBootstrap
  moreLinkArgs := #["-lInit"]

-- Tools
-- Cubical code generators (tools/Cubical/)
lean_lib «CubicalTools» where
  srcDir := "tools"
  roots := #[`Cubical]

lean_exe «toantlr» where
  root := `tools.ToAntlr

lean_exe «totreesitter» where
  root := `tools.ToTreeSitter

lean_exe «tolean» where
  root := `tools.ToLean

-- Code Generation (Single Source of Truth)
-- Generates RedTT, CoolTT, and Lean from Grammar.sexpr
lean_exe «lego-gen» where
  root := `tools.LegoGen

-- Pipeline: CubicalTT → cubical2rosetta → rosetta2lean
lean_exe «pipeline» where
  root := `pipelines.Pipeline

-- Rosetta Pipeline: .rosetta → Rosetta.lego → rosetta2lean → Lean
lean_exe «rosetta-pipeline» where
  root := `pipelines.RosettaPipeline

-- Multi-Target Pipeline: .lego → Rosetta IR → Lean/Scala/Haskell/Rust
lean_exe «multi-target» where
  root := `pipelines.MultiTargetPipeline

-- Comparison test: hand-written vs generated Cubical
@[default_target]
lean_exe «cubical-compare» where
  root := `test.TestCubicalComparison
