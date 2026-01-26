/-
  GrammarDrivenPipeline.lean
  Multi-target code generation using grammar-driven pretty-printing.

  Architecture:
    1. source.lego → parse → AST
    2. Load <L>.lego grammar (contains layout annotations)
    3. AST → grammar interpreter printToString → target code

  The grammar files (Lean.lego, Scala.lego, etc.) define both:
    - Syntax (how to parse target language)
    - Layout (how to format output via @nl, @indent, @dedent)

  This file just provides the types and glue code.
-/

import Lego.Runtime
import Lego.Loader

open Lego.Runtime
open Lego.Loader
open Lego

/-! ## Target Language Configuration -/

/-- Target language enumeration -/
inductive TargetLang | Lean | Scala | Haskell | Rust
  deriving Repr, BEq, Inhabited

instance : ToString TargetLang where
  toString
    | .Lean => "Lean"
    | .Scala => "Scala"
    | .Haskell => "Haskell"
    | .Rust => "Rust"

def TargetLang.ext : TargetLang → String
  | .Lean => ".lean"
  | .Scala => ".scala"
  | .Haskell => ".hs"
  | .Rust => ".rs"

/-- Path to <L>.lego grammar file -/
def TargetLang.grammarPath : TargetLang → String
  | .Lean => "./src/Rosetta/Lean.lego"
  | .Scala => "./src/Rosetta/Scala.lego"
  | .Haskell => "./src/Rosetta/Haskell.lego"
  | .Rust => "./src/Rosetta/Rust.lego"

/-- Language-specific file header -/
def TargetLang.header : TargetLang → String
  | .Haskell => "module Generated where\n\n"
  | .Scala => "package generated\n\n"
  | .Rust => "#![allow(dead_code)]\n#![allow(unused_variables)]\n\n"
  | .Lean => ""

/-! ## Pipeline Result -/

/-- Pipeline result -/
structure TargetResult where
  lang : TargetLang
  code : String
  outPath : String
  deriving Repr

/-! ## Main Pipeline -/

/-- Run grammar-driven pipeline for one target.
    Loads the target grammar and uses printToString from the interpreter. -/
def runForTarget (rt : Runtime) (sourceAst : Term) (lang : TargetLang) (outDir : String)
    (_quiet : Bool := false) : IO (Except String TargetResult) := do
  -- Load the target grammar
  let grammarPath := lang.grammarPath
  let grammar ← match ← loadLanguage rt grammarPath with
    | .error e => return .error s!"Failed to load grammar {grammarPath}: {e}"
    | .ok g => pure g

  -- Use the grammar interpreter to print the AST
  -- The grammar's layout annotations (@nl, @indent, etc.) control formatting
  -- Try various entry points that might match the AST structure
  let entryPoints := ["file", "module", "program", "rosettaFile", "decl", "seq"]
  let code := entryPoints.findSome? (printToString grammar · sourceAst)
    |>.getD s!"-- Failed to print AST for {lang}\n-- AST: {sourceAst}"

  -- Add language-specific header
  let finalCode := lang.header ++ code

  -- Build result
  let moduleName := "Generated"
  let outPath := s!"{outDir}/{moduleName}{lang.ext}"

  return .ok { lang, code := finalCode, outPath }

/-- Run pipeline for all targets -/
def runGrammarDrivenPipeline (rt : Runtime) (sourcePath : String)
    (targets : List TargetLang := [.Lean, .Scala, .Haskell, .Rust])
    (outDir : String := "./generated/Rosetta")
    (quiet : Bool := false)
    : IO (Except String (List TargetResult)) := do

  -- Parse source
  let sourceAst ← match ← parseLegoFilePathE rt sourcePath with
    | .error e => return .error s!"Failed to parse source: {e}"
    | .ok ast => pure ast

  -- Generate for each target
  let mut results : List TargetResult := []
  for lang in targets do
    match ← runForTarget rt sourceAst lang outDir quiet with
    | .error _ => pure ()
    | .ok r => results := results ++ [r]

  -- Write files
  IO.FS.createDirAll outDir
  for r in results do
    IO.FS.writeFile r.outPath r.code

  return .ok results
