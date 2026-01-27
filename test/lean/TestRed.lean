/-
  TestRed: Red-specific tests for Lego

  Tests for parsing .red (redtt) files and cubical validation.
  Run with: lake exe lego-test-red

  NOTE: This test suite uses Runtime.init to ensure Bootstrap.lego
  is loaded first, providing the correct grammar for all .lego file parsing.
-/

import Lego
import Lego.Bootstrap
import Lego.Loader
import Lego.Runtime
import Lego.RedValidation

open Lego
open Lego.Loader
open Lego.Runtime
open Lego.RedValidation

set_option linter.unusedVariables false

/-! ## Test Framework -/

structure TestResult where
  name : String
  passed : Bool
  message : String := ""

def assertTrue (name : String) (cond : Bool) (msg : String := "") : TestResult :=
  { name := name, passed := cond, message := if cond then "✓" else s!"✗ {msg}" }

def assertEq [BEq α] [Repr α] (name : String) (actual expected : α) : TestResult :=
  let passed := actual == expected
  { name := name
    passed := passed
    message := if passed then "✓" else s!"✗ expected {repr expected}, got {repr actual}" }

/-! ## Redtt Parsing Utilities -/

def redttFuel : Nat := 100000

/-- Add containsSubstr helper -/
def String.containsSubstr (s sub : String) : Bool :=
  (s.splitOn sub).length > 1

/-- Get the main token productions to try in priority order -/
def getMainTokenProdsOrdered (tokenProds : Productions) : List String :=
  let names := tokenProds.map (·.1)
  -- Priority: comments/whitespace first (to skip), then longest operators first
  let priority := ["Token.comment", "Token.ws", "Token.string", "Token.op3", "Token.op2",
                   "Token.ident", "Token.number", "Token.sym"]
  priority.filter names.contains

/-- Remove block comments /-...-/ from content (handles nesting) -/
def stripBlockComments (content : String) : String := Id.run do
  let mut result := ""
  let mut depth := 0
  let chars := content.toList
  let mut i := 0
  while i < chars.length do
    let c := chars[i]!
    let nextC := if i + 1 < chars.length then chars[i + 1]! else ' '
    if c == '/' && nextC == '-' then
      depth := depth + 1
      i := i + 2
    else if c == '-' && nextC == '/' then
      depth := max 0 (depth - 1)
      i := i + 2
    else if depth == 0 then
      result := result.push c
      i := i + 1
    else
      i := i + 1
  result

/-- Split a .red file into individual top-level declarations -/
def splitRedDecls (content : String) : List String := Id.run do
  let noBlockComments := stripBlockComments content
  let noComments := noBlockComments.splitOn "\n"
    |>.map (fun line =>
      match line.splitOn "--" with
      | [] => ""
      | first :: _ => first)
    |> String.intercalate "\n"
  let lines := noComments.splitOn "\n"
  let mut decls : List String := []
  let mut current := ""
  for line in lines do
    let trimmed := line.trimLeft
    if trimmed.startsWith "import " || trimmed.startsWith "def " ||
       trimmed.startsWith "data " || trimmed.startsWith "public " ||
       trimmed.startsWith "meta " || trimmed.startsWith "opaque " ||
       trimmed.startsWith "private " || trimmed == "opaque" then
      if !current.isEmpty then
        decls := decls ++ [current.trim]
      current := line
    else
      current := current ++ "\n" ++ line
  if !current.isEmpty then
    decls := decls ++ [current.trim]
  return decls.filter (fun s => !s.isEmpty)

/-- Recursively find all .red files in a directory -/
partial def findRedFiles (dir : String) : IO (List String) := do
  let mut files : List String := []
  try
    let entries ← System.FilePath.readDir dir
    for entry in entries do
      let path := entry.path.toString
      if ← System.FilePath.isDir entry.path then
        let subFiles ← findRedFiles path
        files := files ++ subFiles
      else if path.endsWith ".red" then
        files := files ++ [path]
  catch _ =>
    pure ()
  pure files

/-- Parse a single .red file declaration using Redtt grammar -/
def parseRedDecl (redttProds : List (String × GrammarExpr))
                 (tokenProds : List (String × GrammarExpr))
                 (keywords : List String)
                 (decl : String) : Bool :=
  let declProd := "File.topdecl"
  let tokens := if tokenProds.isEmpty then
    Lego.Bootstrap.tokenizeBootstrap decl
  else
    let mainProds := getMainTokenProdsOrdered tokenProds
    tokenizeWithGrammar redttFuel tokenProds mainProds decl keywords
  match redttProds.find? (·.1 == declProd) with
  | some (_, g) =>
    let st : ParseState := { tokens := tokens, binds := [] }
    let (result, _) := parseGrammar redttFuel redttProds g st
    match result with
    | some (_, st') => st'.tokens.isEmpty
    | none => false
  | none => false

/-- Parse a .red file and return (passed, total, list of failures) -/
def parseRedFileVerbose (redttProds : List (String × GrammarExpr))
                        (tokenProds : List (String × GrammarExpr))
                        (keywords : List String)
                        (path : String) : IO (Nat × Nat × List String) := do
  try
    let content ← IO.FS.readFile path
    let decls := splitRedDecls content
    let mut passed := 0
    let mut total := 0
    let mut failures : List String := []
    for decl in decls do
      total := total + 1
      if parseRedDecl redttProds tokenProds keywords decl then
        passed := passed + 1
      else
        let preview := if decl.length > 200 then decl.take 200 else decl
        let oneLine := preview.replace "\n" " "
        failures := failures ++ [oneLine]
    pure (passed, total, failures)
  catch _ =>
    pure (0, 0, [])

/-! ## RedValidation Tests -/

def redValidationTests : List TestResult :=
  -- Test scope checking
  let validTerm := Term.con "lam" [.var "x", .var "x"]  -- λx.x - valid
  let scopeErrs1 := checkScope ScopeCtx.empty validTerm
  let test1 := assertTrue "scope_valid_lam" scopeErrs1.isEmpty "λx.x should have no scope errors"

  -- Unbound variable
  let unboundTerm := Term.var "y"  -- y unbound
  let scopeErrs2 := checkScope ScopeCtx.empty unboundTerm
  let test2 := assertTrue "scope_unbound_var" (!scopeErrs2.isEmpty) "unbound y should have error"

  -- Test dimension binding
  let validCoe := Term.con "coe" [.con "dim0" [], .con "dim1" [], .var "A", .var "x"]
  let dimErrs1 := checkDimBindings ScopeCtx.empty validCoe
  let test3 := assertTrue "dim_valid_coe" dimErrs1.isEmpty "coe 0 1 A x should be valid"

  -- Dimension variable must be bound (dimension var directly in coe)
  let unboundDim := Term.con "coe" [.var "i", .con "dim1" [], .var "A", .var "x"]
  let ctx := ScopeCtx.empty  -- i not in scope
  let dimErrs2 := checkDimBindings ctx unboundDim
  let test4 := assertTrue "dim_unbound_dimvar" (!dimErrs2.isEmpty) "unbound dim i should error"

  -- With i in scope
  let ctxWithI := ctx.addDim "i"
  let dimErrs3 := checkDimBindings ctxWithI unboundDim
  let test5 := assertTrue "dim_bound_dimvar" dimErrs3.isEmpty "with i bound, coe i 1 A x should be valid"

  -- Test RedValidationResult
  let emptyResult := RedValidationResult.empty
  let test6 := assertTrue "empty_result_passed" emptyResult.passed "empty result should pass"

  let errResult : RedValidationResult := ⟨[.unboundVariable "x" "test"], []⟩
  let test7 := assertTrue "error_result_failed" (!errResult.passed) "result with error should fail"

  [test1, test2, test3, test4, test5, test6, test7]

/-! ## Redtt Library Parsing Tests -/

/-- Run tests on redtt library files if available -/
def runRedttParsingTests (rt : Runtime) : IO (List TestResult) := do
  -- Check for redtt library in common locations
  let possiblePaths := [
    "vendor/redtt/library",
    "../redtt/library"
  ]

  let mut redttPath : Option String := none
  for path in possiblePaths do
    if ← System.FilePath.pathExists path then
      redttPath := some path
      break

  -- Also try with HOME expansion
  if redttPath.isNone then
    if let some home ← IO.getEnv "HOME" then
      let homePath := home ++ "/redtt/library"
      if ← System.FilePath.pathExists homePath then
        redttPath := some homePath

  match redttPath with
  | none =>
    IO.println "  Redtt library not found in vendor/redtt/library or ~/redtt/library"
    IO.println "  To run parsing tests: git clone https://github.com/RedPRL/redtt vendor/redtt"
    return [assertTrue "redtt_library_skipped" true "Library not available"]
  | some libPath =>
    IO.println s!"  Found redtt library at: {libPath}"

    -- Load Redtt grammar
    let redttGrammarPath := "examples/Cubical/syntax/Redtt.lego"
    let grammarResult ← do
      try
        let content ← IO.FS.readFile redttGrammarPath
        pure (Runtime.parseLegoFile rt content)
      catch _ =>
        pure none

    match grammarResult with
    | none =>
      return [assertTrue "redtt_grammar_load" false "Redtt.lego failed to load"]
    | some redttAst =>
      let redttProds := Loader.extractAllProductions redttAst
      let tokenProds := Loader.extractTokenProductions redttAst
      let keywords := Loader.extractKeywords redttProds

      IO.println s!"  Loaded {redttProds.length} productions, {keywords.length} keywords"

      -- Find and parse all .red files
      let files ← findRedFiles libPath
      let sortedFiles := files.toArray.qsort (· < ·) |>.toList

      IO.println s!"  Found {sortedFiles.length} .red files"

      let mut totalParsed := 0
      let mut totalDecls := 0
      let mut failCount := 0

      for filePath in sortedFiles do
        let (passed, total, failures) ← parseRedFileVerbose redttProds tokenProds keywords filePath
        totalParsed := totalParsed + passed
        totalDecls := totalDecls + total
        for failure in failures do
          if failCount < 50 then
            IO.println s!"  FAIL [{filePath}]: {failure.take 120}..."
            failCount := failCount + 1

      let overallRate := if totalDecls > 0 then (totalParsed * 100) / totalDecls else 0
      let allPassed := overallRate >= 99  -- Allow 1% failures
      let checkMark := if allPassed then "✓" else "✗"
      let summaryTest := {
        name := "redtt_library"
        passed := allPassed
        message := s!"{checkMark} ({totalParsed}/{totalDecls} = {overallRate}%) across {sortedFiles.length} files"
      }

      pure [summaryTest]

/-! ## Test Runner -/

def printTestGroup (name : String) (tests : List TestResult) : IO (Nat × Nat) := do
  IO.println s!"\n── {name} ──"
  let mut passed := 0
  let mut failed := 0
  for test in tests do
    if test.passed then
      IO.println s!"  ✓ {test.name}"
      passed := passed + 1
    else
      IO.println s!"  ✗ {test.name}: {test.message}"
      failed := failed + 1
  pure (passed, failed)

def main (args : List String) : IO Unit := do
  IO.println "╔═══════════════════════════════════════════════════════════════╗"
  IO.println "║            Red Tests for Lego (Cubical Type Theory)           ║"
  IO.println "╚═══════════════════════════════════════════════════════════════╝"

  -- Parse arguments
  let runAll := args.contains "--all" || args.contains "-a"
  let runRedtt := args.contains "--redtt" || args.contains "-r" || runAll

  -- CRITICAL: Initialize runtime by loading Bootstrap.lego FIRST
  let rt ← Runtime.init

  let mut totalPassed := 0
  let mut totalFailed := 0

  -- RedValidation unit tests (always run)
  let (p, f) ← printTestGroup "RedValidation Unit Tests" redValidationTests
  totalPassed := totalPassed + p; totalFailed := totalFailed + f

  -- Redtt library parsing tests (optional)
  if runRedtt then
    let redttTests ← runRedttParsingTests rt
    let (p, f) ← printTestGroup "Redtt Library Parsing Tests" redttTests
    totalPassed := totalPassed + p; totalFailed := totalFailed + f
  else
    IO.println "\n── Redtt Library Parsing Tests (skipped, use --all or --redtt) ──"

  IO.println ""
  IO.println "═══════════════════════════════════════════════════════════════"
  IO.println s!"Total: {totalPassed + totalFailed} tests, {totalPassed} passed, {totalFailed} failed"
  if totalFailed == 0 then
    IO.println "All tests passed! ✓"
  else
    IO.println s!"FAILED: {totalFailed} tests"
    IO.Process.exit 1
