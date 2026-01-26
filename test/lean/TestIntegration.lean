/-
  TestIntegration: Integration tests for the full Lego pipeline

  Tests parsing and printing of all .lego, .rosetta, and target language files.
  Verifies the bootstrap chain and roundtrip invariants.

  Run with: lake exe lego-test-pipeline
-/

import Lego
import Lego.Loader
import Lego.Runtime

open Lego
open Lego.Loader
open Lego.Runtime
open System

/-! ## Test Framework -/

/-- Check if a string contains a substring -/
def String.containsSubstr (s sub : String) : Bool :=
  (s.splitOn sub).length > 1

structure TestResult where
  name : String
  passed : Bool
  message : String := ""
  deriving Repr

def assertTrue (name : String) (cond : Bool) (msg : String := "") : TestResult :=
  { name := name
    passed := cond
    message := if cond then "✓" else s!"✗ {msg}" }

/-! ## File Discovery -/

/-- Find all files with given extension in directory recursively -/
partial def findFilesWithExt (dir : FilePath) (ext : String) : IO (List FilePath) := do
  let mut result : List FilePath := []
  if ← dir.pathExists then
    let entries ← dir.readDir
    for entry in entries do
      if ← entry.path.isDir then
        let subFiles ← findFilesWithExt entry.path ext
        result := result ++ subFiles
      else if entry.path.extension == some ext then
        result := result ++ [entry.path]
  return result

/-! ## Bootstrap Chain Tests -/

section BootstrapChain

/-- Test: Hardcoded grammar parses Bootstrap.lego -/
def testHardcodedParsesBootstrap : IO TestResult := do
  -- Read Bootstrap.lego
  let content ← IO.FS.readFile "./test/lego/Bootstrap.lego"

  -- Parse with hardcoded grammar
  match Lego.Bootstrap.parseLegoFile content with
  | none => return assertTrue "hardcoded_bootstrap_parse" false "Parse failed"
  | some ast =>
    return assertTrue "hardcoded_bootstrap_parse" (ast.toString.length > 100) ""

/-- Test: Bootstrap grammar parses Lego.lego -/
def testBootstrapParsesLego : IO TestResult := do
  let rt ← Lego.Runtime.init
  match ← parseLegoFilePathE rt "./src/Lego/Lego.lego" with
  | .error e => return assertTrue "bootstrap_lego_parse" false s!"Failed: {e}"
  | .ok ast =>
    return assertTrue "bootstrap_lego_parse" (ast.toString.length > 100) ""

/-- Test: Lego grammar parses all example files -/
def testLegoGrammarParsesExamples : IO (List TestResult) := do
  let rt ← Lego.Runtime.init
  let exampleFiles ← findFilesWithExt "examples" "lego"

  let mut results : List TestResult := []
  for file in exampleFiles do
    let name := s!"parse_{file.fileName.getD "unknown"}"
    match ← parseLegoFilePathE rt file.toString with
    | .error e =>
      results := results ++ [assertTrue name false s!"Parse failed: {(toString e).take 100}"]
    | .ok _ =>
      results := results ++ [assertTrue name true ""]

  return results

def bootstrapChainTests : IO (List TestResult) := do
  let t1 ← testHardcodedParsesBootstrap
  let t2 ← testBootstrapParsesLego
  let t3 ← testLegoGrammarParsesExamples
  return [t1, t2] ++ t3

end BootstrapChain

/-! ## .lego File Parsing Tests -/

section LegoFileParsing

/-- Parse all .lego files in the project -/
def testAllLegoFiles : IO (List TestResult) := do
  let rt ← Lego.Runtime.init

  -- Collect all .lego files
  let testFiles ← findFilesWithExt "test/lego" "lego"
  let srcFiles ← findFilesWithExt "src/Lego" "lego"
  let rosettaFiles ← findFilesWithExt "src/Rosetta" "lego"
  let exampleFiles ← findFilesWithExt "examples" "lego"

  let allFiles := testFiles ++ srcFiles ++ rosettaFiles ++ exampleFiles

  let mut results : List TestResult := []
  let mut passCount := 0
  let mut failCount := 0

  for file in allFiles do
    let shortName := file.fileName.getD file.toString
    match ← parseLegoFilePathE rt file.toString with
    | .error e =>
      results := results ++ [assertTrue shortName false s!"Parse failed: {(toString e).take 100}"]
      failCount := failCount + 1
    | .ok ast =>
      results := results ++ [assertTrue shortName (ast.toString.length > 0) ""]
      passCount := passCount + 1

  IO.println s!"  Parsed {passCount} .lego files, {failCount} failed"
  return results

end LegoFileParsing

/-! ## .rosetta File Parsing Tests -/

section RosettaFileParsing

/-- Parse all .rosetta files -/
def testAllRosettaFiles : IO (List TestResult) := do
  let rt ← Lego.Runtime.init

  -- Find all .rosetta files
  let files ← findFilesWithExt "src" "rosetta"

  let mut results : List TestResult := []

  for file in files do
    let shortName := file.fileName.getD file.toString
    let content ← IO.FS.readFile file.toString

    match Lego.Loader.parseWithGrammarE rt.rosettaGrammar content with
    | .error e =>
      results := results ++ [assertTrue shortName false s!"Parse failed: {(toString e).take 80}"]
    | .ok ast =>
      results := results ++ [assertTrue shortName (ast.toString.length > 0) ""]

  return results

end RosettaFileParsing

/-! ## Target Language Grammar Tests -/

section TargetLanguageTests

/-- Test that target language grammars load and have required pieces -/
def testTargetLanguageGrammars : IO (List TestResult) := do
  let rt ← Lego.Runtime.init

  let targets := [
    ("./src/Rosetta/Lean.lego", "Lean"),
    ("./src/Rosetta/Scala.lego", "Scala"),
    ("./src/Rosetta/Haskell.lego", "Haskell"),
    ("./src/Rosetta/Rust.lego", "Rust")
  ]

  let mut results : List TestResult := []

  for (path, name) in targets do
    match ← loadLanguage rt path with
    | .error e =>
      results := results ++ [assertTrue s!"{name}_grammar_load" false s!"Failed: {e.take 100}"]
    | .ok grammar =>
      -- Check it has productions
      let hasProds := grammar.productions.length > 20
      results := results ++ [assertTrue s!"{name}_has_productions" hasProds s!"Only {grammar.productions.length} productions"]

  return results

end TargetLanguageTests

/-! ## Roundtrip Tests -/

section RoundtripTests

/-- Test parse-print-parse roundtrip for a file -/
def testFileRoundtrip (rt : Runtime) (path : String) : IO TestResult := do
  let name := s!"roundtrip_{System.FilePath.mk path |>.fileName |>.getD "unknown"}"

  -- Parse original
  match ← parseLegoFilePathE rt path with
  | .error e => return assertTrue name false s!"Initial parse failed: {(toString e).take 100}"
  | .ok ast1 =>
    -- Print to tokens
    match Lego.Loader.printWithGrammar rt.grammar "File.legoFile" ast1 with
    | none => return assertTrue name false "Print failed"
    | some tokens =>
      -- Parse again
      let st : ParseState := { tokens := tokens, binds := [] }
      match parseGrammar defaultFuel rt.grammar.productions (.ref "File.legoFile") st with
      | (none, _) => return assertTrue name false "Reparse failed"
      | (some (term2, _), _) =>
        -- Compare ASTs (string comparison for now)
        let eq := ast1.toString == term2.toString
        return assertTrue name eq s!"ASTs differ"

/-- Test roundtrip for key files -/
def testRoundtripKeyFiles : IO (List TestResult) := do
  let rt ← Lego.Runtime.init

  let keyFiles := [
    "./test/lego/Bootstrap.lego",
    "./examples/Arith.lego",
    "./examples/Lambda.lego"
  ]

  let mut results : List TestResult := []
  for file in keyFiles do
    let result ← testFileRoundtrip rt file
    results := results ++ [result]

  return results

end RoundtripTests

/-! ## Cubical/Red File Tests -/

section CubicalTests

/-- Test parsing Cubical/Red files (larger, more complex) -/
def testCubicalFiles : IO (List TestResult) := do
  let rt ← Lego.Runtime.init

  -- Find Cubical .lego files
  let files ← findFilesWithExt "examples/Cubical" "lego"

  let mut results : List TestResult := []
  let mut passCount := 0

  for file in files.take 20 do  -- Limit to avoid long test time
    let shortName := file.fileName.getD "unknown"
    match ← parseLegoFilePathE rt file.toString with
    | .error e =>
      results := results ++ [assertTrue s!"cubical_{shortName}" false s!"{(toString e).take 80}"]
    | .ok _ast =>
      results := results ++ [assertTrue s!"cubical_{shortName}" true ""]
      passCount := passCount + 1

  IO.println s!"  Parsed {passCount}/{files.take 20 |>.length} Cubical files"
  return results

end CubicalTests

/-! ## Main Test Runner -/

def printResults (category : String) (results : List TestResult) : IO Nat := do
  IO.println s!"\n── {category} ──"
  let mut failed := 0
  for r in results do
    let symbol := if r.passed then "✓" else "✗"
    IO.println s!"  {symbol} {r.name}"
    if !r.passed && r.message.length > 0 then
      IO.println s!"    {r.message}"
    if !r.passed then failed := failed + 1
  return failed

def main : IO UInt32 := do
  IO.println "═══════════════════════════════════════════════════════════════"
  IO.println "  Integration Pipeline Tests"
  IO.println "═══════════════════════════════════════════════════════════════"

  let mut totalPassed := 0
  let mut totalFailed := 0

  -- Bootstrap chain
  let bootstrap ← bootstrapChainTests
  let bootstrapFailed ← printResults "Bootstrap Chain Tests" bootstrap
  totalPassed := totalPassed + bootstrap.length - bootstrapFailed
  totalFailed := totalFailed + bootstrapFailed

  -- .lego files
  IO.println "\n── .lego File Parsing ──"
  let legoFiles ← testAllLegoFiles
  let legoFailed := legoFiles.filter (!·.passed) |>.length
  totalPassed := totalPassed + legoFiles.length - legoFailed
  totalFailed := totalFailed + legoFailed
  IO.println s!"  {legoFiles.length - legoFailed} passed, {legoFailed} failed"

  -- .rosetta files
  let rosettaFiles ← testAllRosettaFiles
  let rosettaFailed ← printResults ".rosetta File Parsing" rosettaFiles
  totalPassed := totalPassed + rosettaFiles.length - rosettaFailed
  totalFailed := totalFailed + rosettaFailed

  -- Target language grammars
  let targetGrammars ← testTargetLanguageGrammars
  let targetFailed ← printResults "Target Language Grammars" targetGrammars
  totalPassed := totalPassed + targetGrammars.length - targetFailed
  totalFailed := totalFailed + targetFailed

  -- Roundtrip tests
  let roundtrip ← testRoundtripKeyFiles
  let roundtripFailed ← printResults "Roundtrip Tests" roundtrip
  totalPassed := totalPassed + roundtrip.length - roundtripFailed
  totalFailed := totalFailed + roundtripFailed

  -- Cubical tests
  IO.println "\n── Cubical/Red Files ──"
  let cubical ← testCubicalFiles
  let cubicalFailed := cubical.filter (!·.passed) |>.length
  totalPassed := totalPassed + cubical.length - cubicalFailed
  totalFailed := totalFailed + cubicalFailed

  -- Summary
  IO.println ""
  IO.println "═══════════════════════════════════════════════════════════════"
  IO.println s!"Total: {totalPassed + totalFailed} tests, {totalPassed} passed, {totalFailed} failed"

  if totalFailed == 0 then
    IO.println "All integration tests passed! ✓"
    return 0
  else
    IO.println s!"{totalFailed} tests failed ✗"
    return 1
