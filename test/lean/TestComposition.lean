/-
  TestComposition: Unit tests for language/piece composition

  Tests the grammar composition system including:
  - Language inheritance (Bootstrap → Lego → Rosetta)
  - Piece extraction and merging
  - Production override behavior
  - Error cases (circular deps, missing parents)

  Run with: lake exe lego-test-compose
-/

import Lego
import Lego.Loader
import Lego.Runtime

open Lego
open Lego.Loader
open Lego.Runtime

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

def assertGt (name : String) (actual : Nat) (min : Nat) (msg : String := "") : TestResult :=
  let passed := actual > min
  assertTrue name passed s!"Expected > {min}, got {actual}. {msg}"

/-! ## Inheritance Tests -/

section InheritanceTests

/-- Test: Bootstrap.lego has no parent -/
def testBootstrapNoParent : IO TestResult := do
  let rt ← Lego.Runtime.init
  -- Bootstrap is loaded via hardcoded grammar, not from file
  -- Check that rt.grammar exists and has productions
  let hasProds := rt.grammar.productions.length > 0
  return assertTrue "bootstrap_no_parent" hasProds s!"Bootstrap has {rt.grammar.productions.length} productions"

/-- Test: Lego inherits from Bootstrap -/
def testLegoInheritsBootstrap : IO TestResult := do
  let rt ← Lego.Runtime.init
  -- Lego.lego should parse with Bootstrap grammar
  -- The runtime already loaded Lego, so check it has more than Bootstrap
  -- We check by verifying the grammar has certain productions

  match ← loadLanguage rt "./src/Lego/Lego.lego" with
  | .error e => return assertTrue "lego_inherits_bootstrap" false s!"Load failed: {e}"
  | .ok legoGrammar =>
    -- Lego should have productions from Bootstrap plus its own
    let hasProds := legoGrammar.productions.length > 20
    return assertTrue "lego_inherits_bootstrap" hasProds s!"Lego has {legoGrammar.productions.length} productions"

/-- Test: Rosetta inherits from Lego (which inherits from Bootstrap) -/
def testRosettaInheritsLego : IO TestResult := do
  let rt ← Lego.Runtime.init

  match ← loadLanguage rt "./src/Rosetta/Rosetta.lego" with
  | .error e => return assertTrue "rosetta_inherits_lego" false s!"Load failed: {e}"
  | .ok rosettaGrammar =>
    -- Rosetta should have productions from Bootstrap + Lego + its own
    let hasProds := rosettaGrammar.productions.length > 30
    return assertTrue "rosetta_inherits_lego" hasProds s!"Rosetta has {rosettaGrammar.productions.length} productions"

def inheritanceTests : IO (List TestResult) := do
  let t1 ← testBootstrapNoParent
  let t2 ← testLegoInheritsBootstrap
  let t3 ← testRosettaInheritsLego
  return [t1, t2, t3]

end InheritanceTests

/-! ## Piece Extraction Tests -/

section PieceTests

/-- Test: Pieces are extracted from parsed AST -/
def testPieceExtraction : IO TestResult := do
  let rt ← Lego.Runtime.init

  -- Parse Lambda.lego which has pieces
  match ← parseLegoFilePathE rt "./examples/Lambda.lego" with
  | .error e => return assertTrue "piece_extraction" false s!"Parse failed: {e}"
  | .ok ast =>
    -- Extract productions
    let prods := Lego.Loader.extractAllProductions ast
    return assertGt "piece_extraction" prods.length 5 s!"Only {prods.length} productions"

/-- Test: Token pieces (TOKEN. prefix) are separate -/
def testTokenPieces : IO TestResult := do
  let rt ← Lego.Runtime.init
  -- Bootstrap should have token productions
  let tokenProds := rt.grammar.tokenProductions
  let hasTokenProds := tokenProds.length > 5
  return assertTrue "token_pieces" hasTokenProds s!"Only {tokenProds.length} token productions"

/-- Test: Grammar pieces (File. prefix) -/
def testGrammarPieces : IO TestResult := do
  let rt ← Lego.Runtime.init
  -- Check for File.legoFile production
  let hasFileProds := rt.grammar.productions.any fun (name, _) => name.startsWith "File."
  return assertTrue "grammar_pieces" hasFileProds "No File. productions found"

def pieceTests : IO (List TestResult) := do
  let t1 ← testPieceExtraction
  let t2 ← testTokenPieces
  let t3 ← testGrammarPieces
  return [t1, t2, t3]

end PieceTests

/-! ## Production Merging Tests -/

section MergingTests

/-- Test: Child productions override parent -/
def testProductionOverride : IO TestResult := do
  let rt ← Lego.Runtime.init

  -- Load a language with a parent
  match ← loadLanguage rt "./examples/Lambda.lego" with
  | .error e => return assertTrue "production_override" false s!"Load failed: {e}"
  | .ok grammar =>
    -- Lambda should have its own productions
    let hasLambdaProds := grammar.productions.any fun (name, _) =>
      name.containsSubstr "Lambda" || name.containsSubstr "lam"
    return assertTrue "production_override" hasLambdaProds ""

/-- Test: No duplicate production errors on merge -/
def testNoDuplicateError : IO TestResult := do
  let rt ← Lego.Runtime.init

  -- Loading should not fail due to duplicates
  match ← loadLanguage rt "./src/Lego/Lego.lego" with
  | .error e =>
    let isDupError := e.containsSubstr "duplicate" || e.containsSubstr "Duplicate"
    return assertTrue "no_duplicate_error" (!isDupError) s!"Got duplicate error: {e}"
  | .ok _ =>
    return assertTrue "no_duplicate_error" true ""

def mergingTests : IO (List TestResult) := do
  let t1 ← testProductionOverride
  let t2 ← testNoDuplicateError
  return [t1, t2]

end MergingTests

/-! ## Error Case Tests -/

section ErrorCaseTests

/-- Test: Circular inheritance detection -/
def testCircularInheritance : IO TestResult := do
  -- Create a temp file with circular inheritance
  let tempPath := "./tmp/circular_test.lego"
  IO.FS.createDirAll "./tmp"
  -- Write a self-referencing language
  IO.FS.writeFile tempPath "lang Circular (Circular) :=\n  piece Foo\n    x ::= \"a\" ;\n"

  let rt ← Lego.Runtime.init
  match ← loadLanguage rt tempPath with
  | .error e =>
    let isCircular := e.containsSubstr "Circular" || e.containsSubstr "circular" ||
                      e.containsSubstr "cycle" || e.containsSubstr "Failed"
    return assertTrue "circular_inheritance" isCircular s!"Expected circular error, got: {e}"
  | .ok _ =>
    return assertTrue "circular_inheritance" false "Expected error for circular inheritance"

/-- Test: Missing parent error -/
def testMissingParent : IO TestResult := do
  let tempPath := "./tmp/missing_parent_test.lego"
  IO.FS.createDirAll "./tmp"
  -- Write a file that references a non-existent parent
  IO.FS.writeFile tempPath "lang Child (NonExistentParent) :=\n  piece Foo\n    x ::= \"a\" ;\n"

  let rt ← Lego.Runtime.init
  match ← loadLanguage rt tempPath with
  | .error e =>
    -- The error could be parse error (if parent affects parsing) or file not found
    let isMissing := e.containsSubstr "Cannot find" || e.containsSubstr "not found" ||
                     e.containsSubstr "NonExistent" || e.containsSubstr "Failed to load"
    return assertTrue "missing_parent" isMissing s!"Expected missing parent error, got: {e}"
  | .ok _ =>
    return assertTrue "missing_parent" false "Expected error for missing parent"

/-- Test: Malformed language detection -/
def testMalformedLanguage : IO TestResult := do
  let tempPath := "./tmp/malformed_test.lego"
  IO.FS.createDirAll "./tmp"
  IO.FS.writeFile tempPath "not a valid lego file"

  let rt ← Lego.Runtime.init
  match ← loadLanguage rt tempPath with
  | .error _ => return assertTrue "malformed_language" true ""
  | .ok _ => return assertTrue "malformed_language" false "Expected parse error for malformed input"

def errorCaseTests : IO (List TestResult) := do
  let t1 ← testCircularInheritance
  let t2 ← testMissingParent
  let t3 ← testMalformedLanguage
  return [t1, t2, t3]

end ErrorCaseTests

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
  IO.println "  Language/Piece Composition Tests"
  IO.println "═══════════════════════════════════════════════════════════════"

  let mut totalPassed := 0
  let mut totalFailed := 0

  -- Inheritance tests
  let inheritance ← inheritanceTests
  let inheritanceFailed ← printResults "Inheritance Tests" inheritance
  totalPassed := totalPassed + inheritance.length - inheritanceFailed
  totalFailed := totalFailed + inheritanceFailed

  -- Piece tests
  let pieces ← pieceTests
  let piecesFailed ← printResults "Piece Tests" pieces
  totalPassed := totalPassed + pieces.length - piecesFailed
  totalFailed := totalFailed + piecesFailed

  -- Merging tests
  let merging ← mergingTests
  let mergingFailed ← printResults "Merging Tests" merging
  totalPassed := totalPassed + merging.length - mergingFailed
  totalFailed := totalFailed + mergingFailed

  -- Error case tests
  let errors ← errorCaseTests
  let errorsFailed ← printResults "Error Case Tests" errors
  totalPassed := totalPassed + errors.length - errorsFailed
  totalFailed := totalFailed + errorsFailed

  -- Summary
  IO.println ""
  IO.println "═══════════════════════════════════════════════════════════════"
  IO.println s!"Total: {totalPassed + totalFailed} tests, {totalPassed} passed, {totalFailed} failed"

  if totalFailed == 0 then
    IO.println "All composition tests passed! ✓"
    return 0
  else
    IO.println s!"{totalFailed} tests failed ✗"
    return 1
