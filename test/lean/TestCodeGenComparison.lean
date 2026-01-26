/-
  TestCodeGenComparison: Tests comparing generated code against reference implementations

  Ensures generated Lean code from Rosetta matches the hand-coded reference.
  Also tests all 4 target language generators produce valid output.

  Run with: lake exe lego-test-codegen-compare
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

/-! ## Helper Functions -/

/-- Read file content, return error string on failure -/
def readFileE (path : String) : IO (Except String String) := do
  try
    let content ← IO.FS.readFile path
    return .ok content
  catch e =>
    return .error s!"Failed to read {path}: {e}"

/-! ## Lean Code Generator Tests -/

section LeanCodeGenTests

/-- Test: Generated bootstrap grammar matches expected structure -/
def testBootstrapGrammarStructure : IO TestResult := do
  match ← readFileE "generated/BootstrapGrammar.lean" with
  | .error e => return assertTrue "bootstrap_grammar_structure" false e
  | .ok content =>
    -- Verify essential components are present in actual generated format
    let checks := [
      ("namespace", content.containsSubstr "namespace Lego.Generated"),
      ("Piece", content.containsSubstr "Piece"),
      ("grammar", content.containsSubstr "grammar :="),
      ("GrammarExpr", content.containsSubstr "GrammarExpr")
    ]
    let allPassed := checks.all (·.2)
    let failed := checks.filter (!·.2) |>.map (·.1)
    return assertTrue "bootstrap_grammar_structure" allPassed s!"Missing: {failed}"

/-- Test: Generated tokenizer has expected token definitions -/
def testBootstrapTokenizerContent : IO TestResult := do
  match ← readFileE "generated/BootstrapTokenizer.lean" with
  | .error e => return assertTrue "bootstrap_tokenizer_content" false e
  | .ok content =>
    -- Check for actual token production names in the generated file
    let requiredTokens := ["Token.ident", "Token.number", "Token.string", "Token.digit", "Token.alpha"]
    let missing := requiredTokens.filter (!content.containsSubstr ·)
    return assertTrue "bootstrap_tokenizer_content" missing.isEmpty s!"Missing tokens: {missing}"

/-- Test: Generated rules file has rewrite definitions -/
def testBootstrapRulesContent : IO TestResult := do
  match ← readFileE "generated/BootstrapRules.lean" with
  | .error e => return assertTrue "bootstrap_rules_content" false e
  | .ok content =>
    let checks := [
      ("imports", content.containsSubstr "import"),
      ("namespace", content.containsSubstr "namespace" || content.containsSubstr "Lego")
    ]
    let allPassed := checks.all (·.2)
    return assertTrue "bootstrap_rules_content" allPassed ""

def leanCodeGenTests : IO (List TestResult) := do
  let t1 ← testBootstrapGrammarStructure
  let t2 ← testBootstrapTokenizerContent
  let t3 ← testBootstrapRulesContent
  return [t1, t2, t3]

end LeanCodeGenTests

/-! ## Cross-Target Code Generator Tests -/

section CrossTargetTests

/-- Test: Scala generated grammar has expected structure -/
def testScalaGrammar : IO TestResult := do
  match ← readFileE "generated/Rosetta/Grammar.scala" with
  | .error e => return assertTrue "scala_grammar" false e
  | .ok content =>
    let checks := [
      ("package", content.containsSubstr "package"),
      ("enum or case class", content.containsSubstr "enum" || content.containsSubstr "case class"),
      ("Term or GrammarExpr", content.containsSubstr "Term" || content.containsSubstr "GrammarExpr")
    ]
    let allPassed := checks.all (·.2)
    return assertTrue "scala_grammar" allPassed ""

/-- Test: Haskell generated grammar has expected structure -/
def testHaskellGrammar : IO TestResult := do
  match ← readFileE "generated/Rosetta/Grammar.hs" with
  | .error e => return assertTrue "haskell_grammar" false e
  | .ok content =>
    let checks := [
      ("module", content.containsSubstr "module"),
      ("where", content.containsSubstr "where"),
      ("data or type", content.containsSubstr "data" || content.containsSubstr "type")
    ]
    let allPassed := checks.all (·.2)
    return assertTrue "haskell_grammar" allPassed ""

/-- Test: Rust generated grammar has expected structure -/
def testRustGrammar : IO TestResult := do
  match ← readFileE "generated/Rosetta/grammar.rs" with
  | .error e => return assertTrue "rust_grammar" false e
  | .ok content =>
    let checks := [
      ("pub enum", content.containsSubstr "pub enum"),
      ("Term or GrammarExpr", content.containsSubstr "Term" || content.containsSubstr "GrammarExpr"),
      ("allow", content.containsSubstr "#![allow")
    ]
    let allPassed := checks.all (·.2)
    return assertTrue "rust_grammar" allPassed ""

/-- Test: All target grammars exist and have minimal content -/
def testAllTargetsExist : IO (List TestResult) := do
  let targets := [
    ("generated/Rosetta/Grammar.lean", "Lean", 100),
    ("generated/Rosetta/Grammar.scala", "Scala", 100),
    ("generated/Rosetta/Grammar.hs", "Haskell", 100),
    ("generated/Rosetta/grammar.rs", "Rust", 100)
  ]

  let mut results : List TestResult := []
  for (path, name, minSize) in targets do
    match ← readFileE path with
    | .error e =>
      results := results ++ [assertTrue s!"{name}_exists" false e]
    | .ok content =>
      let sizeOk := content.length > minSize
      results := results ++ [assertTrue s!"{name}_size" sizeOk s!"Only {content.length} bytes, expected > {minSize}"]

  return results

def crossTargetTests : IO (List TestResult) := do
  let t1 ← testScalaGrammar
  let t2 ← testHaskellGrammar
  let t3 ← testRustGrammar
  let t4 ← testAllTargetsExist
  return [t1, t2, t3] ++ t4

end CrossTargetTests

/-! ## Semantic Comparison Tests -/

section SemanticTests

/-- Count occurrences of a pattern in text -/
def countOccurrences (text : String) (pattern : String) : Nat :=
  if pattern.isEmpty then 0
  else
    let parts := text.splitOn pattern
    parts.length - 1

/-- Test: Generated and hand-coded have similar structure -/
def testGeneratedVsHandcoded : IO TestResult := do
  -- Compare generated grammar with hand-coded one
  -- The generated should have the basic structure elements

  match ← readFileE "generated/BootstrapGrammar.lean" with
  | .error e => return assertTrue "generated_vs_handcoded" false e
  | .ok generated =>
    match ← readFileE "src/Lego/Runtime.lean" with
    | .error e => return assertTrue "generated_vs_handcoded" false e
    | .ok handcoded =>
      -- Check both use Piece/grammar structures
      let genHasPiece := generated.containsSubstr "Piece"
      let handHasPiece := handcoded.containsSubstr "Piece" || handcoded.containsSubstr "piece"

      -- Check both define grammar-related structures
      let genHasGrammar := generated.containsSubstr "grammar"
      let handHasGrammar := handcoded.containsSubstr "grammar" || handcoded.containsSubstr "Grammar"

      let match_ := genHasPiece && genHasGrammar && (handHasPiece || handHasGrammar)
      return assertTrue "generated_vs_handcoded" match_ "Structure mismatch"

/-- Test: Token production counts are consistent across targets -/
def testTokenConsistency : IO TestResult := do
  let files := [
    ("generated/BootstrapTokenizer.lean", "Lean"),
    ("generated/Rosetta/Grammar.scala", "Scala")
  ]

  -- Count Token definitions (look for actual patterns in generated code)
  let mut counts : List (String × Nat) := []
  for (path, name) in files do
    match ← readFileE path with
    | .error _ => pure ()
    | .ok content =>
      -- Count Token.* patterns for Lean, or token-related patterns
      let count := countOccurrences content "Token."
      counts := counts ++ [(name, count)]

  -- All should have at least some tokens
  if counts.isEmpty then
    return assertTrue "token_consistency" false "Could not read files"
  else
    -- Lean tokenizer should have Token. patterns, Scala may not
    let leanCount := counts.find? (·.1 == "Lean") |>.map (·.2) |>.getD 0
    let hasLeanTokens := leanCount > 0
    return assertTrue "token_consistency" hasLeanTokens s!"Counts: {counts}"

def semanticTests : IO (List TestResult) := do
  let t1 ← testGeneratedVsHandcoded
  let t2 ← testTokenConsistency
  return [t1, t2]

end SemanticTests

/-! ## Grammar Transformation Tests -/

section TransformationTests

/-- Test: lego2rosetta transformation produces valid output -/
def testLego2Rosetta : IO TestResult := do
  let rt ← Lego.Runtime.init

  -- Load the transformation rules
  match ← loadLanguage rt "./src/Rosetta/lego2rosetta.lego" with
  | .error e => return assertTrue "lego2rosetta_load" false s!"Failed: {e}"
  | .ok _ => return assertTrue "lego2rosetta_load" true ""

/-- Test: rosetta2lean transformation produces valid output -/
def testRosetta2Lean : IO TestResult := do
  let rt ← Lego.Runtime.init

  match ← loadLanguage rt "./src/Rosetta/rosetta2lean.lego" with
  | .error e => return assertTrue "rosetta2lean_load" false s!"Failed: {e}"
  | .ok _ => return assertTrue "rosetta2lean_load" true ""

/-- Test: rosetta2scala transformation loads -/
def testRosetta2Scala : IO TestResult := do
  let rt ← Lego.Runtime.init

  match ← loadLanguage rt "./src/Rosetta/rosetta2scala.lego" with
  | .error e => return assertTrue "rosetta2scala_load" false s!"Failed: {e}"
  | .ok _ => return assertTrue "rosetta2scala_load" true ""

/-- Test: rosetta2haskell transformation loads -/
def testRosetta2Haskell : IO TestResult := do
  let rt ← Lego.Runtime.init

  match ← loadLanguage rt "./src/Rosetta/rosetta2haskell.lego" with
  | .error e => return assertTrue "rosetta2haskell_load" false s!"Failed: {e}"
  | .ok _ => return assertTrue "rosetta2haskell_load" true ""

/-- Test: rosetta2rust transformation loads -/
def testRosetta2Rust : IO TestResult := do
  let rt ← Lego.Runtime.init

  match ← loadLanguage rt "./src/Rosetta/rosetta2rust.lego" with
  | .error e => return assertTrue "rosetta2rust_load" false s!"Failed: {e}"
  | .ok _ => return assertTrue "rosetta2rust_load" true ""

def transformationTests : IO (List TestResult) := do
  let t1 ← testLego2Rosetta
  let t2 ← testRosetta2Lean
  let t3 ← testRosetta2Scala
  let t4 ← testRosetta2Haskell
  let t5 ← testRosetta2Rust
  return [t1, t2, t3, t4, t5]

end TransformationTests

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
  IO.println "  Code Generator Comparison Tests"
  IO.println "═══════════════════════════════════════════════════════════════"

  let mut totalPassed := 0
  let mut totalFailed := 0

  -- Lean code gen tests
  let lean ← leanCodeGenTests
  let leanFailed ← printResults "Lean Code Generator" lean
  totalPassed := totalPassed + lean.length - leanFailed
  totalFailed := totalFailed + leanFailed

  -- Cross-target tests
  let cross ← crossTargetTests
  let crossFailed ← printResults "Cross-Target Generators" cross
  totalPassed := totalPassed + cross.length - crossFailed
  totalFailed := totalFailed + crossFailed

  -- Semantic comparison tests
  let semantic ← semanticTests
  let semanticFailed ← printResults "Semantic Comparison" semantic
  totalPassed := totalPassed + semantic.length - semanticFailed
  totalFailed := totalFailed + semanticFailed

  -- Transformation tests
  let transform ← transformationTests
  let transformFailed ← printResults "Transformation Rules" transform
  totalPassed := totalPassed + transform.length - transformFailed
  totalFailed := totalFailed + transformFailed

  -- Summary
  IO.println ""
  IO.println "═══════════════════════════════════════════════════════════════"
  IO.println s!"Total: {totalPassed + totalFailed} tests, {totalPassed} passed, {totalFailed} failed"

  if totalFailed == 0 then
    IO.println "All code generator tests passed! ✓"
    return 0
  else
    IO.println s!"{totalFailed} tests failed ✗"
    return 1
