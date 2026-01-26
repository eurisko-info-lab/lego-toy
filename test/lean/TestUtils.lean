/-
  TestUtils: Shared test framework utilities for Lego tests

  This module provides common test infrastructure to avoid duplication
  across test files. All test files should import this module.
-/

namespace Lego.Test

/-! ## Test Result Types -/

/-- Result of a single test -/
structure TestResult where
  name : String
  passed : Bool
  message : String := ""
  category : String := "default"
  deriving Repr

/-- Summary of a test group -/
structure TestGroupSummary where
  name : String
  passed : Nat
  failed : Nat
  total : Nat
  deriving Repr

/-! ## Assertion Functions -/

/-- Assert that a condition is true -/
def assertTrue (name : String) (cond : Bool) (category := "default") : TestResult :=
  { name := name
    passed := cond
    message := if cond then "✓" else "✗ expected true, got false"
    category := category }

/-- Assert that a condition is false -/
def assertFalse (name : String) (cond : Bool) (category := "default") : TestResult :=
  { name := name
    passed := !cond
    message := if !cond then "✓" else "✗ expected false, got true"
    category := category }

/-- Assert equality between two values -/
def assertEq [BEq α] [Repr α] (name : String) (actual expected : α) (category := "default") : TestResult :=
  let passed := actual == expected
  { name := name
    passed := passed
    message := if passed then "✓" else s!"✗ expected {repr expected}, got {repr actual}"
    category := category }

/-- Assert that two values are not equal -/
def assertNe [BEq α] [Repr α] (name : String) (actual notExpected : α) (category := "default") : TestResult :=
  let passed := actual != notExpected
  { name := name
    passed := passed
    message := if passed then "✓" else s!"✗ expected value different from {repr notExpected}"
    category := category }

/-- Assert that an Option is Some -/
def assertSome (name : String) (opt : Option α) (category := "default") : TestResult :=
  { name := name
    passed := opt.isSome
    message := if opt.isSome then "✓" else "✗ expected Some, got None"
    category := category }

/-- Assert that an Option is None -/
def assertNone (name : String) (opt : Option α) (category := "default") : TestResult :=
  { name := name
    passed := opt.isNone
    message := if opt.isNone then "✓" else "✗ expected None, got Some"
    category := category }

/-- Assert that a list is not empty -/
def assertNotEmpty (name : String) (list : List α) (category := "default") : TestResult :=
  { name := name
    passed := !list.isEmpty
    message := if !list.isEmpty then "✓" else "✗ expected non-empty list"
    category := category }

/-- Assert that a list is empty -/
def assertEmpty (name : String) (list : List α) (category := "default") : TestResult :=
  { name := name
    passed := list.isEmpty
    message := if list.isEmpty then "✓" else s!"✗ expected empty list, got {list.length} elements"
    category := category }

/-- Assert that a string contains a substring -/
def assertContains (name : String) (s sub : String) (category := "default") : TestResult :=
  let contains := (s.splitOn sub).length > 1
  { name := name
    passed := contains
    message := if contains then "✓" else s!"✗ expected string to contain '{sub}'"
    category := category }

/-- Assert that a string does not contain a substring -/
def assertNotContains (name : String) (s sub : String) (category := "default") : TestResult :=
  let contains := (s.splitOn sub).length > 1
  { name := name
    passed := !contains
    message := if !contains then "✓" else s!"✗ expected string to NOT contain '{sub}'"
    category := category }

/-- Assert that a value is greater than another -/
def assertGt [Ord α] [Repr α] (name : String) (actual threshold : α) (category := "default") : TestResult :=
  let passed := compare actual threshold == .gt
  { name := name
    passed := passed
    message := if passed then "✓" else s!"✗ expected {repr actual} > {repr threshold}"
    category := category }

/-- Assert that a value is greater than or equal to another -/
def assertGe [Ord α] [Repr α] (name : String) (actual threshold : α) (category := "default") : TestResult :=
  let passed := compare actual threshold != .lt
  { name := name
    passed := passed
    message := if passed then "✓" else s!"✗ expected {repr actual} >= {repr threshold}"
    category := category }

/-- Assert that a value is less than another -/
def assertLt [Ord α] [Repr α] (name : String) (actual threshold : α) (category := "default") : TestResult :=
  let passed := compare actual threshold == .lt
  { name := name
    passed := passed
    message := if passed then "✓" else s!"✗ expected {repr actual} < {repr threshold}"
    category := category }

/-- Assert that a Result is Ok -/
def assertOk (name : String) (result : Except ε α) (category := "default") : TestResult :=
  { name := name
    passed := result.isOk
    message := match result with
      | .ok _ => "✓"
      | .error _ => "✗ expected Ok, got Error"
    category := category }

/-- Assert that a Result is Error -/
def assertError (name : String) (result : Except ε α) (category := "default") : TestResult :=
  { name := name
    passed := !result.isOk
    message := match result with
      | .error _ => "✓"
      | .ok _ => "✗ expected Error, got Ok"
    category := category }

/-! ## String Utilities -/

/-- Check if string contains substring (not in Lean stdlib) -/
def String.containsSubstr (s sub : String) : Bool :=
  (s.splitOn sub).length > 1

/-! ## Test Running Infrastructure -/

/-- Print a test group and return (passed, failed) counts -/
def printTestGroup (name : String) (tests : List TestResult) : IO (Nat × Nat) := do
  IO.println s!"\n── {name} ──"
  let mut passed := 0
  let mut failed := 0
  for t in tests do
    IO.println s!"  {t.message} {t.name}"
    if t.passed then passed := passed + 1 else failed := failed + 1
  pure (passed, failed)

/-- Print a test group with counts in name -/
def printTestGroupWithCount (name : String) (tests : List TestResult) : IO (Nat × Nat) := do
  let passedCount := tests.filter (·.passed) |>.length
  let totalCount := tests.length
  IO.println s!"\n── {name} ({passedCount}/{totalCount}) ──"
  let mut passed := 0
  let mut failed := 0
  for t in tests do
    IO.println s!"  {t.message} {t.name}"
    if t.passed then passed := passed + 1 else failed := failed + 1
  pure (passed, failed)

/-- Run all test groups and print summary -/
def runAllTests (suiteName : String) (groups : List (String × List TestResult)) : IO UInt32 := do
  IO.println "═══════════════════════════════════════════════════════════════"
  IO.println s!"  {suiteName}"
  IO.println "═══════════════════════════════════════════════════════════════"

  let mut totalPassed := 0
  let mut totalFailed := 0

  for (name, tests) in groups do
    let (p, f) ← printTestGroup name tests
    totalPassed := totalPassed + p
    totalFailed := totalFailed + f

  IO.println ""
  IO.println "═══════════════════════════════════════════════════════════════"
  IO.println s!"Total: {totalPassed + totalFailed} tests, {totalPassed} passed, {totalFailed} failed"

  if totalFailed == 0 then
    IO.println "All tests passed! ✓"
    return 0
  else
    IO.println s!"FAILED: {totalFailed} tests"
    return 1

/-- Run IO tests and collect results -/
def runIOTests (tests : List (IO TestResult)) : IO (List TestResult) := do
  let mut results := []
  for test in tests do
    let result ← test
    results := results ++ [result]
  return results

/-- Create a test that runs an IO action and checks for success -/
def ioTest (name : String) (action : IO Bool) (category := "default") : IO TestResult := do
  let passed ← action
  return { name := name, passed := passed, message := if passed then "✓" else "✗", category := category }

/-- Create a test that checks if an IO action succeeds without exception -/
def ioSucceeds (name : String) (action : IO α) (category := "default") : IO TestResult := do
  try
    let _ ← action
    return { name := name, passed := true, message := "✓", category := category }
  catch e =>
    return { name := name, passed := false, message := s!"✗ exception: {e}", category := category }

/-- Create a test that checks if an IO action throws an exception -/
def ioFails (name : String) (action : IO α) (category := "default") : IO TestResult := do
  try
    let _ ← action
    return { name := name, passed := false, message := "✗ expected exception, but succeeded", category := category }
  catch _ =>
    return { name := name, passed := true, message := "✓", category := category }

/-! ## Test Filtering -/

/-- Test category filter -/
inductive TestFilter
  | all
  | category (name : String)
  | names (names : List String)

/-- Filter tests by category or name -/
def filterTests (filter : TestFilter) (tests : List TestResult) : List TestResult :=
  match filter with
  | .all => tests
  | .category name => tests.filter (·.category == name)
  | .names names => tests.filter (fun t => names.contains t.name)

/-! ## Performance Utilities -/

/-- Time an IO action and return (result, milliseconds) -/
def timeIO (action : IO α) : IO (α × Nat) := do
  let start ← IO.monoMsNow
  let result ← action
  let elapsed := (← IO.monoMsNow) - start
  return (result, elapsed)

/-- Create a benchmark test -/
def benchmark (name : String) (action : IO Unit) (maxMs : Nat) (category := "benchmark") : IO TestResult := do
  let (_, elapsed) ← timeIO action
  let passed := elapsed ≤ maxMs
  return {
    name := name
    passed := passed
    message := if passed then s!"✓ ({elapsed}ms)" else s!"✗ took {elapsed}ms, expected ≤{maxMs}ms"
    category := category
  }

end Lego.Test
