/-
  TestAll: Unified test runner for all Lego test suites

  Run with: lake exe lego-test-all [options]

  Options:
    --quick     Run only quick tests (skip pipeline/cubical)
    --verbose   Show all test output
    --help      Show this help

  This runs all registered test suites and provides a unified summary.
-/

import Lego
import TestUtils

open Lego.Test

/-! ## Test Suite Configuration -/

structure TestSuite where
  name : String
  command : String
  isQuick : Bool  -- Can be skipped with --quick
  deriving Repr

def allSuites : List TestSuite := [
  { name := "Core Library", command := "lego-test", isQuick := true },
  { name := "Grammar Interpreter", command := "lego-test-grammar", isQuick := true },
  { name := "Composition", command := "lego-test-compose", isQuick := true },
  { name := "Code Generation", command := "lego-test-codegen-compare", isQuick := true },
  { name := "Pipeline Integration", command := "lego-test-pipeline", isQuick := false }
]

/-! ## Command Line Parsing -/

structure TestConfig where
  quick : Bool := false
  verbose : Bool := false
  showHelp : Bool := false
  deriving Repr

def parseArgs (args : List String) : TestConfig :=
  let rec go (cfg : TestConfig) : List String → TestConfig
    | [] => cfg
    | "--quick" :: rest => go { cfg with quick := true } rest
    | "-q" :: rest => go { cfg with quick := true } rest
    | "--verbose" :: rest => go { cfg with verbose := true } rest
    | "-v" :: rest => go { cfg with verbose := true } rest
    | "--help" :: rest => go { cfg with showHelp := true } rest
    | "-h" :: rest => go { cfg with showHelp := true } rest
    | _ :: rest => go cfg rest
  go {} args

def showHelp : IO Unit := do
  IO.println "Usage: lake exe lego-test-all [options]"
  IO.println ""
  IO.println "Run all Lego test suites and provide a unified summary."
  IO.println ""
  IO.println "Options:"
  IO.println "  --quick, -q   Run only quick tests (skip pipeline/cubical)"
  IO.println "  --verbose, -v Show all test output"
  IO.println "  --help, -h    Show this help message"
  IO.println ""
  IO.println "Test Suites:"
  for suite in allSuites do
    let quickMark := if suite.isQuick then "" else " (slow)"
    IO.println s!"  {suite.name}{quickMark}"

/-! ## Test Execution -/

/-- Parse test output to extract pass/fail counts -/
def parseTestOutput (output : String) : Option (Nat × Nat) := do
  -- Look for "Total: N tests, M passed, K failed"
  let lines := output.splitOn "\n"
  for line in lines do
    if line.containsSubstr "Total:" && line.containsSubstr "passed" then
      -- Extract numbers using simple parsing
      let parts := line.splitOn ","
      for part in parts do
        if part.containsSubstr "passed" then
          let numStr := part.trim.takeWhile (·.isDigit)
          if let some passed := numStr.toNat? then
            -- Find failed count
            for p2 in parts do
              if p2.containsSubstr "failed" then
                let failStr := p2.trim.takeWhile (·.isDigit)
                if let some failed := failStr.toNat? then
                  return (passed, failed)
  none

/-- Run a single test suite and return results -/
def runSuite (suite : TestSuite) (verbose : Bool) : IO (String × Nat × Nat × Bool) := do
  let result ← IO.Process.output {
    cmd := "lake"
    args := #["exe", suite.command]
  }

  let output := result.stdout ++ result.stderr
  let success := result.exitCode == 0

  if verbose then
    IO.println output

  match parseTestOutput output with
  | some (passed, failed) => return (suite.name, passed, failed, success)
  | none =>
    -- Couldn't parse, assume success if exit code 0
    if success then
      return (suite.name, 1, 0, true)
    else
      return (suite.name, 0, 1, false)

/-! ## Main -/

def main (args : List String) : IO UInt32 := do
  let cfg := parseArgs args

  if cfg.showHelp then
    showHelp
    return 0

  IO.println "╔═══════════════════════════════════════════════════════════════╗"
  IO.println "║                   Lego Unified Test Runner                    ║"
  IO.println "╚═══════════════════════════════════════════════════════════════╝"
  IO.println ""

  let suitesToRun := if cfg.quick then
    allSuites.filter (·.isQuick)
  else
    allSuites

  if cfg.quick then
    IO.println s!"Running {suitesToRun.length} quick test suites (use --verbose for details)"
  else
    IO.println s!"Running {suitesToRun.length} test suites (use --verbose for details)"
  IO.println ""

  let mut totalPassed := 0
  let mut totalFailed := 0
  let mut results : List (String × Nat × Nat × Bool) := []

  for suite in suitesToRun do
    IO.print s!"  {suite.name}... "
    IO.FS.Stream.flush (← IO.getStdout)
    let (name, passed, failed, success) ← runSuite suite cfg.verbose
    results := results ++ [(name, passed, failed, success)]
    totalPassed := totalPassed + passed
    totalFailed := totalFailed + failed

    let statusIcon := if success && failed == 0 then "✓" else if success then "⚠" else "✗"
    IO.println s!"{statusIcon} {passed}/{passed + failed}"

  IO.println ""
  IO.println "═══════════════════════════════════════════════════════════════"
  IO.println "                          Summary"
  IO.println "═══════════════════════════════════════════════════════════════"
  IO.println ""

  for (name, passed, failed, _) in results do
    let status := if failed == 0 then "✓ PASS" else s!"⚠ {failed} FAIL"
    let paddedName := name ++ String.mk (List.replicate (30 - name.length) ' ')
    IO.println s!"  {paddedName} {passed}/{passed + failed} {status}"

  IO.println ""
  IO.println "───────────────────────────────────────────────────────────────"
  IO.println s!"  Total: {totalPassed + totalFailed} tests, {totalPassed} passed, {totalFailed} failed"

  if totalFailed == 0 then
    IO.println ""
    IO.println "  🎉 All tests passed!"
    return 0
  else
    IO.println ""
    IO.println s!"  ⚠️  {totalFailed} tests failed"
    return 1
