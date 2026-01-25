/-
  Test runner for Cubical Runtime tests

  Run with: lake env lean --run test/lean/TestCubicalRuntime.lean
-/

import Runtime.Cubical.Lean.Runtime

open Cubical.Runtime

def main : IO Unit := do
  runStandardTests

  -- Check all pass and exit with appropriate code
  let results := runTests emptyRules 1000 standardTests
  let (passed, failed) := countResults results

  if failed > 0 then
    IO.eprintln s!"FAIL: {failed} tests failed"
    IO.Process.exit 1
  else
    IO.println s!"SUCCESS: All {passed} tests passed!"
