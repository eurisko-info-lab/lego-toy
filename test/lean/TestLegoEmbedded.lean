/-
  TestLegoEmbedded: Run tests embedded in .lego files

  This executable parses Cubical/Lego/*.lego files and runs their
  embedded test declarations against the Core evaluation engine.
-/

import Lego
import Lego.Runtime
import Cubical.Core
import Cubical.TestRunner

open Lego
open Lego.Runtime
open Cubical.TestRunner

/-- Parse a .lego file and return its AST using the runtime -/
def parseLegoFile (rt : Runtime) (path : String) : IO (Option Term) := do
  parseLegoFilePath rt path

/-- List of Cubical .lego files to test (ordered by dependency) -/
def cubicalLegoFiles : List String := [
  "examples/Cubical/Lego/Core.lego",
  "examples/Cubical/Lego/Cofibration.lego",
  "examples/Cubical/Lego/Domain.lego",  -- Domain before Kan (has dimEqD rules)
  "examples/Cubical/Lego/Kan.lego",
  "examples/Cubical/Lego/Quote.lego",
  "examples/Cubical/Lego/TermBuilder.lego"
]

/-- Main: run all embedded tests -/
def main (args : List String) : IO UInt32 := do
  let verbose := args.contains "-v" || args.contains "--verbose"

  IO.println "Cubical .lego Embedded Tests"
  IO.println "============================\n"

  -- First, load the bootstrap to get the runtime
  IO.println "Loading bootstrap grammar..."
  match ← loadBootstrap "./test/lego/Bootstrap.lego" with
  | Except.error e =>
    IO.println s!"Failed to load bootstrap: {e}"
    return 1
  | Except.ok rt =>
    IO.println s!"✓ Loaded runtime with {rt.grammar.productions.length} productions"

    -- First pass: parse all files and collect all rules
    let mut allAsts : List (String × Term) := []
    let mut allRules : List Lego.Rule := []

    for path in cubicalLegoFiles do
      match ← parseLegoFile rt path with
      | some ast =>
        allAsts := allAsts ++ [(path, ast)]
        let rules := Lego.Loader.extractRules ast
        allRules := allRules ++ rules
      | none =>
        IO.println s!"{path}: Failed to parse"

    IO.println s!"✓ Loaded {allRules.length} rules from {allAsts.length} files\n"

    -- Second pass: run tests with combined rules
    let mut totalPassed : Nat := 0
    let mut totalFailed : Nat := 0
    let mut totalSkipped : Nat := 0

    for (path, ast) in allAsts do
      let (p, f, s) ← runFileTestsWithRules ast allRules path verbose
      totalPassed := totalPassed + p
      totalFailed := totalFailed + f
      totalSkipped := totalSkipped + s

    printSummary totalPassed totalFailed totalSkipped

    if totalFailed > 0 then
      return 1
    else
      return 0
