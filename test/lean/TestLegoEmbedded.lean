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

/-- List of Cubical .lego files to test -/
def cubicalLegoFiles : List String := [
  "examples/Cubical/Lego/Core.lego"
  -- Add more files as needed
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
    IO.println s!"✓ Loaded runtime with {rt.grammar.productions.length} productions\n"

    let mut totalPassed : Nat := 0
    let mut totalFailed : Nat := 0
    let mut totalSkipped : Nat := 0

    for path in cubicalLegoFiles do
      match ← parseLegoFile rt path with
      | some ast =>
        let (p, f, s) ← runFileTests ast path verbose
        totalPassed := totalPassed + p
        totalFailed := totalFailed + f
        totalSkipped := totalSkipped + s
      | none =>
        IO.println s!"{path}: Failed to parse"

    printSummary totalPassed totalFailed totalSkipped

    if totalFailed > 0 then
      return 1
    else
      return 0
