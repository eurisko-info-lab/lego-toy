/-
  TestKnownFailures: Run only the known-failing tests

  These are tests that are expected to fail currently.
  Use this to check progress on fixing them.

  Run with: lake exe lego-test-known-failures
-/

import Lego
import Lego.Loader
import Lego.Runtime
import TestUtils

open Lego
open Lego.Loader
open Lego.Runtime
open Lego.Test
open System

/-! ## Known Failing Files -/

/-- List of .lego files that are known to fail parsing -/
def knownFailingLegoFiles : List String := [
  -- Examples that use advanced grammar features
  "ScrumTeam.lego",
  "Core4.lego",
  "RosettaMath.lego",
  "Cool.lego",
  "TypeTheoryFromMath.lego",
  "CoreCompact.lego",
  "CoreDerived.lego",
  "CubicalCompact.lego",
  "CubicalFoundation.lego",
  "CubicalTT-converted.lego",
  "CategoryTheory.lego",
  "cubical2rosetta.lego",
  "C12.lego",
  "Quantum.lego"
]

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

/-! ## Test Runner -/

def main : IO UInt32 := do
  IO.println "═══════════════════════════════════════════════════════════════"
  IO.println "  Known-Failing Tests (checking progress)"
  IO.println "═══════════════════════════════════════════════════════════════"
  IO.println ""
  IO.println s!"Testing {knownFailingLegoFiles.length} known-failing files..."
  IO.println ""

  let rt ← Lego.Runtime.initQuiet

  -- Collect all .lego files
  let testFiles ← findFilesWithExt "test/lego" "lego"
  let srcFiles ← findFilesWithExt "src/Lego" "lego"
  let rosettaFiles ← findFilesWithExt "src/Rosetta" "lego"
  let exampleFiles ← findFilesWithExt "examples" "lego"

  let allFiles := testFiles ++ srcFiles ++ rosettaFiles ++ exampleFiles

  let mut stillFailing := 0
  let mut nowPassing := 0

  for file in allFiles do
    let shortName := file.fileName.getD file.toString
    if knownFailingLegoFiles.contains shortName then
      match ← parseLegoFilePathE rt file.toString with
      | .error e =>
        IO.println s!"  ✗ {shortName} (still failing)"
        IO.println s!"      {(toString e).take 80}"
        stillFailing := stillFailing + 1
      | .ok _ =>
        IO.println s!"  ✓ {shortName} (NOW PASSING! 🎉)"
        nowPassing := nowPassing + 1

  IO.println ""
  IO.println "═══════════════════════════════════════════════════════════════"
  IO.println s!"  Still failing: {stillFailing}"
  IO.println s!"  Now passing:   {nowPassing}"
  IO.println ""

  if nowPassing > 0 then
    IO.println "🎉 Some tests are now passing! Consider removing them from"
    IO.println "   knownFailingLegoFiles in TestIntegration.lean"
    IO.println ""

  -- Return 0 regardless - these are expected failures
  return 0
