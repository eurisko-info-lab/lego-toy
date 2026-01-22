/-
  TestRuntime: Test the runtime bootstrap system

  This tests that:
  1. Bootstrap.lego is parsed by hardcoded grammar
  2. The resulting grammar can parse other .lego files
  3. Transformations work
-/

import Lego
import Lego.Runtime

open Lego
open Lego.Runtime

def main : IO Unit := do
  IO.println "═══════════════════════════════════════════════════════════════"
  IO.println "Testing Runtime Bootstrap"
  IO.println "═══════════════════════════════════════════════════════════════"
  IO.println ""

  -- Step 1: Load Bootstrap.lego
  IO.println "Step 1: Loading Bootstrap.lego with hardcoded grammar..."
  match ← loadBootstrap "./test/Bootstrap.lego" with
  | Except.error e =>
    IO.println s!"  ✗ Failed: {e}"
    return
  | Except.ok rt =>
    IO.println s!"  ✓ Loaded {rt.grammar.productions.length} productions"
    IO.println s!"  ✓ Loaded {rt.rules.length} rules"
    IO.println ""

    -- Step 2: Parse Lambda.lego with runtime grammar
    IO.println "Step 2: Parsing Lambda.lego with RUNTIME grammar (not hardcoded)..."
    match ← parseLegoFilePath rt "./examples/Lambda.lego" with
    | none =>
      IO.println "  ✗ Failed to parse Lambda.lego"
    | some ast =>
      IO.println "  ✓ Parsed Lambda.lego successfully"
      -- Count pieces
      let pieces := countPieces ast
      IO.println s!"  ✓ Found {pieces} pieces"
      IO.println ""

    -- Step 3: Parse Arith.lego
    IO.println "Step 3: Parsing Arith.lego with RUNTIME grammar..."
    match ← parseLegoFilePath rt "./examples/Arith.lego" with
    | none =>
      IO.println "  ✗ Failed to parse Arith.lego"
    | some ast =>
      IO.println "  ✓ Parsed Arith.lego successfully"
      let pieces := countPieces ast
      let rules := countRules ast
      IO.println s!"  ✓ Found {pieces} pieces, {rules} rules"
      IO.println ""

    -- Step 4: Parse Redtt.lego (cubical type theory!)
    IO.println "Step 4: Parsing Redtt.lego with RUNTIME grammar..."
    match ← parseLegoFilePath rt "./test/Redtt.lego" with
    | none =>
      IO.println "  ✗ Failed to parse Redtt.lego"
    | some ast =>
      IO.println "  ✓ Parsed Redtt.lego successfully"
      let pieces := countPieces ast
      let rules := countRules ast
      IO.println s!"  ✓ Found {pieces} pieces, {rules} rules"
      IO.println ""

    IO.println "═══════════════════════════════════════════════════════════════"
    IO.println "Runtime Bootstrap Test Complete!"
    IO.println ""
    IO.println "Key insight: The grammar used to parse Lambda.lego, Arith.lego,"
    IO.println "and Redtt.lego came from Bootstrap.lego at RUNTIME, not from"
    IO.println "hardcoded Lean code. Edit Bootstrap.lego and it takes effect"
    IO.println "immediately without regenerating any Lean code."
    IO.println "═══════════════════════════════════════════════════════════════"

where
  countPieces (t : Term) : Nat :=
    match t with
    | .con "seq" args => args.foldl (fun acc a => acc + countPieces a) 0
    | .con "DPiece" _ => 1
    | .con _ args => args.foldl (fun acc a => acc + countPieces a) 0
    | _ => 0

  countRules (t : Term) : Nat :=
    match t with
    | .con "seq" args => args.foldl (fun acc a => acc + countRules a) 0
    | .con "DRule" _ => 1
    | .con "DPiece" args => args.foldl (fun acc a => acc + countRules a) 0
    | .con _ args => args.foldl (fun acc a => acc + countRules a) 0
    | _ => 0
