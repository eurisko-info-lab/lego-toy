/-
  RosettaPipeline.lean
  Parse .rosetta files via Rosetta.lego grammar,
  transform via rosetta2target.lego rules,
  print via Lean.lego grammar.
-/

import Lego.Runtime
import Lego.Bootstrap
import Lego.Loader
import Lego.Interp

open Lego.Runtime
open Lego.Bootstrap
open Lego.Loader
open Lego

/-- Parse with grammar-aware tokenization (handles keywords) -/
def parseWithKeywords (grammar : LoadedGrammar) (input : String) (extraKeywords : List String := []) : Option Term :=
  -- Bootstrap tokenize handles parens, idents, strings, numbers
  -- We just need to ensure keywords are recognized as symbols, not idents
  let tokens := Bootstrap.tokenize input
  -- Reclassify idents that are keywords as syms
  let tokens' := tokens.map fun t =>
    match t with
    | .ident s => if extraKeywords.contains s then .sym s else t
    | _ => t
  let st : ParseState := { tokens := tokens', binds := [] }
  -- Use findAllProductions to combine multiple alternatives
  match findAllProductions grammar.productions grammar.startProd with
  | some g =>
    let (result, _) := parseGrammar defaultFuel grammar.productions g st
    match result with
    | some (t, st') => if st'.tokens.isEmpty then some t else none
    | none => none
  | none => none

def main : IO Unit := do
  IO.println "═══════════════════════════════════════════════════════════════"
  IO.println "Rosetta Pipeline: .rosetta → Rosetta.lego → rosetta2lean → Lean"
  IO.println "═══════════════════════════════════════════════════════════════"

  -- Step 0: Initialize Runtime by loading Bootstrap.lego
  let rt ← Lego.Runtime.init

  -- Step 1: Load Rosetta.lego as SOURCE grammar
  IO.println "\n[1] Loading Rosetta.lego (source grammar)..."
  let rosettaGrammar ← match ← loadLanguage rt "./src/Rosetta/Rosetta.lego" with
    | Except.error e => IO.eprintln s!"  ✗ {e}"; return
    | Except.ok g =>
      -- Override startProd to use our term production
      let g' := { g with startProd := "CorePrimitives.term" }
      IO.println s!"  ✓ {g'.productions.length} productions"
      IO.println s!"  Start production: {g'.startProd}"
      pure g'

  -- Step 2: Parse example.rosetta WITH Rosetta grammar
  IO.println "\n[2] Parsing example.rosetta..."
  let sourceContent ← IO.FS.readFile "./src/Rosetta/prelude.rosetta"
  IO.println s!"  Source content: {repr sourceContent}"
  -- Rosetta keywords (from Rosetta.lego grammar literals)
  let rosettaKeywords := ["Univ", "Var", "App", "Subst", "Lam", "DLam", "Pi", "Sigma", "Fst", "Snd", "Pair", "adtDef", "rewriteRule", "judgeDecl", "testDecl", "moduleDecl", "importDecl", "when", "lang"]
  let tokens := Bootstrap.tokenize sourceContent
  IO.println s!"  Raw tokens: {repr tokens}"
  -- Convert keywords
  let tokens' := tokens.map fun t =>
    match t with
    | Token.ident s => if rosettaKeywords.contains s then Token.sym s else t
    | _ => t
  IO.println s!"  Converted tokens: {repr tokens'}"
  -- Show available productions
  IO.println s!"  Production for startProd: {repr (rosettaGrammar.productions.find? (·.1 == rosettaGrammar.startProd))}"
  let ast ← match parseWithKeywords rosettaGrammar sourceContent rosettaKeywords with
  | none =>
    IO.eprintln "  ✗ Failed to parse example.rosetta"
    return
  | some a =>
    IO.println s!"  ✓ Parsed example.rosetta"
    IO.println s!"  AST: {repr a}"
    pure a

  -- Step 3: Load rosetta2target rules
  IO.println "\n[3] Loading rosetta2target.lego rules..."
  let rules ← match ← loadTransformRules rt "./src/Rosetta/rosetta2target.lego" with
    | Except.error e => IO.eprintln s!"  ✗ {e}"; return
    | Except.ok r => IO.println s!"  ✓ {r.length} rules"; pure r

  -- Step 4: Transform
  IO.println "\n[4] Transforming..."
  let leanAst := transform rules ast
  IO.println s!"  ✓ Transformed: {repr leanAst}"

  -- Step 5: Load Lean.lego grammar
  IO.println "\n[5] Loading Lean.lego grammar..."
  let leanGrammar ← match ← loadLanguage rt "./src/Rosetta/Lean.lego" with
    | Except.error e => IO.eprintln s!"  ✗ {e}"; return
    | Except.ok g =>
      IO.println s!"  ✓ {g.productions.length} productions"
      IO.println s!"  Start: {g.startProd}"
      pure g

  -- Step 6: Print via Lean.lego grammar
  IO.println "\n[6] Printing via Lean.lego grammar..."
  match printWithGrammar leanGrammar "LeanExpr.expr" leanAst with
  | some tokens =>
    let code := tokens.map Token.toString |> String.intercalate " "
    IO.println "───────────────────────────────────────────────────────────────"
    IO.println code
    IO.println "───────────────────────────────────────────────────────────────"
    IO.FS.createDirAll "./generated/Rosetta"
    IO.FS.writeFile "./generated/Rosetta/Example.lean" code
    IO.println "✓ Wrote generated/Rosetta/Example.lean"
  | none =>
    IO.eprintln "  ✗ Print failed"
