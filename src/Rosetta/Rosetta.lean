/-
  Rosetta: Generic Lego → Lean code generator

  This module transforms parsed .lego AST into Lean code.
  It is GENERIC - no domain-specific types hard-coded.
  All domain knowledge comes from the .lego grammar.

  Pipeline:
  1. Parse .lego file using Runtime grammar → Term AST
  2. Walk AST to extract pieces, rules, types, tests
  3. Generate Lean code from extracted data

  NOTE: This module uses Runtime to ensure Bootstrap.lego is loaded first.
-/

import Lego.Loader
import Lego.Bootstrap
import Lego.Runtime
import Lego.Algebra

namespace Rosetta

open Lego
open Lego.Runtime

/-! ## Rosetta IR Types

Simple intermediate representation for code generation.
No domain-specific knowledge - just generic constructs.
-/

/-- Constructor info extracted from grammar -/
structure ConstrInfo where
  name : String
  arity : Nat  -- number of arguments
  deriving Repr

/-- Rule info extracted from rules section -/
structure RuleInfo where
  name : String
  pattern : Term
  template : Term
  deriving Repr

/-- Test info extracted from tests section -/
structure TestInfo where
  name : String
  input : Term
  expected : Term
  deriving Repr

/-- Piece info extracted from AST -/
structure PieceInfo where
  name : String
  constrs : List ConstrInfo
  rules : List RuleInfo
  tests : List TestInfo
  deriving Repr

/-- Language info -/
structure LangInfo where
  name : String
  pieces : List PieceInfo
  deriving Repr

/-! ## AST Walking

Extract structured info from raw Term AST.
-/

/-- Extract string from Term -/
def getString : Term → Option String
  | .lit s => some s
  | .var s => some s
  | _ => none

/-- Extract constructor name and arity from production -/
def extractConstr (prod : Term) : Option ConstrInfo := do
  -- Production shape: (proddecl name (seq ... → conName))
  match prod with
  | .con "proddecl" [.var name, _grammar] =>
    -- Just count as arity 0 for now - would need grammar analysis
    some { name := name, arity := 0 }
  | _ => none

/-- Extract rule info -/
def extractRule (rule : Term) : Option RuleInfo := do
  match rule with
  | .con "rule" [.var name, pattern, template] =>
    some { name := name, pattern := pattern, template := template }
  | .con "rule" [.var name, pattern, template, _cond] =>
    some { name := name, pattern := pattern, template := template }
  | _ => none

/-- Extract test info -/
def extractTest (test : Term) : Option TestInfo := do
  match test with
  | .con "test" [.lit name, input, expected] =>
    some { name := name, input := input, expected := expected }
  | _ => none

/-- Safe list indexing -/
def listGet? (xs : List α) (i : Nat) : Option α :=
  match xs, i with
  | [], _ => none
  | x :: _, 0 => some x
  | _ :: xs, n+1 => listGet? xs n

/-- Extract ident string from AST node -/
def getIdent : Term → Option String
  | .con "ident" [.var s] => some s
  | .var s => some s
  | _ => none

/-- Extract rule from DRule AST node -/
def extractDRule (rule : Term) : Option RuleInfo := do
  match rule with
  | .con "DRule" args =>
    -- DRule: [lit "rule", ident name, lit ":", pattern, lit "~>", template, ...]
    let name ← listGet? args 1 >>= getIdent
    let pattern ← listGet? args 3
    let template ← listGet? args 5
    some { name := name, pattern := pattern, template := template }
  | _ => none

/-- Extract test from DTest AST node -/
def extractDTest (test : Term) : Option TestInfo := do
  match test with
  | .con "DTest" args =>
    -- DTest: [lit "test", string name, lit ":", input, lit "~~>", expected, ...]
    match listGet? args 1 with
    | some (.con "string" [.lit name]) =>
      let input ← listGet? args 3
      let expected ← listGet? args 5
      some { name := name, input := input, expected := expected }
    | _ => none
  | _ => none

/-- Extract piece from DPiece AST node -/
partial def extractPiece (piece : Term) : Option PieceInfo := do
  match piece with
  | .con "DPiece" args =>
    -- DPiece: [lit "piece", ident name, ...items...]
    let name ← listGet? args 1 >>= getIdent
    let items := args.drop 2  -- Skip "piece" and name
    let rules := items.filterMap extractDRule
    let tests := items.filterMap extractDTest
    -- TODO: extract constrs from DGrammar
    some { name := name, constrs := [], rules := rules, tests := tests }
  | _ => none

/-- Extract all pieces from language AST -/
partial def extractLang (ast : Term) : Option LangInfo := do
  match ast with
  | .con "DLang" args =>
    -- DLang: [lit "lang", ident name, imports, lit ":=", ...pieces...]
    let name ← listGet? args 1 >>= getIdent
    let items := args.drop 4  -- Skip "lang", name, imports, ":="
    let pieces := items.filterMap extractPiece
    some { name := name, pieces := pieces }
  | .con "seq" args =>
    -- Top level is often wrapped in seq
    for arg in args do
      if let some info := extractLang arg then
        return info
    none
  | .con "file" args =>
    for arg in args do
      if let some info := extractLang arg then
        return info
    none
  | _ => none

/-! ## Lean Code Generation -/

/-- Capitalize first letter -/
def capitalize (s : String) : String :=
  match s.toList with
  | [] => s
  | c :: cs => String.mk (c.toUpper :: cs)

/-- Check if string is a metavariable (starts with $) -/
def isMetavar (s : String) : Bool :=
  s.startsWith "$"

/-- Convert Lego pattern to clean Lean pattern -/
partial def patternToLean : Term → String
  -- Metavariable: $x → x (pattern var)
  | .con "var" [.lit "$", .con "ident" [.var s]] => s
  | .con "var" [.con "ident" [.var s]] => s
  | .var s => if isMetavar s then s.drop 1 else s
  -- Number literal: num (number "0") → .i0 (or just 0 for now)
  | .con "num" [.con "number" [.lit n]] => s!".i{n}"
  | .con "number" [.lit n] => s!".i{n}"
  -- Constructor application: (f a b) → .f a b
  | .con "con" args =>
    match args.filter (· != .lit "(") |>.filter (· != .lit ")") with
    | .con "ident" [.var name] :: rest =>
      let argsStr := rest.map patternToLean |>.intersperse " " |> String.join
      if rest.isEmpty then s!".{name}" else s!"(.{name} {argsStr})"
    | _ => "_"
  -- Identifier
  | .con "ident" [.var s] => s!".{s}"
  | .lit s => s!"\"{s}\""
  | _ => "_"

/-- Convert Lego term to clean Lean expression -/
partial def termToLean : Term → String
  -- Metavariable: $x → x
  | .con "var" [.lit "$", .con "ident" [.var s]] => s
  | .con "var" [.con "ident" [.var s]] => s
  | .var s => if isMetavar s then s.drop 1 else s
  -- Number literal: num (number "0") → .i0
  | .con "num" [.con "number" [.lit n]] => s!".i{n}"
  | .con "number" [.lit n] => s!".i{n}"
  -- Constructor application: (f a b) → f a b
  | .con "con" args =>
    match args.filter (· != .lit "(") |>.filter (· != .lit ")") with
    | .con "ident" [.var name] :: rest =>
      let argsStr := rest.map termToLean |>.intersperse " " |> String.join
      if rest.isEmpty then s!".{name}" else s!"(.{name} {argsStr})"
    | _ => "_unknown_"
  -- Identifier
  | .con "ident" [.var s] => s
  | .lit s => s!"\"{s}\""
  | .con name [] => capitalize name
  | .con name args =>
    let argsStr := args.map termToLean |>.intersperse " " |> String.join
    s!"({capitalize name} {argsStr})"

/-- Generate rule as Lean match case -/
def ruleToLean (rule : RuleInfo) : String :=
  s!"  -- {rule.name}\n  | {patternToLean rule.pattern} => some {termToLean rule.template}"

/-- Generate test as Lean example -/
def testToLean (test : TestInfo) : String :=
  s!"/-- {test.name} -/\nexample : step {termToLean test.input} = some {termToLean test.expected} := rfl"

/-- Generate piece as Lean namespace -/
def pieceToLean (langName : String) (piece : PieceInfo) : String :=
  let header := s!"/-
  {langName}.{piece.name}
  Generated from {langName}.lego via Rosetta pipeline
-/

namespace {langName}.{piece.name}

"
  let rules := if piece.rules.isEmpty then "" else
    let cases := piece.rules.map ruleToLean |>.intersperse "\n" |> String.join
    s!"/-! ## Reduction Rules -/

def step : Term → Option Term
{cases}
  | _ => none

"
  let tests := if piece.tests.isEmpty then "" else
    let testStrs := piece.tests.map testToLean |>.intersperse "\n\n" |> String.join
    s!"/-! ## Tests -/

{testStrs}

"
  header ++ rules ++ tests ++ s!"end {langName}.{piece.name}\n"

/-- Generate language index file -/
def langIndexToLean (info : LangInfo) : String :=
  let imports := info.pieces.map (fun p => s!"import {info.name}.{p.name}")
                   |>.intersperse "\n" |> String.join
  s!"/-
  {info.name} - Generated from {info.name}.lego via Rosetta pipeline
-/

{imports}

namespace {info.name}

-- Re-exports

end {info.name}
"

/-! ## Main Entry Point -/

/-- Parse and generate Lean from a .lego file -/
def generateFromFile (rt : Runtime) (path : String) : IO (Option String) := do
  let content ← IO.FS.readFile path
  match Runtime.parseLegoFile rt content with
  | some ast =>
    match extractLang ast with
    | some info =>
      -- Generate index file
      return some (langIndexToLean info)
    | none =>
      IO.eprintln s!"Could not extract language structure from {path}"
      return none
  | none =>
    IO.eprintln s!"Failed to parse {path}"
    return none

/-- Generate all piece files -/
def generatePieceFiles (rt : Runtime) (path : String) (outDir : String) : IO Bool := do
  let content ← IO.FS.readFile path
  match Runtime.parseLegoFile rt content with
  | some ast =>
    match extractLang ast with
    | some info =>
      for piece in info.pieces do
        let pieceCode := pieceToLean info.name piece
        let outPath := s!"{outDir}/{piece.name}.lean"
        IO.FS.writeFile outPath pieceCode
        IO.println s!"Generated {outPath}"
      -- Generate index
      let indexPath := s!"{outDir}/{info.name}.lean"
      IO.FS.writeFile indexPath (langIndexToLean info)
      IO.println s!"Generated {indexPath}"
      return true
    | none =>
      IO.eprintln s!"Could not extract language structure"
      return false
  | none =>
    IO.eprintln s!"Failed to parse {path}"
    return false

end Rosetta
