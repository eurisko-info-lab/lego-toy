-- Test Lean.lego grammar parsing generated Lean files
import Lego.Interp
import Lego.Bootstrap
import Rosetta.Lean

namespace LeanGrammarTest

open Lego GrammarExpr

def interp : LangInterp := Lego.Lean.grammar.toInterp "Lean.coreTerm"

def parse (content : String) : Option Term :=
  interp.parse (Lego.Bootstrap.tokenize content)

def main : IO Unit := do
  IO.println "=== Testing Lean.lego Grammar ==="

  -- Test simple expressions that should parse with the @ explicit app
  let tests : List (String × String) := [
    ("var", "x"),
    ("num", "42"),
    ("string", "\"hello\""),
    ("bool", "true"),
    ("unit", "()"),
    ("hole", "_"),
    ("list", "[1, 2, 3]"),
    ("array", "#[1, 2]"),
    ("paren", "(x)"),
    ("tuple", "(1, 2)"),
    -- Operators
    ("add", "x + y"),
    ("mul", "x * y"),
    ("arrow", "Nat → Nat"),
    ("prod", "Nat × Nat"),
    ("cons", "x :: xs"),
    ("pipe", "x |> f"),
    ("eq", "x == y"),
    ("and", "x && y"),
    -- Control
    ("if", "if b then x else y"),
    ("fun", "fun x => x"),
    ("lambda", "λ x => x"),
    ("let", "let x := 1 in x"),
    ("forall", "∀ x, x"),
    -- Match
    ("match", "match x with | 0 => 1"),
    -- Do
    ("do", "do pure x"),
    -- Proofs
    ("by rfl", "by rfl"),
    -- Type
    ("Type", "Type"),
    ("Prop", "Prop"),
    -- Field access (projection)
    ("proj", "x.foo"),
    -- Explicit application (@ prefix)
    ("app", "f @ x"),
    ("app2", "f @ x @ y"),
    ("nested", "f @ (g @ x)")
  ]

  let mut passed := 0
  let mut failed := 0

  for (name, input) in tests do
    match parse input with
    | some _ =>
      IO.println s!"  ✓ {name}: {input}"
      passed := passed + 1
    | none =>
      IO.println s!"  ✗ {name}: {input}"
      failed := failed + 1

  IO.println ""
  IO.println s!"Results: {passed} passed, {failed} failed"

  if failed > 0 then
    IO.Process.exit 1

#eval main
