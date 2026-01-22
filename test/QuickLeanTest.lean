import Lego.Interp
import Lego.Bootstrap
import Rosetta.Lean

open Lego GrammarExpr

def interp : LangInterp := Lego.Lean.grammar.toInterp "Core.coreTerm"

def parse (content : String) : Option Term :=
  interp.parse (Lego.Bootstrap.tokenize content)

#eval do
  IO.println "=== Full test suite ==="

  let tests : List (String × String) := [
    ("var", "x"),
    ("num", "42"),
    ("string", "\"hello\""),
    ("bool true", "true"),
    ("bool false", "false"),
    ("unit", "()"),
    ("hole", "_"),
    ("paren", "(x)"),
    ("add", "x + y"),
    ("mul", "x * y"),
    ("arrow", "Nat → Nat"),
    ("prod", "Nat × Nat"),
    ("cons", "x :: xs"),
    ("pipe", "x |> f"),
    ("eq", "x == y"),
    ("and", "x && y"),
    ("if", "if b then x else y"),
    ("fun", "fun x => x"),
    ("lambda", "λ x => x"),
    ("let", "let x := 1 in x"),
    ("forall", "∀ x, x"),
    ("Type", "Type"),
    ("Prop", "Prop"),
    ("proj", "x.foo"),
    ("app", "f @ x"),
    ("app2", "f @ x @ y"),
    ("nested", "f @ (g @ x)"),
    ("typed fun", "fun (x : Nat) => x"),
    ("double arrow", "Nat → Nat → Nat"),
    ("complex app", "f @ x @ y @ z"),
    ("nested paren", "((x))"),
    ("op chain", "x + y + z"),
    ("nested fun", "fun x => fun y => x"),
    ("let chain", "let x := 1 in let y := 2 in x"),
    ("complex if", "if x then y else z + 1"),
    ("match0", "match x with"),
    ("match1", "match x with | 0 => 1"),
    ("match2", "match x with | 0 => 1 | _ => 0"),
    ("by rfl", "by rfl"),
    ("do pure", "do pure x"),
    ("array", "#[1, 2, 3]"),
    ("list", "[1, 2, 3]"),
    ("tuple", "(1, 2)"),
    ("struct lit", "{x := 1}")
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
