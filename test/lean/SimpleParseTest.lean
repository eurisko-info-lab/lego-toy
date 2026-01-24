import Lego.Bootstrap
import Lego.Algebra
import Lego.Interp

namespace SimpleParseTest

open Lego GrammarExpr

-- Grammar where args are operator-only, application is explicit with @
def simplePiece : Piece := {
  name := "Simple"
  grammar := [
    -- atom: specific keyword forms first, then general ident/num
    ("Simple.atom", 
      (node "fun" ((((lit "fun").seq (ref "TOKEN.ident")).seq (lit "=>")).seq (ref "Simple.term"))).alt (
      (node "let" ((((((lit "let").seq (ref "TOKEN.ident")).seq (lit ":=")).seq (ref "Simple.term")).seq (lit "in")).seq (ref "Simple.term"))).alt (
      (node "if" ((((((lit "if").seq (ref "Simple.term")).seq (lit "then")).seq (ref "Simple.term")).seq (lit "else")).seq (ref "Simple.term"))).alt (
      (node "paren" (((lit "(").seq (ref "Simple.term")).seq (lit ")"))).alt (
      (node "list" (((lit "[").seq (ref "Simple.termList")).seq (lit "]"))).alt (
      (ref "TOKEN.ident").alt (
      (ref "TOKEN.number"))))))))
    -- termList for lists
    , ("Simple.termList", (ref "Simple.termListItem").star)
    , ("Simple.termListItem", (ref "Simple.term").alt (lit ","))
    -- arg: ONLY operator forms, NOT bare atom (avoid consuming keywords)
    , ("Simple.arg",
        (node "add" ((lit "+").seq (ref "Simple.term"))).alt (
        (node "mul" ((lit "*").seq (ref "Simple.term"))).alt (
        (node "cons" (((lit ":").seq (lit ":")).seq (ref "Simple.term"))).alt (
        (node "pipe" (((lit "|").seq (lit ">")).seq (ref "Simple.term"))).alt (
        (node "arrow" ((lit "→").seq (ref "Simple.term"))).alt (
        (node "app" ((lit "@").seq (ref "Simple.atom")))))))))  -- explicit application with @
    -- term: atom followed by zero or more args
    , ("Simple.term", node "expr" ((ref "Simple.atom").seq ((ref "Simple.arg").star)))
  ]
  rules := []
}

def simpleLang : Language := {
  name := "Simple"
  pieces := [simplePiece]
}

def interp : LangInterp := simpleLang.toInterp "Simple.term"

def parse (content : String) : Option Term :=
  interp.parse (Lego.Bootstrap.tokenize content)

def main : IO Unit := do
  IO.println "=== Grammar with explicit app ==="
  
  let tests := [
    ("var", "x"),
    ("num", "42"),
    ("app", "f @ x"),  -- explicit app
    ("app2", "f @ x @ y"),
    ("nested app", "f @ (g @ x) @ y"),
    ("paren", "(x)"),
    ("fun", "fun x => x"),
    ("arrow", "Nat → Nat"),
    ("let", "let x := 1 in x"),
    ("if", "if b then x else y"),
    ("list", "[1, 2, 3]"),
    ("operator", "x + y"),
    ("cons", "x :: xs"),
    ("pipe", "x |> f"),
    ("complex", "fun x => x + 1")
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
  
  IO.println s!"\nResults: {passed} passed, {failed} failed"

#eval main
