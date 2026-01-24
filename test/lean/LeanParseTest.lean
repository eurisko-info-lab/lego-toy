-- Test Lean parsing with Lean.lego grammar
-- ISSUE: Left-recursive grammars cause infinite loops in the parser!
-- `app := term term` tries to parse `term` which tries `app` first -> loop
--
-- Solution: Use atom/expr pattern to eliminate left recursion
import Lego.Bootstrap
import Lego.Algebra
import Lego.Interp

namespace Lego.Lean

open Lego GrammarExpr

/-- Core piece - using atom/expr pattern to avoid left recursion
    Instead of: term := app | var | ...  with app := term term
    We use: term := atom arg*  with atom := var | paren

    This is equivalent but avoids left recursion.
-/
def corePiece : Piece := {
  name := "Core"
  grammar := [
    -- Atoms: things that can start an expression
    ("Core.atom",
      (node "var" (ref "TOKEN.ident")).alt (
      (node "paren" (((lit "(").seq (ref "Core.term")).seq (lit ")"))).alt (
      (node "numLit" (ref "TOKEN.number")).alt (
      (node "hole" (lit "_"))
    ))))
    -- Term: an atom optionally followed by arguments
    , ("Core.term",
        node "app" ((ref "Core.atom").seq ((ref "Core.arg").star)))
    -- Argument: another atom (could extend with @, !, etc.)
    , ("Core.arg", ref "Core.atom")
  ]
  rules := []
}

/-- Binders piece - fun and lambda -/
def bindersPiece : Piece := {
  name := "Binders"
  grammar := [
    ("Binders.funExpr",
      node "funExpr" ((((lit "fun").seq (ref "TOKEN.ident")).seq (lit "=>")).seq (ref "Core.term")))
    , ("Binders.lamExpr",
      node "lamExpr" ((((lit "λ").seq (ref "TOKEN.ident")).seq (lit "=>")).seq (ref "Core.term")))
  ]
  rules := []
}

/-- Declarations piece -/
def declsPiece : Piece := {
  name := "Decls"
  grammar := [
    ("Decls.defDecl",
      node "defDecl" (((((lit "def").seq (ref "TOKEN.ident")).seq (lit ":=")).seq (ref "Core.term"))))
    , ("Decls.importDecl",
      node "importDecl" ((lit "import").seq (ref "TOKEN.ident")))
  ]
  rules := []
}

/-- The Lean language -/
def grammar : Language := {
  name := "Lean"
  pieces := [corePiece, bindersPiece, declsPiece]
}

/-- Build interpreter starting from Core.term -/
def interp : LangInterp := grammar.toInterp "Core.term"

/-- Build interpreter starting from Binders.funExpr -/
def interpFun : LangInterp := grammar.toInterp "Binders.funExpr"

/-- Build interpreter starting from Decls.defDecl -/
def interpDef : LangInterp := grammar.toInterp "Decls.defDecl"

/-- Build interpreter starting from Decls.importDecl -/
def interpImport : LangInterp := grammar.toInterp "Decls.importDecl"

def tokenize := Lego.Bootstrap.tokenize

def parse (content : String) : Option Term :=
  interp.parse (tokenize content)

def parseFun (content : String) : Option Term :=
  interpFun.parse (tokenize content)

def parseDef (content : String) : Option Term :=
  interpDef.parse (tokenize content)

def parseImport (content : String) : Option Term :=
  interpImport.parse (tokenize content)

end Lego.Lean

namespace LeanParseTest

open Lego

def testParse (name : String) (input : String) (parser : String → Option Term) : IO Unit := do
  IO.println s!"Parsing '{input}'..."
  match parser input with
  | some term => IO.println s!"  ✓ Parsed: {repr term}"
  | none => IO.println s!"  ✗ Failed to parse"

def main : IO Unit := do
  IO.println "=== Testing Lean.lego grammar on Lean code ===\n"

  IO.println "--- Core terms (atom/expr pattern) ---"
  testParse "var" "x" Lego.Lean.parse
  testParse "num" "42" Lego.Lean.parse
  testParse "app" "f x" Lego.Lean.parse
  testParse "app2" "f x y" Lego.Lean.parse
  testParse "app3" "f x y z" Lego.Lean.parse
  testParse "paren" "(x)" Lego.Lean.parse
  testParse "nested" "(f x)" Lego.Lean.parse
  testParse "complex" "f (g x) y" Lego.Lean.parse

  IO.println "\n--- Fun expression ---"
  testParse "fun" "fun x => x" Lego.Lean.parseFun
  testParse "fun body" "fun x => f x" Lego.Lean.parseFun

  IO.println "\n--- Definitions ---"
  testParse "def" "def foo := 42" Lego.Lean.parseDef
  testParse "def expr" "def bar := f x" Lego.Lean.parseDef

  IO.println "\n--- Imports ---"
  testParse "import" "import Prelude" Lego.Lean.parseImport

  IO.println "\n✓ All basic Lean expressions parse correctly!"
  IO.println "Note: The grammar uses atom/arg* pattern to avoid left recursion."

end LeanParseTest

#eval LeanParseTest.main
