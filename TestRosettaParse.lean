import Lego.Runtime
import Lego.Loader

open Lego.Runtime
open Lego.Loader
open Lego

def main : IO Unit := do
  let rt ← Lego.Runtime.init

  -- Load Rosetta.lego grammar
  match ← loadLanguage rt "./src/Rosetta/Rosetta.lego" with
  | .error e => IO.println s!"Failed to load Rosetta grammar: {e}"
  | .ok rosettaGrammar =>
    IO.println s!"✓ Loaded Rosetta grammar with {rosettaGrammar.productions.length} productions"

    -- Test parsing adtDecl with simpler input
    let adtTests := [
      "adt X { A : X }",
      "adt Foo { Bar : String -> Foo }",
      "adt Term { Var : String -> Term, Lit : String -> Term }"
    ]

    for input in adtTests do
      IO.println s!"\nParsing adtDecl: {input}"
      let grammar := { rosettaGrammar with startProd := "File.adtDecl" }
      match Loader.parseWithGrammarE grammar input with
      | .error e => IO.println s!"  ✗ {e.message} at token {e.tokenPos}"
      | .ok ast => IO.println s!"  ✓ {repr ast |>.pretty 150}"

    -- Now parse full Algebra.rosetta
    IO.println "\n\n=== Parsing Algebra.rosetta ==="
    let content ← IO.FS.readFile "./src/Lego/Algebra.rosetta"
    let grammar := { rosettaGrammar with startProd := "File.rosettaFile" }
    match Loader.parseWithGrammarE grammar content with
    | .error e => IO.println s!"✗ {e.message} at token {e.tokenPos} in: {e.production}"
    | .ok ast =>
      IO.println s!"✓ Parsed Algebra.rosetta!"
      -- Count declarations
      let countDecls (t : Term) : Nat := match t with
        | .con "seq" args => args.length
        | _ => 1
      IO.println s!"  Declarations: {countDecls ast}"
