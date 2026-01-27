/-
  Main: Lego REPL and test runner
-/

import Lego

open Lego

def main : IO Unit := do
  IO.println "═══════════════════════════════════════════════════════════════"
  IO.println "Lego: A Minimal Language for Building Languages"
  IO.println "═══════════════════════════════════════════════════════════════"
  IO.println ""

  -- Initialize runtime and show keyword info
  let rt ← Runtime.initQuiet
  IO.println s!"Keywords ({rt.grammar.keywords.length}): {rt.grammar.keywords.take 20}"
  IO.println s!"Token productions: {rt.grammar.tokenProductions.length}"
  -- Check for LegoKeywords.keyword
  let keywordProds := rt.grammar.tokenProductions.filter fun (n, _) => n.endsWith ".keyword"
  IO.println s!"Keyword prods: {keywordProds.map (·.1)}"
  IO.println ""

  IO.println "Core types:"
  IO.println "  Iso A B        -- Partial isomorphism A ⇌ B"
  IO.println "  Term           -- Universal AST (var | con | lit)"
  IO.println "  GrammarExpr    -- Grammar algebra (Kleene *-semiring)"
  IO.println "  Rule           -- Rewrite rule (pattern ⇌ template)"
  IO.println "  Piece          -- Grammar + Rules (with free interpreter)"
  IO.println "  Language       -- ⊔ Pieces (pushout composition)"
  IO.println ""
  IO.println "Bootstrap pieces:"
  for p in Bootstrap.metaGrammar.pieces do
    IO.println s!"  {p.name}: {p.grammar.length} productions, {p.rules.length} rules"
  IO.println ""
  IO.println "Languages are defined in .lego files:"
  IO.println "  test/Lambda.lego  -- Lambda calculus with beta reduction"
  IO.println "  test/Arith.lego   -- Natural numbers with fib, fact"
  IO.println "  test/INet.lego    -- Interaction nets"
  IO.println "  test/Meta.lego    -- Simple expression language"
  IO.println ""
  IO.println "Run 'lake exe lego-test' to parse .lego files and run eval tests."
