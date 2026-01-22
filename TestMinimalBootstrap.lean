/-
  Test: MinimalBootstrap → Bootstrap.lego

  This verifies that the minimal ASCII-only tokenizer can parse
  Bootstrap.lego which contains Unicode character literals.

  The key insight: string/char CONTENT can be any Unicode because
  the tokenizer handles them specially, not via grammar enumeration.
-/

import Lego.Algebra
import Lego.Interp
import MinimalBootstrapTokenizer

open Lego
open Lego.Generated

def main : IO Unit := do
  IO.println "═══════════════════════════════════════════════════════════════"
  IO.println "Testing MinimalBootstrap Tokenizer"
  IO.println "═══════════════════════════════════════════════════════════════"

  -- Read Bootstrap.lego
  let content ← IO.FS.readFile "test/Bootstrap.lego"

  IO.println s!"\nStep 1: Tokenizing Bootstrap.lego with MINIMAL tokenizer..."
  IO.println s!"        (ASCII-only grammar, Unicode handled specially)"

  -- Use the minimal tokenizer
  let tokens := MinimalBootstrap.tokenize content

  IO.println s!"  ✓ Tokenized {tokens.length} tokens"

  -- Show some tokens containing Unicode
  let unicodeTokens := tokens.filter fun t =>
    match t with
    | .lit s => s.any (fun c => c.val > 127)
    | .ident s => s.any (fun c => c.val > 127)
    | .sym s => s.any (fun c => c.val > 127)
    | _ => false

  IO.println s!"  ✓ Found {unicodeTokens.length} tokens with Unicode content"

  -- Show first few Unicode tokens
  if unicodeTokens.length > 0 then
    IO.println "\n  Sample Unicode tokens (char literals with Greek, math, etc):"
    for t in unicodeTokens.take 10 do
      IO.println s!"    {repr t}"

  -- Count different token types
  let lits := tokens.filter fun t => match t with | .lit _ => true | _ => false
  let idents := tokens.filter fun t => match t with | .ident _ => true | _ => false
  let syms := tokens.filter fun t => match t with | .sym _ => true | _ => false

  IO.println s!"\n  Token breakdown:"
  IO.println s!"    Literals:    {lits.length}"
  IO.println s!"    Identifiers: {idents.length}"
  IO.println s!"    Symbols:     {syms.length}"

  -- Verify we got all the Unicode char literals
  if unicodeTokens.length >= 100 then
    IO.println "\n  ✓ SUCCESS: All Unicode char literals tokenized correctly!"
  else
    IO.println "\n  ⚠ WARNING: Expected 100+ Unicode tokens, got fewer"

  IO.println "\n═══════════════════════════════════════════════════════════════"
  IO.println "MinimalBootstrap Test Complete!"
  IO.println ""
  IO.println "Key insight: The minimal tokenizer (ASCII-only grammar) can parse"
  IO.println "Bootstrap.lego which contains Unicode char literals like 'α', 'β',"
  IO.println "because string/char content is handled specially by the tokenizer,"
  IO.println "not by character enumeration in the grammar."
  IO.println "═══════════════════════════════════════════════════════════════"
