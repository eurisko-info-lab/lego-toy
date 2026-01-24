/-
  Lego.Bootstrap: The Seed Grammar (hardcoded)

  PURPOSE: Parse Bootstrap.lego ONCE to get the real grammar.

  This module is the "seed" that breaks the chicken-and-egg problem:
  - We need a grammar to parse Bootstrap.lego
  - Bootstrap.lego defines the grammar
  - This hardcoded seed parses Bootstrap.lego
  - Then Runtime.lean uses the PARSED grammar for everything else

  Architecture:
    ┌─────────────────────┐
    │  This Module        │ ──parses──▶ Bootstrap.lego
    │  (hardcoded seed)   │                   │
    └─────────────────────┘                   │
                                              ▼
                                      ┌─────────────────┐
                                      │ Runtime Grammar │ ──parses──▶ *.lego
                                      │ (from Bootstrap)│
                                      └─────────────────┘

  The hardcoded parts (in generated/):
  - BootstrapGrammar.lean: grammar productions
  - BootstrapTokenizer.lean: character-level tokenizer
  - BootstrapRules.lean: interpreter rules

  To regenerate (if Bootstrap.lego changes):
    lake exe tolean --grammar test/lego/Bootstrap.lego -o generated/BootstrapGrammar.lean
    lake exe tolean --tokenizer test/lego/Bootstrap.lego -o generated/BootstrapTokenizer.lean
    lake exe tolean --rules test/lego/Bootstrap.lego -o generated/BootstrapRules.lean
-/

import Lego.Algebra
import Lego.Interp
import BootstrapGrammar
import BootstrapTokenizer
import BootstrapRules

namespace Lego.Bootstrap

open GrammarExpr

/-! ## Grammar (imported from generated) -/

def allPieces := Lego.Generated.Bootstrap.allPieces

/-- The complete Meta language -/
def metaGrammar : Language := {
  name := "Meta"
  pieces := allPieces
}

/-- Build the interpreter for parsing .lego files -/
def metaInterp : LangInterp := metaGrammar.toInterp "File.legoFile"

/-! ## Tokenizer (imported from generated) -/

/-- Raw tokenizer - DO NOT USE DIRECTLY. Use tokenizeBootstrap instead. -/
private def tokenizeRaw := Lego.Generated.Bootstrap.tokenize

/-! ## Rules (imported from generated) -/

def allRules := Lego.Generated.Bootstrap.allRules
def ruleInterp := Lego.Generated.Bootstrap.ruleInterp
def normalize := Lego.Generated.Bootstrap.normalize

/-! ## Bootstrap-Only Parsing

    These functions are ONLY for parsing Bootstrap.lego itself.
    For any other .lego file, use Runtime.parseLegoFileE.
-/

/-- Tokenize Bootstrap.lego content ONLY.
    ⚠️  This tokenizer is ONLY for Bootstrap.lego! -/
def tokenizeBootstrap (content : String) : List Token :=
  tokenizeRaw content

/-- Parse Bootstrap.lego content ONLY using the hardcoded grammar.

    ⚠️  WARNING: This function should ONLY be used to parse Bootstrap.lego itself!

    For parsing any other .lego file, use:
      let rt ← Lego.Runtime.init
      let ast ← Lego.Runtime.parseLegoFileE rt content

    The bootstrap chain is:
      Hardcoded Grammar → Bootstrap.lego → Full Grammar → All other .lego files -/
private def parseBootstrapContent (content : String) : Option Term :=
  metaInterp.parse (tokenizeRaw content)

/-- Parse Bootstrap.lego from a file path. ONLY accepts Bootstrap.lego!
    This is the ONLY entry point for bootstrap parsing. -/
def parseBootstrapFile (path : String) : IO (Option Term) := do
  if !path.endsWith "Bootstrap.lego" then
    IO.eprintln s!"FATAL: Bootstrap.parseBootstrapFile only accepts Bootstrap.lego, got: {path}"
    IO.eprintln "For other .lego files, use Runtime.parseLegoFileE"
    IO.Process.exit 1
  let content ← IO.FS.readFile path
  return parseBootstrapContent content

/-- Parse bootstrap-format lego content (used by Runtime.loadBootstrap).
    Note: This exists for backward compatibility - prefer parseBootstrapFile for IO. -/
def parseLegoFile (content : String) : Option Term :=
  parseBootstrapContent content

/-- The tokenize function - only exposed for Runtime.loadBootstrap compatibility -/
def tokenize := tokenizeRaw

end Lego.Bootstrap
