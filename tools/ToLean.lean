/-
  ToLean: Generate Lean code from Lego grammar

  Usage:
    lake exe tolean test/lego/Bootstrap.lego                    # Full module
    lake exe tolean --grammar test/lego/Bootstrap.lego          # Grammar only
    lake exe tolean --tokenizer test/lego/Bootstrap.lego        # Tokenizer only
    lake exe tolean --rules test/lego/Bootstrap.lego            # Rules only

  This achieves meta-circularity: Bootstrap.lego can generate code
  equivalent to src/Lego/Bootstrap.lean, allowing the system to
  bootstrap itself.

  Output modes:
    --grammar    Generate only grammar pieces (for import by hand-written code)
    --tokenizer  Generate only tokenizer function
    --rules      Generate only rewrite rules and interpreter
    (default)    Generate complete standalone module

  Translation:
    .lego                         Lean
    ──────────────────────────    ──────────────────────────────────
    piece Atom                    def atomPiece : Piece := { ... }
    ident ::= <ident> ;           ("Atom.ident", ref "TOKEN.ident")
    foo → con                     node "con" (...)
    foo | bar                     (...).alt (...)
    foo bar                       (...).seq (...)
    foo*                          (...).star
    foo+                          (...).plus
    foo?                          (...).alt empty
    token Token                   Character predicates + tokenize fn
-/

import Lego.Algebra
import Lego.Bootstrap
import Lego.Loader
import Lego.Runtime

namespace Lego.ToLean

open Lego

/-- Escape a string for Lean string literal -/
def escapeLeanString (s : String) : String :=
  s.foldl (fun acc c =>
    match c with
    | '"' => acc ++ "\\\""
    | '\\' => acc ++ "\\\\"
    | '\n' => acc ++ "\\n"
    | '\t' => acc ++ "\\t"
    | c => acc.push c
  ) ""

/-- Well-known cross-piece production mappings -/
def crossPieceRefs : List (String × String) := [
  -- Atom pieces
  ("ident", "Atom.ident"),
  ("string", "Atom.string"),
  ("number", "Atom.number"),
  ("char", "Atom.char"),
  -- Term pieces
  ("term", "Term.term"),
  ("conname", "Term.conname"),
  -- Pattern/Template pieces
  ("pattern", "Pattern.pattern"),
  ("template", "Template.template"),
  -- GrammarExpr pieces
  ("expr", "GrammarExpr.expr"),
  ("alt", "GrammarExpr.alt"),
  ("seq", "GrammarExpr.seq"),
  ("seqBase", "GrammarExpr.seqBase"),
  ("suffix", "GrammarExpr.suffix"),
  ("atom", "GrammarExpr.atom")
]

/-- Qualify a reference name if it matches a known piece production -/
def qualifyRef (currentPiece : String) (name : String) : String :=
  if name.startsWith "TOKEN." then name
  else if name.contains '.' then
    -- Already qualified - but check if it's a mis-qualified cross-piece ref
    -- e.g., "File.expr" should be "GrammarExpr.expr"
    let shortName := name.splitOn "." |>.getLast!
    match crossPieceRefs.find? (·.1 == shortName) with
    | some (_, qualified) =>
      -- Only fix if current qualification is wrong
      if qualified != name then qualified else name
    | none => name
  -- Check for well-known cross-piece references
  else match crossPieceRefs.find? (·.1 == name) with
    | some (_, qualified) => qualified
    | none => s!"{currentPiece}.{name}"

/-- Convert GrammarExpr to Lean source code -/
partial def exprToLean (pieceName : String) (g : GrammarExpr) : String :=
  match g with
  | .mk .empty => "empty"
  | .mk (.lit s) => s!"(lit \"{escapeLeanString s}\")"
  | .mk (.ref name) =>
    let qualName := if name.startsWith "TOKEN." then name
                    else qualifyRef pieceName name
    s!"(ref \"{qualName}\")"
  | .mk (.seq g1 g2) =>
    let s1 := exprToLean pieceName g1
    let s2 := exprToLean pieceName g2
    s!"({s1}.seq {s2})"
  | .mk (.alt g1 g2) =>
    let s1 := exprToLean pieceName g1
    let s2 := exprToLean pieceName g2
    s!"({s1}.alt {s2})"
  | .mk (.star g') =>
    s!"({exprToLean pieceName g'}.star)"
  | .mk (.bind x g') =>
    s!"(bind \"{x}\" {exprToLean pieceName g'})"
  | .mk (.node name g') =>
    s!"(node \"{name}\" {exprToLean pieceName g'})"
  -- PEG extensions
  | .mk (.cut g') =>
    s!"(cut {exprToLean pieceName g'})"
  | .mk (.ordered g1 g2) =>
    let s1 := exprToLean pieceName g1
    let s2 := exprToLean pieceName g2
    s!"(ordered {s1} {s2})"
  | .mk (.longest gs) =>
    let exprs := gs.map (exprToLean pieceName) |> String.intercalate ", "
    s!"(longest [{exprs}])"
  -- Layout annotations
  | .mk (.layout kind) =>
    s!"(layout \"{kind}\")"

/-- Convert a single production to Lean tuple -/
def prodToLean (pieceName : String) (name : String) (expr : GrammarExpr) : String :=
  s!"    (\"{name}\", {exprToLean pieceName expr})"

/-- Extract token piece names from AST (pieces defined with 'token' keyword) -/
partial def extractTokenPieceNames (ast : Term) : List String :=
  go ast
where
  go (t : Term) : List String :=
    match t with
    | .con "DToken" (.lit _ :: .con "ident" [.var pieceName] :: _) =>
      [pieceName]
    | .con "DLang" ts =>
      ts.flatMap go
    | .con "seq" ts =>
      ts.flatMap go
    | .con _ ts =>
      ts.flatMap go
    | _ => []

/-- Group productions by piece name -/
def groupByPiece (prods : Productions) : List (String × Productions) :=
  let pieceNames := prods.map (fun (n, _) =>
    match n.splitOn "." with
    | [p, _] => p
    | _ => "Unknown"
  ) |>.eraseDups
  pieceNames.map fun pname =>
    (pname, prods.filter fun (n, _) =>
      match n.splitOn "." with
      | [p, _] => p == pname
      | _ => false)

/-- Convert piece name to Lean identifier (camelCase) -/
def pieceToLeanIdent (name : String) : String :=
  let first := name.toList.head? |>.map Char.toLower |>.getD 'x'
  s!"{first}{name.drop 1}Piece"

/-- Generate a Piece definition with appropriate level -/
def generatePiece (pieceName : String) (prods : Productions) (isToken : Bool := false) : String :=
  let leanIdent := pieceToLeanIdent pieceName
  let prodStrs := prods.map (fun (n, e) => prodToLean pieceName n e)
  let grammar := ",\n".intercalate prodStrs
  let levelLine := if isToken then "\n  level := .token" else ""
  s!"/-- {pieceName} piece -/
def {leanIdent} : Piece := \{
  name := \"{pieceName}\"{levelLine}
  grammar := [
{grammar}
  ]
  rules := []
}"

/-- Default tokenizer when no token piece is defined -/
def defaultTokenizer : String :=
"
/-- Default tokenizer (uses Bootstrap tokenizer) -/
def tokenize : String → TokenStream := Lego.Bootstrap.tokenize"

/-- Generate tokenizer module that uses grammar-driven lexing -/
def generateTokenizerModule (langName : String) (tokenProds : Productions) : String :=
  -- Generate the Token piece definition (same as grammar piece but for chars)
  let tokenPiece := generatePiece "Token" tokenProds (isToken := true)

  -- Build main productions in priority order:
  -- 1. comment (skip before anything else)
  -- 2. ws (whitespace - skip)
  -- 3. hashident (before operator - operator's symch fallback would only match '#')
  -- 4. special (before operator - operator's symch fallback would only match '<')
  -- 5. operator (multi-char operators with #longest - includes symch fallback)
  -- 6. op3 (3-char operators like ::= - legacy separate rules)
  -- 7. op2 (2-char operators like ~>, := - legacy separate rules)
  -- 8. layout (pretty-print annotations - legacy separate rules)
  -- 9. string (before ident to handle "...")
  -- 10. char (before ident to handle '...')
  -- 11. ident
  -- 12. number
  -- 13. sym (single symbol fallback - legacy separate rule)
  let priorityOrder := ["comment", "ws", "hashident", "special", "operator", "op3", "op2", "layout", "string", "char", "ident", "number", "sym"]
  let mainProds := priorityOrder.filterMap fun shortName =>
    -- Find the production with this short name
    tokenProds.find? (fun (name, _) =>
      match name.splitOn "." with
      | [_, n] => n == shortName
      | _ => name == shortName
    ) |>.map fun (name, _) => s!"\"{name}\""
  let mainProdList := ", ".intercalate mainProds

  s!"/-
  Generated Tokenizer from {langName}.lego

  Purely grammar-driven lexing. All token patterns are defined in the
  Token piece grammar and interpreted by tokenizeWithGrammar.

  DO NOT EDIT - regenerate with:
    lake exe tolean --tokenizer test/{langName}.lego -o generated/{langName}Tokenizer.lean
-/

import Lego.Algebra
import Lego.Interp

namespace Lego.Generated.{langName}

open GrammarExpr
open Lego

/-! ## Token Grammar -/

{tokenPiece}

/-- Token productions -/
def tokenProductions : Productions := tokenPiece.grammar

/-- Main token productions in priority order -/
def mainTokenProds : List String := [{mainProdList}]

/-! ## Tokenizer -/

/-- Tokenize using grammar-driven lexing -/
def tokenize (s : String) : TokenStream :=
  tokenizeWithGrammar defaultFuel tokenProductions mainTokenProds s

end Lego.Generated.{langName}
"

/-! ## Rule Generation -/

/-- Convert a Term to Lean source code -/
partial def termToLean (t : Term) : String :=
  match t with
  | .var name => s!".var \"{escapeLeanString name}\""
  | .lit s => s!".lit \"{escapeLeanString s}\""
  | .con c [] => s!".con \"{escapeLeanString c}\" []"
  | .con c args =>
    let argStrs := args.map termToLean
    s!".con \"{escapeLeanString c}\" [{", ".intercalate argStrs}]"

/-- Generate a Rule definition -/
def ruleToLean (r : Rule) : String :=
  let patLean := termToLean r.pattern
  let tmplLean := termToLean r.template
  s!"/-- Rule: {r.name} -/
def rule_{r.name.replace "-" "_"} : Rule := \{
  name := \"{r.name}\"
  pattern := {patLean}
  template := {tmplLean}
}"

/-- Generate all rule definitions -/
def generateRules (rules : List Rule) : String :=
  if rules.isEmpty then ""
  else
    let ruleDefs := rules.map ruleToLean
    let ruleNames := rules.map (fun r => s!"rule_{r.name.replace "-" "_"}")
    let ruleList := ", ".intercalate ruleNames
    s!"/-! ## Rewrite Rules -/

{"\n\n".intercalate ruleDefs}

/-- All rules for this language -/
def allRules : List Rule := [{ruleList}]

/-- Combined interpreter from all rules -/
def ruleInterp : Iso Term Term := Language.combineRules allRules

/-- Apply rules to normalize a term -/
partial def normalize (t : Term) : Term :=
  match ruleInterp.forward t with
  | some t' => normalize t'
  | none =>
    match t with
    | .con c args => .con c (args.map normalize)
    | _ => t"

/-- Hand-coded helper functions that the interpreter needs.
    These implement the same logic as the rewrite rules but as direct Lean functions
    for efficiency during parsing. -/
def helperFunctions : String :=
"/-! ## Helper Functions (used by Interp.lean) -/

/-- Combine two terms into a sequence -/
def combineSeq (t1 t2 : Term) : Term :=
  match t1, t2 with
  | .con \"seq\" ts, .con \"seq\" us => .con \"seq\" (ts ++ us)
  | .con \"seq\" ts, t => .con \"seq\" (ts ++ [t])
  | t, .con \"seq\" us => .con \"seq\" (t :: us)
  | .con \"unit\" [], t => t
  | t, .con \"unit\" [] => t
  | t1, t2 => .con \"seq\" [t1, t2]

/-- Split first element from a sequence -/
def splitSeq (t : Term) : Term × Term :=
  match t with
  | .con \"seq\" (h :: rest) => (h, .con \"seq\" rest)
  | t => (t, .con \"unit\" [])

/-- Wrap a term with a node name -/
def wrapNode (name : String) (t : Term) : Term :=
  match t with
  | .con \"seq\" ts => .con name ts
  | _ => .con name [t]

/-- Unwrap a node if name matches -/
def unwrapNode (name : String) (t : Term) : Term :=
  match t with
  | .con n ts => if n == name then .con \"seq\" ts else t
  | _ => t
"

/-- Generate rules-only module (for import by hand-written code) -/
def generateRulesModule (langName : String) (rules : List Rule) : String :=
  let rulesCode := generateRules rules
  let hasRules := !rules.isEmpty

  s!"/-
  Bootstrap Rules and Helper Functions

  This module contains:
  1. Hand-coded helper functions (combineSeq, splitSeq, wrapNode, unwrapNode)
     used by the interpreter during parsing
  2. Generated rewrite rules from {langName}.lego that express the same logic

  Eventually the hand-coded functions can be replaced by applying the rules,
  but for now we keep both for bootstrapping.

  Regenerate with:
    lake exe tolean --rules test/{langName}.lego -o generated/{langName}Rules.lean
-/

import Lego.Algebra

namespace Lego.Generated.{langName}

open Lego

{helperFunctions}

{if hasRules then rulesCode else "/-- No rules defined -/\ndef allRules : List Rule := []"}

end Lego.Generated.{langName}
"

/-- Find the best start production -/
def findStartProd (prods : Productions) : String :=
  -- Prefer File.legoFile, then first File.* production, then first overall
  match prods.find? (fun (n, _) => n == "File.legoFile") with
  | some (n, _) => n
  | none =>
    match prods.find? (fun (n, _) => n.startsWith "File.") with
    | some (n, _) => n
    | none =>
      match prods with
      | (n, _) :: _ => n
      | _ => "File.legoFile"

/-! ## Grammar-Only Generation -/

/-- Generate grammar-only module (for import by hand-written code)
    Excludes token pieces - those go in the tokenizer module -/
def generateGrammarModule (langName : String) (prods : Productions) (tokenPieceNames : List String := []) : String :=
  let grouped := groupByPiece prods
  -- Filter out token pieces (they belong in the tokenizer module)
  let nonTokenGroups := grouped.filter (fun (n, _) => !tokenPieceNames.contains n)
  let pieces := nonTokenGroups.map (fun (n, ps) => generatePiece n ps false)
  let pieceCode := "\n\n".intercalate pieces

  let pieceNames := nonTokenGroups.map (·.1)
  let pieceIdents := pieceNames.map pieceToLeanIdent
  let pieceList := ", ".intercalate pieceIdents

  s!"/-
  Generated Grammar from {langName}.lego

  This module contains ONLY the grammar piece definitions.
  Import this from your hand-written Bootstrap.lean to use
  the generated grammar while keeping hand-written tokenizer
  and other infrastructure.

  DO NOT EDIT - regenerate with:
    lake exe tolean --grammar test/{langName}.lego > generated/{langName}Grammar.lean
-/

import Lego.Algebra
import Lego.Interp

namespace Lego.Generated.{langName}

open GrammarExpr
open Lego

/-! ## Grammar Pieces -/

{pieceCode}

/-! ## Combined Grammar -/

/-- All piece definitions -/
def allPieces : List Piece := [{pieceList}]

/-- Get all productions from all pieces -/
def allProductions : Productions :=
  allPieces.foldl (fun acc p => acc ++ p.grammar) []

end Lego.Generated.{langName}
"

/-- Generate the complete Lean module -/
def generateLeanModule (langName : String) (prods : Productions) (tokenProds : Productions) (rules : List Rule) (tokenPieceNames : List String := []) : String :=
  let grouped := groupByPiece prods
  let pieces := grouped.map (fun (n, ps) => generatePiece n ps (tokenPieceNames.contains n))
  let pieceCode := "\n\n".intercalate pieces

  let pieceNames := grouped.map (·.1)
  let pieceIdents := pieceNames.map pieceToLeanIdent
  let pieceList := ", ".intercalate pieceIdents

  let startProd := findStartProd prods

  -- Generate tokenizer section
  let (tokenizerCode, tokenizerImport) :=
    if tokenProds.isEmpty then
      (defaultTokenizer, "\nimport Lego.Bootstrap")
    else
      -- Generate Token piece for grammar-driven tokenizing
      let tokenPiece := generatePiece "Token" tokenProds (isToken := true)
      let mainProds := tokenProds.filterMap fun (name, _) =>
        let shortName := match name.splitOn "." with
          | [_, n] => n
          | _ => name
        if shortName ∈ ["ident", "number", "string"] then some s!"\"{name}\""
        else none
      let mainProdList := ", ".intercalate mainProds
      let code := s!"
{tokenPiece}

/-- Token productions -/
def tokenProductions : Productions := tokenPiece.grammar

/-- Main token production names -/
def mainTokenProds : List String := [{mainProdList}]

/-- Tokenize using grammar-driven lexing -/
def tokenize (s : String) : TokenStream :=
  Lego.tokenizeWithGrammar tokenProductions mainTokenProds s"
      (code, "")

  -- Generate rules
  let rulesCode := generateRules rules

  s!"/-
  Generated from {langName}.lego

  This module was automatically generated by ToLean.
  It should be structurally equivalent to hand-written Bootstrap.lean.
-/

import Lego.Algebra
import Lego.Interp{tokenizerImport}

namespace Lego.{langName}

open GrammarExpr

/-! ## Grammar Pieces -/

{pieceCode}

/-! ## Language Definition -/

/-- The complete {langName} language -/
def grammar : Language := \{
  name := \"{langName}\"
  pieces := [{pieceList}]
}

/-- Build the interpreter -/
def interp : LangInterp := grammar.toInterp \"{startProd}\"

/-! ## Tokenizer -/
{tokenizerCode}

/-- Parse input -/
def parse (content : String) : Option Term :=
  interp.parse (tokenize content)

{rulesCode}

end Lego.{langName}
"

/-- Extract grammar name from file path -/
def extractGrammarName (path : String) : String :=
  let basename := path.splitOn "/" |>.getLast!
  match basename.splitOn "." with
  | name :: _ => name
  | _ => "Grammar"

/-- Output mode for code generation -/
inductive OutputMode
  | full      -- Complete standalone module
  | grammar   -- Grammar pieces only (for import)
  | tokenizer -- Tokenizer only
  | rules     -- Rules only

/-- Load a .lego file and convert to Lean -/
def legoFileToLean (path : String) (mode : OutputMode := .full) : IO String := do
  let content ← IO.FS.readFile path
  let langName := extractGrammarName path
  -- Use Bootstrap parser only for Bootstrap.lego, Runtime parser for everything else
  let ast ← if path.endsWith "Bootstrap.lego" then
    match Bootstrap.parseBootstrapContent content with
    | some ast => pure ast
    | none => throw (IO.userError s!"Failed to parse Bootstrap.lego")
  else do
    -- Load Runtime from Bootstrap.lego for non-Bootstrap files
    let rt ← Runtime.loadBootstrapOrError
    match Runtime.parseLegoFileE rt content with
    | .ok ast => pure ast
    | .error e => throw (IO.userError s!"Failed to parse {path}: {e}")
  let prods := Loader.extractProductionsOnly ast
  let tokenProds := Loader.extractTokenProductions ast
  let tokenPieceNames := extractTokenPieceNames ast
  let rules := Loader.extractRules ast
  match mode with
  | .full => pure (generateLeanModule langName prods tokenProds rules tokenPieceNames)
  | .grammar => pure (generateGrammarModule langName prods tokenPieceNames)
  | .tokenizer =>
    if tokenProds.isEmpty then
      pure defaultTokenizer
    else
      pure (generateTokenizerModule langName tokenProds)
  | .rules => pure (generateRulesModule langName rules)

end Lego.ToLean

/-- Main entry point -/
def main (args : List String) : IO Unit := do
  let (mode, path, outputPath) ← match args with
    | ["--grammar", p, "-o", out] => pure (Lego.ToLean.OutputMode.grammar, p, some out)
    | ["--grammar", p] => pure (Lego.ToLean.OutputMode.grammar, p, none)
    | ["--tokenizer", p, "-o", out] => pure (Lego.ToLean.OutputMode.tokenizer, p, some out)
    | ["--tokenizer", p] => pure (Lego.ToLean.OutputMode.tokenizer, p, none)
    | ["--rules", p, "-o", out] => pure (Lego.ToLean.OutputMode.rules, p, some out)
    | ["--rules", p] => pure (Lego.ToLean.OutputMode.rules, p, none)
    | [p, "-o", out] => pure (Lego.ToLean.OutputMode.full, p, some out)
    | [p] => pure (Lego.ToLean.OutputMode.full, p, none)
    | _ =>
      IO.eprintln "Usage: tolean [--grammar|--tokenizer|--rules] <file.lego> [-o <output.lean>]"
      IO.eprintln ""
      IO.eprintln "Converts a Lego grammar to Lean source code."
      IO.eprintln ""
      IO.eprintln "Options:"
      IO.eprintln "  --grammar    Generate only grammar pieces (for import)"
      IO.eprintln "  --tokenizer  Generate only tokenizer function"
      IO.eprintln "  --rules      Generate only rewrite rules"
      IO.eprintln "  -o <file>    Write to file (creates .bak backup) instead of stdout"
      IO.eprintln "  (default)    Generate complete standalone module"
      IO.eprintln ""
      IO.eprintln "Examples:"
      IO.eprintln "  lake exe tolean test/lego/Bootstrap.lego"
      IO.eprintln "  lake exe tolean --grammar test/lego/Bootstrap.lego -o generated/BootstrapGrammar.lean"
      IO.Process.exit 1

  -- Generate code in memory first
  let lean ← Lego.ToLean.legoFileToLean path mode

  match outputPath with
  | none =>
    -- Print to stdout
    IO.println lean
  | some out =>
    -- Write to file with backup
    let outPath := System.FilePath.mk out
    if ← outPath.pathExists then
      let bakPath := System.FilePath.mk (out ++ ".bak")
      IO.FS.rename outPath bakPath
    IO.FS.writeFile outPath lean
    IO.eprintln s!"Wrote {lean.length} bytes to {out}"
