/-
  ToAntlr: Generate ANTLR4 grammar from Lego grammar

  Usage:
    lake exe toantlr examples/languages/red/Redtt.lego > Redtt.g4

  Translation:
    Lego                    ANTLR4
    ────────────────────    ────────────────────
    foo ::= ... ;           foo : ... ;
    "keyword"               'keyword'
    <ident>                 IDENT
    foo*                    foo*
    foo+                    foo+
    foo?                    foo?
    foo | bar               foo | bar
    → ConName               # ConName
-/

import Lego.Algebra
import Lego.Bootstrap
import Lego.Loader

namespace Lego.ToAntlr

open Lego

/-- Convert a production name to ANTLR format (lowercase, no dots) -/
def toAntlrProdName (name : String) : String :=
  let parts := name.splitOn "."
  match parts with
  | [_, prod] => prod.toLower
  | _ => name.toLower

/-- Lego built-in token names that map to lexer rules -/
def builtinTokens : List (String × String) := [
  ("name", "IDENT"),
  ("ident", "IDENT"),
  ("string", "STRING"),
  ("number", "NUMBER")
]

/-- Convert a reference name to ANTLR format -/
def toAntlrRef (name : String) : String :=
  if name.startsWith "TOKEN." then
    -- TOKEN.ident → IDENT (lexer rule, uppercase)
    name.drop 6 |>.toUpper
  else
    -- Check if it's a built-in token name
    match builtinTokens.find? (·.1 == name) with
    | some (_, antlrName) => antlrName
    | none => toAntlrProdName name

/-- Escape a string for ANTLR literal -/
def escapeAntlrLit (s : String) : String :=
  s.foldl (fun acc c =>
    match c with
    | '\'' => acc ++ "\\'"
    | '\\' => acc ++ "\\\\"
    | '\n' => acc ++ "\\n"
    | '\t' => acc ++ "\\t"
    | c => acc.push c
  ) ""

/-- Check if expression needs parentheses in ANTLR -/
def needsParens : GrammarExpr → Bool
  | .mk (.alt _ _) => true
  | _ => false

/-- Convert GrammarExpr to ANTLR syntax -/
partial def exprToAntlr : GrammarExpr → String
  | .mk .empty => ""
  | .mk (.lit s) => s!"'{escapeAntlrLit s}'"
  | .mk (.ref name) => toAntlrRef name
  | .mk (.seq g1 g2) =>
    let s1 := exprToAntlr g1
    let s2 := exprToAntlr g2
    if s1.isEmpty then s2
    else if s2.isEmpty then s1
    else s!"{s1} {s2}"
  | .mk (.alt g1 g2) =>
    s!"{exprToAntlr g1} | {exprToAntlr g2}"
  | .mk (.star g) =>
    let inner := exprToAntlr g
    if needsParens g then s!"({inner})*" else s!"{inner}*"
  | .mk (.bind _ g) => exprToAntlr g
  | .mk (.node _ g) =>
    -- ANTLR uses # for AST node labels (alternative labels)
    s!"{exprToAntlr g}"  -- We'll add # label at production level
  | .mk (.longest gs) =>
    -- ANTLR doesn't have longest match; use regular alternation
    let alts := gs.map exprToAntlr
    "(" ++ String.intercalate " | " alts ++ ")"
  | .mk (.ordered g1 g2) =>
    -- Ordered choice - in ANTLR alternation is ordered by default
    s!"{exprToAntlr g1} | {exprToAntlr g2}"
  | .mk (.cut g) =>
    -- ANTLR doesn't have cut; just emit the inner expression
    exprToAntlr g
  | .mk (.layout _) =>
    -- Layout annotations are for pretty-printing only, ignored in parsing
    ""

/-- Convert a single production to ANTLR rule -/
def prodToAntlr (name : String) (expr : GrammarExpr) : String :=
  let ruleName := toAntlrProdName name
  let ruleBody := exprToAntlr expr
  -- Check if top-level is a node wrapper
  match expr with
  | .mk (.node nodeName inner) =>
    s!"{ruleName} : {exprToAntlr inner}  # {nodeName} ;"
  | _ =>
    s!"{ruleName} : {ruleBody} ;"

/-- Generate all parser rules from productions -/
def generateParserRules (prods : Productions) : String :=
  let rules := prods.map (fun (name, expr) => prodToAntlr name expr)
  String.intercalate "\n" rules

/-- Standard lexer rules for Lego grammars -/
def standardLexerRules : String :=
"// Lexer rules
IDENT   : [a-zA-Z_\\u03B1-\\u03C9\\u03A0-\\u03A9] [a-zA-Z0-9_\\u03B1-\\u03C9\\u03A0-\\u03A9]* ;
NUMBER  : [0-9]+ ;
STRING  : '\"' (~[\"])* '\"' ;
CHAR    : '\\'' . '\\'' ;

// Skip whitespace and comments
WS          : [ \\t\\r\\n]+ -> skip ;
LINE_COMMENT: '--' ~[\\r\\n]* -> skip ;
BLOCK_COMMENT: '/-' .*? '-/' -> skip ;"

/-- Extract grammar name from file path -/
def extractGrammarName (path : String) : String :=
  -- Get basename without extension: "foo/bar/Redtt.lego" → "Redtt"
  let basename := path.splitOn "/" |>.getLast!
  match basename.splitOn "." with
  | name :: _ => name
  | _ => "Grammar"

/-- Generate complete ANTLR4 grammar file -/
def generateAntlr (prods : Productions) (grammarName : String) : String :=
  let parserRules := generateParserRules prods
  s!"// Generated from Lego grammar
// Usage: antlr4 {grammarName}.g4

grammar {grammarName};

// Parser rules
{parserRules}

{standardLexerRules}
"

/-- Load a .lego file and convert to ANTLR -/
def legoFileToAntlr (path : String) : IO String := do
  let content ← IO.FS.readFile path
  let grammarName := extractGrammarName path
  match Bootstrap.parseLegoFile content with
  | some ast =>
    let prods := Loader.extractProductionsOnly ast
    pure (generateAntlr prods grammarName)
  | none =>
    throw (IO.userError s!"Failed to parse {path}")

end Lego.ToAntlr

/-- Main entry point -/
def main (args : List String) : IO Unit := do
  match args with
  | [path] =>
    let antlr ← Lego.ToAntlr.legoFileToAntlr path
    IO.println antlr
  | _ =>
    IO.eprintln "Usage: toantlr <file.lego>"
    IO.eprintln ""
    IO.eprintln "Converts a Lego grammar to ANTLR4 format."
    IO.eprintln ""
    IO.eprintln "Example:"
    IO.eprintln "  lake exe toantlr examples/Redtt.lego > Redtt.g4"
    IO.eprintln "  antlr4 -Dlanguage=Cpp Redtt.g4"
    IO.Process.exit 1
