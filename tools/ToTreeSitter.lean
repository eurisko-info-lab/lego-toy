/-
  ToTreeSitter: Generate tree-sitter grammar from Lego grammar

  Usage:
    lake exe totreesitter test/Arith.lego > grammar.js

  Tree-sitter grammars are JavaScript files that define:
  - rules: parser rules (CFG)
  - extras: whitespace/comments to skip
  - conflicts: ambiguity resolution

  Translation:
    Lego                    Tree-sitter
    ────────────────────    ────────────────────
    foo ::= ... ;           foo: $ => ...
    "keyword"               'keyword'
    <ident>                 $.identifier (external)
    foo*                    repeat($.foo)
    foo+                    repeat1($.foo)
    foo?                    optional($.foo)
    foo | bar               choice($.foo, $.bar)
    foo bar                 seq($.foo, $.bar)
-/

import Lego.Algebra
import Lego.Bootstrap
import Lego.Loader

namespace Lego.ToTreeSitter

open Lego

/-- Convert a production name to tree-sitter format (snake_case) -/
def toTsRuleName (name : String) : String :=
  let parts := name.splitOn "."
  match parts with
  | [_, prod] => prod.toLower
  | _ => name.toLower

/-- Lego built-in token names that map to tree-sitter externals -/
def builtinTokens : List (String × String) := [
  ("name", "$.identifier"),
  ("ident", "$.identifier"),
  ("string", "$.string"),
  ("number", "$.number")
]

/-- Convert a reference name to tree-sitter format -/
def toTsRef (name : String) : String :=
  if name.startsWith "TOKEN." then
    let tokName := name.drop 6
    match tokName with
    | "ident" => "$.identifier"
    | "string" => "$.string"
    | "number" => "$.number"
    | "char" => "$.char"
    | _ => s!"$.{tokName}"
  else
    match builtinTokens.find? (·.1 == name) with
    | some (_, tsName) => tsName
    | none => s!"$.{toTsRuleName name}"

/-- Escape a string for JavaScript -/
def escapeJsString (s : String) : String :=
  s.foldl (fun acc c =>
    match c with
    | '\'' => acc ++ "\\'"
    | '\\' => acc ++ "\\\\"
    | '\n' => acc ++ "\\n"
    | '\t' => acc ++ "\\t"
    | '"' => acc ++ "\\\""
    | c => acc.push c
  ) ""

/-- Check if expression is a simple atom (no wrapping needed) -/
def isSimpleAtom : GrammarExpr → Bool
  | .mk (.lit _) => true
  | .mk (.ref _) => true
  | .mk .empty => true
  | _ => false

/-- Convert GrammarExpr to tree-sitter JavaScript syntax -/
partial def exprToTs : GrammarExpr → String
  | .mk .empty => "blank()"
  | .mk (.lit s) => s!"'{escapeJsString s}'"
  | .mk (.ref name) => toTsRef name
  | .mk (.seq g1 g2) =>
    let s1 := exprToTs g1
    let s2 := exprToTs g2
    if s1 == "blank()" then s2
    else if s2 == "blank()" then s1
    else s!"seq({s1}, {s2})"
  | .mk (.alt g1 g2) =>
    -- Collect all alternatives into a flat list
    let alts := collectAlts g1 ++ collectAlts g2
    let altStrs := alts.map exprToTs
    s!"choice({", ".intercalate altStrs})"
  | .mk (.star g) =>
    s!"repeat({exprToTs g})"
  | .mk (.bind _ g) => exprToTs g
  | .mk (.node _ g) => exprToTs g
where
  collectAlts : GrammarExpr → List GrammarExpr
    | .mk (.alt g1 g2) => collectAlts g1 ++ collectAlts g2
    | g => [g]

/-- Handle plus (one or more) - tree-sitter has repeat1 -/
def exprToTsWithPlus : GrammarExpr → String
  | .mk (.seq g (.mk (.star g'))) =>
    if g == g' then s!"repeat1({exprToTs g})"
    else s!"seq({exprToTs g}, repeat({exprToTs g'}))"
  | g => exprToTs g

/-- Convert a single production to tree-sitter rule -/
def prodToTs (name : String) (expr : GrammarExpr) : String :=
  let ruleName := toTsRuleName name
  let ruleBody := exprToTsWithPlus expr
  s!"    {ruleName}: $ => {ruleBody}"

/-- Generate all parser rules from productions -/
def generateTsRules (prods : Productions) : String :=
  let rules := prods.map (fun (name, expr) => prodToTs name expr)
  String.intercalate ",\n\n" rules

/-- Standard extras (whitespace, comments) -/
def standardExtras : String :=
"  extras: $ => [
    /\\s/,
    $.comment,
  ]"

/-- Standard external tokens -/
def standardExternals : String :=
"  externals: $ => [
    $.identifier,
    $.number,
    $.string,
    $.char,
  ]"

/-- Built-in token rules -/
def builtinRules : String :=
"    // Built-in tokens
    identifier: $ => /[a-zA-Z_][a-zA-Z0-9_]*/,

    number: $ => /[0-9]+/,

    string: $ => seq('\"', repeat(choice(/[^\"]/, /\\\\./)), '\"'),

    char: $ => seq('\\'', /[^']|\\\\./,'\\''),

    comment: $ => choice(
      seq('--', /.*/),
      seq('/-', /[^]*?/, '-/')
    )"

/-- Extract grammar name from file path -/
def extractGrammarName (path : String) : String :=
  let basename := path.splitOn "/" |>.getLast!
  match basename.splitOn "." with
  | name :: _ => name.toLower
  | _ => "grammar"

/-- Generate complete tree-sitter grammar.js file -/
def generateTreeSitter (prods : Productions) (grammarName : String) : String :=
  let tsRules := generateTsRules prods
  s!"// Generated from Lego grammar
// Usage: tree-sitter generate

module.exports = grammar(\{
  name: '{grammarName}',

{standardExtras},

  rules: \{
{tsRules},

{builtinRules}
  }
});
"

/-- Load a .lego file and convert to tree-sitter -/
def legoFileToTreeSitter (path : String) : IO String := do
  let content ← IO.FS.readFile path
  let grammarName := extractGrammarName path
  match Bootstrap.parseLegoFile content with
  | some ast =>
    let prods := Loader.extractProductionsOnly ast
    pure (generateTreeSitter prods grammarName)
  | none =>
    throw (IO.userError s!"Failed to parse {path}")

end Lego.ToTreeSitter

/-- Main entry point -/
def main (args : List String) : IO Unit := do
  match args with
  | [path] =>
    let ts ← Lego.ToTreeSitter.legoFileToTreeSitter path
    IO.println ts
  | _ =>
    IO.eprintln "Usage: totreesitter <file.lego>"
    IO.eprintln ""
    IO.eprintln "Converts a Lego grammar to tree-sitter grammar.js format."
    IO.eprintln ""
    IO.eprintln "Example:"
    IO.eprintln "  lake exe totreesitter examples/Arith.lego > grammar.js"
    IO.eprintln "  tree-sitter generate"
    IO.eprintln "  tree-sitter parse test.arith"
    IO.Process.exit 1
