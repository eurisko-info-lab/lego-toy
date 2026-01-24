/-
  MultiTargetPipeline.lean
  Automatic code generation for multiple targets from a single source.

  Pipeline:
    source.lego → lego2rosetta → Rosetta IR → rosetta2<L> → <L> code

  Targets: Lean, Scala, Haskell, Rust

  Each target has:
  - <L>.lego: Pure AST definition for target language
  - rosetta2<L>.lego: Transformation rules from Rosetta IR
  - CodeGen functions: Convert AST to printable code
-/

import Lego.Runtime
import Lego.Loader

open Lego.Runtime
open Lego.Loader
open Lego

/-! ## Language Definitions -/

/-- Target language enumeration -/
inductive TargetLang | Lean | Scala | Haskell | Rust
  deriving Repr, BEq, Inhabited

instance : ToString TargetLang where
  toString
    | .Lean => "Lean"
    | .Scala => "Scala"
    | .Haskell => "Haskell"
    | .Rust => "Rust"

/-- File extension for each target -/
def TargetLang.ext : TargetLang → String
  | .Lean => ".lean"
  | .Scala => ".scala"
  | .Haskell => ".hs"
  | .Rust => ".rs"

/-- Path to rosetta2<L>.lego for each target -/
def TargetLang.transformPath : TargetLang → String
  | .Lean => "./src/Rosetta/rosetta2lean.lego"
  | .Scala => "./src/Rosetta/rosetta2scala.lego"
  | .Haskell => "./src/Rosetta/rosetta2haskell.lego"
  | .Rust => "./src/Rosetta/rosetta2rust.lego"

/-! ## Reserved Keywords per Language -/

def leanKeywords : List String := [
  "partial", "unsafe", "private", "protected", "scoped", "local",
  "where", "rec", "match", "let", "in", "if", "then", "else",
  "do", "return", "for", "fun", "by", "have", "show", "with",
  "structure", "inductive", "class", "instance", "def", "theorem",
  "axiom", "example", "abbrev", "opaque", "variable", "universe",
  "end", "section", "namespace", "open", "import", "export", "Type"
]

def scalaKeywords : List String := [
  "abstract", "case", "catch", "class", "def", "do", "else",
  "enum", "export", "extends", "false", "final", "finally", "for",
  "given", "if", "implicit", "import", "lazy", "match", "new",
  "null", "object", "override", "package", "private", "protected",
  "return", "sealed", "super", "then", "this", "throw", "trait",
  "true", "try", "type", "val", "var", "while", "with", "yield"
]

def haskellKeywords : List String := [
  "case", "class", "data", "default", "deriving", "do", "else",
  "forall", "foreign", "if", "import", "in", "infix", "infixl",
  "infixr", "instance", "let", "mdo", "module", "newtype", "of",
  "pattern", "proc", "qualified", "rec", "then", "type", "where"
]

def rustKeywords : List String := [
  "as", "async", "await", "break", "const", "continue", "crate",
  "dyn", "else", "enum", "extern", "false", "fn", "for", "if",
  "impl", "in", "let", "loop", "match", "mod", "move", "mut",
  "pub", "ref", "return", "self", "Self", "static", "struct",
  "super", "trait", "true", "type", "unsafe", "use", "where", "while"
]

def TargetLang.keywords : TargetLang → List String
  | .Lean => leanKeywords
  | .Scala => scalaKeywords
  | .Haskell => haskellKeywords
  | .Rust => rustKeywords

/-- Sanitize identifier for target language -/
def sanitizeIdent (lang : TargetLang) (name : String) : String :=
  if lang.keywords.contains name then name ++ "_"
  else name

/-! ## Code Generation Helpers -/

def nl : String := "\n"

/-- Capitalize first letter -/
def capitalize (s : String) : String :=
  if s.isEmpty then s
  else
    let c := s.get ⟨0⟩
    s!"{c.toUpper}{s.drop 1}"

/-- Lowercase first letter -/
def lowercase (s : String) : String :=
  if s.isEmpty then s
  else
    let c := s.get ⟨0⟩
    s!"{c.toLower}{s.drop 1}"

/-- Join lines with newlines -/
def joinLines (lines : List String) : String :=
  nl.intercalate lines

/-! ## AST → Code Printers -/

/-- Extract grammar alternatives from DGrammar -/
partial def extractGrammarAlts (body : Term) : List String :=
  match body with
  | .con "alt" [l, _, r] => extractGrammarAlts l ++ extractGrammarAlts r
  | .con "arrow" [_, .con "ident" [.var name]] => [name]
  | .con "seq" args => args.flatMap extractGrammarAlts
  | _ => []

/-- Extract constructors from a piece/grammar -/
partial def extractPieceCtors (t : Term) : List (String × List (String × String)) :=
  match t with
  | .con "DGrammar" args =>
    -- DGrammar has form: (ident name) "::=" body ";"
    let filtered := args.filter (· != .lit "::=") |>.filter (· != .lit ";")
    match filtered with
    | .con "ident" [.var name] :: rest =>
      let alts := rest.flatMap extractGrammarAlts
      [(name, alts.map (·, "Term"))]
    | _ => []
  | .con "DPiece" args => args.flatMap extractPieceCtors
  | .con "DLang" args => args.flatMap extractPieceCtors
  | .con "seq" ts => ts.flatMap extractPieceCtors
  | .con _ args => args.flatMap extractPieceCtors
  | _ => []

/-- Extract rules from a parsed .lego AST -/
partial def extractLegoRules (t : Term) : List (String × Term × Term) :=
  match t with
  | .con "DRule" args =>
    -- Filter out keywords and punctuation
    let filtered := args.filter (· != .lit "rule")
                       |>.filter (· != .lit ":")
                       |>.filter (· != .lit "~>")
                       |>.filter (· != .lit "~~>")
                       |>.filter (· != .lit ";")
                       |>.filter (· != .con "unit" [])
    match filtered with
    | .con "ident" [.var name] :: rest =>
      match rest with
      | [pat, tmpl] => [(name, pat, tmpl)]
      | [pat] => [(name, pat, pat)]
      | _ => []
    | _ => []
  | .con "DPiece" args => args.flatMap extractLegoRules
  | .con "DLang" args => args.flatMap extractLegoRules
  | .con "seq" ts => ts.flatMap extractLegoRules
  | .con _ args => args.flatMap extractLegoRules
  | _ => []

/-- Extract constructor definitions from transformed AST.
    Looks for patterns like (adtDef name (ctor c1 ty1) (ctor c2 ty2) ...) -/
partial def extractAdtDefs (t : Term) : List (String × List (String × String)) :=
  -- First try standard Rosetta format, then fall back to Lego format
  let rosettaDefs := extractRosettaAdtDefs t
  if rosettaDefs.isEmpty then extractPieceCtors t else rosettaDefs
where
  extractRosettaAdtDefs : Term → List (String × List (String × String))
    | .con "adtDef" args =>
      match args with
      | .var name :: ctors =>
        let ctorList := ctors.filterMap fun c =>
          match c with
          | .con "ctor" [.var cname, .var cty] => some (cname, cty)
          | .con "ctor" [.con "ident" [.var cname], ty] =>
            some (cname, termToTypeString ty)
          | _ => none
        [(name, ctorList)]
      | .con "ident" [.var name] :: ctors =>
        let ctorList := ctors.filterMap fun c =>
          match c with
          | .con "ctor" [.var cname, .var cty] => some (cname, cty)
          | .con "ctor" [.con "ident" [.var cname], ty] =>
            some (cname, termToTypeString ty)
          | _ => none
        [(name, ctorList)]
      | _ => []
    | .con "moduleDecl" [_, .con "seq" body] =>
      body.flatMap extractRosettaAdtDefs
    | .con "seq" ts => ts.flatMap extractRosettaAdtDefs
    | .con _ args => args.flatMap extractRosettaAdtDefs
    | _ => []

  termToTypeString : Term → String
    | .var s => s
    | .con "Arrow" [a, b] => s!"{termToTypeString a} → {termToTypeString b}"
    | .con "ident" [.var s] => s
    | _ => "Any"

/-- Extract rewrite rules from transformed AST -/
partial def extractRewriteRules (t : Term) : List (String × Term × Term) :=
  -- First try standard Rosetta format, then fall back to Lego format
  let rosettaRules := extractRosettaRules t
  if rosettaRules.isEmpty then extractLegoRules t else rosettaRules
where
  extractRosettaRules : Term → List (String × Term × Term)
    | .con "rewriteRule" args =>
      match args with
      | [.var name, pat, tmpl] => [(name, pat, tmpl)]
      | [.con "ident" [.var name], pat, tmpl] => [(name, pat, tmpl)]
      | _ => []
    | .con "moduleDecl" [_, .con "seq" body] =>
      body.flatMap extractRosettaRules
    | .con "seq" ts => ts.flatMap extractRosettaRules
    | .con _ args => args.flatMap extractRosettaRules
    | _ => []

/-- Convert Term to string (generic, used for patterns/templates) -/
partial def termToString (t : Term) : String :=
  match t with
  | .var name => name
  | .lit s => s
  | .con "ident" [.var name] => name
  | .con "metavar" [.var name] => "$" ++ name
  | .con name args =>
    if args.isEmpty then name
    else "(" ++ name ++ " " ++ " ".intercalate (args.map termToString) ++ ")"

/-- Clean pattern/template: extract meaningful structure from raw Lego AST -/
partial def cleanLegoTerm (t : Term) : Term :=
  match t with
  -- Extract variable from (var "$" (ident name))
  | .con "var" [.lit "$", .con "ident" [.var name]] => .var ("$" ++ name)
  | .con "var" (.lit "$" :: .con "ident" [.var name] :: _) => .var ("$" ++ name)
  -- S-expression: (con "(" head args... ")")
  | .con "con" args =>
    let filtered := args.filter fun x =>
      match x with | .lit "(" => false | .lit ")" => false | _ => true
    match filtered with
    | .con "ident" [.var head] :: rest =>
      .con head (rest.map cleanLegoTerm)
    | [single] => cleanLegoTerm single
    | _ => t
  -- Sequence
  | .con "seq" args =>
    let cleaned := args.map cleanLegoTerm
    .con "seq" cleaned
  -- Recursive clean
  | .con name args => .con name (args.map cleanLegoTerm)
  | _ => t

/-! ## Lean Code Generator -/

/-- Generate Lean 4 inductive type -/
def genLeanInductive (name : String) (ctors : List (String × String)) : String :=
  let ctorLines := ctors.map fun (cname, cty) =>
    s!"  | {lowercase cname} : {cty} → {name}"
  let body := joinLines ctorLines
  s!"inductive {name} where" ++ nl ++ body ++ nl ++ "  deriving Repr, BEq" ++ nl

partial def termToLeanPattern (t : Term) : String :=
  let cleaned := cleanLegoTerm t
  go cleaned
where
  go : Term → String
    | .var n =>
      if n.startsWith "$" then sanitizeIdent .Lean (n.drop 1)
      else sanitizeIdent .Lean n
    | .con "ident" [.var n] => sanitizeIdent .Lean n
    | .con "metavar" [.var n] => sanitizeIdent .Lean n
    | .con name args =>
      if args.isEmpty then s!".{lowercase name}"
      else s!"(.{lowercase name} {" ".intercalate (args.map go)})"
    | t => termToString t

partial def termToLeanExpr (t : Term) : String :=
  let cleaned := cleanLegoTerm t
  go cleaned
where
  go : Term → String
    | .var n =>
      if n.startsWith "$" then sanitizeIdent .Lean (n.drop 1)
      else sanitizeIdent .Lean n
    | .con "ident" [.var n] => sanitizeIdent .Lean n
    | .con "metavar" [.var n] => sanitizeIdent .Lean n
    | .con name args =>
      if args.isEmpty then s!".{lowercase name}"
      else s!"(.{lowercase name} {" ".intercalate (args.map go)})"
    | t => termToString t

/-- Generate Lean 4 function from rewrite rule -/
def genLeanFunction (name : String) (pat : Term) (tmpl : Term) : String :=
  let patStr := termToLeanPattern pat
  let tmplStr := termToLeanExpr tmpl
  s!"def {name} : Expr → Option Expr" ++ nl ++
  s!"  | {patStr} => some {tmplStr}" ++ nl ++
  "  | _ => none" ++ nl

/-- Generate complete Lean file -/
def genLeanFile (moduleName : String) (ast : Term) : String :=
  let header := "/-" ++ nl ++ "  Generated from Rosetta IR" ++ nl ++
    s!"  Module: {moduleName}" ++ nl ++ "-/" ++ nl ++ nl
  let adts := extractAdtDefs ast
  let rules := extractRewriteRules ast

  let adtCode := adts.map fun (name, ctors) => genLeanInductive name ctors
  let ruleCode := rules.map fun (name, pat, tmpl) => genLeanFunction name pat tmpl

  header ++ joinLines adtCode ++ nl ++ joinLines ruleCode

/-! ## Scala Code Generator -/

/-- Generate Scala 3 enum type -/
def genScalaEnum (name : String) (ctors : List (String × String)) : String :=
  let ctorLines := ctors.map fun (cname, cty) =>
    let args := scalaTypeArgs cty
    s!"  case {capitalize cname}({args})"
  let body := joinLines ctorLines
  s!"enum {name}:" ++ nl ++ body ++ nl
where
  scalaTypeArgs (ty : String) : String :=
    let parts := ty.splitOn " → "
    let indexed := parts.dropLast.mapIdx fun i p => s!"arg{i + 1}: {p}"
    ", ".intercalate indexed

/-- Generate Scala function from rewrite rule -/
def genScalaFunction (name : String) (pat : Term) (tmpl : Term) : String :=
  let patStr := goPattern (cleanLegoTerm pat)
  let tmplStr := goExpr (cleanLegoTerm tmpl)
  s!"def {name}(e: Expr): Option[Expr] = e match" ++ nl ++
  s!"  case {patStr} => Some({tmplStr})" ++ nl ++
  "  case _ => None" ++ nl
where
  goPattern : Term → String
    | .var n =>
      if n.startsWith "$" then sanitizeIdent .Scala (n.drop 1)
      else sanitizeIdent .Scala n
    | .con "ident" [.var n] => sanitizeIdent .Scala n
    | .con "metavar" [.var n] => sanitizeIdent .Scala n
    | .con nm args =>
      if args.isEmpty then s!"{capitalize nm}()"
      else s!"{capitalize nm}({", ".intercalate (args.map goPattern)})"
    | t => termToString t

  goExpr : Term → String
    | .var n =>
      if n.startsWith "$" then sanitizeIdent .Scala (n.drop 1)
      else sanitizeIdent .Scala n
    | .con "ident" [.var n] => sanitizeIdent .Scala n
    | .con "metavar" [.var n] => sanitizeIdent .Scala n
    | .con nm args =>
      if args.isEmpty then s!"{capitalize nm}()"
      else s!"{capitalize nm}({", ".intercalate (args.map goExpr)})"
    | t => termToString t

/-- Generate complete Scala file -/
def genScalaFile (moduleName : String) (ast : Term) : String :=
  let header := "// Generated from Rosetta IR" ++ nl ++
    s!"// Module: {moduleName}" ++ nl ++ nl ++ "package generated" ++ nl ++ nl
  let adts := extractAdtDefs ast
  let rules := extractRewriteRules ast

  let adtCode := adts.map fun (name, ctors) => genScalaEnum name ctors
  let ruleCode := rules.map fun (name, pat, tmpl) => genScalaFunction name pat tmpl

  header ++ joinLines adtCode ++ nl ++ joinLines ruleCode

/-! ## Haskell Code Generator -/

/-- Generate Haskell data type (GADT style) -/
def genHaskellData (name : String) (ctors : List (String × String)) : String :=
  let ctorLines := ctors.map fun (cname, cty) =>
    let ty := haskellType cty
    s!"  {capitalize cname} :: {ty}"
  let body := joinLines ctorLines
  s!"data {name} where" ++ nl ++ body ++ nl ++ "  deriving (Show, Eq)" ++ nl
where
  haskellType (ty : String) : String :=
    ty.replace " → " " -> "

/-- Generate Haskell function from rewrite rule -/
def genHaskellFunction (name : String) (pat : Term) (tmpl : Term) : String :=
  let patStr := goPattern (cleanLegoTerm pat)
  let tmplStr := goExpr (cleanLegoTerm tmpl)
  s!"{name} :: Expr -> Maybe Expr" ++ nl ++
  s!"{name} ({patStr}) = Just ({tmplStr})" ++ nl ++
  s!"{name} _ = Nothing" ++ nl
where
  goPatternArg : Term → String  -- Wrap nested constructors in parens
    | .var n =>
      if n.startsWith "$" then sanitizeIdent .Haskell (n.drop 1)
      else sanitizeIdent .Haskell n
    | .con "ident" [.var n] => sanitizeIdent .Haskell n
    | .con "metavar" [.var n] => sanitizeIdent .Haskell n
    | .con nm args =>
      if args.isEmpty then capitalize nm
      else s!"({capitalize nm} {" ".intercalate (args.map goPatternArg)})"
    | t => termToString t

  goPattern : Term → String  -- Top-level (no extra parens)
    | .var n =>
      if n.startsWith "$" then sanitizeIdent .Haskell (n.drop 1)
      else sanitizeIdent .Haskell n
    | .con "ident" [.var n] => sanitizeIdent .Haskell n
    | .con "metavar" [.var n] => sanitizeIdent .Haskell n
    | .con nm args =>
      if args.isEmpty then capitalize nm
      else s!"{capitalize nm} {" ".intercalate (args.map goPatternArg)}"
    | t => termToString t

  goExpr : Term → String
    | .var n =>
      if n.startsWith "$" then sanitizeIdent .Haskell (n.drop 1)
      else sanitizeIdent .Haskell n
    | .con "ident" [.var n] => sanitizeIdent .Haskell n
    | .con "metavar" [.var n] => sanitizeIdent .Haskell n
    | .con nm args =>
      if args.isEmpty then capitalize nm
      else s!"({capitalize nm} {" ".intercalate (args.map goExpr)})"
    | t => termToString t

/-- Generate complete Haskell file -/
def genHaskellFile (moduleName : String) (ast : Term) : String :=
  let pragma1 := "{-# LANGUAGE GADTs #-}"
  let pragma2 := "{-# LANGUAGE StandaloneDeriving #-}"
  let header := "{-" ++ nl ++ "  Generated from Rosetta IR" ++ nl ++
    s!"  Module: {moduleName}" ++ nl ++ "-}" ++ nl ++ nl ++
    pragma1 ++ nl ++ pragma2 ++ nl ++ nl ++
    s!"module {moduleName} where" ++ nl ++ nl
  let adts := extractAdtDefs ast
  let rules := extractRewriteRules ast

  let adtCode := adts.map fun (name, ctors) => genHaskellData name ctors
  let ruleCode := rules.map fun (name, pat, tmpl) => genHaskellFunction name pat tmpl

  header ++ joinLines adtCode ++ nl ++ joinLines ruleCode

/-! ## Rust Code Generator -/

/-- Generate Rust enum type -/
def genRustEnum (name : String) (ctors : List (String × String)) : String :=
  let ctorLines := ctors.map fun (cname, cty) =>
    let fields := rustFields cty
    if fields.isEmpty then s!"    {capitalize cname},"
    else "    " ++ capitalize cname ++ " { " ++ fields ++ " },"
  let body := joinLines ctorLines
  "#[derive(Debug, Clone, PartialEq)]" ++ nl ++
  "pub enum " ++ name ++ " {" ++ nl ++ body ++ nl ++ "}" ++ nl
where
  rustFields (ty : String) : String :=
    let parts := ty.splitOn " → "
    let indexed := parts.dropLast.mapIdx fun i p =>
      let rustTy := if p == "Term" || p == "Expr" then "Box<Expr>" else p
      s!"arg{i + 1}: {rustTy}"
    ", ".intercalate indexed

partial def termToRustPattern (t : Term) : String :=
  go (cleanLegoTerm t)
where
  go : Term → String
    | .var n =>
      if n.startsWith "$" then sanitizeIdent .Rust (n.drop 1)
      else sanitizeIdent .Rust n
    | .con "ident" [.var n] => sanitizeIdent .Rust n
    | .con "metavar" [.var n] => sanitizeIdent .Rust n
    | .con nm args =>
      if args.isEmpty then s!"Expr::{capitalize nm}"
      else
        let fields := args.mapIdx fun i a =>
          s!"arg{i + 1}: {go a}"
        "Expr::" ++ capitalize nm ++ " { " ++ ", ".intercalate fields ++ " }"
    | t => termToString t

partial def termToRustExpr (t : Term) : String :=
  go (cleanLegoTerm t)
where
  go : Term → String
    | .var n =>
      let safe := if n.startsWith "$" then sanitizeIdent .Rust (n.drop 1)
                  else sanitizeIdent .Rust n
      s!"{safe}.clone()"
    | .con "ident" [.var n] =>
      let safe := sanitizeIdent .Rust n
      s!"{safe}.clone()"
    | .con "metavar" [.var n] =>
      let safe := sanitizeIdent .Rust n
      s!"{safe}.clone()"
    | .con nm args =>
      if args.isEmpty then s!"Expr::{capitalize nm}"
      else
        let fields := args.mapIdx fun i a =>
          s!"arg{i + 1}: Box::new({go a})"
        "Expr::" ++ capitalize nm ++ " { " ++ ", ".intercalate fields ++ " }"
    | t => termToString t

/-- Generate Rust function from rewrite rule -/
def genRustFunction (name : String) (pat : Term) (tmpl : Term) : String :=
  let patStr := termToRustPattern pat
  let tmplStr := termToRustExpr tmpl
  "pub fn " ++ name ++ "(e: &Expr) -> Option<Expr> {" ++ nl ++
  "    match e {" ++ nl ++
  "        " ++ patStr ++ " => Some(" ++ tmplStr ++ ")," ++ nl ++
  "        _ => None," ++ nl ++
  "    }" ++ nl ++
  "}" ++ nl

/-- Generate complete Rust file -/
def genRustFile (moduleName : String) (ast : Term) : String :=
  let header := "// Generated from Rosetta IR" ++ nl ++
    s!"// Module: {moduleName}" ++ nl ++ nl
  let adts := extractAdtDefs ast
  let rules := extractRewriteRules ast

  let adtCode := adts.map fun (name, ctors) => genRustEnum name ctors
  let ruleCode := rules.map fun (name, pat, tmpl) => genRustFunction name pat tmpl

  header ++ joinLines adtCode ++ nl ++ joinLines ruleCode

/-! ## Unified Code Generator -/

/-- Generate code for a specific target language -/
def genCode (lang : TargetLang) (moduleName : String) (ast : Term) : String :=
  match lang with
  | .Lean => genLeanFile moduleName ast
  | .Scala => genScalaFile moduleName ast
  | .Haskell => genHaskellFile moduleName ast
  | .Rust => genRustFile moduleName ast

/-! ## Multi-Target Pipeline -/

/-- Pipeline result for one target -/
structure TargetResult where
  lang : TargetLang
  code : String
  outPath : String
  deriving Repr

/-- Run the complete pipeline for all targets -/
def runMultiTargetPipeline (rt : Runtime) (sourcePath : String)
    (targets : List TargetLang := [.Lean, .Scala, .Haskell, .Rust])
    (outDir : String := "./generated/Rosetta")
    : IO (Except String (List TargetResult)) := do

  -- Step 1: Parse source .lego file
  IO.println s!"[1] Parsing source: {sourcePath}"
  let sourceAst ← match ← parseLegoFilePathE rt sourcePath with
    | .error e => return .error s!"Failed to parse source: {e}"
    | .ok ast => pure ast
  IO.println s!"    ✓ Parsed AST"

  -- Step 2: Direct transformation to target code
  -- (Skip Rosetta IR transformation since the rule files use pseudo-code)
  IO.println s!"[2] Generating code for {targets.length} targets..."
  let results ← targets.mapM fun lang => do
    IO.println s!"    → {lang}..."

    -- Generate code directly from source AST
    let moduleName := sourcePath.splitOn "/" |>.getLast! |>.replace ".lego" "" |> capitalize
    let code := genCode lang moduleName sourceAst

    -- Determine output path
    let outPath := s!"{outDir}/{moduleName}{lang.ext}"

    IO.println s!"      ✓ Generated {code.length} chars"
    pure { lang, code, outPath }

  -- Step 3: Write output files
  IO.println s!"[3] Writing output files..."
  IO.FS.createDirAll outDir
  for result in results do
    IO.FS.writeFile result.outPath result.code
    IO.println s!"    ✓ {result.outPath}"

  return .ok results

/-! ## Main Entry Point -/

def main (args : List String) : IO Unit := do
  let sourcePath := args.getD 0 "./src/Rosetta/Rosetta.lego"
  let outDir := args.getD 1 "./generated/Rosetta"

  IO.println "═══════════════════════════════════════════════════════════════"
  IO.println "Multi-Target Rosetta Pipeline"
  IO.println "═══════════════════════════════════════════════════════════════"
  IO.println s!"Source: {sourcePath}"
  IO.println s!"Output: {outDir}"
  IO.println ""

  -- Initialize runtime
  let rt ← Lego.Runtime.init

  -- Run pipeline
  match ← runMultiTargetPipeline rt sourcePath [.Lean, .Scala, .Haskell, .Rust] outDir with
  | .error e =>
    IO.eprintln s!"✗ Pipeline failed: {e}"
    return
  | .ok results =>
    IO.println ""
    IO.println "═══════════════════════════════════════════════════════════════"
    IO.println s!"✓ Generated {results.length} files:"
    for r in results do
      IO.println s!"  • {r.outPath}"
    IO.println "═══════════════════════════════════════════════════════════════"
