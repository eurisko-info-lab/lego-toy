/-
  GrammarDrivenPipeline.lean
  Code generation driven by grammar rules, not hardcoded generators.

  Architecture:
    1. source.lego → parse → Rosetta IR (AST)
    2. Load <L>.lego grammar → extract layout rules
    3. Load rosetta2<L>.lego → extract transformation rules
    4. Rosetta IR + transform rules → <L> AST
    5. <L> AST + grammar layout → pretty-print → code string

  This replaces hardcoded generators like genScalaFunction with
  grammar-driven pretty-printing using @nl, @indent, @dedent annotations.
-/

import Lego.Runtime
import Lego.Loader

open Lego.Runtime
open Lego.Loader
open Lego

/-! ## Target Language Configuration -/

/-- Target language enumeration -/
inductive TargetLang | Lean | Scala | Haskell | Rust
  deriving Repr, BEq, Inhabited

instance : ToString TargetLang where
  toString
    | .Lean => "Lean"
    | .Scala => "Scala"
    | .Haskell => "Haskell"
    | .Rust => "Rust"

def TargetLang.ext : TargetLang → String
  | .Lean => ".lean"
  | .Scala => ".scala"
  | .Haskell => ".hs"
  | .Rust => ".rs"

/-- Path to <L>.lego grammar file -/
def TargetLang.grammarPath : TargetLang → String
  | .Lean => "./src/Rosetta/Lean.lego"
  | .Scala => "./src/Rosetta/Scala.lego"
  | .Haskell => "./src/Rosetta/Haskell.lego"
  | .Rust => "./src/Rosetta/Rust.lego"

/-- Path to rosetta2<L>.lego transform file -/
def TargetLang.transformPath : TargetLang → String
  | .Lean => "./src/Rosetta/rosetta2lean.lego"
  | .Scala => "./src/Rosetta/rosetta2scala.lego"
  | .Haskell => "./src/Rosetta/rosetta2haskell.lego"
  | .Rust => "./src/Rosetta/rosetta2rust.lego"

/-! ## Pretty-Printer State -/

-- NOTE: Layout annotations (@nl, @indent, @dedent, @sp, @nsp) are embedded
-- directly in the grammar files (<L>.lego), not in separate print files.
-- The parser ignores them; only the pretty-printer uses them.

structure PPState where
  output : String := ""
  indentLevel : Nat := 0
  currentCol : Nat := 0
  indentSize : Nat := 2
  needSpace : Bool := false
  deriving Repr

def nl : String := "\n"

def PPState.emit (s : String) (st : PPState) : PPState :=
  let st := if st.needSpace && !s.isEmpty && !s.startsWith " " && st.currentCol > 0
            then { st with output := st.output ++ " ", currentCol := st.currentCol + 1 }
            else st
  { st with output := st.output ++ s, currentCol := st.currentCol + s.length, needSpace := false }

def PPState.newline (st : PPState) : PPState :=
  let indent := String.mk (List.replicate (st.indentLevel * st.indentSize) ' ')
  { st with output := st.output ++ nl ++ indent, currentCol := indent.length, needSpace := false }

def PPState.indent (st : PPState) : PPState :=
  { st with indentLevel := st.indentLevel + 1 }

def PPState.dedent (st : PPState) : PPState :=
  { st with indentLevel := if st.indentLevel > 0 then st.indentLevel - 1 else 0 }

def PPState.space (st : PPState) : PPState :=
  { st with needSpace := true }

def PPState.noSpace (st : PPState) : PPState :=
  { st with needSpace := false }

/-! ## Layout Annotations -/

/-- Layout commands extracted from grammar -/
inductive LayoutCmd
  | text : String → LayoutCmd
  | ref : String → LayoutCmd   -- Reference to a sub-production
  | nl : LayoutCmd
  | indent : LayoutCmd
  | dedent : LayoutCmd
  | space : LayoutCmd
  | noSpace : LayoutCmd
  | star : LayoutCmd → LayoutCmd    -- Zero or more
  | plus : LayoutCmd → LayoutCmd    -- One or more
  | opt : LayoutCmd → LayoutCmd     -- Optional
  | seq : List LayoutCmd → LayoutCmd
  deriving Repr, Inhabited

/-- Grammar production with layout info -/
structure PrettyProduction where
  name : String              -- Production name (e.g., "inductiveDecl")
  layout : List LayoutCmd    -- Layout commands in order
  deriving Repr

/-! ## Extract Layout from Grammar AST -/

/-- Check if a term is a layout annotation (@nl, @indent, @dedent, @sp, @nsp) -/
def isLayoutCmd (t : Term) : Option LayoutCmd :=
  match t with
  -- Layout annotations from grammar (constructor form)
  | .con "layoutNl" _ => some .nl
  | .con "layoutIndent" _ => some .indent
  | .con "layoutDedent" _ => some .dedent
  | .con "layoutSpace" _ => some .space
  | .con "layoutNoSpace" _ => some .noSpace
  -- Also recognize @-prefixed atoms in raw grammar
  | .con "ident" [.var "@nl"] => some .nl
  | .con "ident" [.var "@indent"] => some .indent
  | .con "ident" [.var "@dedent"] => some .dedent
  | .con "ident" [.var "@sp"] => some .space
  | .con "ident" [.var "@nsp"] => some .noSpace
  | .var "@nl" => some .nl
  | .var "@indent" => some .indent
  | .var "@dedent" => some .dedent
  | .var "@sp" => some .space
  | .var "@nsp" => some .noSpace
  | _ => none

/-- Convert grammar expr to layout commands -/
partial def grammarExprToLayout (t : Term) : List LayoutCmd :=
  -- First check if it's a layout annotation
  match isLayoutCmd t with
  | some cmd => [cmd]
  | none =>
    match t with
    | .con "annotated" [body, .con "ident" [.var _]] =>
      -- This is a named production - the body has the layout
      grammarExprToLayout body
    | .con "seq" args =>
      args.flatMap grammarExprToLayout
    | .con "lit" [.lit s] =>
      [.text (s.replace "\"" "")]
    | .con "ref" [.con "ident" [.var name]] =>
      [.ref name]
    | .con "star" [inner] =>
      [.star (.seq (grammarExprToLayout inner))]
    | .con "plus" [inner] =>
      [.plus (.seq (grammarExprToLayout inner))]
    | .con "opt" [inner] =>
      [.opt (.seq (grammarExprToLayout inner))]
    | .con "alt" [l, _, r] =>
      -- For alternatives, just take the first (simplification)
      grammarExprToLayout l
    | .con _ args =>
      args.flatMap grammarExprToLayout
    | .var name =>
      -- Check for @-prefixed layout
      if name.startsWith "@" then
        match isLayoutCmd t with
        | some cmd => [cmd]
        | none => [.ref name]
      else [.ref name]
    | .lit s => [.text s]

/-- Extract named productions from grammar -/
partial def extractProductions (t : Term) : List PrettyProduction :=
  match t with
  | .con "DGrammar" args =>
    -- Grammar: name ::= body → prodName
    extractFromBody args
  | .con "DPiece" args => args.flatMap extractProductions
  | .con "DLang" args => args.flatMap extractProductions
  | .con "seq" ts => ts.flatMap extractProductions
  | .con _ args => args.flatMap extractProductions
  | _ => []
where
  extractFromBody (args : List Term) : List PrettyProduction :=
    -- Parse: ident ::= expr → prodName
    match args.filter (· != .lit "::=") |>.filter (· != .lit ";") with
    | .con "ident" [.var grammarName] :: bodyParts =>
      extractAlternatives grammarName bodyParts
    | _ => []

  extractAlternatives (grammarName : String) (body : List Term) : List PrettyProduction :=
    body.flatMap fun b => extractAlt grammarName b

  extractAlt (grammarName : String) (t : Term) : List PrettyProduction :=
    match t with
    | .con "annotated" [body, .con "ident" [.var prodName]] =>
      let layout := grammarExprToLayout body
      [{ name := prodName, layout := layout }]
    | .con "alt" [l, _, r] =>
      extractAlt grammarName l ++ extractAlt grammarName r
    | _ => []

/-! ## Extract Transformation Rules -/

/-- Transformation rule: name, pattern, template -/
structure TransformRule where
  name : String
  pattern : Term
  template : Term
  deriving Repr

/-- Extract transformation rules from rosetta2<L>.lego -/
partial def extractTransformRules (t : Term) : List TransformRule :=
  match t with
  | .con "DRule" args =>
    let filtered := args.filter (· != .lit "rule")
                       |>.filter (· != .lit ":")
                       |>.filter (· != .lit "~>")
                       |>.filter (· != .lit "~~>")
                       |>.filter (· != .lit ";")
                       |>.filter (· != .con "unit" [])
    match filtered with
    | .con "ident" [.var name] :: rest =>
      match rest with
      | [pat, tmpl] => [{ name, pattern := pat, template := tmpl }]
      | [pat] => [{ name, pattern := pat, template := pat }]
      | _ => []
    | _ => []
  | .con "DPiece" args => args.flatMap extractTransformRules
  | .con "DLang" args => args.flatMap extractTransformRules
  | .con "seq" ts => ts.flatMap extractTransformRules
  | .con _ args => args.flatMap extractTransformRules
  | _ => []

/-! ## Apply Transformations -/

/-- Simple pattern unification -/
partial def unifyPattern (pat : Term) (t : Term) (env : List (String × Term))
    : Option (List (String × Term)) :=
  match pat, t with
  | .var n, _ =>
    if n.startsWith "$" then
      some ((n.drop 1, t) :: env)
    else if n == "_" then
      some env
    else
      match t with
      | .var m => if n == m then some env else none
      | _ => none
  | .lit s1, .lit s2 => if s1 == s2 then some env else none
  | .con n1 args1, .con n2 args2 =>
    if n1 == n2 && args1.length == args2.length then
      args1.zip args2 |>.foldlM (fun e (p, t) => unifyPattern p t e) env
    else none
  | _, _ => none

/-- Substitute variables in template -/
partial def substituteTemplate (tmpl : Term) (env : List (String × Term)) : Term :=
  match tmpl with
  | .var n =>
    if n.startsWith "$" then
      match env.find? (·.1 == n.drop 1) with
      | some (_, t) => t
      | none => tmpl
    else tmpl
  | .con name args => .con name (args.map (substituteTemplate · env))
  | _ => tmpl

/-- Apply transformation rules to AST -/
partial def applyTransforms (rules : List TransformRule) (t : Term) : Term :=
  -- Try each rule
  match rules.findSome? (fun r =>
    match unifyPattern r.pattern t {} with
    | some env => some (substituteTemplate r.template env)
    | none => none
  ) with
  | some result => applyTransforms rules result
  | none =>
    -- No rule matched, recurse
    match t with
    | .con name args => .con name (args.map (applyTransforms rules))
    | _ => t

/-! ## Grammar-Driven Pretty-Printer -/

/-- Pretty-print using grammar layout -/
partial def prettyPrint (prods : List PrettyProduction) (t : Term) : String :=
  (go t {}).output
where
  go (t : Term) (st : PPState) : PPState :=
    match t with
    | .var n => st.emit n |>.space
    | .lit s => st.emit s |>.space
    | .con name args =>
      -- Look up production for this constructor
      match prods.find? (·.name == name) with
      | some prod => applyLayout prod.layout args st
      | none =>
        -- Default: emit constructor name and args
        let st := st.emit name |>.space
        args.foldl (fun s a => go a s) st

  applyLayout (cmds : List LayoutCmd) (_args : List Term) (st : PPState) : PPState :=
    cmds.foldl (fun s cmd => applyCmd cmd _args s) st

  applyCmd (cmd : LayoutCmd) (_args : List Term) (st : PPState) : PPState :=
    match cmd with
    | .text t => st.emit t |>.space
    | .ref _name =>
      -- Find matching arg by trying to match production names
      -- Simplified: just print next arg
      st  -- TODO: proper arg matching
    | .nl => st.newline
    | .indent => st.indent
    | .dedent => st.dedent
    | .space => st.space
    | .noSpace => st.noSpace
    | .star _inner => st  -- TODO: handle repetition
    | .plus _inner => st  -- TODO: handle repetition
    | .opt _inner => st   -- TODO: handle optional
    | .seq cmds => cmds.foldl (fun s c => applyCmd c _args s) st

/-! ## Main Pipeline -/

/-- Pipeline result -/
structure TargetResult where
  lang : TargetLang
  code : String
  outPath : String
  deriving Repr

/-- Run grammar-driven pipeline for one target -/
def runForTarget (rt : Runtime) (sourceAst : Term) (lang : TargetLang) (outDir : String)
    : IO (Except String TargetResult) := do
  -- 1. Load grammar file - contains both syntax AND layout annotations
  IO.println s!"  Loading {lang} grammar..."
  let grammarAst ← match ← parseLegoFilePathE rt lang.grammarPath with
    | .error e => return .error s!"Failed to load grammar: {e}"
    | .ok ast => pure ast
  let prods := extractProductions grammarAst
  IO.println s!"    Found {prods.length} productions (with layout annotations)"

  -- 2. Load transformation rules (rosetta2<L>.lego)
  IO.println s!"  Loading transformation rules..."
  let transformAst ← match ← parseLegoFilePathE rt lang.transformPath with
    | .error _ =>
      IO.println s!"    Warning: No transform file, using source AST directly"
      pure sourceAst
    | .ok ast => pure ast
  let rules := extractTransformRules transformAst
  IO.println s!"    Found {rules.length} rules"

  -- 3. Apply transformations
  let transformed := if rules.isEmpty then sourceAst else applyTransforms rules sourceAst

  -- 4. Pretty-print using grammar layout annotations
  let code := prettyPrint prods transformed

  -- 5. Build result
  let moduleName := "Generated"  -- TODO: extract from source
  let outPath := s!"{outDir}/{moduleName}{lang.ext}"

  return .ok { lang, code, outPath }

/-- Run pipeline for all targets -/
def runGrammarDrivenPipeline (rt : Runtime) (sourcePath : String)
    (targets : List TargetLang := [.Lean, .Scala, .Haskell, .Rust])
    (outDir : String := "./generated/Rosetta")
    : IO (Except String (List TargetResult)) := do

  IO.println "═══════════════════════════════════════════════════════════════"
  IO.println "Grammar-Driven Rosetta Pipeline"
  IO.println "═══════════════════════════════════════════════════════════════"

  -- Parse source
  IO.println s!"[1] Parsing source: {sourcePath}"
  let sourceAst ← match ← parseLegoFilePathE rt sourcePath with
    | .error e => return .error s!"Failed to parse source: {e}"
    | .ok ast => pure ast
  IO.println "    ✓ Parsed"

  -- Generate for each target
  IO.println s!"[2] Generating for {targets.length} targets..."
  let mut results : List TargetResult := []
  for lang in targets do
    IO.println s!"  → {lang}..."
    match ← runForTarget rt sourceAst lang outDir with
    | .error e => IO.println s!"    ✗ {e}"
    | .ok r =>
      results := results ++ [r]
      IO.println s!"    ✓ {r.code.length} chars"

  -- Write files
  IO.println "[3] Writing files..."
  IO.FS.createDirAll outDir
  for r in results do
    IO.FS.writeFile r.outPath r.code
    IO.println s!"    ✓ {r.outPath}"

  return .ok results

/-! ## Main -/

def main (args : List String) : IO Unit := do
  let sourcePath := args.getD 0 "./examples/Arith.lego"
  let outDir := args.getD 1 "./generated/Rosetta"

  let rt ← Lego.Runtime.init

  match ← runGrammarDrivenPipeline rt sourcePath [.Lean, .Scala, .Haskell, .Rust] outDir with
  | .error e => IO.eprintln s!"✗ {e}"
  | .ok results =>
    IO.println ""
    IO.println s!"✓ Generated {results.length} files"
