/-
  GenericPrettyPrinter.lean
  Grammar-driven pretty-printing for any target language.

  The pretty-printer reads layout annotations from grammar rules
  and uses them to format AST nodes. This replaces hardcoded
  language-specific generators like genScalaFunction.

  Architecture:
    1. Source .lego → parse → Rosetta IR (AST)
    2. Rosetta IR + rosetta2<L>.lego → transform → <L> AST
    3. <L> AST + <L>.lego (with layout) → pretty-print → code string

  Layout annotations in grammar:
    @nl      - newline + indent
    @indent  - increase indent level
    @dedent  - decrease indent level
    @sp      - space
    @nsp     - no space (suppress auto-space)
-/

import Lego.Runtime
import Lego.Loader

open Lego.Runtime
open Lego.Loader
open Lego

/-! ## Pretty-Printer State -/

/-- Pretty-printer configuration -/
structure PPConfig where
  indentSize : Nat := 2        -- Spaces per indent level
  maxLineWidth : Nat := 100    -- Target line width
  deriving Repr, Inhabited

/-- Pretty-printer state -/
structure PPState where
  output : String := ""
  indentLevel : Nat := 0
  currentCol : Nat := 0
  config : PPConfig := {}
  deriving Repr

/-- Emit string without newline -/
def emit (s : String) (st : PPState) : PPState :=
  { st with output := st.output ++ s, currentCol := st.currentCol + s.length }

/-- Emit newline and indent -/
def newline (st : PPState) : PPState :=
  let indent := String.mk (List.replicate (st.indentLevel * st.config.indentSize) ' ')
  { st with output := st.output ++ "\n" ++ indent, currentCol := indent.length }

/-- Increase indent level -/
def indent (st : PPState) : PPState :=
  { st with indentLevel := st.indentLevel + 1 }

/-- Decrease indent level -/
def dedent (st : PPState) : PPState :=
  { st with indentLevel := if st.indentLevel > 0 then st.indentLevel - 1 else 0 }

/-- Emit space -/
def space (st : PPState) : PPState := emit " " st

/-! ## Layout Annotations Parser -/

/-- Layout command extracted from AST -/
inductive LayoutCmd
  | text : String → LayoutCmd     -- Raw text
  | newline : LayoutCmd           -- @nl
  | indent : LayoutCmd            -- @indent
  | dedent : LayoutCmd            -- @dedent
  | space : LayoutCmd             -- @sp
  | noSpace : LayoutCmd           -- @nsp
  | group : List LayoutCmd → LayoutCmd  -- @group
  deriving Repr, Inhabited

/-- Check if term is a layout annotation -/
def isLayoutAnnotation (t : Term) : Option LayoutCmd :=
  match t with
  | .con "newline" [] => some .newline
  | .con "indent" [] => some .indent
  | .con "dedent" [] => some .dedent
  | .con "space" [] => some .space
  | .con "noSpace" [] => some .noSpace
  | .var "@nl" => some .newline
  | .var "@indent" => some .indent
  | .var "@dedent" => some .dedent
  | .var "@sp" => some .space
  | .var "@nsp" => some .noSpace
  | _ => none

/-! ## Grammar-Driven Pretty-Printer -/

/-- Production rule with layout information -/
structure PrettyRule where
  name : String                -- Production name (e.g., "defDecl")
  pattern : List String        -- Keywords/symbols in order
  layout : List LayoutCmd      -- Layout commands
  deriving Repr

/-- Extract pretty-printing rules from a grammar definition -/
partial def extractPrettyRules (t : Term) : List PrettyRule :=
  match t with
  | .con "DGrammar" args =>
    -- Parse grammar alternative → productionName
    extractFromGrammar args
  | .con "DPiece" args => args.flatMap extractPrettyRules
  | .con "DLang" args => args.flatMap extractPrettyRules
  | .con "seq" ts => ts.flatMap extractPrettyRules
  | .con _ args => args.flatMap extractPrettyRules
  | _ => []
where
  extractFromGrammar (args : List Term) : List PrettyRule :=
    -- TODO: Parse grammar rules and extract layout info
    []

/-- Generic AST to string printer using grammar rules -/
partial def prettyPrint (rules : List PrettyRule) (t : Term) : String :=
  let st := go t {}
  st.output
where
  go (t : Term) (st : PPState) : PPState :=
    match t with
    | .var n => emit n st
    | .lit s => emit s st
    | .con name args =>
      -- Look up rule for this constructor
      match rules.find? (·.name == name) with
      | some rule => applyRule rule args st
      | none =>
        -- Default: print constructor and args
        let st := emit name st
        args.foldl (fun s a => go a (space s)) st

  applyRule (rule : PrettyRule) (args : List Term) (st : PPState) : PPState :=
    -- Apply layout commands from the rule
    rule.layout.foldl (fun s cmd =>
      match cmd with
      | .text t => emit t s
      | .newline => newline s
      | .indent => indent s
      | .dedent => dedent s
      | .space => space s
      | .noSpace => s
      | .group cmds => cmds.foldl applyLayoutCmd s
    ) st

  applyLayoutCmd (st : PPState) (cmd : LayoutCmd) : PPState :=
    match cmd with
    | .text t => emit t st
    | .newline => newline st
    | .indent => indent st
    | .dedent => dedent st
    | .space => space st
    | .noSpace => st
    | .group cmds => cmds.foldl applyLayoutCmd st

/-! ## Default Pretty-Printer for Common Constructs -/

/-- Default pretty-printing rules for common patterns -/
def defaultPrettyRules : List PrettyRule := [
  -- Inductive type
  { name := "inductiveDecl"
    pattern := ["inductive", "ident", "where"]
    layout := [.text "inductive ", .text "$1", .text " where", .newline, .indent] },
  -- Constructor
  { name := "ctor"
    pattern := ["|", "ident", ":", "term"]
    layout := [.text "| ", .text "$1", .text " : ", .text "$2", .newline] },
  -- Definition
  { name := "defDecl"
    pattern := ["def", "ident", ":=", "term"]
    layout := [.text "def ", .text "$1", .text " :=", .newline, .indent, .text "$2", .dedent, .newline] },
  -- Function application
  { name := "app"
    pattern := ["term", "term"]
    layout := [.text "$1", .space, .text "$2"] },
  -- Lambda
  { name := "lam"
    pattern := ["fun", "binder", "=>", "term"]
    layout := [.text "fun ", .text "$1", .text " => ", .text "$2"] }
]

/-! ## Transform + Pretty-Print Pipeline -/

/-- Apply transformation rules from rosetta2<L>.lego to an AST -/
partial def applyTransformRules (rules : List (String × Term × Term)) (t : Term) : Term :=
  -- First, try to match any rule
  match rules.findSome? (fun (_, pat, tmpl) => matchAndSubst pat tmpl t) with
  | some result => applyTransformRules rules result  -- Keep transforming
  | none =>
    -- No rule matched, recurse into children
    match t with
    | .con name args => .con name (args.map (applyTransformRules rules))
    | _ => t
where
  -- Simple pattern matching with substitution
  matchAndSubst (pat : Term) (tmpl : Term) (t : Term) : Option Term :=
    match unify pat t {} with
    | some env => some (substitute tmpl env)
    | none => none

  -- Unification: match pattern against term, collect bindings
  unify (pat : Term) (t : Term) (env : List (String × Term)) : Option (List (String × Term)) :=
    match pat, t with
    | .var n, _ =>
      if n.startsWith "$" then
        -- Meta-variable: bind to term
        some ((n.drop 1, t) :: env)
      else if n == "_" then
        some env  -- Wildcard matches anything
      else
        -- Literal variable: must match exactly
        match t with
        | .var m => if n == m then some env else none
        | _ => none
    | .lit s1, .lit s2 => if s1 == s2 then some env else none
    | .con n1 args1, .con n2 args2 =>
      if n1 == n2 && args1.length == args2.length then
        args1.zip args2 |>.foldlM (fun e (p, t) => unify p t e) env
      else none
    | _, _ => none

  -- Substitute variables in template
  substitute (tmpl : Term) (env : List (String × Term)) : Term :=
    match tmpl with
    | .var n =>
      if n.startsWith "$" then
        match env.find? (·.1 == n.drop 1) with
        | some (_, t) => t
        | none => tmpl
      else tmpl
    | .con name args => .con name (args.map (substitute · env))
    | _ => tmpl

/-! ## Main: Transform + Print -/

/-- Full pipeline: transform AST using rules, then pretty-print -/
def transformAndPrint (transformRules : List (String × Term × Term))
                       (prettyRules : List PrettyRule)
                       (ast : Term) : String :=
  let transformed := applyTransformRules transformRules ast
  prettyPrint prettyRules transformed
