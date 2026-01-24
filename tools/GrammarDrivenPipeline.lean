/-
  GrammarDrivenPipeline.lean
  Code generation driven by grammar rules, not hardcoded generators.

  IDEAL ARCHITECTURE:
    1. source.rosetta → parse → Rosetta IR (AST)
    2. Load <L>.lego grammar → extract layout rules
    3. Load rosetta2<L>.lego → extract transformation rules
    4. Rosetta IR + transform rules → <L> AST
    5. <L> AST + grammar layout → pretty-print → code string

  CURRENT STATE:
    The transform rules in rosetta2<L>.lego define the mapping from Rosetta
    nodes (adtDef, constr, rewriteRule) to target nodes (inductiveDecl,
    sealedTrait, dataDecl, enumItem).

    However, the current Lego parser doesn't support layout annotations
    (@nl, @indent, @dedent) in grammar productions. Until the parser is
    extended, the target-specific pretty-printing logic lives here as
    Lean code (goConstrs, goScalaConstrs, goHaskellConstrs, goRustConstrs).

  TO MAKE FULLY DECLARATIVE:
    1. Extend Lego parser to recognize @nl, @indent, @dedent, @sp, @nsp
       as grammar tokens (not just comments)
    2. Update <L>.lego files with layout annotations:
       ctor ::= "|" <ident> ":" term @nl → ctor ;
    3. Implement grammar-driven pretty-printer that applies layout
       commands extracted from grammar productions
    4. Remove hardcoded handlers from this file

  FILE STRUCTURE FOR TARGET LANGUAGES:
    - src/Rosetta/<L>.lego        - Target grammar (AST definition)
    - src/Rosetta/rosetta2<L>.lego - Transform rules (Rosetta → Target)
-/

import Lego.Runtime
import Lego.Loader
import Rosetta.CodeGen
import Rosetta.UnifiedCodeGen

open Lego.Runtime
open Lego.Loader
open Lego
open CodeGen

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

/-- Convert to UnifiedCodeGen.TargetLang for unified code generation -/
def TargetLang.toUnified : TargetLang → UnifiedCodeGen.TargetLang
  | .Lean => .Lean
  | .Scala => .Scala
  | .Haskell => .Haskell
  | .Rust => .Rust

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

partial def LayoutCmd.toString : LayoutCmd → String
  | .text s => s!"\"{s}\""
  | .ref s => s!"<{s}>"
  | .nl => "@nl"
  | .indent => "@indent"
  | .dedent => "@dedent"
  | .space => "@sp"
  | .noSpace => "@nsp"
  | .star c => s!"({c.toString})*"
  | .plus c => s!"({c.toString})+"
  | .opt c => s!"({c.toString})?"
  | .seq cs => cs.map LayoutCmd.toString |> " ".intercalate

instance : ToString LayoutCmd := ⟨LayoutCmd.toString⟩

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
      -- Strip all quotes from the literal
      let clean := s.replace "\"" "" |>.replace "'" ""
      [.text clean]
    | .con "lit" [.var s] =>
      let clean := s.replace "\"" "" |>.replace "'" ""
      [.text clean]
    | .lit s =>
      let clean := s.replace "\"" "" |>.replace "'" ""
      if clean.isEmpty then [] else [.text clean]
    | .con "ref" [.con "ident" [.var name]] =>
      [.ref name]
    | .con "star" [inner] =>
      [.star (.seq (grammarExprToLayout inner))]
    | .con "plus" [inner] =>
      [.plus (.seq (grammarExprToLayout inner))]
    | .con "opt" [inner] =>
      [.opt (.seq (grammarExprToLayout inner))]
    | .con "alt" [l, _, _r] =>
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

/-- Get constructor name for debug -/
def Term.ctorDbg : Term → String
  | .con n _ => n
  | .var n => s!"var:{n}"
  | .lit s => s!"lit:{s}"

/-- Collect all DGrammar nodes from AST -/
partial def collectDGrammars (t : Term) : List Term :=
  match t with
  | .con "DGrammar" _ => [t]
  | .con _ args => args.flatMap collectDGrammars
  | _ => []

/-- Extract named productions from grammar (no debug version) -/
partial def extractProductions (t : Term) (_debug : Bool := false) : List PrettyProduction :=
  match t with
  | .con "DGrammar" args =>
    extractFromBody args
  | .con "DPiece" args =>
    args.flatMap (extractProductions ·)
  | .con "DLang" args =>
    args.flatMap (extractProductions ·)
  | .con "seq" ts =>
    ts.flatMap (extractProductions ·)
  | .con _ args =>
    args.flatMap (extractProductions ·)
  | _ => []
where
  extractFromBody (args : List Term) : List PrettyProduction :=
    let filtered := args.filter (· != .lit "::=") |>.filter (· != .lit ";")
    match filtered with
    | .con "ident" [.var _grammarName] :: bodyParts =>
      extractAlternatives bodyParts
    | _ => []

  extractAlternatives (body : List Term) : List PrettyProduction :=
    body.flatMap extractAlt

  extractAlt (t : Term) : List PrettyProduction :=
    match t with
    -- Pattern: (annotated body... "→" (ident prodName))
    | .con "annotated" args =>
      -- Last arg should be (ident prodName), second-to-last is "→"
      match args.reverse with
      | .con "ident" [.var prodName] :: .lit "→" :: bodyParts =>
        let layout := bodyParts.reverse.flatMap grammarExprToLayout
        [{ name := prodName, layout := layout }]
      | _ => []
    | .con "alt" [l, _, r] =>
      extractAlt l ++ extractAlt r
    | _ => []

/-! ## Extract Transformation Rules -/

/-- Rule annotation kind: entry point, file-level, expression, type, declaration -/
inductive RuleAnnot
  | entry  -- Entry point for whole file/module transformation
  | file   -- Handles file-level constructs
  | expr   -- Handles expressions
  | type   -- Handles types
  | decl   -- Handles declarations
  | none   -- No annotation (regular rule)
  deriving Repr, BEq

/-- Transformation rule: name, pattern, template, annotation -/
structure TransformRule where
  name : String
  pattern : Term
  template : Term
  annot : RuleAnnot := .none
  deriving Repr

/-- Convert parsed pattern/template AST to Term
    The Bootstrap grammar parses (toLean Univ) as:
      (con "(" (ident toLean) (con (ident Univ)) ")")
    We need to convert it to:
      (con "toLean" [(con "Univ" [])])

    Pattern variables like $x are parsed as:
      (var "$" (ident x))  or  (var "$" x)
    We convert to:
      .var "$x"
-/
partial def parsedToTerm (t : Term) : Term :=
  match t with
  -- Rosetta grammar: metavar ["$", "x"] → .var "$x"
  | .con "metavar" [.lit "$", .lit name] => .var s!"${name}"
  | .con "metavar" [.lit "$", .var name] => .var s!"${name}"
  | .con "metavar" [.var "$", .con "ident" [.var name]] => .var s!"${name}"
  | .con "metavar" [.lit "$", .con "ident" [.var name]] => .var s!"${name}"
  | .con "metavar" args =>
    match args with
    | [_, nameT] =>
      let name := match nameT with
        | .var n => n
        | .lit n => n
        | .con "ident" [.var n] => n
        | .con "ident" [.lit n] => n
        | _ => "unknown"
      .var s!"${name}"
    | _ => t

  -- Rosetta grammar: compound ["(", "Con", arg1, ..., ")"] → .con "Con" [arg1', ...]
  | .con "compound" args =>
    let filtered := args.filter (fun a => a != .lit "(" && a != .lit ")")
    match filtered with
    | [] => .con "unit" []
    | [single] => parsedToTerm single
    | first :: rest =>
      let conName := match first with
        | .var n => n
        | .lit n => n
        | .con "ident" [.var n] => n
        | .con "ident" [.lit n] => n
        | _ => "app"
      .con conName (rest.map parsedToTerm)

  -- Rosetta grammar: binder [name, ".", body]
  -- Note: Do NOT add $ prefix to binder variables - these are lambda parameter names
  | .con "binder" args =>
    let filtered := args.filter (· != .lit ".")
    match filtered with
    | [nameT, body] =>
      let varName := match nameT with
        | .var n => n                            -- Keep as-is, no $ prefix
        | .lit n => n                            -- Keep as-is, no $ prefix
        | .con "ident" [.var n] => n             -- Keep as-is, no $ prefix
        | .con "metavar" [_, .con "ident" [.var n]] => s!"${n}"  -- Actual metavar gets $
        | .con "metavar" [_, .var n] => s!"${n}"                  -- Actual metavar gets $
        | _ => "x"                               -- Fallback plain name
      .con "binder" [.var varName, parsedToTerm body]
    | [.con "ident" [.var n], .lit ".", body] =>
      .con "binder" [.var n, parsedToTerm body]  -- No $ prefix for lambda params
    | _ => .con "binder" (args.map parsedToTerm)

  -- Pattern variable: $x → .var "$x"
  -- Bootstrap parses "$x" as (var "$" (ident x)) or (var "$" x)
  | .con "var" [.lit "$", .con "ident" [.var name]] => .var s!"${name}"
  | .con "var" [.lit "$", .var name] => .var s!"${name}"
  | .con "var" [.con "ident" [.var name]] => .var s!"${name}"
  | .con "var" [.var name] => .var s!"${name}"

  -- TypedVar: $x : ty → expand to [.var "$x", .lit ":", ty]
  -- This is used to flatten typedVars in con arguments
  | .con "typedVar" args =>
    match args with
    | [.lit "$", .con "ident" [.var name], .lit ":", ty] =>
      -- Return a marker that the con handler can flatten
      .con "_typedVar_" [.var s!"${name}", .lit ":", parsedToTerm ty]
    | [.lit "$", .var name, .lit ":", ty] =>
      .con "_typedVar_" [.var s!"${name}", .lit ":", parsedToTerm ty]
    | _ => .con "typedVar" (args.map parsedToTerm)

  -- Constructor: (name args...)
  | .con "con" args =>
    -- Filter out literal parens
    let filtered := args.filter (· != .lit "(") |>.filter (· != .lit ")")
    -- Check if it's a single operator like "->", ":", etc. - no children means just an operator
    match filtered with
    | [] => .con "unit" []  -- empty parens
    | [.con "ident" [.var op]] =>
      -- Single identifier - check if it's an operator
      if op ∈ ["->", "→", ":", "~~>", "~>", "|", "×", "↦", "@@", "=I="] then
        .lit op
      else
        .con op []
    | [.var op] =>
      if op ∈ ["->", "→", ":", "~~>", "~>", "|", "×", "↦", "@@", "=I="] then
        .lit op
      else
        .con op []
    -- Handle (con "->") pattern - parsed as [ident "con", lit "->"] or similar
    | [.con "ident" [.var "con"], .lit op] =>
      if op ∈ ["->", "→", ":", "~~>", "~>", "|", "×", "↦", "@@", "=I="] then
        .lit op
      else
        .con "con" [.lit op]
    | [.con "ident" [.lit "con"], .lit op] =>
      if op ∈ ["->", "→", ":", "~~>", "~>", "|", "×", "↦", "@@", "=I="] then
        .lit op
      else
        .con "con" [.lit op]
    | [.var "con", .lit op] =>
      if op ∈ ["->", "→", ":", "~~>", "~>", "|", "×", "↦", "@@", "=I="] then
        .lit op
      else
        .con "con" [.lit op]
    -- Handle single literal like "->"
    | [.lit op] =>
      if op ∈ ["->", "→", ":", "~~>", "~>", "|", "×", "↦", "@@", "=I="] then
        .lit op
      else
        .con "con" [.lit op]
    | _ =>
      -- Flatten any typedVar constructs
      let flattened := filtered.flatMap fun arg =>
        let t := parsedToTerm arg
        match t with
        | .con "_typedVar_" children => children
        | other => [other]
      match flattened with
      | [] => .con "unit" []
      | (.con "ident" [.var name]) :: rest =>
        .con name rest
      | (.var name) :: rest =>
        .con name rest
      | (.con name []) :: rest =>
        -- If the name is an operator, convert to literal
        if name ∈ ["->", "→", ":", "~~>", "~>", "|", "×", "↦", "@@", "=I="] then
          if rest.isEmpty then .lit name
          else .con "_seq_" ([.lit name] ++ rest)
        else
          .con name rest
      | _ => .con "con" flattened

  -- Identifier alone becomes a constructor with no args
  | .con "ident" [.var name] => .con name []
  | .con "ident" [.lit name] => .con name []

  -- Literals
  | .lit s => .lit s
  -- Bare identifiers (not metavars with $) become 0-argument constructors
  -- e.g., `isoId` in pattern `isoId ~> ...` becomes `.con "isoId" []`
  | .var n =>
    if n.startsWith "$" then .var n  -- Keep metavars as-is
    else .con n []  -- Bare idents become 0-arg constructors

  -- Operators as constructors (no args) - convert to literals
  | .con "->" [] => .lit "->"
  | .con "→" [] => .lit "→"
  | .con ":" [] => .lit ":"
  | .con "~~>" [] => .lit "~~>"
  | .con "~>" [] => .lit "~>"
  | .con "|" [] => .lit "|"
  | .con "×" [] => .lit "×"
  | .con "↦" [] => .lit "↦"
  | .con "@@" [] => .lit "@@"
  | .con "=I=" [] => .lit "=I="

  -- Recurse into other constructors
  | .con name args =>
    -- debug removed
    .con name (args.map parsedToTerm)

/-- Parse annotation from AST
    Actual structure is (annot "@" (file "file")) which parses to:
    .con "annot" [.lit "@", .con "file" [.lit "file"]] -/
def parseAnnot (t : Term) : RuleAnnot :=
  match t with
  -- Handle actual parsed structure: (annot "@" (kind "kind"))
  | .con "annot" [.lit "@", .con "entry" _] => .entry
  | .con "annot" [.lit "@", .con "file" _] => .file
  | .con "annot" [.lit "@", .con "expr" _] => .expr
  | .con "annot" [.lit "@", .con "type" _] => .type
  | .con "annot" [.lit "@", .con "decl" _] => .decl
  -- Also handle simpler structure just in case
  | .con "annot" [.con "entry" _] => .entry
  | .con "annot" [.con "file" _] => .file
  | .con "annot" [.con "expr" _] => .expr
  | .con "annot" [.con "type" _] => .type
  | .con "annot" [.con "decl" _] => .decl
  | _ => .none

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
    -- Check for annotation at start
    let (annot, rest) := match filtered with
      | (.con "annot" annotArgs) :: r => (parseAnnot (.con "annot" annotArgs), r)
      | r => (RuleAnnot.none, r)
    match rest with
    | .con "ident" [.var name] :: patTmpl =>
      match patTmpl with
      | [pat, tmpl] =>
        let pat' := parsedToTerm pat
        let tmpl' := parsedToTerm tmpl
        [{ name, pattern := pat', template := tmpl', annot }]
      | [pat] =>
        let p := parsedToTerm pat
        [{ name, pattern := p, template := p, annot }]
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
    if n1 == n2 then
      -- Special case: if pattern ends with a metavar, it can capture remaining args
      if args1.length == args2.length then
        args1.zip args2 |>.foldlM (fun e (p, t) => unifyPattern p t e) env
      else if args1.length > 0 then
        -- Check if the last pattern element is a metavar that should capture rest
        match args1.getLast? with
        | some (.var n) =>
          if n.startsWith "$" then
            -- Pattern has fewer args and ends with metavar - bind metavar to a seq of remaining args
            let prefixLen := args1.length - 1
            if args2.length >= prefixLen then
              let patPrefix := args1.take prefixLen
              let tPrefix := args2.take prefixLen
              let tRest := args2.drop prefixLen
              -- Match the prefix
              match patPrefix.zip tPrefix |>.foldlM (fun e (p, t) => unifyPattern p t e) env with
              | some e =>
                -- Bind the trailing metavar to a seq of remaining args (or single if just 1)
                let restTerm := if tRest.length == 1 then tRest[0]! else .con "seq" tRest
                some ((n.drop 1, restTerm) :: e)
              | none => none
            else none
          else none
        | _ => none
      else none
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

/-- Convert Lego AST (DLang, DPiece, DRule) to Rosetta IR format -/
partial def legoToRosetta (t : Term) : Term :=
  match t with
  | .con "DLang" args =>
    -- DLang lang_name imports? ":=" body
    -- → seq of declarations from body
    let bodyDecls := args.flatMap extractLegoDecls
    .con "seq" bodyDecls
  | .con "DPiece" args =>
    -- DPiece "piece" name items*
    -- → seq of declarations from items
    let decls := args.flatMap extractLegoDecls
    .con "seq" decls
  | .con "DGrammar" args =>
    -- Skip grammar definitions for now
    .con "seq" []
  | .con "DRule" args =>
    -- DRule annot? "rule" name ":" pattern arrow template guard? ";"
    convertRule args
  | .con "DType" args =>
    -- DType "type" name ":" term ":" type "when" premises
    -- → type judgment (skip for now, generate comment)
    .con "comment" [.lit "-- type judgment"]
  | .con "seq" ts =>
    let converted := ts.map legoToRosetta
    let flattened := converted.flatMap (fun t =>
      match t with
      | .con "seq" inner => inner
      | _ => [t])
    .con "seq" flattened
  | .con name args =>
    .con name (args.map legoToRosetta)
  | _ => t
where
  extractLegoDecls (t : Term) : List Term :=
    match t with
    | .con "DPiece" args => args.flatMap extractLegoDecls
    | .con "DLang" args => args.flatMap extractLegoDecls
    | .con "DRule" args => [convertRule args]
    | .con "DType" _ => []  -- Skip type judgments
    | .con "DGrammar" _ => []  -- Skip grammar defs
    | .con "seq" ts => ts.flatMap extractLegoDecls
    -- Skip everything else - only emit rewrite rules
    | _ => []

  convertRule (args : List Term) : Term :=
    -- Filter out literals like "rule", ":", "~~>", ";"
    let filtered := args.filter (· != .lit "rule")
                       |>.filter (· != .lit ":")
                       |>.filter (· != .lit "~>")
                       |>.filter (· != .lit "~~>")
                       |>.filter (· != .lit ";")
                       |>.filter (· != .con "unit" [])
    -- Look for the name (ident node)
    let (name, rest) := match filtered with
      | (.con "ident" [.var n]) :: r => (n, r)
      | (.con "annot" _) :: (.con "ident" [.var n]) :: r => (n, r)
      | _ => ("unknown", filtered)
    -- rest should be [pattern, template] or [pattern, template, guard]
    match rest with
    | [pat, tmpl] =>
      -- Build a rewriteRule node in Rosetta IR format
      .con "rewriteRule" [.lit "rewrite", .var name, .lit ":", pat, .lit "~>", tmpl, .con "unit" [], .lit ";"]
    | [pat, tmpl, _guard] =>
      .con "rewriteRule" [.lit "rewrite", .var name, .lit ":", pat, .lit "~>", tmpl, .con "unit" [], .lit ";"]
    | _ => .con "comment" [.lit s!"-- rule {name} (malformed)"]

/-- Apply transformation rules to AST
    Entry-annotated rules are tried first at the top level.
    Then all rules are applied recursively. -/
partial def applyTransforms (rules : List TransformRule) (t : Term) (isTopLevel : Bool := true) : Term :=
  -- At top level, prioritize entry/file rules
  let prioritizedRules := if isTopLevel then
    let entryRules := rules.filter (fun r => r.annot == .entry || r.annot == .file)
    entryRules ++ rules.filter (fun r => r.annot != .entry && r.annot != .file)
  else rules
  -- Try each rule
  let matched := prioritizedRules.findSome? (fun r =>
    match unifyPattern r.pattern t {} with
    | some env => some (r, env, substituteTemplate r.template env)
    | none => none
  )
  match matched with
  | some (_r, _env, result) =>
    -- Only recurse if result is different (avoid infinite loop)
    if result == t then t
    else applyTransforms rules result false
  | none =>
    -- No rule matched, recurse into children
    match t with
    | .con name args => .con name (args.map (applyTransforms rules · false))
    | _ => t

/-! ## Grammar-Driven Pretty-Printer -/

/-- Pretty-print state with argument tracking -/
structure PPState' where
  output : String := ""
  indent : Nat := 0
  needSpace : Bool := false
  argIndex : Nat := 0  -- Current arg index for ref
  deriving Repr

namespace PPState'

def emit (s : PPState') (t : String) : PPState' :=
  let space := if s.needSpace && !s.output.isEmpty && !t.isEmpty then " " else ""
  { s with output := s.output ++ space ++ t, needSpace := true }

def space (s : PPState') : PPState' := { s with needSpace := true }
def noSpace (s : PPState') : PPState' := { s with needSpace := false }
def newline (s : PPState') : PPState' :=
  let ind := String.mk (List.replicate (s.indent * 2) ' ')
  { s with output := s.output ++ "\n" ++ ind, needSpace := false }
def addIndent (s : PPState') : PPState' := { s with indent := s.indent + 1 }
def dedent (s : PPState') : PPState' := { s with indent := if s.indent > 0 then s.indent - 1 else 0 }
def nextArg (s : PPState') : PPState' := { s with argIndex := s.argIndex + 1 }
def resetArgs (s : PPState') : PPState' := { s with argIndex := 0 }

end PPState'

/-- Extract module path string from DImport args -/
def extractModulePath (args : List Term) : String :=
  -- Args: ["import", (modulePath ...), ";"] or similar
  let rec go (t : Term) : String :=
    match t with
    | .var n => n
    | .lit s => if s == "import" || s == ";" || s == "." then "" else s
    | .con "modulePath" inner =>
      let parts := inner.filterMap (fun a => match a with
        | .var n => some n
        | .lit s => if s != "." then some s else none
        | .con "ident" [.var n] => some n
        | _ => none)
      parts.foldl (fun acc p => if acc.isEmpty then p else acc ++ "." ++ p) ""
    | .con "ident" [.var n] => n
    | .con _ inner => inner.map go |>.filter (!·.isEmpty) |>.foldl (fun acc p => if acc.isEmpty then p else acc ++ "." ++ p) ""
  args.map go |>.filter (!·.isEmpty) |>.head?.getD "Unknown"

/-- Check if a string is a type variable (lowercase single letter or short lowercase name) -/
def isTypeVar (s : String) : Bool :=
  !s.isEmpty && (s.get! 0).isLower && s.length <= 2

/-- Extract type variables from a type term -/
partial def collectTypeVars (t : Term) : List String :=
  match t with
  | .var n => if isTypeVar n then [n] else []
  | .lit _ => []
  | .con _ args => args.flatMap collectTypeVars |>.eraseDups

/-- Get the return type from a constructor type (the last type in arrow chain) -/
partial def getReturnType (t : Term) : Term :=
  match t with
  | .con "typeExpr" args =>
    match args with
    | [_, .lit "->", right] => getReturnType right
    | [single] => single
    | _ => t
  | _ => t

/-- Extract type parameters from ADT constructors
    Look at return types like "Iso a b" and extract [a, b] -/
def extractTypeParams (tyName : String) (constrs : List Term) : List String :=
  -- For each constructor, get its return type and extract type vars
  let allVars := constrs.flatMap fun c =>
    match c with
    | .con "constr" [_, _, ty] =>
      -- Get the return type (e.g., "Iso a b") and collect its type vars
      let retTy := getReturnType ty
      match retTy with
      | .con "typeApp" args =>
        -- Skip the type name itself, collect vars from arguments
        args.drop 1 |>.flatMap collectTypeVars
      | _ => collectTypeVars retTy
    | .con "seq" inner => inner.flatMap fun c' =>
      match c' with
      | .con "constr" [_, _, ty'] =>
        let retTy := getReturnType ty'
        match retTy with
        | .con "typeApp" args => args.drop 1 |>.flatMap collectTypeVars
        | _ => collectTypeVars retTy
      | _ => []
    | _ => []
  allVars.eraseDups

/-- Known parameterized types and their arity (for adding _ placeholders when used without args) -/
def knownPolyTypes : List (String × Nat) := [
  ("Iso", 2), ("List", 1), ("Option", 1), ("AST", 1)
]

/-! ## Rosetta AST Normalization

The Rosetta parser produces AST with structural nodes like:
  - compound ["(", "Con", arg1, arg2, ")"]  → Con "Con" [arg1', arg2']
  - metavar ["$", "x"]                       → Var "$x"
  - binder ["x", ".", body]                  → Con "binder" [Var "$x", body']

We need to normalize these before code generation.
-/

/-- Normalize Rosetta-parsed term to clean Term structure -/
partial def normalizeRosettaTerm (t : Term) : Term :=
  match t with
  -- metavar: ($ x) → Var "$x"
  | .con "metavar" [.lit "$", .lit name] => .var s!"${name}"
  | .con "metavar" [.lit "$", .var name] => .var s!"${name}"
  | .con "metavar" [.var "$", .con "ident" [.var name]] => .var s!"${name}"
  | .con "metavar" [.lit "$", .con "ident" [.var name]] => .var s!"${name}"
  | .con "metavar" args =>
    -- Fallback: try to extract name
    match args with
    | [_, nameT] =>
      let name := match nameT with
        | .var n => n
        | .lit n => n
        | .con "ident" [.var n] => n
        | .con "ident" [.lit n] => n
        | _ => "unknown"
      .var s!"${name}"
    | _ => t

  -- compound: (name args...) → Con name [normalized args]
  | .con "compound" args =>
    -- Filter out literal parens
    let filtered := args.filter (fun a => a != .lit "(" && a != .lit ")")
    match filtered with
    | [] => .con "unit" []
    | [single] => normalizeRosettaTerm single
    | first :: rest =>
      -- First element is constructor name, rest are args
      let conName := match first with
        | .var n => n
        | .lit n => n
        | .con "ident" [.var n] => n
        | .con "ident" [.lit n] => n
        | _ => "app"
      let normArgs := rest.map normalizeRosettaTerm
      .con conName normArgs

  -- binder: x . body → Con "binder" [$x, body]
  | .con "binder" args =>
    let filtered := args.filter (· != .lit ".")
    match filtered with
    | [nameT, body] =>
      let varName := match nameT with
        | .var n => s!"${n}"
        | .lit n => s!"${n}"
        | .con "ident" [.var n] => s!"${n}"
        | _ => "$x"
      .con "binder" [.var varName, normalizeRosettaTerm body]
    | [.con "ident" [.var n], .lit ".", body] =>
      .con "binder" [.var s!"${n}", normalizeRosettaTerm body]
    | _ => .con "binder" (args.map normalizeRosettaTerm)

  -- ident: just the name
  | .con "ident" [.var n] => .var n
  | .con "ident" [.lit n] => .lit n

  -- Regular constructor - recurse
  | .con name args => .con name (args.map normalizeRosettaTerm)

  -- Pass through vars and lits
  | .var n => .var n
  | .lit s => .lit s

/-- Pretty-print using grammar layout -/
partial def prettyPrint (prods : List PrettyProduction) (t : Term) (lang : TargetLang := .Lean) : String :=
  (go t { : PPState' }).output
where
  go (t : Term) (st : PPState') : PPState' :=
    match t with
    | .var n => st.emit n
    | .lit s => st.emit s
    | .con name args =>
      -- For target AST nodes (from transformation), use defaultPrint
      -- These are the constructs our transforms produce:
      let targetNodes := ["leanModule", "inductiveDecl", "whereCtors", "ctor", "arrowTy", "var",
                          "scalaFile", "sealedTrait", "caseClass",
                          "haskellModule", "dataDecl", "dataCon",
                          "rustFile", "enumDecl", "enumVariant",
                          "tyVar", "tyFun", "tyApp", "tyPath", "tyGeneric", "tyFn", "typeList", "tyAny", "unitTy"]
      if targetNodes.contains name then
        defaultPrint name args st
      else
        -- Look up production for this constructor
        match prods.find? (·.name == name) with
        | some prod =>
          -- Apply layout with args available
          applyLayout prod.layout args (st.resetArgs)
        | none =>
          -- No production found - fall back to default
          defaultPrint name args st

  -- Default printing for constructs without grammar productions
  defaultPrint (name : String) (args : List Term) (st : PPState') : PPState' :=
    match name with
    -- === Lean target nodes ===
    | "inductiveDecl" =>
      match args with
      | [tyName, ctors] =>
        let st := st.emit "inductive" |>.emit (termToString tyName) |>.emit "where" |>.newline |>.addIndent
        let st := go ctors st |>.dedent
        st.emit "deriving BEq, Repr" |>.newline
      | _ => st.emit s!"inductiveDecl({args.length})"
    | "whereCtors" =>
      args.foldl (fun s a => go a s) st
    | "ctor" =>
      match args with
      | [ctorName, ty] =>
        st.emit "|" |>.emit (termToString ctorName) |>.emit ":" |>.space |> (go ty ·) |>.newline
      | _ => st.emit s!"ctor({args.length})"
    | "arrowTy" =>
      match args with
      | [l, r] =>
        go l st |>.emit "→" |> (go r ·)
      | _ => st.emit "arrowTy?"
    | "var" =>
      match args with
      | [.var n] => st.emit n
      | [.lit s] => st.emit s
      | _ => args.foldl (fun s a => go a s) st

    -- === Scala target nodes ===
    | "scalaFile" => args.foldl (fun s a => go a s) st
    | "sealedTrait" =>
      match args with
      | [tyName, ctors] =>
        let st := st.emit "sealed trait" |>.emit (termToString tyName) |>.newline |>.newline
        go ctors st
      | _ => st.emit s!"sealedTrait({args.length})"
    | "caseClass" =>
      match args with
      | [ctorName, fields, parent] =>
        let st := st.emit "case class" |>.emit (termToString ctorName) |>.noSpace |>.emit "("
        let st := go fields st
        st.noSpace |>.emit ")" |>.emit "extends" |>.emit (termToString parent) |>.newline
      | _ => st.emit s!"caseClass({args.length})"

    -- === Haskell target nodes ===
    | "haskellModule" => args.foldl (fun s a => go a s) st
    | "dataDecl" =>
      match args with
      | [tyName, ctors] =>
        let st := st.emit "data" |>.emit (termToString tyName) |>.emit "=" |>.newline |>.addIndent
        go ctors st |>.dedent
      | _ => st.emit s!"dataDecl({args.length})"
    | "dataCon" =>
      match args with
      | [ctorName, fields] =>
        let st := st.emit "|" |>.emit (termToString ctorName)
        go fields st |>.newline
      | _ => st.emit s!"dataCon({args.length})"

    -- === Rust target nodes ===
    | "rustFile" => args.foldl (fun s a => go a s) st
    | "enumDecl" =>
      match args with
      | [tyName, variants] =>
        let st := st.emit "#[derive(Clone)]" |>.newline |>.emit "pub enum" |>.emit (termToString tyName) |>.emit "{" |>.newline |>.addIndent
        let st := go variants st
        st.dedent |>.emit "}" |>.newline
      | _ => st.emit s!"enumDecl({args.length})"
    | "enumVariant" =>
      match args with
      | [varName, fields] =>
        let st := st.emit (termToString varName)
        let st := if hasFields fields then st.noSpace |>.emit "(" |> (go fields ·) |>.noSpace |>.emit ")" else st
        st.emit "," |>.newline
      | _ => st.emit s!"enumVariant({args.length})"

    -- === Type target nodes (shared across languages) ===
    | "tyVar" =>
      match args with
      | [.var n] => st.emit n
      | [.lit s] => st.emit s
      | _ => args.foldl (fun s a => go a s) st
    | "tyFun" =>
      match args with
      | [l, r] => go l st |>.emit "→" |> (go r ·)
      | _ => st.emit "tyFun?"
    | "tyApp" =>
      match args with
      | [f, a] => go f st |>.noSpace |>.emit "[" |> (go a ·) |>.noSpace |>.emit "]"
      | _ => args.foldl (fun s a => go a s) st
    | "tyPath" =>
      match args with
      | [.var n] => st.emit n
      | [.lit s] => st.emit s
      | _ => args.foldl (fun s a => go a s) st
    | "tyGeneric" =>
      match args with
      | [f, a] => go f st |>.noSpace |>.emit "<" |> (go a ·) |>.noSpace |>.emit ">"
      | _ => args.foldl (fun s a => go a s) st
    | "tyFn" =>
      -- Rust fn type: fn(args) -> ret
      match args with
      | [argTypes, retType] =>
        st.emit "fn" |>.noSpace |>.emit "(" |> (go argTypes ·) |>.noSpace |>.emit ")" |>.emit "->" |> (go retType ·)
      | _ => st.emit "tyFn?"
    | "typeList" =>
      args.foldl (fun s a => go a s) st
    | "tyAny" => st.emit "Any"
    | "unitTy" => st.emit "()"

    -- === Import handling (per-language) ===
    | "DImport" =>
      -- Skip imports in single-file output (all definitions merged)
      -- TODO: For multi-file output, would emit proper imports
      st

    | "modulePath" =>
      -- (modulePath ident ("." ident)*)
      let parts := args.filterMap (fun a => match a with
        | .var n => some n
        | .lit s => if s != "." then some s else none
        | .con "ident" [.var n] => some n
        | _ => none)
      st.emit (parts.foldl (fun acc p => if acc.isEmpty then p else acc ++ "." ++ p) "")

    -- === Rosetta source nodes → Target-specific code generation ===
    | "leanModule" | "toLeanDecl" | "toScala" | "toHaskell" | "toRust" | "toLean" | "seq" =>
      -- Sequence nodes: just process all children
      args.foldl (fun s a => go a s) st

    | "adtDef" =>
      -- (adtDef "adt" Name "{" constrs... "}")
      -- The args are: [kw, name, lb, ...constrs, rb]
      if args.length >= 4 then
        let nameArg := args[1]!
        let tyName := match nameArg with
          | .var n => n
          | .lit s => s
          | _ => "Unknown"
        -- All middle args (from index 3 to len-2) are constructors
        let constrs := args.drop 3 |>.dropLast
        -- Extract type parameters from constructor return types
        let tyParams := extractTypeParams tyName constrs
        match lang with
        | .Lean =>
          let tyParamStr := if tyParams.isEmpty then "" else " " ++ (tyParams.map (fun p => s!"({p} : Type)") |> " ".intercalate)
          let st := st.emit "inductive" |>.emit tyName |>.emit tyParamStr |>.emit "where" |>.addIndent |>.newline
          let st := constrs.foldl (fun s c => goConstrs c s) st
          -- Check if any constructor has function parameters (-> in parameter types)
          -- Types with function fields can't derive BEq/Repr
          -- Also skip deriving for types containing certain problematic types
          let nonDerivableTypes := ["Iso", "AST"]  -- Types that can't derive BEq
          let anyHasFunctions := constrs.any (fun c =>
            match c with
            | .con "constr" [_, _, ty] =>
              let paramTypes := getParamTypes ty
              let hasArrow := paramTypes.any (fun pt => ((typeToHaskell pt).splitOn "->").length > 1)
              let hasNonDerivable := paramTypes.any (fun pt =>
                let tyStr := typeToHaskell pt
                nonDerivableTypes.any (fun nd => (tyStr.splitOn nd).length > 1))
              hasArrow || hasNonDerivable
            | _ => false)
          if anyHasFunctions then
            st.dedent |>.newline |>.newline  -- No deriving clause for types with function params
          else
            st.dedent |>.emit "deriving BEq, Repr" |>.newline |>.newline
        | .Scala =>
          let tyParamStr := if tyParams.isEmpty then "" else "[" ++ tyParams.foldl (fun acc p => if acc.isEmpty then p else acc ++ ", " ++ p) "" ++ "]"
          let st := st.emit "sealed trait" |>.emit tyName |>.noSpace |>.emit tyParamStr |>.newline |>.newline
          let st := constrs.foldl (fun s c => goScalaConstrs tyName tyParamStr c s) st
          st.newline
        | .Haskell =>
          let tyParamStr := if tyParams.isEmpty then "" else " " ++ tyParams.foldl (fun acc p => if acc.isEmpty then p else acc ++ " " ++ p) ""
          let st := st.emit "data" |>.emit tyName |>.emit tyParamStr |>.addIndent |>.newline
          -- For Haskell, first constructor uses =, rest use |
          let indexed := constrs.zip (List.range constrs.length)
          let st := indexed.foldl (fun s (c, i) => goHaskellConstrs c (i == 0) s) st
          -- Check if any constructor has function parameters (-> in type before return)
          -- Types with function fields can't derive Show/Eq
          -- Also skip deriving for types containing Iso (no Show/Eq instance)
          let nonDerivableTypes := ["Iso"]
          let anyHasFunctions := constrs.any (fun c =>
            match c with
            | .con "constr" [_, _, ty] =>
              let paramTypes := getParamTypes ty
              let hasArrow := paramTypes.any (fun pt => ((typeToHaskell pt).splitOn "->").length > 1)
              let hasNonDerivable := paramTypes.any (fun pt =>
                let tyStr := typeToHaskell pt
                nonDerivableTypes.any (fun nd => (tyStr.splitOn nd).length > 1))
              hasArrow || hasNonDerivable
            | _ => false)
          if anyHasFunctions then
            st.dedent |>.newline |>.newline  -- No deriving clause
          else
            st.dedent |>.newline |>.emit "  deriving (Show, Eq)" |>.newline |>.newline
        | .Rust =>
          -- Rust type params should be uppercase
          let rustTyParams := tyParams.map (fun p => p.capitalize)
          let tyParamStr := if rustTyParams.isEmpty then "" else "<" ++ rustTyParams.foldl (fun acc p => if acc.isEmpty then p else acc ++ ", " ++ p) "" ++ ">"
          let st := st.emit "#[derive(Clone)]" |>.newline |>.emit "pub enum" |>.emit tyName |>.noSpace |>.emit tyParamStr |>.emit "{" |>.addIndent |>.newline
          let st := constrs.foldl (fun s c => goRustConstrs tyName rustTyParams c s) st
          st.dedent |>.emit "}" |>.newline |>.newline
      else st.emit s!"-- adtDef({args.length})\n"

    | "constr" =>
      -- Forward to appropriate target handler
      match lang with
      | .Lean =>
        match args with
        | [.var ctorName, _colon, ty] =>
          st.noSpace |>.emit "|" |>.emit ctorName |>.emit ":" |> (goType ty ·) |>.newline
        | [.lit ctorName, _colon, ty] =>
          st.noSpace |>.emit "|" |>.emit ctorName |>.emit ":" |> (goType ty ·) |>.newline
        | _ => st.emit s!"-- constr({args.length})\n"
      | _ => go t st  -- Other targets handle in their specific functions

    | "rewriteRule" =>
      -- (rewriteRule "rewrite" name ":" lhs "~>" rhs guard ";")
      match args with
      | [_kw, .var name, _colon, lhs, _arrow, rhs, _guard, _semi] =>
        -- Convert the AST to our Term representation
        let lhsTerm := parsedToTerm lhs
        let rhsTerm := parsedToTerm rhs
        -- Use unified code generation via CodeGen AST
        let frag := UnifiedCodeGen.emitRewriteRule lang.toUnified name lhsTerm rhsTerm
        let code := CodeGen.render frag
        st.emit code
      | _ => st.emit s!"-- rewriteRule({args.length})\n"

    | "DTest" =>
      -- Skip tests for now
      st

    | _ =>
      -- Generic: just print args
      args.foldl (fun s a => go a s) st

  -- Process constructors for Lean (handles seq of constrs)
  goConstrs (t : Term) (st : PPState') : PPState' :=
    match t with
    | .con "seq" args => args.foldl (fun s a => goConstrs a s) st
    | .con "constr" args =>
      match args with
      | [.var ctorName, _colon, ty] =>
        st.noSpace |>.emit "|" |>.emit ctorName |>.emit ":" |> (goType ty ·) |>.newline
      | [.lit ctorName, _colon, ty] =>
        st.noSpace |>.emit "|" |>.emit ctorName |>.emit ":" |> (goType ty ·) |>.newline
      | _ => st.emit s!"-- constr({args.length})\n"
    | .lit "," => st.noSpace  -- skip comma separators
    | _ => go t st

  -- Process constructors for Scala (case classes extending sealed trait)
  goScalaConstrs (parentName : String) (tyParamStr : String) (t : Term) (st : PPState') : PPState' :=
    match t with
    | .con "seq" args => args.foldl (fun s a => goScalaConstrs parentName tyParamStr a s) st
    | .con "constr" args =>
      match args with
      | [.var ctorName, _colon, ty] =>
        -- Case class also needs type parameters if extending a parameterized trait
        st.noSpace |>.emit "case class" |>.emit ctorName |>.noSpace |>.emit tyParamStr |>.noSpace |>.emit "(" |> (goScalaType ty ·) |>.noSpace |>.emit ")" |>.emit "extends" |>.emit parentName |>.noSpace |>.emit tyParamStr |>.newline
      | [.lit ctorName, _colon, ty] =>
        st.noSpace |>.emit "case class" |>.emit ctorName |>.noSpace |>.emit tyParamStr |>.noSpace |>.emit "(" |> (goScalaType ty ·) |>.noSpace |>.emit ")" |>.emit "extends" |>.emit parentName |>.noSpace |>.emit tyParamStr |>.newline
      | _ => st.emit s!"// constr({args.length})\n"
    | .lit "," => st.noSpace
    | _ => go t st

  -- Process constructors for Haskell (data constructors)
  -- isFirst indicates whether this is the first constructor (uses = instead of |)
  goHaskellConstrs (t : Term) (isFirst : Bool) (st : PPState') : PPState' :=
    let sep := if isFirst then "=" else "|"
    match t with
    | .con "seq" args => args.foldl (fun s a => goHaskellConstrs a false s) st
    | .con "constr" args =>
      match args with
      | [.var ctorName, _colon, ty] =>
        st.emit sep |>.emit ctorName |> (goHaskellType ty ·) |>.newline
      | [.lit ctorName, _colon, ty] =>
        st.emit sep |>.emit ctorName |> (goHaskellType ty ·) |>.newline
      | _ => st.emit s!"-- constr({args.length})\n"
    | .lit "," => st.noSpace
    | _ => go t st

  -- Process constructors for Rust (enum variants)
  -- rustTyParams are already uppercased (e.g., ["A", "B"])
  goRustConstrs (adtName : String) (rustTyParams : List String) (t : Term) (st : PPState') : PPState' :=
    match t with
    | .con "seq" args => args.foldl (fun s a => goRustConstrs adtName rustTyParams a s) st
    | .con "constr" args =>
      match args with
      | [.var ctorName, _colon, ty] =>
        let hasFields := match ty with
          | .con "typeExpr" [.con "typeApp" [_]] => false  -- simple type, no fields
          | _ => true
        if hasFields then
          st.noSpace |>.emit ctorName |>.noSpace |>.emit "(" |> (goRustTypeBoxed adtName rustTyParams ty ·) |>.noSpace |>.emit ")," |>.newline
        else
          st.noSpace |>.emit ctorName |>.emit "," |>.newline
      | [.lit ctorName, _colon, ty] =>
        let hasFields := match ty with
          | .con "typeExpr" [.con "typeApp" [_]] => false
          | _ => true
        if hasFields then
          st.noSpace |>.emit ctorName |>.noSpace |>.emit "(" |> (goRustTypeBoxed adtName rustTyParams ty ·) |>.noSpace |>.emit ")," |>.newline
        else
          st.noSpace |>.emit ctorName |>.emit "," |>.newline
      | _ => st.emit s!"// constr({args.length})\n"
    | .lit "," => st.noSpace
    | _ => go t st

  -- Convert Rosetta type expressions to Lean types
  goType (t : Term) (st : PPState') : PPState' :=
    match t with
    | .con "typeExpr" args =>
      -- (typeExpr left "->" right) or (typeExpr base)
      match args with
      | [left, .lit "->", right] => goType left st |>.emit "→" |> (goType right ·)
      | [single] => goType single st
      | _ => args.foldl (fun s a => goType a s) st
    | .con "typeApp" args =>
      -- (typeApp Name args...) → Name args
      match args with
      | [.var name] =>
        -- Check if this is a known poly type used without args
        match knownPolyTypes.find? (fun (n, _) => n == name) with
        | some (_, arity) =>
          let placeholders := (List.range arity).map (fun _ => "_") |> " ".intercalate
          st.emit "(" |>.emit name |>.emit placeholders |>.emit ")"
        | none => st.emit name
      | [.lit name] =>
        match knownPolyTypes.find? (fun (n, _) => n == name) with
        | some (_, arity) =>
          let placeholders := (List.range arity).map (fun _ => "_") |> " ".intercalate
          st.emit "(" |>.emit name |>.emit placeholders |>.emit ")"
        | none => st.emit name
      | [.var name, arg] => st.emit "(" |>.emit name |> (goType arg ·) |>.emit ")"
      | [.lit name, arg] => st.emit "(" |>.emit name |> (goType arg ·) |>.emit ")"
      | _ => args.foldl (fun s a => goType a s) st
    | .var name => st.emit name
    | .lit s => st.emit s
    | _ => go t st

  -- Extract parameter types from a constructor type (all but the last in arrow chain)
  -- e.g., String -> Term -> Result becomes [String, Term]
  getParamTypes (t : Term) : List Term :=
    match t with
    | .con "typeExpr" args =>
      match args with
      | [left, .lit "->", right] =>
        -- Arrow: left is a param, recurse right
        left :: getParamTypes right
      | [single] =>
        -- Single type = return type, no params from this level
        []
      | _ => []
    | _ => []

  -- Convert Rosetta type to Scala types (as parameters) - only params, not return type
  goScalaType (t : Term) (st : PPState') : PPState' :=
    let params := getParamTypes t
    let indexed := params.zip (List.range params.length)
    indexed.foldl (fun s (p, i) =>
      let tyStr := typeToScala p
      s.emit s!"v{i}: {tyStr}" |>.emit (if i < params.length - 1 then ", " else "")
    ) st

  typeToScala (t : Term) : String :=
    match t with
    | .con "typeExpr" args =>
      match args with
      | [left, .lit "->", right] => s!"({typeToScala left}) => {typeToScala right}"
      | [single] => typeToScala single
      | _ => args.map typeToScala |>.filter (!·.isEmpty) |> " ".intercalate
    | .con "parenType" args =>
      -- Parenthesized type - unwrap the contents but may need to add parens
      let inner := args.map typeToScala |>.filter (!·.isEmpty) |> "".intercalate
      -- If inner contains =>, add parens (function type), otherwise no parens needed
      if (inner.splitOn "=>").length > 1 then s!"({inner})" else inner
    | .con "typeApp" args =>
      -- Handle special types before converting, to preserve arguments correctly
      match args with
      | [.var "List", arg] => s!"List[{typeToScala arg}]"
      | [.var "Option", arg] => s!"Option[{typeToScala arg}]"
      | [.var "List"] => "List[Any]"
      | [.var "Option"] => "Option[Any]"
      | [.var n] =>
        -- Check if this is a known poly type used without arguments
        match knownPolyTypes.find? (fun (tn, _) => tn == n) with
        | some (_, arity) =>
          let anyList := (List.replicate arity "Any").foldl (fun acc s => if acc.isEmpty then s else acc ++ ", " ++ s) ""
          s!"{n}[{anyList}]"
        | none => n
      | _ =>
        let names := args.map typeToScala |>.filter (!·.isEmpty)
        match names with
        | [n] => n
        | n :: rest => s!"{n}[{rest.foldl (fun acc s => if acc.isEmpty then s else acc ++ ", " ++ s) ""}]"
        | [] => "Any"
    | .var name =>
      -- For bare variable names, don't expand poly types - only expand in typeApp
      name
    | .lit s => if s == "(" || s == ")" then "" else s
    | .con _ args => args.map typeToScala |>.filter (!·.isEmpty) |> "".intercalate

  -- Convert Rosetta type to Haskell types (just param types for data constructors)
  goHaskellType (t : Term) (st : PPState') : PPState' :=
    let params := getParamTypes t
    params.foldl (fun s p =>
      s.emit (typeToHaskell p)
    ) st

  typeToHaskell (t : Term) : String :=
    match t with
    | .con "typeExpr" args =>
      match args with
      | [left, .lit "->", right] =>
        -- For Haskell, don't add extra parens here - the caller (goHaskellType)
        -- will wrap in parens if needed for data constructor context
        s!"{typeToHaskell left} -> {typeToHaskell right}"
      | [single] => typeToHaskell single
      | _ => args.map typeToHaskell |> " ".intercalate
    | .con "parenType" args =>
      -- Parenthesized type - add parens since source had them (needed for fn types in data ctors)
      let inner := args.map typeToHaskell |>.filter (!·.isEmpty) |> "".intercalate
      if inner.isEmpty then "" else s!"({inner})"
    | .con "typeApp" args =>
      -- First check for special type constructors before converting
      match args with
      | [.var "List", arg] => s!"[{typeToHaskell arg}]"
      | [.var "Option", arg] => s!"(Maybe {typeToHaskell arg})"
      | [.var "List"] => "[()]"
      | [.var "Option"] => "Maybe ()"
      | [.var n] =>
        -- Check if this is a known poly type used without arguments
        match knownPolyTypes.find? (fun (tn, _) => tn == n) with
        | some (_, arity) => s!"({n} {String.join (List.replicate arity "() ")})"
        | none => n
      -- Handle parenthesized type: typeApp [lit "(", typeExpr [...], lit ")"]
      -- The AST puts parentheses as literal children, so we detect and unwrap
      | [.lit "(", inner, .lit ")"] =>
        -- Just process the inner type with parens (the source had parens so we keep them)
        let innerStr := typeToHaskell inner
        s!"({innerStr})"
      | .var tyName :: restArgs =>
        -- Type constructor with arguments: just emit "TyName arg1 arg2 ..."
        let argStrs := restArgs.map typeToHaskell
        s!"({tyName} {argStrs.foldl (fun acc s => if acc.isEmpty then s else acc ++ " " ++ s) ""})"
      | .lit tyName :: restArgs =>
        -- But skip if tyName is just a paren
        if tyName == "(" || tyName == ")" then
          let argStrs := restArgs.map typeToHaskell |>.filter (!·.isEmpty)
          s!"({argStrs.foldl (fun acc s => if acc.isEmpty then s else acc ++ " " ++ s) ""})"
        else
          let argStrs := restArgs.map typeToHaskell
          s!"({tyName} {argStrs.foldl (fun acc s => if acc.isEmpty then s else acc ++ " " ++ s) ""})"
      | _ =>
        let names := args.map typeToHaskell
        match names with
        | [n] => n
        | n :: rest => s!"({n} {rest.foldl (fun acc s => if acc.isEmpty then s else acc ++ " " ++ s) ""})"
        | [] => "?"
    | .var name =>
      -- Map Rosetta types to Haskell equivalents
      match name with
      | "Option" => "Maybe ()"
      | "List" => "[()]"  -- Bare List becomes [()]
      | "Int" => "Int"
      | "String" => "String"
      | _ =>
        -- Check if this is a known poly type used without arguments
        match knownPolyTypes.find? (fun (tn, _) => tn == name) with
        | some (_, arity) => s!"({name} {String.join (List.replicate arity "() ")})"
        | none => name
    | .lit s =>
      -- Filter out literal parentheses (they're handled by structure)
      if s == "(" || s == ")" || s.trim == "(" || s.trim == ")" then "" else s
    | .con _ _ =>
      ""  -- Unknown node types produce empty string
  goHaskellTypeAtom (t : Term) (st : PPState') : PPState' :=
    match t with
    | .con "typeApp" args =>
      match args with
      | [.var name] => st.emit name
      | [.lit name] => st.emit name
      | [.var name, arg] => st.emit "(" |>.emit name |> (goHaskellTypeAtom arg ·) |>.emit ")"
      | [.lit name, arg] => st.emit "(" |>.emit name |> (goHaskellTypeAtom arg ·) |>.emit ")"
      | _ => st.emit "?"
    | .var name => st.emit name
    | .lit s => st.emit s
    | _ => st.emit "?"

  -- Convert Rosetta type to Rust types (just param types for enum variants)
  goRustType (t : Term) (st : PPState') : PPState' :=
    let params := getParamTypes t
    let indexed := params.zip (List.range params.length)
    indexed.foldl (fun s (p, i) =>
      let tyStr := typeToRust p
      s.emit tyStr |>.emit (if i < params.length - 1 then ", " else "")
    ) st

  -- Convert Rosetta type to Rust, wrapping recursive self-references in Box<>
  -- rustTyParams contains already-uppercased type param names (e.g., ["A", "B"])
  goRustTypeBoxed (adtName : String) (rustTyParams : List String) (t : Term) (st : PPState') : PPState' :=
    let params := getParamTypes t
    let indexed := params.zip (List.range params.length)
    indexed.foldl (fun s (p, i) =>
      let tyStr := typeToRustWithParams adtName rustTyParams p
      s.emit tyStr |>.emit (if i < params.length - 1 then ", " else "")
    ) st

  -- Convert type to Rust string, with Box<> wrapping for self-reference and uppercase type params
  typeToRustWithParams (adtName : String) (rustTyParams : List String) (t : Term) : String :=
    match t with
    | .con "typeExpr" args =>
      match args with
      | [left, .lit "->", right] =>
        s!"fn({typeToRustWithParams adtName rustTyParams left}) -> {typeToRustWithParams adtName rustTyParams right}"
      | [single] => typeToRustWithParams adtName rustTyParams single
      | _ => args.map (typeToRustWithParams adtName rustTyParams) |>.filter (!·.isEmpty) |> ", ".intercalate
    | .con "parenType" args =>
      args.map (typeToRustWithParams adtName rustTyParams) |>.filter (!·.isEmpty) |> "".intercalate
    | .con "typeApp" args =>
      match args with
      | [.var "String"] => "String"
      | [.var "Int"] => "i64"
      | [.var "List", arg] => s!"Vec<{typeToRustWithParams adtName rustTyParams arg}>"
      | [.var "Option", arg] => s!"Option<{typeToRustWithParams adtName rustTyParams arg}>"
      | [.var "List"] => "Vec<()>"
      | [.var "Option"] => "Option<()>"
      | [.var n] =>
        -- Self-reference needs Box<>
        if n == adtName then s!"Box<{n}>"
        -- Type parameter needs uppercasing
        else if rustTyParams.contains n.capitalize then n.capitalize
        else
          match knownPolyTypes.find? (fun (tn, _) => tn == n) with
          | some (_, arity) =>
            let anyList := (List.replicate arity "()").foldl (fun acc s => if acc.isEmpty then s else acc ++ ", " ++ s) ""
            s!"{n}<{anyList}>"
          | none => n
      | _ =>
        let names := args.map (typeToRustWithParams adtName rustTyParams) |>.filter (!·.isEmpty)
        match names with
        | [n] => n
        | n :: rest => s!"{n}<{rest.foldl (fun acc s => if acc.isEmpty then s else acc ++ ", " ++ s) ""}>"
        | [] => "?"
    | .var n =>
      -- Self-reference needs Box<>
      if n == adtName then s!"Box<{n}>"
      -- Type parameter needs uppercasing
      else if rustTyParams.contains n.capitalize then n.capitalize
      else
        match n with
        | "Int" => "i64"
        | _ => n
    | .lit s => if s == "(" || s == ")" then "" else s
    | .con _ args => args.map (typeToRustWithParams adtName rustTyParams) |>.filter (!·.isEmpty) |> "".intercalate

  typeToRust (t : Term) : String :=
    match t with
    | .con "typeExpr" args =>
      match args with
      | [left, .lit "->", right] => s!"fn({typeToRust left}) -> {typeToRust right}"
      | [single] => typeToRust single
      | _ => args.map typeToRust |>.filter (!·.isEmpty) |> ", ".intercalate
    | .con "parenType" args =>
      -- Parenthesized type - unwrap the contents
      args.map typeToRust |>.filter (!·.isEmpty) |> "".intercalate
    | .con "typeApp" args =>
      -- Handle special types before converting, to preserve arguments correctly
      match args with
      | [.var "String"] => "String"
      | [.var "Int"] => "i64"
      | [.var "List", arg] => s!"Vec<{typeToRust arg}>"
      | [.var "Option", arg] => s!"Option<{typeToRust arg}>"
      | [.var "List"] => "Vec<()>"
      | [.var "Option"] => "Option<()>"
      | [.var n] =>
        -- Check if this is a known poly type used without arguments
        match knownPolyTypes.find? (fun (tn, _) => tn == n) with
        | some (_, arity) =>
          let anyList := (List.replicate arity "()").foldl (fun acc s => if acc.isEmpty then s else acc ++ ", " ++ s) ""
          s!"{n}<{anyList}>"
        | none => n
      | _ =>
        let names := args.map typeToRust |>.filter (!·.isEmpty)
        match names with
        | [n] => n
        | n :: rest => s!"{n}<{rest.foldl (fun acc s => if acc.isEmpty then s else acc ++ ", " ++ s) ""}>"
        | [] => "?"
    | .var name =>
      -- Map special types
      match name with
      | "Int" => "i64"
      | _ => name  -- Don't expand poly types for bare vars, only in typeApp
    | .lit s => if s == "(" || s == ")" then "" else s
    | .con _ args => args.map typeToRust |>.filter (!·.isEmpty) |> "".intercalate

  goRustTypeAtom (t : Term) (st : PPState') : PPState' :=
    st.emit (typeToRust t)

  -- Check if a term has any content
  hasFields : Term → Bool
    | .con _ [] => false
    | .con _ _ => true
    | _ => false

  termToString : Term → String
    | .var n => n
    | .lit s => s
    | .con n [] => n
    | .con _ args => args.map termToString |> " ".intercalate

  applyLayout (cmds : List LayoutCmd) (args : List Term) (st : PPState') : PPState' :=
    cmds.foldl (fun s cmd => applyCmd cmd args s) st

  applyCmd (cmd : LayoutCmd) (args : List Term) (st : PPState') : PPState' :=
    match cmd with
    | .text t => st.emit t
    | .ref _name =>
      -- Use next arg in sequence
      match args[st.argIndex]? with
      | some arg => (go arg st).nextArg
      | none => st.nextArg
    | .nl => st.newline
    | .indent => st.addIndent
    | .dedent => st.dedent
    | .space => st.space
    | .noSpace => st.noSpace
    | .star inner =>
      -- For star/plus, try to apply to remaining args
      let remaining := args.drop st.argIndex
      remaining.foldl (fun s a =>
        let s' := applyCmd inner [a] s
        s'.nextArg
      ) st
    | .plus inner => applyCmd (.star inner) args st
    | .opt inner =>
      if st.argIndex < args.length then
        applyCmd inner args st
      else st
    | .seq cmds => cmds.foldl (fun s c => applyCmd c args s) st

/-! ## Main Pipeline -/

/-- Pipeline result -/
structure TargetResult where
  lang : TargetLang
  code : String
  outPath : String
  deriving Repr

/-- Check if a declaration is a type/ADT definition (should come first) -/
def isTypeDecl (t : Term) : Bool :=
  match t with
  | .con "inductiveDecl" _ => true  -- Lean
  | .con "sealedTrait" _ => true    -- Scala
  | .con "caseClass" _ => true      -- Scala
  | .con "dataDecl" _ => true       -- Haskell
  | .con "enumDecl" _ => true       -- Rust
  | .con "adtDef" _ => true         -- Generic
  | _ => false

/-- Sort declarations so type definitions come before functions -/
partial def sortDeclarations (t : Term) : Term :=
  match t with
  | .con "seq" children =>
    -- Partition into type declarations and other declarations
    let (types, others) := children.partition isTypeDecl
    -- Recursively sort nested sequences
    let sortedTypes := types.map sortDeclarations
    let sortedOthers := others.map sortDeclarations
    -- Types first, then other declarations
    .con "seq" (sortedTypes ++ sortedOthers)
  | .con name args =>
    -- Recursively sort inside other constructors (e.g., modules)
    .con name (args.map sortDeclarations)
  | _ => t

/-- Run grammar-driven pipeline for one target -/
def runForTarget (rt : Runtime) (sourceAst : Term) (lang : TargetLang) (outDir : String)
    (_quiet : Bool := false) : IO (Except String TargetResult) := do
  -- 1. Load grammar file - contains both syntax AND layout annotations
  let (grammarAst, _) ← match ← loadLanguage rt lang.grammarPath with
    | .error e => return .error s!"Failed to load grammar: {e}"
    | .ok grammarLang =>
      let content ← IO.FS.readFile lang.grammarPath
      match parseWithGrammarE grammarLang content with
      | .error _ =>
        match parseLegoFileE rt content with
        | .error e2 => return .error s!"Failed to parse grammar file: {e2}"
        | .ok ast => pure (ast, grammarLang.productions.length)
      | .ok ast => pure (ast, grammarLang.productions.length)

  let prods := extractProductions grammarAst

  -- 2. Load transformation rules (rosetta2<L>.lego)
  -- Use parseLegoFileE directly since loadLanguage can hang on complex files
  let rules ← do
    let content ← IO.FS.readFile lang.transformPath
    match parseLegoFileE rt content with
    | .error _e =>
      pure ([] : List TransformRule)
    | .ok ast =>
      pure (extractTransformRules ast)

  -- 3. Apply transformations
  let entryFn := match lang with
    | .Lean => "toLean"
    | .Scala => "toScala"
    | .Haskell => "toHaskell"
    | .Rust => "toRust"

  -- First convert Lego AST (DLang/DPiece/DRule) to Rosetta IR format
  let rosettaIR := legoToRosetta sourceAst

  let wrappedAst := Term.con entryFn [rosettaIR]
  let transformed := if rules.isEmpty then rosettaIR else applyTransforms rules wrappedAst true

  -- Sort declarations: ADTs/inductives first, then rewrites
  -- This ensures type definitions appear before functions that use them
  let sorted := sortDeclarations transformed

  -- 4. Pretty-print using grammar layout annotations
  let code := prettyPrint prods sorted lang

  -- 5. Add language-specific headers
  let finalCode := match lang with
    | .Haskell => "module Generated where\n\n" ++ code
    | .Scala => "package generated\n\n" ++ code
    | .Rust => "#![allow(dead_code)]\n#![allow(unused_variables)]\n\n" ++
               "// Helper function to extract argument from Term (returns reference into boxed term)\n" ++
               "fn get_arg(t: &Term, i: usize) -> &Term {\n" ++
               "    match t {\n" ++
               "        Term::Con(_, args) => &*args[i],\n" ++
               "        _ => panic!(\"get_arg called on non-Con\")\n" ++
               "    }\n" ++
               "}\n\n" ++ code
    | .Lean => code

  -- 6. Build result
  let moduleName := "Generated"
  let outPath := s!"{outDir}/{moduleName}{lang.ext}"

  return .ok { lang, code := finalCode, outPath }

/-- Run pipeline for all targets (library function) -/
def runGrammarDrivenPipeline (rt : Runtime) (sourcePath : String)
    (targets : List TargetLang := [.Lean, .Scala, .Haskell, .Rust])
    (outDir : String := "./generated/Rosetta")
    (quiet : Bool := false)
    : IO (Except String (List TargetResult)) := do

  -- Parse source
  let sourceAst ← match ← parseLegoFilePathE rt sourcePath with
    | .error e => return .error s!"Failed to parse source: {e}"
    | .ok ast => pure ast

  -- Generate for each target
  let mut results : List TargetResult := []
  for lang in targets do
    match ← runForTarget rt sourceAst lang outDir quiet with
    | .error _ => pure ()
    | .ok r => results := results ++ [r]

  -- Write files
  IO.FS.createDirAll outDir
  for r in results do
    IO.FS.writeFile r.outPath r.code

  return .ok results
