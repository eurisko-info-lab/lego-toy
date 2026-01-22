/-
  Pipeline.lean
  cubical := parse CubicalTT.lego
  lifted := run rules cubical2rosetta.lego on cubical
  lean := run rules rosetta2lean.lego on lifted
  print lean → generated/

  Now generates VALID Lean 4 code that uses Term pattern matching.
-/

import Lego.Runtime
import Lego.Loader

open Lego.Runtime
open Lego.Loader
open Lego

/-- Check if a Term is a var -/
def Term.isVar : Term → Bool
  | .var _ => true
  | _ => false

/-- Get var name from a Term -/
def Term.getVarName : Term → Option String
  | .var name => some name
  | _ => none

/-- Collect all metavariables from a pattern -/
partial def collectMetavars : Term → List String
  | .con "metavar" [.var name] => [name]
  | .con "var" [_, .con "ident" [.var name]] => [name]
  | .var name => if name.startsWith "$" then [name] else []
  | .con _ args => args.flatMap collectMetavars
  | .lit _ => []

/-- Lean 4 reserved keywords that can't be used as identifiers -/
def leanReservedKeywords : List String := [
  "partial", "unsafe", "private", "protected", "scoped", "local",
  "where", "rec", "match", "let", "in", "if", "then", "else",
  "do", "return", "for", "fun", "by", "have", "show", "with",
  "structure", "inductive", "class", "instance", "def", "theorem",
  "axiom", "example", "abbrev", "opaque", "variable", "universe",
  "end", "section", "namespace", "open", "import", "export"
]

/-- Sanitize variable name - rename Lean reserved keywords -/
def sanitizeVarName (name : String) : String :=
  if leanReservedKeywords.contains name then name ++ "_"
  else name

/-- Convert a constructor name to lowercase (for native Lean patterns) -/
def lowercaseCtor (name : String) : String :=
  if name.isEmpty then name
  else
    let first := name.data[0]!
    let rest := name.drop 1
    String.singleton first.toLower ++ rest

/-- Map .lego constructor names to Lego.Core.Expr constructor names -/
def mapCtorName (name : String) : String :=
  -- Handle specific mappings from Cubical.lego conventions to Lego.Core.Expr
  match name with
  | "Lam" => "lam"
  | "App" => "app"
  | "Pi" => "pi"
  | "Sigma" => "sigma"
  | "Let" => "letE"
  | "Fst" => "fst"
  | "Snd" => "snd"
  | "Pair" => "pair"
  | "Cons" => "pair"  -- Cons is pair in Lego.Core
  | "Univ" => "univ"
  | "Type" => "univ"
  | "Var" => "ix"
  | "Ix" => "ix"
  | "Lit" => "lit"
  -- Dimension/interval operations
  | "Dim0" => "dim0"
  | "Dim1" => "dim1"
  | "DimVar" => "dimVar"
  -- Cofibrations
  | "CofTop" => "cof_top"
  | "CofBot" => "cof_bot"
  | "CofEq" => "cof_eq"
  | "CofAnd" => "cof_and"
  | "CofOr" => "cof_or"
  -- Path types
  | "Path" => "path"
  | "PathLam" => "plam"
  | "PathApp" => "papp"
  | "PLam" => "plam"
  | "PApp" => "papp"
  | "ExtLam" => "plam"
  | "ExtApp" => "papp"
  | "Refl" => "refl"
  -- Kan operations
  | "Coe" => "coe"
  | "HCom" => "hcom"
  | "Com" => "com"
  | "GHCom" => "ghcom"
  | "GCom" => "gcom"
  | "FHCom" => "fhcom"
  -- Box/Cap
  | "BoxEl" => "boxEl"
  | "CapEl" => "capEl"
  -- Systems
  | "Sys" => "sys"
  -- V-types (glue types)
  | "VType" => "vtype"
  | "VIn" => "vin"
  | "VProj" => "vproj"
  -- Levels
  | "LZero" => "lzero"
  | "LSuc" => "lsuc"
  | "LMax" => "lmax"
  | "LVar" => "lvar"
  -- Substitution
  | "Subst" => "subst"
  -- Keep lowercase identifiers as-is (already correct)
  | s => lowercaseCtor s  -- Default: lowercase first letter

/-- Mode for code generation -/
inductive GenMode where
  | termRewriting  -- Generate Term.con/Term.var based code
  | nativeLean     -- Generate native Lean inductive types and functions
  deriving BEq

/-- Current generation mode (can be changed at runtime) -/
def genMode : GenMode := GenMode.termRewriting

/-! ## Native Lean Generation

    These functions generate proper Lean 4 code with:
    - Native inductive types from grammar definitions
    - Pattern matching on constructors
    - Direct function application
-/

/-- Convert a pattern to native Lean pattern syntax -/
partial def nativePatternToLean (t : Term) (seen : List String := []) : String × List String :=
  match t with
  -- Metavariable: becomes a binding variable
  | .con "metavar" [.var name] =>
    let safeName := sanitizeVarName name
    if seen.contains safeName then (safeName ++ "_dup", (safeName ++ "_dup") :: seen)
    else (safeName, safeName :: seen)
  | .con "var" [_, .con "ident" [.var name]] =>
    let safeName := sanitizeVarName name
    if seen.contains safeName then (safeName ++ "_dup", (safeName ++ "_dup") :: seen)
    else (safeName, safeName :: seen)
  | .var name =>
    if name.startsWith "$" then
      let safeName := sanitizeVarName (name.drop 1)
      if seen.contains safeName then (safeName ++ "_dup", (safeName ++ "_dup") :: seen)
      else (safeName, safeName :: seen)
    else (name, seen)  -- Regular identifier in pattern

  -- After rosetta transform: (app head args...) where head is a constructor name
  -- This handles the output of transformCon: (con "(" (ident "lam") body ")") ~~> (app lam body)
  | .con "app" (.var head :: rest) =>
    let mappedHead := mapCtorName head
    let (argStrs, finalSeen) := rest.foldl (fun (acc, s) arg =>
      let (str, s') := nativePatternToLean arg s
      (acc ++ [str], s')
    ) ([], seen)
    if argStrs.isEmpty then (s!".{mappedHead}", finalSeen)
    else (s!"(.{mappedHead} {" ".intercalate argStrs})", finalSeen)

  -- S-expression: (con head args...) -> Constructor pattern
  | .con "con" args =>
    let filtered := args.filter fun x =>
      match x with | .lit "(" => false | .lit ")" => false | _ => true
    match filtered with
    | .var head :: rest =>
      let mappedHead := mapCtorName head
      let (argStrs, finalSeen) := rest.foldl (fun (acc, s) arg =>
        let (str, s') := nativePatternToLean arg s
        (acc ++ [str], s')
      ) ([], seen)
      if argStrs.isEmpty then (s!".{mappedHead}", finalSeen)
      else (s!"(.{mappedHead} {" ".intercalate argStrs})", finalSeen)
    | .con "ident" [.var head] :: rest =>
      let mappedHead := mapCtorName head
      let (argStrs, finalSeen) := rest.foldl (fun (acc, s) arg =>
        let (str, s') := nativePatternToLean arg s
        (acc ++ [str], s')
      ) ([], seen)
      if argStrs.isEmpty then (s!".{mappedHead}", finalSeen)
      else (s!"(.{mappedHead} {" ".intercalate argStrs})", finalSeen)
    | [single] => nativePatternToLean single seen
    | _ =>
      let (argStrs, finalSeen) := filtered.foldl (fun (acc, s) arg =>
        let (str, s') := nativePatternToLean arg s
        (acc ++ [str], s')
      ) ([], seen)
      (s!"({", ".intercalate argStrs})", finalSeen)

  -- Identifier alone: nullary constructor
  | .con "ident" [.var name] =>
    let mappedName := mapCtorName name
    (s!".{mappedName}", seen)

  -- Number literal
  | .con "num" [.con "number" [.lit n]] =>
    let inner := if n.startsWith "\"" && n.endsWith "\"" && n.length ≥ 2
                 then n.drop 1 |>.dropRight 1 else n
    (inner, seen)

  -- String literal
  | .con "lit" [.con "string" [.lit s]] =>
    let inner := if s.startsWith "\"" && s.endsWith "\"" && s.length ≥ 2
                 then s.drop 1 |>.dropRight 1 else s
    (s!"\"{inner}\"", seen)
  | .con "string" [.lit s] =>
    let inner := if s.startsWith "\"" && s.endsWith "\"" && s.length ≥ 2
                 then s.drop 1 |>.dropRight 1 else s
    (s!"\"{inner}\"", seen)
  | .lit s =>
    let inner := if s.startsWith "\"" && s.endsWith "\"" && s.length ≥ 2
                 then s.drop 1 |>.dropRight 1 else s
    (s!"\"{inner}\"", seen)

  -- Unit
  | .con "unit" [] => ("()", seen)

  -- Generic fallback
  | .con tag args =>
    let mappedTag := mapCtorName tag
    let (argStrs, finalSeen) := args.foldl (fun (acc, s) arg =>
      let (str, s') := nativePatternToLean arg s
      (acc ++ [str], s')
    ) ([], seen)
    if argStrs.isEmpty then (s!".{mappedTag}", finalSeen)
    else (s!"(.{mappedTag} {" ".intercalate argStrs})", finalSeen)

/-- Convert a template to native Lean expression syntax -/
partial def nativeTemplateToLean (t : Term) (boundVars : List String := []) : String :=
  match t with
  -- Metavariable: reference to bound variable
  | .con "metavar" [.var name] =>
    let safeName := sanitizeVarName name
    safeName
  | .con "var" [_, .con "ident" [.var name]] =>
    let safeName := sanitizeVarName name
    safeName
  | .var name =>
    if name.startsWith "$" then sanitizeVarName (name.drop 1)
    else name

  -- After rosetta transform: (app head args...) where head could be constructor or function
  -- Note: Some operations like "subst" are functions, not constructors
  | .con "app" (.var head :: rest) =>
    let mappedHead := mapCtorName head
    let argStrs := rest.map (nativeTemplateToLean · boundVars)
    -- Check if it's a function call vs constructor
    let isFunctionCall := ["subst", "substDim", "shift", "add", "eq", "concat"].contains mappedHead
    if isFunctionCall then
      -- Function call: no leading dot
      if argStrs.isEmpty then mappedHead
      else s!"({mappedHead} {" ".intercalate argStrs})"
    else
      -- Constructor: leading dot
      if argStrs.isEmpty then s!".{mappedHead}"
      else s!"(.{mappedHead} {" ".intercalate argStrs})"

  -- S-expression: (con head args...) -> Constructor application
  | .con "con" args =>
    let filtered := args.filter fun x =>
      match x with | .lit "(" => false | .lit ")" => false | _ => true
    match filtered with
    | .var head :: rest =>
      let mappedHead := mapCtorName head
      let argStrs := rest.map (nativeTemplateToLean · boundVars)
      if argStrs.isEmpty then s!".{mappedHead}"
      else s!"(.{mappedHead} {" ".intercalate argStrs})"
    | .con "ident" [.var head] :: rest =>
      let mappedHead := mapCtorName head
      let argStrs := rest.map (nativeTemplateToLean · boundVars)
      if argStrs.isEmpty then s!".{mappedHead}"
      else s!"(.{mappedHead} {" ".intercalate argStrs})"
    | [single] => nativeTemplateToLean single boundVars
    | _ =>
      let argStrs := filtered.map (nativeTemplateToLean · boundVars)
      s!"({", ".intercalate argStrs})"

  -- Identifier alone: nullary constructor
  | .con "ident" [.var name] =>
    let mappedName := mapCtorName name
    s!".{mappedName}"

  -- Number literal
  | .con "num" [.con "number" [.lit n]] =>
    let inner := if n.startsWith "\"" && n.endsWith "\"" && n.length ≥ 2
                 then n.drop 1 |>.dropRight 1 else n
    inner

  -- String literal
  | .con "lit" [.con "string" [.lit s]] =>
    let inner := if s.startsWith "\"" && s.endsWith "\"" && s.length ≥ 2
                 then s.drop 1 |>.dropRight 1 else s
    s!"\"{inner}\""
  | .con "string" [.lit s] =>
    let inner := if s.startsWith "\"" && s.endsWith "\"" && s.length ≥ 2
                 then s.drop 1 |>.dropRight 1 else s
    s!"\"{inner}\""
  | .lit s =>
    let inner := if s.startsWith "\"" && s.endsWith "\"" && s.length ≥ 2
                 then s.drop 1 |>.dropRight 1 else s
    s!"\"{inner}\""

  -- Unit
  | .con "unit" [] => "()"

  -- Generic fallback
  | .con tag args =>
    let mappedTag := mapCtorName tag
    let argStrs := args.map (nativeTemplateToLean · boundVars)
    if argStrs.isEmpty then s!".{mappedTag}"
    else s!"(.{mappedTag} {" ".intercalate argStrs})"

/-- Parse grammar production to extract constructor info
    Format: "keyword" arg1 arg2 → constructorName
    Returns: (constructorName, argTypes) -/
def parseGrammarProduction (t : Term) : Option (String × List String) :=
  match t with
  | .con "arrow" [lhs, .var ctorName] =>
    -- Extract argument types from LHS
    let rec extractArgs : Term → List String
      | .con "seq" args => (args.map extractArgs).flatten
      | .con "ref" [.var typeName] => [typeName]
      | .con "terminal" _ => []
      | .lit _ => []
      | .var _ => []
      | _ => []
    some (ctorName, extractArgs lhs)
  | _ => none

/-- Generate inductive type from grammar piece -/
def grammarToInductive (pieceName : String) (productions : List Term) (indent : Nat) : String :=
  let pad := String.mk (List.replicate (indent * 2) ' ')
  let ctors := productions.filterMap fun prod =>
    match prod with
    | .con "DGrammar" args =>
      -- Extract: name ::= alternatives ;
      match args with
      | .con "ident" [.var _] :: _ :: body :: _ =>
        -- Parse alternatives in body
        let rec parseAlts : Term → List String
          | .con "alt" [left, _, right] =>
            parseAlts left ++ parseAlts right
          | .con "arrow" [_, .con "ident" [.var ctorName]] =>
            [s!"{pad}  | {ctorName}"]
          | _ => []
        some (parseAlts body)
      | _ => none
    | _ => none
  let allCtors := ctors.flatten |> String.intercalate "\n"
  s!"{pad}inductive {pieceName} where\n{allCtors}\n{pad}  deriving Repr, BEq"

/-! ## Traversal Algebra

    All term operations (subst, shift, eval, freeVars, map) are catamorphisms.
    We define ONE generic fold and derive everything from it.

    A Traversal is characterized by:
    - binderF : how to handle binders (lam, pi, sigma, ...)
    - appF    : how to handle non-binders
    - varF    : how to handle variables/indices

    The grammar tells us WHICH constructors are binders.
-/

/-- Traversal algebra: one structure, all operations -/
inductive TraversalKind | subst | shift | eval | map | freeVars
  deriving Repr, BEq

/-- Extract binder constructors from grammar (heuristic + explicit) -/
def binderCtors : List String := ["lam", "pi", "sigma", "plam", "pathLam", "extLam", "let", "glue"]

/-- Generate the generic catamorphism for a grammar -/
def genCata (grammarName : String) (ctors : List (String × Nat)) (indent : Nat) : String :=
  let pad := String.mk (List.replicate (indent * 2) ' ')
  let cases := ctors.map fun (ctor, arity) =>
    let isBinder := binderCtors.contains ctor
    let args := List.range arity |>.map (s!"a{·}")
    let argPat := if args.isEmpty then "[]" else s!"[{String.intercalate ", " args}]"
    let recCalls := args.map (s!"f {·}") |> String.intercalate ", "
    if isBinder then
      s!"{pad}    | .con \"{ctor}\" {argPat} => .con \"{ctor}\" [f' {recCalls}]"
    else if arity == 0 then
      s!"{pad}    | .con \"{ctor}\" [] => t"
    else
      s!"{pad}    | .con \"{ctor}\" {argPat} => .con \"{ctor}\" [{recCalls}]"
  s!"{pad}def cata{grammarName} (f : Term → Term) (f' : Term → Term) (t : Term) : Term :=\n{pad}  match t with\n{String.intercalate "\n" cases}\n{pad}    | _ => t"

/-- Derive subst from cata: f = subst k v, f' = subst (k+1) (shift 0 1 v) -/
def deriveSubst (grammarName : String) (indent : Nat) : String :=
  let pad := String.mk (List.replicate (indent * 2) ' ')
  s!"{pad}def subst{grammarName} (k : Term) (v : Term) : Term → Term :=
{pad}  cata{grammarName}
{pad}    (fun t => substCore k v t)
{pad}    (fun t => substCore (.con \"add\" [k, .lit \"1\"]) (.con \"shift\" [.lit \"0\", .lit \"1\", v]) t)"

/-- Derive shift from cata: f = shift c n, f' = shift (c+1) n -/
def deriveShift (grammarName : String) (indent : Nat) : String :=
  let pad := String.mk (List.replicate (indent * 2) ' ')
  s!"{pad}def shift{grammarName} (c : Term) (n : Term) : Term → Term :=
{pad}  cata{grammarName}
{pad}    (fun t => shiftCore c n t)
{pad}    (fun t => shiftCore (.con \"add\" [c, .lit \"1\"]) n t)"

/-- Count term references in a grammar expression -/
partial def countTermRefs : Term → Nat
  | .con "seq" args => args.foldl (fun acc t => acc + countTermRefs t) 0
  | .con "ref" [.var n] =>
    let nl := n.toLower
    if nl == "term" || nl == "expr" || nl == "level" || nl == "dim" then 1 else 0
  | _ => 0

/-- Extract constructor arities from grammar body -/
def extractCtorArities (body : Term) : List (String × Nat) :=
  let rec go : Term → List (String × Nat)
    | .con "alt" [l, _, r] => go l ++ go r
    | .con "arrow" [lhs, .con "ident" [.var name]] => [(name, countTermRefs lhs)]
    | _ => []
  go body

/-- Generate all derived operations for a grammar -/
def deriveAll (grammarName : String) (body : Term) (indent : Nat) : String :=
  let ctors := extractCtorArities body
  let pad := String.mk (List.replicate (indent * 2) ' ')
  s!"{pad}-- Derived operations for {grammarName}
{genCata grammarName ctors indent}

{deriveSubst grammarName indent}

{deriveShift grammarName indent}"

/-- Convert a pattern Term to Lean 4 pattern syntax.
    The parsed AST has structure like:
    - (con "(" (ident head) args... ")") for s-expressions
    - (var "$" (ident name)) for metavariables
    After transformation, identifiers may be simplified to just .var "name"
    Track seen variable names to deduplicate
-/
partial def patternToLean (t : Term) (seen : List String := []) : String × List String :=
  match t with
  -- Metavariable: (metavar name) -> name (binding)
  | .con "metavar" [.var name] =>
    let safeName := sanitizeVarName name
    if seen.contains safeName then
      let newName := safeName ++ "_dup"
      (newName, newName :: seen)
    else (safeName, safeName :: seen)
  -- Old metavariable format: (var "$" (ident name))
  | .con "var" [_, .con "ident" [.var name]] =>
    let safeName := sanitizeVarName name
    if seen.contains safeName then
      let newName := safeName ++ "_dup"
      (newName, newName :: seen)
    else (safeName, safeName :: seen)
  | .var name =>
    if name.startsWith "$" then
      let actualName := sanitizeVarName (name.drop 1)
      if seen.contains actualName then
        let newName := actualName ++ "_dup"
        (newName, newName :: seen)
      else (actualName, actualName :: seen)
    else (s!".var \"{name}\"", seen)

  -- S-expression after transformation: (con "(" head args... ")")
  -- The head may be .var "name" (after transform) or .con "ident" [.var "name"] (before)
  | .con "con" args =>
    let filtered := args.filter fun x =>
      match x with | .lit "(" => false | .lit ")" => false | _ => true
    match filtered with
    -- Head is .var (post-transform)
    | .var head :: rest =>
      let (argStrs, finalSeen) := rest.foldl (fun (acc, s) arg =>
        let (str, s') := patternToLean arg s
        (acc ++ [str], s')
      ) ([], seen)
      if argStrs.isEmpty then (s!".con \"{head}\" []", finalSeen)
      else (s!".con \"{head}\" [{", ".intercalate argStrs}]", finalSeen)
    -- Head is .con "ident" [.var name] (pre-transform)
    | .con "ident" [.var head] :: rest =>
      let (argStrs, finalSeen) := rest.foldl (fun (acc, s) arg =>
        let (str, s') := patternToLean arg s
        (acc ++ [str], s')
      ) ([], seen)
      if argStrs.isEmpty then (s!".con \"{head}\" []", finalSeen)
      else (s!".con \"{head}\" [{", ".intercalate argStrs}]", finalSeen)
    | [single] => patternToLean single seen  -- single element, recurse
    | _ =>
      -- Multiple elements without an ident head - unusual
      let (argStrs, finalSeen) := filtered.foldl (fun (acc, s) arg =>
        let (str, s') := patternToLean arg s
        (acc ++ [str], s')
      ) ([], seen)
      (s!".con \"tuple\" [{", ".intercalate argStrs}]", finalSeen)

  -- Identifier alone: (ident name) -> .con "name" [] (nullary constructor)
  | .con "ident" [.var name] => (s!".con \"{name}\" []", seen)

  -- Number: (num (number n))
  | .con "num" [.con "number" [.lit n]] =>
    let inner := if n.startsWith "\"" && n.endsWith "\"" && n.length ≥ 2
                 then n.drop 1 |>.dropRight 1 else n
    (s!".con \"num\" [.con \"number\" [.lit \"{inner}\"]]", seen)

  -- Literal string in pattern - strip outer quotes from parser
  | .con "lit" [.con "string" [.lit s]] =>
    let inner := if s.startsWith "\"" && s.endsWith "\"" && s.length ≥ 2
                 then s.drop 1 |>.dropRight 1 else s
    (s!".con \"lit\" [.con \"string\" [.lit \"{inner}\"]]", seen)
  | .con "string" [.lit s] =>
    let inner := if s.startsWith "\"" && s.endsWith "\"" && s.length ≥ 2
                 then s.drop 1 |>.dropRight 1 else s
    (s!".con \"string\" [.lit \"{inner}\"]", seen)
  | .lit s =>
    let inner := if s.startsWith "\"" && s.endsWith "\"" && s.length ≥ 2
                 then s.drop 1 |>.dropRight 1 else s
    (s!".lit \"{inner}\"", seen)

  -- Unit
  | .con "unit" [] => (".con \"unit\" []", seen)

  -- Generic fallback
  | .con tag args =>
    let (argStrs, finalSeen) := args.foldl (fun (acc, s) arg =>
      let (str, s') := patternToLean arg s
      (acc ++ [str], s')
    ) ([], seen)
    if argStrs.isEmpty then (s!".con \"{tag}\" []", finalSeen)
    else (s!".con \"{tag}\" [{", ".intercalate argStrs}]", finalSeen)

/-- Helper to check if a term is a specific literal -/
def isLit (s : String) (t : Term) : Bool := match t with
  | .lit s' => s' == s
  | .con "con" [.lit s'] => s' == s  -- wrapped literal
  | _ => false

/-- Helper to extract arms from match arguments -/
partial def parseMatchArms (args : List Term) : List (Term × Term) :=
  match args with
  | [] => []
  | pipe :: pat :: arrow :: body :: rest =>
    if isLit "|" pipe && isLit "=>" arrow then
      (pat, body) :: parseMatchArms rest
    else
      parseMatchArms (pat :: arrow :: body :: rest)  -- skip and try again
  | _ :: rest => parseMatchArms rest

/-- Convert a match pattern to Lean pattern syntax -/
partial def matchPatternToLean (t : Term) : String :=
  match t with
  | .var name => if name.startsWith "$" then name.drop 1 else name
  | .lit s =>
    let inner := if s.startsWith "\"" && s.endsWith "\"" && s.length ≥ 2
                 then s.drop 1 |>.dropRight 1 else s
    inner
  -- Metavar is a bound variable in pattern context
  | .con "metavar" [.var name] => name
  | .con "con" args =>
    let filtered := args.filter fun x =>
      match x with | .lit "(" => false | .lit ")" => false | _ => true
    match filtered with
    | .var head :: rest =>
      let argStrs := rest.map matchPatternToLean
      if argStrs.isEmpty then s!".{head}"
      else s!".{head} {" ".intercalate argStrs}"
    | .con "ident" [.var head] :: rest =>
      let argStrs := rest.map matchPatternToLean
      if argStrs.isEmpty then s!".{head}"
      else s!".{head} {" ".intercalate argStrs}"
    | _ => s!"({", ".intercalate (filtered.map matchPatternToLean)})"
  | .con "app" [f, a] =>
    -- For patterns like (some $x), we want .some x
    let fStr := matchPatternToLean f
    let aStr := matchPatternToLean a
    s!".{fStr} {aStr}"
  | .con tag args =>
    let argStrs := args.map matchPatternToLean
    if argStrs.isEmpty then s!".{tag}"
    else s!".{tag} {" ".intercalate argStrs}"

mutual
/-- Debug helper to show term structure -/
partial def debugTerm (t : Term) : String := match t with
  | .lit s => s!"lit({s})"
  | .var s => s!"var({s})"
  | .con tag children => s!"con({tag})[{",".intercalate (children.map debugTerm)}]"

/-- Convert template to actual Lean expression (for match scrutinee and arm bodies) -/
partial def templateToLeanExpr (t : Term) (boundVars : List String := []) : String :=
  match t with
  | .var name => if name.startsWith "$" then name.drop 1 else name
  | .con "metavar" [.var name] => name
  | .con "app" [f, a] => s!"{templateToLeanExpr f boundVars} {templateToLeanExpr a boundVars}"
  -- Number literal: (num (number "1")) -> 1
  | .con "num" [.con "number" [.lit n]] =>
    let inner := if n.startsWith "\"" && n.endsWith "\"" && n.length ≥ 2
                 then n.drop 1 |>.dropRight 1 else n
    inner
  | .con "con" args =>
    let filtered := args.filter fun x =>
      match x with | .lit "(" => false | .lit ")" => false | _ => true
    match filtered with
    | .var head :: rest =>
      let argStrs := rest.map fun arg =>
        let s := templateToLeanExpr arg boundVars
        -- Parenthesize complex args (those containing spaces)
        if s.contains ' ' then s!"({s})" else s
      if argStrs.isEmpty then head
      else s!"{head} {" ".intercalate argStrs}"
    | _ => s!"({", ".intercalate (filtered.map (templateToLeanExpr · boundVars))})"
  | .lit s =>
    let inner := if s.startsWith "\"" && s.endsWith "\"" && s.length ≥ 2
                 then s.drop 1 |>.dropRight 1 else s
    inner
  | _ => templateToLean t boundVars  -- fallback to Term constructor

/-- Generate Term constructor for match (not actual Lean match) -/
partial def templateMatchToLean (args : List Term) (boundVars : List String) : String :=
  -- Generate Term constructors since actual Lean match would require
  -- the scrutinee function to be defined in Lean
  let argStrs := args.map (templateToLean · boundVars)
  s!"Term.con \"match\" [{", ".intercalate argStrs}]"

/-- Convert a template Term to Lean 4 expression syntax
    boundVars: variables bound in the LHS pattern (become Lean references)
    Other metavariables become Term.var "name" -/
partial def templateToLean (t : Term) (boundVars : List String := []) : String :=
  match t with
  -- Metavariable: (metavar name) -> reference if bound, else Term.var
  | .con "metavar" [.var name] =>
    let safeName := sanitizeVarName name
    if boundVars.contains safeName then safeName
    else s!"Term.var \"{name}\""
  -- Old metavariable format: (var "$" (ident name))
  | .con "var" [_, .con "ident" [.var name]] =>
    let safeName := sanitizeVarName name
    if boundVars.contains safeName then safeName
    else s!"Term.var \"{name}\""
  | .var name =>
    if name.startsWith "$" then
      let stripped := name.drop 1
      let safeName := sanitizeVarName stripped
      if boundVars.contains safeName then safeName
      else s!"Term.var \"{stripped}\""
    else s!"Term.var \"{name}\""

  -- S-expression after transformation: (con "(" head args... ")")
  | .con "con" args =>
    let filtered := args.filter fun x =>
      match x with | .lit "(" => false | .lit ")" => false | _ => true
    match filtered with
    -- Head is .var (post-transform)
    | .var head :: rest =>
      -- Special case: match expressions
      if head == "match" then
        templateMatchToLean rest boundVars
      else
        let argStrs := rest.map (templateToLean · boundVars)
        if argStrs.isEmpty then s!"Term.con \"{head}\" []"
        else s!"Term.con \"{head}\" [{", ".intercalate argStrs}]"
    -- Head is .con "ident" [.var name] (pre-transform)
    | .con "ident" [.var head] :: rest =>
      -- Special case: match expressions
      if head == "match" then
        templateMatchToLean rest boundVars
      else
        let argStrs := rest.map (templateToLean · boundVars)
        if argStrs.isEmpty then s!"Term.con \"{head}\" []"
        else s!"Term.con \"{head}\" [{", ".intercalate argStrs}]"
    | [single] => templateToLean single boundVars
    | _ =>
      let argStrs := filtered.map (templateToLean · boundVars)
      s!"Term.con \"tuple\" [{", ".intercalate argStrs}]"

  -- Identifier: (ident name) -> Term.con "name" []
  | .con "ident" [.var name] => s!"Term.con \"{name}\" []"

  -- Literals - strip outer quotes if present (parser keeps them) and re-wrap properly
  | .con "lit" [.con "string" [.lit s]] =>
    let inner := if s.startsWith "\"" && s.endsWith "\"" && s.length ≥ 2
                 then s.drop 1 |>.dropRight 1 else s
    s!"Term.con \"lit\" [Term.con \"string\" [Term.lit \"{inner}\"]]"
  | .con "string" [.lit s] =>
    let inner := if s.startsWith "\"" && s.endsWith "\"" && s.length ≥ 2
                 then s.drop 1 |>.dropRight 1 else s
    s!"Term.con \"string\" [Term.lit \"{inner}\"]"
  | .lit s =>
    -- Strip outer quotes if present (parser keeps them)
    let inner := if s.startsWith "\"" && s.endsWith "\"" && s.length ≥ 2
                 then s.drop 1 |>.dropRight 1 else s
    s!"Term.lit \"{inner}\""
  | .con "unit" [] => "Term.con \"unit\" []"
  | .con "num" [.con "number" [.lit n]] =>
    let inner := if n.startsWith "\"" && n.endsWith "\"" && n.length ≥ 2
                 then n.drop 1 |>.dropRight 1 else n
    s!"Term.con \"num\" [Term.con \"number\" [Term.lit \"{inner}\"]]"

  -- Match expression: generate actual Lean match
  -- Structure: (match scrutinee "with" "|" pat1 "=>" body1 "|" pat2 "=>" body2 ...)
  | .con "match" args => templateMatchToLean args boundVars

  -- Generic fallback
  | .con tag args =>
    let argStrs := args.map (templateToLean · boundVars)
    if argStrs.isEmpty then s!"Term.con \"{tag}\" []"
    else s!"Term.con \"{tag}\" [{", ".intercalate argStrs}]"
end -- close mutual

/-- Pretty-print a transformed Term to Lean 4 code -/
partial def termToLean (t : Term) (indent : Nat := 0) : String :=
  let pad := String.mk (List.replicate (indent * 2) ' ')
  match t with
  | .var name => name
  | .lit s => s
  | .con "seq" children =>
    -- Filter out DImport nodes
    let filtered := children.filter fun c =>
      match c with | .con "DImport" _ => false | _ => true
    filtered.map (termToLean · indent) |> String.intercalate "\n\n"
  | .con "DImport" _ => ""  -- Skip imports (handled separately)
  | .con "DLang" args =>
    -- Extract lang name and body
    let name := args.find? Term.isVar |>.bind Term.getVarName |>.getD "Unknown"
    let body := args.filterMap fun t =>
      match t with
      | .con "DToken" _ => some t
      | .con "DPiece" _ => some t
      | .con "DDerive" _ => some t  -- Include derive declarations
      | _ => none
    s!"{pad}namespace {name}\n\n{body.map (termToLean · (indent + 1)) |> String.intercalate "\n\n"}\n\n{pad}end {name}"
  | .con "DToken" args =>
    -- Comment out token definitions (not valid Lean code)
    let name := args.find? Term.isVar |>.bind Term.getVarName |>.getD "Token"
    s!"{pad}-- Token definitions for: {name} (commented out)"
  | .con "DPiece" args =>
    -- Piece definitions become sections with rules
    let name := args.find? Term.isVar |>.bind Term.getVarName |>.getD "Piece"
    let contents := args.filter fun t =>
      match t with
      | .con "DRule" _ => true  -- Include rules
      | .con "DTest" _ => true  -- Include tests
      | .con "DDerive" _ => true  -- Include derive declarations
      | _ => false  -- Comment out grammar/inductive definitions
    s!"{pad}section {name}\n\n{contents.map (termToLean · (indent + 1)) |> String.intercalate "\n\n"}\n\n{pad}end {name}"
  | .con "DRule" args =>
    -- Transform DRule to Lean 4
    -- Structure: [lit "rule", ident name, lit ":", pat (idx 3), lit "~>", tmpl (idx 5), unit, lit ";"]
    let rawName := match args[1]? with
      | some (.con "ident" [.var n]) => n
      | some (.var n) => n
      | _ => args.find? Term.isVar |>.bind Term.getVarName |>.getD "rule"
    let name := rawName.replace "-" "_"
    let pat := args[3]? |>.getD (.con "unit" [])
    let tmpl := args[5]? |>.getD (.con "unit" [])
    -- Check generation mode
    if genMode == .nativeLean then
      -- Native Lean generation with pattern matching on Expr constructors
      let (patStr, boundVars) := nativePatternToLean pat []
      let tmplStr := nativeTemplateToLean tmpl boundVars
      s!"{pad}def {name} (e : Expr) : Expr :=\n{pad}  match e with\n{pad}  | {patStr} => {tmplStr}\n{pad}  | _ => e"
    else
      -- Term-based generation with Term.con/Term.var
      let (patStr, boundVars) := patternToLean pat []
      let tmplStr := templateToLean tmpl boundVars
      s!"{pad}def {name} (t : Term) : Term :=\n{pad}  match t with\n{pad}  | {patStr} => {tmplStr}\n{pad}  | _ => t"
  | .con "DTest" args =>
    -- Transform DTest directly in printer
    let name := args.find? (fun t => match t with | .lit s => s.startsWith "\"" | _ => false) |>.map (fun t => match t with | .lit s => s | _ => "") |>.getD "test"
    let body := args.find? (fun t => match t with | .con "con" _ => true | _ => false) |>.getD (.con "unit" [])
    s!"{pad}-- Test: {name}\n{pad}-- {termToLean body 0}"
  | .con "DDerive" args =>
    -- Derive traversal operations from grammar
    -- Structure: [lit "derive", deriveKind, lit "for", ident grammarName, deriveWith?, lit ";"]
    let kind := match args[1]? with
      | some (.con "DSubst" _) => "subst"
      | some (.con "DShift" _) => "shift"
      | some (.con "DMap" _) => "map"
      | some (.con "DFold" _) => "fold"
      | some (.con "DCata" _) => "cata"
      | some (.con "DAna" _) => "ana"
      | some (.con "DHylo" _) => "hylo"
      | some (.con "DPara" _) => "para"
      | some (.con "DNormalize" _) => "normalize"
      | some (.con "DConv" _) => "conv"
      | some (.con "DInfer" _) => "infer"
      | some (.con "DCheck" _) => "check"
      | some (.con "DEval" _) => "eval"
      | some (.con "DEq" _) => "eq"
      | _ => "cata"
    let grammarName := match args[3]? with
      | some (.con "ident" [.var n]) => n
      | some (.var n) => n
      | _ => "Term"
    -- Extract binder list from deriveWith if present
    let binders : List String := match args[4]? with
      | some (Term.con "deriveWith" mods) =>
        let extracted : List (List String) := mods.filterMap fun m => match m with
          | Term.con "binderList" ids =>
            some (ids.filterMap fun i => match i with
              | Term.con "ident" [Term.var n] => some n
              | Term.var n => some n
              | _ => none)
          | _ => none
        extracted.flatten
      | _ => binderCtors  -- Default binders
    let binderList := String.intercalate ", " (binders.map (fun b => "\"" ++ b ++ "\""))
    -- Generate actual code based on kind
    match kind with
    | "subst" =>
      let lines := [
        s!"-- Derived substitution for {grammarName}",
        s!"-- Binders: {binders}",
        "mutual",
        s!"partial def subst{grammarName} (k : Nat) (v : Term) (t : Term) : Term :=",
        "  match t with",
        "  | Term.con \"ix\" [Term.con \"number\" [Term.lit n]] =>",
        "    let idx := n.toNat!",
        "    if idx == k then v",
        "    else if idx > k then Term.con \"ix\" [Term.con \"number\" [Term.lit (toString (idx - 1))]]",
        "    else t",
        "  | Term.con tag args =>",
        s!"    let isBinder := [{binderList}].contains tag",
        "    if isBinder && args.length > 0 then",
        s!"      Term.con tag (args.dropLast.map (subst{grammarName} k v) ++ [subst{grammarName} (k + 1) (shift{grammarName} 0 1 v) args.getLast!])",
        "    else",
        s!"      Term.con tag (args.map (subst{grammarName} k v))",
        "  | _ => t",
        "",
        s!"partial def shift{grammarName} (c : Nat) (n : Int) (t : Term) : Term :=",
        "  match t with",
        "  | Term.con \"ix\" [Term.con \"number\" [Term.lit m]] =>",
        "    let idx := m.toNat!",
        "    if idx >= c then Term.con \"ix\" [Term.con \"number\" [Term.lit (toString (Int.toNat (idx + n)))]]",
        "    else t",
        "  | Term.con tag args =>",
        s!"    let isBinder := [{binderList}].contains tag",
        "    if isBinder && args.length > 0 then",
        s!"      Term.con tag (args.dropLast.map (shift{grammarName} c n) ++ [shift{grammarName} (c + 1) n args.getLast!])",
        "    else",
        s!"      Term.con tag (args.map (shift{grammarName} c n))",
        "  | _ => t",
        "end"
      ]
      lines.map (pad ++ ·) |> String.intercalate "\n"
    | "shift" =>
      s!"{pad}-- Derived shift for {grammarName} (included with subst)"
    | "normalize" =>
      let fuelVal : String := match args[4]? with
        | some (Term.con "deriveWith" mods) =>
          let found := mods.filterMap fun m => match m with
            | Term.con "fuelMod" [Term.con "number" [Term.lit n]] => some n
            | _ => none
          match found with
          | h :: _ => h
          | [] => "1000"
        | _ => "1000"
      let lines := [
        s!"-- Derived normalizer for {grammarName} with fuel={fuelVal}",
        "mutual",
        s!"partial def normalize{grammarName} (fuel : Nat) (t : Term) : Term :=",
        "  if fuel == 0 then t else",
        s!"  let t' := step{grammarName} t",
        s!"  if t' == t then t else normalize{grammarName} (fuel - 1) t'",
        "",
        s!"partial def step{grammarName} (t : Term) : Term :=",
        "  match t with",
        s!"  | Term.con \"app\" [Term.con \"lam\" [body], arg] => subst{grammarName} 0 arg body",
        "  | Term.con \"fst\" [Term.con \"pair\" [a, _]] => a",
        "  | Term.con \"snd\" [Term.con \"pair\" [_, b]] => b",
        s!"  | Term.con tag args => Term.con tag (args.map step{grammarName})",
        "  | _ => t",
        "end"
      ]
      lines.map (pad ++ ·) |> String.intercalate "\n"
    | "cata" =>
      let lines := [
        s!"-- Derived catamorphism for {grammarName}",
        s!"partial def cata{grammarName} [Inhabited α] (alg : String → List α → α) (varF : String → α) (t : Term) : α :=",
        "  match t with",
        "  | Term.var n => varF n",
        "  | Term.lit s => alg \"lit\" []",
        s!"  | Term.con tag args => alg tag (args.map (cata{grammarName} alg varF))"
      ]
      lines.map (pad ++ ·) |> String.intercalate "\n"
    | "ana" =>
      let lines := [
        s!"-- Derived anamorphism for {grammarName}",
        s!"partial def ana{grammarName} (coalg : α → (String × List α)) (seed : α) : Term :=",
        "  let (tag, children) := coalg seed",
        s!"  Term.con tag (children.map (ana{grammarName} coalg))"
      ]
      lines.map (pad ++ ·) |> String.intercalate "\n"
    | "hylo" =>
      let lines := [
        s!"-- Derived hylomorphism for {grammarName} (ana then cata)",
        s!"def hylo{grammarName} [Inhabited α] [Inhabited β] (alg : String → List β → β) (coalg : α → (String × List α)) (depth : Nat) (seed : α) : β :=",
        "  if depth == 0 then alg \"⊥\" [] else",
        "  let (tag, children) := coalg seed",
        s!"  alg tag (children.map (hylo{grammarName} alg coalg (depth - 1)))"
      ]
      lines.map (pad ++ ·) |> String.intercalate "\n"
    | "para" =>
      let lines := [
        s!"-- Derived paramorphism for {grammarName} (cata with original)",
        s!"partial def para{grammarName} [Inhabited α] (alg : String → List (Term × α) → α) (varF : String → α) (t : Term) : α :=",
        "  match t with",
        "  | Term.var n => varF n",
        "  | Term.lit s => alg \"lit\" []",
        s!"  | Term.con tag args => alg tag (args.map fun a => (a, para{grammarName} alg varF a))"
      ]
      lines.map (pad ++ ·) |> String.intercalate "\n"
    | "map" =>
      let lines := [
        s!"-- Derived functor map for {grammarName}",
        s!"partial def map{grammarName} (f : Term → Term) (t : Term) : Term :=",
        "  match t with",
        "  | Term.var n => f (Term.var n)",
        "  | Term.lit s => f (Term.lit s)",
        s!"  | Term.con tag args => f (Term.con tag (args.map (map{grammarName} f)))"
      ]
      lines.map (pad ++ ·) |> String.intercalate "\n"
    | "fold" =>
      let lines := [
        s!"-- Derived fold for {grammarName}",
        s!"partial def fold{grammarName} (f : Term → Term → Term) (z : Term) (t : Term) : Term :=",
        "  match t with",
        "  | Term.var _ => z",
        "  | Term.lit _ => z",
        s!"  | Term.con _ args => args.foldl (fun acc a => f acc (fold{grammarName} f z a)) z"
      ]
      lines.map (pad ++ ·) |> String.intercalate "\n"
    | "eq" =>
      let lines := [
        s!"-- Derived structural equality for {grammarName}",
        s!"partial def eq{grammarName} (t1 t2 : Term) : Bool :=",
        "  match t1, t2 with",
        "  | Term.var n1, Term.var n2 => n1 == n2",
        "  | Term.lit s1, Term.lit s2 => s1 == s2",
        "  | Term.con tag1 args1, Term.con tag2 args2 =>",
        s!"    tag1 == tag2 && args1.length == args2.length && (args1.zip args2).all fun (a, b) => eq{grammarName} a b",
        "  | _, _ => false"
      ]
      lines.map (pad ++ ·) |> String.intercalate "\n"
    | "infer" =>
      let lines := [
        s!"-- Derived type inference for {grammarName}",
        s!"partial def infer{grammarName} (ctx : List (String × Term)) (t : Term) : Option Term :=",
        "  match t with",
        "  | Term.var n => ctx.lookup n",
        "  | Term.lit _ => some (Term.con \"Lit\" [])",
        "  | Term.con \"app\" [f, a] =>",
        s!"    match infer{grammarName} ctx f with",
        "    | some (Term.con \"Pi\" [_, _, cod]) => some cod",
        "    | _ => none",
        "  | Term.con \"lam\" [body] =>",
        s!"    match infer{grammarName} ((\"x\", Term.con \"_\" []) :: ctx) body with",
        "    | some bodyTy => some (Term.con \"Pi\" [Term.con \"_\" [], Term.con \"_\" [], bodyTy])",
        "    | _ => none",
        "  | Term.con \"pair\" [a, b] =>",
        s!"    match infer{grammarName} ctx a, infer{grammarName} ctx b with",
        "    | some aTy, some bTy => some (Term.con \"Sigma\" [aTy, bTy])",
        "    | _, _ => none",
        "  | Term.con \"fst\" [p] =>",
        s!"    match infer{grammarName} ctx p with",
        "    | some (Term.con \"Sigma\" [a, _]) => some a",
        "    | _ => none",
        "  | Term.con \"snd\" [p] =>",
        s!"    match infer{grammarName} ctx p with",
        "    | some (Term.con \"Sigma\" [_, b]) => some b",
        "    | _ => none",
        "  | Term.con \"U\" [] => some (Term.con \"U\" [])",
        "  | _ => none"
      ]
      lines.map (pad ++ ·) |> String.intercalate "\n"
    | "check" =>
      let lines := [
        s!"-- Derived type checking for {grammarName}",
        s!"partial def check{grammarName} (ctx : List (String × Term)) (t : Term) (ty : Term) : Bool :=",
        s!"  match infer{grammarName} ctx t with",
        s!"  | some inferredTy => conv{grammarName} inferredTy ty",
        "  | none => false"
      ]
      lines.map (pad ++ ·) |> String.intercalate "\n"
    | "conv" =>
      let lines := [
        s!"-- Derived conversion check for {grammarName}",
        s!"def conv{grammarName} (t1 t2 : Term) : Bool :=",
        s!"  normalize{grammarName} 1000 t1 == normalize{grammarName} 1000 t2"
      ]
      lines.map (pad ++ ·) |> String.intercalate "\n"
    | _ =>
      s!"{pad}-- Derived {kind} for {grammarName}\n{pad}-- (TODO: implement {kind} generation)"
  -- Macro: definitional abbreviation (inline expansion)
  | .con "DMacro" args =>
    let name := args[1]?.bind Term.getVarName |>.getD "macro"
    let params := match args[2]? with
      | some (.con "macroParams" ps) => ps.filterMap Term.getVarName
      | _ => []
    let body := args.getLast? |>.getD (.con "unit" [])
    let paramStr := if params.isEmpty then "" else s!" ({String.intercalate " " params} : Term)"
    let lines := [
      s!"-- Macro: {name}",
      s!"@[inline] def {name}{paramStr} : Term :=",
      s!"  {termToLean body 0}"
    ]
    lines.map (pad ++ ·) |> String.intercalate "\n"
  -- Algebra laws: generate law lemmas (as comments for now)
  | .con "DAlgebra" args =>
    let name := args[1]?.bind Term.getVarName |>.getD "algebra"
    let sort := args[3]?.bind Term.getVarName |>.getD "sort"
    let laws := args.filter fun t => match t with | .con "lawEq" _ => true | .con "lawEq2" _ => true | _ => false
    let lawLines := laws.map fun law =>
      match law with
      | .con "lawEq" [.var n, lhs, _, rhs, _] => s!"  -- {n}: {termToLean lhs 0} = {termToLean rhs 0}"
      | .con "lawEq2" _ => s!"  -- (paired law)"
      | _ => ""
    let lines := [
      s!"-- Algebra {name} for {sort}",
      s!"-- Laws (used by normalizer):"
    ] ++ lawLines
    lines.map (pad ++ ·) |> String.intercalate "\n"
  -- Grammar algebra operations (categorical constructions)
  | .con "DPushout" args =>
    let g1 := args[1]?.bind Term.getVarName |>.getD "G1"
    let g2 := args[2]?.bind Term.getVarName |>.getD "G2"
    let along := args[4]?.bind Term.getVarName |>.getD "f"
    s!"{pad}-- Pushout: {g1} +_{along} {g2}\n{pad}-- (Universal property: merge grammars along shared subgrammar)"
  | .con "DPullback" args =>
    let g1 := args[1]?.bind Term.getVarName |>.getD "G1"
    let g2 := args[2]?.bind Term.getVarName |>.getD "G2"
    let over := args[4]?.bind Term.getVarName |>.getD "f"
    s!"{pad}-- Pullback: {g1} ×_{over} {g2}\n{pad}-- (Universal property: restrict grammars to common fragment)"
  | .con "DQuotient" args =>
    let g := args[1]?.bind Term.getVarName |>.getD "G"
    let rel := args[3]?.bind Term.getVarName |>.getD "R"
    s!"{pad}-- Quotient: {g} / {rel}\n{pad}-- (Identify terms related by {rel})"
  | .con "DCoproduct" args =>
    let g1 := args[1]?.bind Term.getVarName |>.getD "G1"
    let g2 := args[2]?.bind Term.getVarName |>.getD "G2"
    s!"{pad}-- Coproduct: {g1} + {g2}\n{pad}-- (Disjoint union of grammars)"
  | .con "DProduct" args =>
    let g1 := args[1]?.bind Term.getVarName |>.getD "G1"
    let g2 := args[2]?.bind Term.getVarName |>.getD "G2"
    s!"{pad}-- Product: {g1} × {g2}\n{pad}-- (Paired terms from both grammars)"
  | .con "DExtends" args =>
    let child := args[0]?.bind Term.getVarName |>.getD "Child"
    let parent := args[2]?.bind Term.getVarName |>.getD "Parent"
    s!"{pad}-- Extension: {child} extends {parent}\n{pad}-- (Inherit all productions and rules from parent)"
  | .con "DInitial" args =>
    let g := args[1]?.bind Term.getVarName |>.getD "G"
    s!"{pad}-- Initial: ⊥ → {g}\n{pad}-- (Empty grammar, unique morphism to any grammar)"
  | .con "DTerminal" args =>
    let g := args[1]?.bind Term.getVarName |>.getD "G"
    s!"{pad}-- Terminal: {g} → ⊤\n{pad}-- (Unit grammar, unique morphism from any grammar)"
  -- Effect algebra handlers
  | .con "DEffect" args =>
    let name := args[1]?.bind Term.getVarName |>.getD "Effect"
    s!"{pad}-- Effect: {name}\n{pad}-- (Algebraic effect with operations and handlers)"
  | .con "DHandler" args =>
    let name := args[1]?.bind Term.getVarName |>.getD "Handler"
    let eff := args[3]?.bind Term.getVarName |>.getD "Effect"
    s!"{pad}-- Handler: {name} for {eff}\n{pad}-- (Effect handler interpreting operations)"
  | .con "DFree" args =>
    let name := args[1]?.bind Term.getVarName |>.getD "Free"
    let functor := args[3]?.bind Term.getVarName |>.getD "F"
    s!"{pad}-- Free monad: {name} over {functor}\n{pad}-- (Initial algebra: μX. A + F X)"
  | .con "DCofree" args =>
    let name := args[1]?.bind Term.getVarName |>.getD "Cofree"
    let functor := args[3]?.bind Term.getVarName |>.getD "F"
    s!"{pad}-- Cofree comonad: {name} over {functor}\n{pad}-- (Terminal coalgebra: νX. A × F X)"
  | .con "DMonad" args =>
    let name := args[1]?.bind Term.getVarName |>.getD "M"
    s!"{pad}-- Monad: {name}\n{pad}-- (Generates return, bind, and monad laws)"
  -- Optics: bidirectional transformations
  | .con "DLens" args =>
    let name := args[1]?.bind Term.getVarName |>.getD "lens"
    let s := args[3]?.bind Term.getVarName |>.getD "S"
    let a := args[5]?.bind Term.getVarName |>.getD "A"
    s!"{pad}-- Lens: {name} : {s} ⟷ {a}\n{pad}-- get : {s} → {a}, set : {s} → {a} → {s}\n{pad}-- Laws: get∘set = id, set∘get = id, set∘set = set"
  | .con "DPrism" args =>
    let name := args[1]?.bind Term.getVarName |>.getD "prism"
    let s := args[3]?.bind Term.getVarName |>.getD "S"
    let a := args[5]?.bind Term.getVarName |>.getD "A"
    s!"{pad}-- Prism: {name} : {s} ⟷ {a}\n{pad}-- match : {s} → {a} + {s}, build : {a} → {s}"
  | .con "DIso" args =>
    let name := args[1]?.bind Term.getVarName |>.getD "iso"
    let a := args[3]?.bind Term.getVarName |>.getD "A"
    let b := args[5]?.bind Term.getVarName |>.getD "B"
    s!"{pad}-- Iso: {name} : {a} ≅ {b}\n{pad}-- to : {a} → {b}, from : {b} → {a}\n{pad}-- Laws: to∘from = id, from∘to = id"
  | .con "DTraversal" args =>
    let name := args[1]?.bind Term.getVarName |>.getD "traversal"
    let s := args[3]?.bind Term.getVarName |>.getD "S"
    let a := args[5]?.bind Term.getVarName |>.getD "A"
    s!"{pad}-- Traversal: {name} : {s} ⟿ {a}\n{pad}-- traverse : ∀F. Applicative F ⇒ ({a} → F {a}) → {s} → F {s}"
  -- Adjunctions: Free ⊣ Forgetful
  | .con "DAdjunction" args =>
    let left := args[0]?.bind Term.getVarName |>.getD "F"
    let right := args[2]?.bind Term.getVarName |>.getD "G"
    let c := args[4]?.bind Term.getVarName |>.getD "C"
    let d := args[6]?.bind Term.getVarName |>.getD "D"
    s!"{pad}-- Adjunction: {left} ⊣ {right} : {c} ⇄ {d}\n{pad}-- unit : Id → G∘F, counit : F∘G → Id\n{pad}-- Hom({left} a, b) ≅ Hom(a, {right} b)"
  | .con "DLeftAdj" args =>
    let left := args[2]?.bind Term.getVarName |>.getD "F"
    let right := args[4]?.bind Term.getVarName |>.getD "G"
    s!"{pad}-- Left adjoint: {left} ⊣ {right}\n{pad}-- (Free construction, preserves colimits)"
  | .con "DRightAdj" args =>
    let right := args[2]?.bind Term.getVarName |>.getD "G"
    let left := args[4]?.bind Term.getVarName |>.getD "F"
    s!"{pad}-- Right adjoint: {left} ⊣ {right}\n{pad}-- (Forgetful functor, preserves limits)"
  -- Kan extensions
  | .con "DLan" args =>
    let f := args[1]?.bind Term.getVarName |>.getD "F"
    let k := args[3]?.bind Term.getVarName |>.getD "K"
    s!"{pad}-- Left Kan extension: Lan_{k} {f}\n{pad}-- Universal property: Nat(Lan F, G) ≅ Nat(F, G∘K)"
  | .con "DRan" args =>
    let f := args[1]?.bind Term.getVarName |>.getD "F"
    let k := args[3]?.bind Term.getVarName |>.getD "K"
    s!"{pad}-- Right Kan extension: Ran_{k} {f}\n{pad}-- Universal property: Nat(G, Ran F) ≅ Nat(G∘K, F)"
  | .con "DYoneda" args =>
    let c := args[1]?.bind Term.getVarName |>.getD "C"
    s!"{pad}-- Yoneda embedding: y : {c} → [{c}^op, Set]\n{pad}-- Nat(y(a), F) ≅ F(a)  (Yoneda lemma)"
  | .con "DCodensity" args =>
    let f := args[1]?.bind Term.getVarName |>.getD "F"
    s!"{pad}-- Codensity monad: Ran_{f} {f}\n{pad}-- Always a monad, even if F isn't"
  -- Operads
  | .con "DOperad" args =>
    let name := args[1]?.bind Term.getVarName |>.getD "O"
    s!"{pad}-- Operad: {name}\n{pad}-- Multi-arity operations with composition"
  | .con "DOperadAlg" args =>
    let name := args[1]?.bind Term.getVarName |>.getD "A"
    let op := args[3]?.bind Term.getVarName |>.getD "O"
    s!"{pad}-- {op}-algebra: {name}\n{pad}-- Object with {op}-operations satisfying coherence"
  -- Natural transformations
  | .con "DNat" args =>
    let name := args[0]?.bind Term.getVarName |>.getD "α"
    let f := args[4]?.bind Term.getVarName |>.getD "F"
    let g := args[6]?.bind Term.getVarName |>.getD "G"
    s!"{pad}-- Natural transformation: {name} : {f} ⟹ {g}\n{pad}-- Naturality: G(f) ∘ α_A = α_B ∘ F(f)"
  | .con "DDinat" args =>
    let name := args[1]?.bind Term.getVarName |>.getD "δ"
    let f := args[3]?.bind Term.getVarName |>.getD "F"
    let g := args[5]?.bind Term.getVarName |>.getD "G"
    s!"{pad}-- Dinatural transformation: {name} : {f} ⤇ {g}\n{pad}-- Wedge condition for profunctors"
  | .con "DExtranat" args =>
    let name := args[1]?.bind Term.getVarName |>.getD "ε"
    let f := args[3]?.bind Term.getVarName |>.getD "F"
    let g := args[5]?.bind Term.getVarName |>.getD "G"
    s!"{pad}-- Extranatural transformation: {name} : {f} ⟾ {g}\n{pad}-- Extranatural in both variance positions"
  -- RosettaMath: Layer 1 - Initial Algebras
  | .con "DFunctor" args =>
    let name := args[1]?.bind Term.getVarName |>.getD "F"
    s!"{pad}-- Functor: {name} : Type → Type\n{pad}-- Defines shape of recursive data"
  | .con "DMu" args =>
    let f := args[1]?.bind Term.getVarName |>.getD "F"
    s!"{pad}-- Initial algebra: μ{f}\n{pad}-- Least fixed point: μF ≅ F(μF)"
  | .con "DNu" args =>
    let f := args[1]?.bind Term.getVarName |>.getD "F"
    s!"{pad}-- Terminal coalgebra: ν{f}\n{pad}-- Greatest fixed point: νF ≅ F(νF)"
  | .con "DCata" args =>
    let name := args[1]?.bind Term.getVarName |>.getD "fold"
    let target := args[3]?.bind Term.getVarName |>.getD "Term"
    s!"{pad}-- Catamorphism: {name} for {target}\n{pad}-- The universal fold: (F A → A) → μF → A"
  | .con "DAna" args =>
    let name := args[1]?.bind Term.getVarName |>.getD "unfold"
    let target := args[3]?.bind Term.getVarName |>.getD "Term"
    s!"{pad}-- Anamorphism: {name} for {target}\n{pad}-- The universal unfold: (A → F A) → A → νF"
  | .con "DHylo" args =>
    let name := args[1]?.bind Term.getVarName |>.getD "hylo"
    s!"{pad}-- Hylomorphism: {name}\n{pad}-- ana ; cata with no intermediate data structure"
  | .con "DPara" args =>
    let name := args[1]?.bind Term.getVarName |>.getD "para"
    let target := args[3]?.bind Term.getVarName |>.getD "Term"
    s!"{pad}-- Paramorphism: {name} for {target}\n{pad}-- Fold with access to original: (F (μF × A) → A) → μF → A"
  | .con "DBisim" args =>
    let name := args[1]?.bind Term.getVarName |>.getD "bisim"
    s!"{pad}-- Bisimulation: {name}\n{pad}-- Equality for coalgebras (observational equivalence)"
  -- RosettaMath: Layer 4 - Comonads
  | .con "DComonad" args =>
    let name := args[1]?.bind Term.getVarName |>.getD "W"
    s!"{pad}-- Comonad: {name}\n{pad}-- Generates extract, extend, duplicate"
  -- RosettaMath: Layer 5 - Profunctors
  | .con "DProfunctor" args =>
    let name := args[1]?.bind Term.getVarName |>.getD "P"
    let c := args[3]?.bind Term.getVarName |>.getD "C"
    let d := args[5]?.bind Term.getVarName |>.getD "D"
    s!"{pad}-- Profunctor: {name} : {c}^op × {d} → Set\n{pad}-- Bifunctor contravariant in first arg"
  | .con "DAffine" args =>
    let name := args[1]?.bind Term.getVarName |>.getD "affine"
    let s := args[3]?.bind Term.getVarName |>.getD "S"
    let a := args[5]?.bind Term.getVarName |>.getD "A"
    s!"{pad}-- Affine: {name} : {s} ⤳ {a}\n{pad}-- At most one target (0 or 1)"
  | .con "DGetter" args =>
    let name := args[1]?.bind Term.getVarName |>.getD "getter"
    let s := args[3]?.bind Term.getVarName |>.getD "S"
    let a := args[5]?.bind Term.getVarName |>.getD "A"
    s!"{pad}-- Getter: {name} : {s} → {a}\n{pad}-- Read-only access"
  | .con "DSetter" args =>
    let name := args[1]?.bind Term.getVarName |>.getD "setter"
    let s := args[3]?.bind Term.getVarName |>.getD "S"
    let a := args[5]?.bind Term.getVarName |>.getD "A"
    s!"{pad}-- Setter: {name} : {s} ← {a}\n{pad}-- Write-only access"
  | .con "DReview" args =>
    let name := args[1]?.bind Term.getVarName |>.getD "review"
    let a := args[3]?.bind Term.getVarName |>.getD "A"
    let s := args[5]?.bind Term.getVarName |>.getD "S"
    s!"{pad}-- Review: {name} : {a} ↩ {s}\n{pad}-- Construct whole from part"
  -- RosettaMath: Layer 6 - Free/Forgetful
  | .con "DFreeAdj" args =>
    let name := args[1]?.bind Term.getVarName |>.getD "Free"
    let target := args[3]?.bind Term.getVarName |>.getD "Alg"
    s!"{pad}-- Free construction: {name} for {target}\n{pad}-- Left adjoint to forgetful"
  | .con "DForgetful" args =>
    let name := args[1]?.bind Term.getVarName |>.getD "U"
    let source := args[3]?.bind Term.getVarName |>.getD "Alg"
    let target := args[5]?.bind Term.getVarName |>.getD "Set"
    s!"{pad}-- Forgetful: {name} : {source} → {target}\n{pad}-- Forgets algebraic structure"
  -- RosettaMath: Layer 7 - More Kan
  | .con "DCoYoneda" args =>
    let c := args[1]?.bind Term.getVarName |>.getD "C"
    s!"{pad}-- CoYoneda: {c} → [C, Set]^op\n{pad}-- Density comonad representation"
  | .con "DDensity" args =>
    let f := args[1]?.bind Term.getVarName |>.getD "F"
    s!"{pad}-- Density comonad: Lan_{f} {f}\n{pad}-- Always a comonad"
  -- RosettaMath: Judgments
  | .con "DJudgment" args =>
    let name := args[1]?.bind Term.getVarName |>.getD "J"
    s!"{pad}-- Judgment: {name}\n{pad}-- Typing rules with premises and conclusions"
  -- RosettaMath: Properties and Examples
  | .con "DProperty" args =>
    let name := match args[1]? with
      | some (.lit s) => s
      | _ => "property"
    s!"{pad}-- Property: {name}\n{pad}-- QuickCheck-style universal property"
  | .con "DExample" args =>
    let name := match args[1]? with
      | some (.lit s) => s
      | _ => "example"
    s!"{pad}-- Example: {name}"
  -- Comment out grammar/parser definitions since they're not valid Lean
  | .con "inductive" [.var name, _body] =>
    s!"{pad}-- Grammar: {name}"
  | .con "inductive" args =>
    let name := args.head?.map (termToLean · 0) |>.getD "unknown"
    s!"{pad}-- Grammar: {name}"
  | .con "choice" [left, right] =>
    s!"({termToLean left 0} <|> {termToLean right 0})"
  | .con "char" [.lit c] =>
    s!"char {c}"
  | .con "many" [inner] =>
    s!"many ({termToLean inner 0})"
  | .con "optional" [inner] =>
    s!"optional ({termToLean inner 0})"
  | .con "ref" [.var name] =>
    name
  | .con "terminal" [.lit s] =>
    s!"str {s}"
  | .con "def" [.var name, pat, tmpl] =>
    s!"{pad}def {name} : Rule :=\n{pad}  match · with\n{pad}  | {termToLean pat 0} => {termToLean tmpl 0}\n{pad}  | t => t"
  | .con "def" args =>
    let name := args.head?.map (termToLean · 0) |>.getD "unknown"
    s!"{pad}-- def {name} ..."
  | .con "example" [.lit name, body] =>
    s!"{pad}-- test {name}: {termToLean body 0}"
  | .con "app" (head :: args) =>
    s!"({termToLean head 0} {args.map (termToLean · 0) |> String.intercalate " "})"
  | .con "metavar" [.var name] =>
    s!"${name}"
  | .con "var" [.lit "$", .con "ident" [.var name]] =>
    s!"${name}"
  | .con "var" args =>
    -- Fallback for var nodes
    let inner := args.map (termToLean · 0) |> String.intercalate " "
    s!"$({inner})"
  | .con "ident" [.var name] =>
    name
  | .con "unit" [] =>
    "()"
  | .con "con" args =>
    -- S-expression: (con arg1 arg2 ...)
    let inner := args.filter (fun t => match t with | .lit "(" => false | .lit ")" => false | _ => true)
    s!"({inner.map (termToLean · 0) |> String.intercalate " "})"
  | .con tag args =>
    if args.isEmpty then tag
    else s!"({tag} {args.map (termToLean · 0) |> String.intercalate " "})"

def main : IO Unit := do
  -- Step 0: Initialize runtime by loading Bootstrap.lego
  let rt ← Lego.Runtime.init

  -- Load transformation rules
  let c2rContent ← IO.FS.readFile "./src/Rosetta/cubical2rosetta.lego"
  let c2rAst ← match parseLegoFileE rt c2rContent with
    | .error e => IO.eprintln s!"parse cubical2rosetta failed: {e}"; return
    | .ok ast => pure ast
  let rules1 := extractRules c2rAst

  let r2lContent ← IO.FS.readFile "./src/Rosetta/rosetta2lean.lego"
  let r2lAst ← match parseLegoFileE rt r2lContent with
    | .error e => IO.eprintln s!"parse rosetta2lean failed: {e}"; return
    | .ok ast => pure ast
  let rules2 := extractRules r2lAst

  -- Process multiple .lego files
  let files := [
    -- Core cubical files
    ("./test/Redtt.lego", "./generated/Cubical/Redtt.lean"),
    ("./src/Lego/Cubical/CubicalTT.lego", "./generated/Cubical/CubicalTT.lean"),
    ("./src/Lego/Cubical/Red.lego", "./generated/Cubical/Red.lean"),
    -- Generated cubical modules (~6800 lines)
    ("./src/Lego/Cubical/generated/Cofibration.lego", "./generated/Cubical/Cofibration.lean"),
    ("./src/Lego/Cubical/generated/Conversion.lego", "./generated/Cubical/Conversion.lean"),
    ("./src/Lego/Cubical/generated/Core.lego", "./generated/Cubical/Core.lean"),
    ("./src/Lego/Cubical/generated/Datatype.lego", "./generated/Cubical/Datatype.lean"),
    ("./src/Lego/Cubical/generated/Domain.lego", "./generated/Cubical/Domain.lean"),
    ("./src/Lego/Cubical/generated/Elaborate.lego", "./generated/Cubical/Elaborate.lean"),
    ("./src/Lego/Cubical/generated/ExtType.lego", "./generated/Cubical/ExtType.lean"),
    ("./src/Lego/Cubical/generated/FHCom.lego", "./generated/Cubical/FHCom.lean"),
    ("./src/Lego/Cubical/generated/GlobalEnv.lego", "./generated/Cubical/GlobalEnv.lean"),
    ("./src/Lego/Cubical/generated/HIT.lego", "./generated/Cubical/HIT.lean"),
    ("./src/Lego/Cubical/generated/Kan.lego", "./generated/Cubical/Kan.lean"),
    ("./src/Lego/Cubical/generated/Module.lego", "./generated/Cubical/Module.lean"),
    ("./src/Lego/Cubical/generated/Quote.lego", "./generated/Cubical/Quote.lean"),
    ("./src/Lego/Cubical/generated/RefineMonad.lego", "./generated/Cubical/RefineMonad.lean"),
    ("./src/Lego/Cubical/generated/Semantics.lego", "./generated/Cubical/Semantics.lean"),
    ("./src/Lego/Cubical/generated/Signature.lego", "./generated/Cubical/Signature.lean"),
    ("./src/Lego/Cubical/generated/Splice.lego", "./generated/Cubical/Splice.lean"),
    ("./src/Lego/Cubical/generated/SubType.lego", "./generated/Cubical/SubType.lean"),
    ("./src/Lego/Cubical/generated/Tactic.lego", "./generated/Cubical/Tactic.lean"),
    ("./src/Lego/Cubical/generated/TermBuilder.lego", "./generated/Cubical/TermBuilder.lean"),
    ("./src/Lego/Cubical/generated/TypeAttrs.lego", "./generated/Cubical/TypeAttrs.lean"),
    ("./src/Lego/Cubical/generated/Unify.lego", "./generated/Cubical/Unify.lean"),
    ("./src/Lego/Cubical/generated/VType.lego", "./generated/Cubical/VType.lean"),
    ("./src/Lego/Cubical/generated/Visitor.lego", "./generated/Cubical/Visitor.lean")
    -- Cool.lego has unsupported 'for' syntax in type constraints, skipped for now
  ]

  IO.FS.createDirAll "./generated/Cubical"

  -- Header for generated files depends on generation mode
  let header := if genMode == .nativeLean then
    "/-\n  AUTO-GENERATED from .lego files\n  Do not edit directly.\n-/\n\nimport Lego.Cubical.Core\n\nopen Lego.Core\nopen Lego.Core.Expr\n\n"
  else
    "/-\n  AUTO-GENERATED from .lego files\n  Do not edit directly.\n-/\n\nimport Lego.Algebra\n\nopen Lego\n\n"

  for (input, output) in files do
    let content ← IO.FS.readFile input
    match parseLegoFileE rt content with
    | .error e => IO.eprintln s!"parse {input} failed: {e}"
    | .ok ast =>
      let lifted := transform rules1 ast
      let lean := transform rules2 lifted
      let leanCode := header ++ termToLean lean
      IO.FS.writeFile output leanCode
      IO.println s!"Wrote {output}"
