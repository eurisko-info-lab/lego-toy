/-
  UnifiedCodeGen.lean: Language-agnostic code generation via CodeGen AST

  This replaces the duplicated termToLeanExpr/termToScalaExpr/etc. functions
  with a single set of functions that produce CodeGen.Frag AST nodes.

  The target-specific rendering is handled by:
  1. LangConfig (keywords, escaping, syntax details)
  2. CodeGen.render (Frag → String)
-/

import Lego.Algebra
import Rosetta.CodeGen
import Std.Data.HashSet

namespace UnifiedCodeGen

open CodeGen
open Lego (Term)

/-! ## Pattern Generation State -/

/-- State for tracking duplicate pattern variables -/
structure PatGenState where
  seen    : Std.HashSet String
  counter : Nat
  guards  : List (String × String)  -- (freshName, originalName)

instance : Inhabited PatGenState where
  default := { seen := {}, counter := 0, guards := [] }

def PatGenState.init : PatGenState := default

/-! ## Core Term → Frag Conversion -/

/-- Collect pattern variable names from a Term (variables starting with $) -/
partial def collectPatternVars (t : Term) : List String :=
  match t with
  | .var n => if n.startsWith "$" then [n.drop 1] else []
  | .lit _ => []
  | .con _ args => args.flatMap collectPatternVars

/-- Convert a Term to a pattern Frag, tracking duplicates -/
partial def termToPatternFrag (cfg : LangConfig) (t : Term) (st : PatGenState)
    : (Frag × PatGenState) :=
  match t with
  | .var n =>
    if n.startsWith "$" then
      let varName := sanitizeVar cfg (n.drop 1)
      if st.seen.contains varName then
        -- Duplicate: generate fresh name
        let freshName := varName ++ "_" ++ toString st.counter
        (.Ident freshName, { st with counter := st.counter + 1, guards := (freshName, varName) :: st.guards })
      else
        (.Ident varName, { st with seen := st.seen.insert varName })
    else
      -- Literal match
      (.FSeq [.Raw ".Lit \"", .Raw (cfg.escapeString n), .Raw "\""], st)
  | .lit s =>
    (.FSeq [.Raw ".Lit \"", .Raw (cfg.escapeString s), .Raw "\""], st)
  | .con name args =>
    if args.isEmpty then
      (.FSeq [.Raw ".Con \"", .Raw (cfg.escapeString name), .Raw "\" ", .Raw cfg.listEmpty], st)
    else
      let (argFrags, finalSt) := args.foldl (fun (accFrags, accSt) arg =>
        let (f, newSt) := termToPatternFrag cfg arg accSt
        (accFrags ++ [f], newSt)
      ) ([], st)
      let frag := Frag.FSeq [
        .Raw ".Con \"", .Raw (cfg.escapeString name), .Raw "\" ",
        .Raw cfg.listStart, .Sep ", " argFrags, .Raw cfg.listEnd
      ]
      (frag, finalSt)

/-- Convert a Term to an expression Frag.
    boundVars contains variables bound in the pattern (from collectPatternVars). -/
partial def termToExprFrag (cfg : LangConfig) (t : Term) (boundVars : List String) : Frag :=
  match t with
  | .var n =>
    if n.startsWith "$" then
      let varName := n.drop 1
      if boundVars.contains varName then
        .Ident (sanitizeVar cfg varName)  -- Use as variable reference
      else
        .FSeq [.Raw ".Var \"", .Raw (cfg.escapeString varName), .Raw "\""]  -- Free var
    else
      .FSeq [.Raw ".Lit \"", .Raw (cfg.escapeString n), .Raw "\""]
  | .lit s =>
    .FSeq [.Raw ".Lit \"", .Raw (cfg.escapeString s), .Raw "\""]
  | .con name args =>
    if args.isEmpty then
      .FSeq [.Raw ".Con \"", .Raw (cfg.escapeString name), .Raw "\" ", .Raw cfg.listEmpty]
    else
      let argFrags := args.map (fun a => termToExprFrag cfg a boundVars)
      .FSeq [
        .Raw ".Con \"", .Raw (cfg.escapeString name), .Raw "\" ",
        .Raw cfg.listStart, .Sep ", " argFrags, .Raw cfg.listEnd
      ]

/-! ## Lean-Specific Emission -/

/-- Generate a Lean rewrite rule function -/
def emitLeanRewriteRule (name : String) (lhs rhs : Term) : Frag :=
  let cfg := leanConfig
  let patVars := collectPatternVars lhs
  let (patFrag, genSt) := termToPatternFrag cfg lhs PatGenState.init
  let resFrag := termToExprFrag cfg rhs patVars

  if genSt.guards.isEmpty then
    .Lines [
      .Line (.FSeq [.Keyword "def", .Raw " ", .Ident name, .Raw " : Term → Option Term"]),
      .Line (.FSeq [.Raw "  | ", patFrag, .Raw " => some (", resFrag, .Raw ")"]),
      .Line (.Raw "  | _ => none"),
      .FEmpty
    ]
  else
    let guardChecks := genSt.guards.map (fun (fresh, orig) =>
      .FSeq [.Ident fresh, .Op " == ", .Ident orig])
    .Lines [
      .Line (.FSeq [.Keyword "def", .Raw " ", .Ident name, .Raw " : Term → Option Term"]),
      .Line (.FSeq [.Raw "  | ", patFrag, .Raw " => if ", .Sep " && " guardChecks,
                    .Raw " then some (", resFrag, .Raw ") else none"]),
      .Line (.Raw "  | _ => none"),
      .FEmpty
    ]

/-- Generate a Lean inductive type -/
def emitLeanInductive (name : String) (ctors : List (String × List String)) : Frag :=
  let ctorFrags := ctors.map fun (ctorName, args) =>
    if args.isEmpty then
      .Line (.FSeq [.Raw "  | ", .Ident ctorName, .Raw " : ", .Ident name])
    else
      let argTypes := args.map (fun ty => .FSeq [.Ident ty, .Raw " → "])
      .Line (.FSeq ([.Raw "  | ", .Ident ctorName, .Raw " : "] ++ argTypes ++ [.Ident name]))
  .Lines ([
    .Line (.FSeq [.Keyword "inductive", .Raw " ", .Ident name, .Raw " where"]),
  ] ++ ctorFrags ++ [
    .Line (.Raw "  deriving Repr, BEq"),
    .FEmpty
  ])

/-! ## Scala-Specific Emission -/

/-- Generate a Scala rewrite rule function -/
def emitScalaRewriteRule (name : String) (lhs rhs : Term) : Frag :=
  let cfg := scalaConfig
  let patVars := collectPatternVars lhs
  let (patFrag, genSt) := termToPatternFrag cfg lhs PatGenState.init
  let resFrag := termToExprFrag cfg rhs patVars

  if genSt.guards.isEmpty then
    .Lines [
      .Line (.FSeq [.Keyword "def", .Raw " ", .Ident name, .Raw "(t: Term): Option[Term] = t match {"]),
      .Line (.FSeq [.Raw "  case ", patFrag, .Raw " => Some(", resFrag, .Raw ")"]),
      .Line (.Raw "  case _ => None"),
      .Line (.Raw "}"),
      .FEmpty
    ]
  else
    let guardChecks := genSt.guards.map (fun (fresh, orig) =>
      .FSeq [.Ident fresh, .Op " == ", .Ident orig])
    .Lines [
      .Line (.FSeq [.Keyword "def", .Raw " ", .Ident name, .Raw "(t: Term): Option[Term] = t match {"]),
      .Line (.FSeq [.Raw "  case ", patFrag, .Raw " if ", .Sep " && " guardChecks,
                    .Raw " => Some(", resFrag, .Raw ")"]),
      .Line (.Raw "  case _ => None"),
      .Line (.Raw "}"),
      .FEmpty
    ]

/-- Generate a Scala sealed trait + case classes -/
def emitScalaADT (name : String) (ctors : List (String × List String)) : Frag :=
  let ctorFrags := ctors.map fun (ctorName, args) =>
    if args.isEmpty then
      .Line (.FSeq [.Keyword "case", .Raw " ", .Keyword "object", .Raw " ",
                    .Ident ctorName, .Raw " extends ", .Ident name])
    else
      let argParams := args.mapIdx (fun j ty => .FSeq [.Ident s!"arg{j}", .Raw ": ", .Ident ty])
      .Line (.FSeq [.Keyword "case", .Raw " ", .Keyword "class", .Raw " ",
                    .Ident ctorName, .Raw "(", .Sep ", " argParams, .Raw ") extends ", .Ident name])
  .Lines ([
    .Line (.FSeq [.Keyword "sealed", .Raw " ", .Keyword "trait", .Raw " ", .Ident name]),
  ] ++ ctorFrags ++ [.FEmpty])

/-! ## Haskell-Specific Emission -/

/-- Generate a Haskell rewrite rule function -/
def emitHaskellRewriteRule (name : String) (lhs rhs : Term) : Frag :=
  let cfg := haskellConfig
  let patVars := collectPatternVars lhs
  let (patFrag, genSt) := termToPatternFrag cfg lhs PatGenState.init
  let resFrag := termToExprFrag cfg rhs patVars

  if genSt.guards.isEmpty then
    .Lines [
      .Line (.FSeq [.Ident name, .Raw " :: Term -> Maybe Term"]),
      .Line (.FSeq [.Ident name, .Raw " (", patFrag, .Raw ") = Just (", resFrag, .Raw ")"]),
      .Line (.FSeq [.Ident name, .Raw " _ = Nothing"]),
      .FEmpty
    ]
  else
    let guardChecks := genSt.guards.map (fun (fresh, orig) =>
      .FSeq [.Ident fresh, .Op " == ", .Ident orig])
    .Lines [
      .Line (.FSeq [.Ident name, .Raw " :: Term -> Maybe Term"]),
      .Line (.FSeq [.Ident name, .Raw " (", patFrag, .Raw ") | ", .Sep " && " guardChecks,
                    .Raw " = Just (", resFrag, .Raw ")"]),
      .Line (.FSeq [.Ident name, .Raw " _ = Nothing"]),
      .FEmpty
    ]

/-- Generate a Haskell data type -/
def emitHaskellADT (name : String) (ctors : List (String × List String)) : Frag :=
  let ctorFrags := ctors.mapIdx fun i (ctorName, args) =>
    let pfx := if i == 0 then "= " else "| "
    if args.isEmpty then
      .FSeq [.Raw pfx, .Ident ctorName]
    else
      .FSeq ([.Raw pfx, .Ident ctorName] ++ args.map (fun ty => .FSeq [.Raw " ", .Ident ty]))
  .Lines [
    .Line (.FSeq [.Keyword "data", .Raw " ", .Ident name]),
    .Indent (.Lines (ctorFrags.map .Line)),
    .Line (.Raw "  deriving (Show, Eq)"),
    .FEmpty
  ]

/-! ## Rust-Specific Emission -/

/-- Generate a Rust rewrite rule function -/
def emitRustRewriteRule (name : String) (lhs rhs : Term) : Frag :=
  let cfg := rustConfig
  let patVars := collectPatternVars lhs
  let (patFrag, genSt) := termToPatternFrag cfg lhs PatGenState.init
  let resFrag := termToExprFrag cfg rhs patVars

  if genSt.guards.isEmpty then
    .Lines [
      .Line (.FSeq [.Keyword "pub", .Raw " ", .Keyword "fn", .Raw " ", .Ident name,
                    .Raw "(t: &Term) -> Option<Term> {"]),
      .Line (.FSeq [.Raw "    match t {"]),
      .Line (.FSeq [.Raw "        ", patFrag, .Raw " => Some(", resFrag, .Raw "),"]),
      .Line (.Raw "        _ => None,"),
      .Line (.Raw "    }"),
      .Line (.Raw "}"),
      .FEmpty
    ]
  else
    let guardChecks := genSt.guards.map (fun (fresh, orig) =>
      .FSeq [.Ident fresh, .Op " == ", .Ident orig])
    .Lines [
      .Line (.FSeq [.Keyword "pub", .Raw " ", .Keyword "fn", .Raw " ", .Ident name,
                    .Raw "(t: &Term) -> Option<Term> {"]),
      .Line (.FSeq [.Raw "    match t {"]),
      .Line (.FSeq [.Raw "        ", patFrag, .Raw " if ", .Sep " && " guardChecks,
                    .Raw " => Some(", resFrag, .Raw "),"]),
      .Line (.Raw "        _ => None,"),
      .Line (.Raw "    }"),
      .Line (.Raw "}"),
      .FEmpty
    ]

/-- Generate a Rust enum -/
def emitRustADT (name : String) (ctors : List (String × List String)) : Frag :=
  let ctorFrags := ctors.map fun (ctorName, args) =>
    if args.isEmpty then
      .Line (.FSeq [.Raw "    ", .Ident ctorName, .Raw ","])
    else
      let argTypes := args.map (fun ty => .Ident ty)
      .Line (.FSeq [.Raw "    ", .Ident ctorName, .Raw "(", .Sep ", " argTypes, .Raw "),"])
  .Lines ([
    .Line (.Raw "#[derive(Debug, Clone, PartialEq)]"),
    .Line (.FSeq [.Keyword "pub", .Raw " ", .Keyword "enum", .Raw " ", .Ident name, .Raw " {"]),
  ] ++ ctorFrags ++ [
    .Line (.Raw "}"),
    .FEmpty
  ])

/-! ## Unified Dispatch -/

/-- Target language enum -/
inductive TargetLang where
  | Lean | Scala | Haskell | Rust
  deriving Repr, BEq, Inhabited

/-- Get config for target language -/
def getConfig : TargetLang → LangConfig
  | .Lean => leanConfig
  | .Scala => scalaConfig
  | .Haskell => haskellConfig
  | .Rust => rustConfig

/-- Generate a rewrite rule for any target -/
def emitRewriteRule (lang : TargetLang) (name : String) (lhs rhs : Term) : Frag :=
  match lang with
  | .Lean => emitLeanRewriteRule name lhs rhs
  | .Scala => emitScalaRewriteRule name lhs rhs
  | .Haskell => emitHaskellRewriteRule name lhs rhs
  | .Rust => emitRustRewriteRule name lhs rhs

/-- Generate an ADT for any target -/
def emitADT (lang : TargetLang) (name : String) (ctors : List (String × List String)) : Frag :=
  match lang with
  | .Lean => emitLeanInductive name ctors
  | .Scala => emitScalaADT name ctors
  | .Haskell => emitHaskellADT name ctors
  | .Rust => emitRustADT name ctors

/-- Render a Frag to String -/
def renderToString (f : Frag) : String := render f

end UnifiedCodeGen
