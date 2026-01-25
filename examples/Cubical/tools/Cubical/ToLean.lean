/-
  Lego.CodeGen.ToLean: Generate Lean 4 code from Grammar.sexpr

  This generates the executable implementation.
  The generated code should be semantically equivalent to
  the verified RedTT/CoolTT code.

  Output:
  1. Inductive types for AST nodes
  2. Parser functions
  3. Printer functions
  4. Rewrite rules
-/

import Cubical.SExpr

namespace Cubical.ToLean

open SExpr

/-! ## Lean Code Generation -/

/-- Lean constructor -/
structure LeanConstr where
  name : String
  args : List (String × String)
  deriving Repr

/-- Lean inductive type -/
structure LeanInductive where
  name    : String
  params  : List (String × String)
  constrs : List LeanConstr
  deriving Repr

/-- Lean definition -/
structure LeanDef where
  name      : String
  ty        : String
  body      : String
  isPartial : Bool := false
  deriving Repr

/-- Lean structure -/
structure LeanStruct where
  name   : String
  fields : List (String × String)
  deriving Repr

/-- Generated Lean module -/
structure LeanModule where
  nsName     : String      -- renamed from 'namespace' (reserved)
  imports    : List String
  inductives : List LeanInductive
  structs    : List LeanStruct
  defs       : List LeanDef
  deriving Repr

/-! ## Grammar to Lean Conversion -/

private def capitalize (s : String) : String :=
  match s.data with
  | c :: cs => String.mk (c.toUpper :: cs)
  | [] => s

private def refToType (name : String) : String :=
  let parts := name.splitOn "."
  match parts with
  | ["Atom", "ident"] => "String"
  | ["Atom", "string"] => "String"
  | ["Atom", "number"] => "String"
  | [_, localName] => capitalize localName
  | _ => "Term"

/-- Convert grammar expression type to Lean type -/
def exprToLeanType : SExpr → String
  | .list [.atom "ref", .str name] => refToType name
  | .list [.atom "ref", .atom name] => refToType name
  | .list [.atom "star", inner] => s!"List ({exprToLeanType inner})"
  | .list [.atom "alt", _, _] => "Term"  -- alternatives become sum
  | .str _ => "String"
  | _ => "Term"

/-- Extract arguments from grammar expression -/
def extractArgs : SExpr → List (String × String)
  | .list (.atom "seq" :: rest) => rest.flatMap extractArgs
  | .list [.atom "bind", .str x, typeExpr] => [(x, exprToLeanType typeExpr)]
  | .list [.atom "bind", .atom x, typeExpr] => [(x, exprToLeanType typeExpr)]
  | .list [.atom "node", _, inner] => extractArgs inner
  | _ => []

/-- Extract constructor from production -/
def productionToConstr (prod : GrammarProd) : Option (String × LeanConstr) := do
  let parts := prod.name.splitOn "."
  match parts with
  | [typeName, constrName] =>
    let args := extractArgs prod.expr
    some (typeName, { name := constrName, args })
  | _ => none

/-- Group by type -/
def groupByType (prods : List GrammarProd) : List (String × List LeanConstr) :=
  let pairs := prods.filterMap productionToConstr
  pairs.foldl (fun acc (ty, constr) =>
    match acc.find? (·.1 == ty) with
    | some _ =>
      acc.map (fun (t, cs) => if t == ty then (t, cs ++ [constr]) else (t, cs))
    | none => acc ++ [(ty, [constr])]) []

/-- Convert to Lean inductives -/
def toInductives (groups : List (String × List LeanConstr)) : List LeanInductive :=
  groups.map fun (name, constrs) => {
    name := capitalize name
    params := []
    constrs := constrs.map fun c => { c with name := c.name }
  }

/-! ## Lean Code Emission -/

/-- Emit constructor -/
def emitConstr (c : LeanConstr) : String :=
  let argsStr := c.args.map (fun (x, ty) => s!"{x} : {ty}") |> " → ".intercalate
  if argsStr.isEmpty then
    s!"  | {c.name}"
  else
    s!"  | {c.name} : {argsStr} → _"

/-- Emit inductive -/
def emitInductive (ind : LeanInductive) : String :=
  let paramsStr := ind.params.map (fun (x, ty) => s!"({x} : {ty})") |> " ".intercalate
  let header := if paramsStr.isEmpty
    then s!"inductive {ind.name} where"
    else s!"inductive {ind.name} {paramsStr} where"
  let constrs := ind.constrs.map emitConstr |> "\n".intercalate
  s!"{header}\n{constrs}\n  deriving Repr, BEq, Inhabited"

/-- Emit structure -/
def emitStruct (st : LeanStruct) : String :=
  let fields := st.fields.map (fun (x, ty) => s!"  {x} : {ty}") |> "\n".intercalate
  s!"structure {st.name} where\n{fields}\n  deriving Repr, BEq"

/-- Emit definition -/
def emitDef (d : LeanDef) : String :=
  let partialKw := if d.isPartial then "partial " else ""
  s!"{partialKw}def {d.name} : {d.ty} :=\n  {d.body}"

/-- Emit module -/
def emitModule (m : LeanModule) : String :=
  let imports := m.imports.map (s!"import {·}") |> "\n".intercalate
  let nsOpen := s!"namespace {m.nsName}"
  let inductives := m.inductives.map emitInductive |> "\n\n".intercalate
  let structs := m.structs.map emitStruct |> "\n\n".intercalate
  let defs := m.defs.map emitDef |> "\n\n".intercalate
  let nsClose := s!"end {m.nsName}"
  s!"{imports}\n\n{nsOpen}\n\n{inductives}\n\n{structs}\n\n{defs}\n\n{nsClose}"

/-! ## Main Entry Point -/

/-- Generate Lean from S-expression -/
def generateFromSExpr (sexpr : SExpr) (moduleName : String := "Generated") : Option String := do
  let prods ← SExpr.extractGrammar sexpr
  let groups := groupByType prods
  let inductives := toInductives groups

  -- Standard structures
  let isoStruct : LeanStruct := {
    name := "Iso"
    fields := [("forward", "α → Option β"), ("backward", "β → Option α")]
  }

  let ruleStruct : LeanStruct := {
    name := "Rule"
    fields := [("name", "String"), ("lhs", "Term"), ("rhs", "Term")]
  }

  let mod : LeanModule := {
    nsName := moduleName
    imports := ["Init"]
    inductives
    structs := [isoStruct, ruleStruct]
    defs := []
  }

  some (emitModule mod)

/-- Generate from file content -/
def generate (content : String) (moduleName : String := "Generated") : Option String := do
  let sexpr ← SExpr.parseAll content
  generateFromSExpr sexpr moduleName

/-! ## Core Lego Implementation in Lean -/

def coreImpl : String := "
/-
  Lego Core Implementation (Lean 4)
  Generated from single source of truth
-/

inductive Term where
  | var : String → Term
  | app : String → List Term → Term
  | lam : String → Term → Term
  | fix : String → Term → Term
  deriving Repr, BEq, Inhabited

structure Iso (α β : Type) where
  forward  : α → Option β
  backward : β → Option α

def Iso.compose [Monad m] (f : Iso α β) (g : Iso β γ) : Iso α γ := {
  forward  := fun a => f.forward a >>= g.forward
  backward := fun c => g.backward c >>= f.backward
}

structure Rule where
  name : String
  lhs  : Term
  rhs  : Term
  deriving Repr

partial def normalize (rules : List Rule) (t : Term) : Term :=
  match rules.findSome? (fun r => matchTerm r.lhs t |>.map (fun σ => subst σ r.rhs)) with
  | some t' => normalize rules t'
  | none => t
where
  matchTerm (pat t : Term) : Option (List (String × Term)) :=
    match pat, t with
    | .var x, t => some [(x, t)]
    | .app f ps, .app g qs =>
      if f == g && ps.length == qs.length then
        (ps.zip qs).foldlM (fun σ (p, q) =>
          matchTerm p q |>.map (σ ++ ·)) []
      else none
    | _, _ => none

  subst (σ : List (String × Term)) (t : Term) : Term :=
    match t with
    | .var x => σ.find? (·.1 == x) |>.map (·.2) |>.getD t
    | .app f args => .app f (args.map (subst σ))
    | .lam x body => .lam x (subst σ body)
    | .fix x body => .fix x (subst σ body)
"

end Cubical.ToLean
