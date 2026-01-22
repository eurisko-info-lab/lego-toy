/-
  Lego.CodeGen.ToRedTT: Generate RedTT code from Grammar.sexpr

  RedTT is a proof-relevant type theory with HITs (Higher Inductive Types).
  We generate:
  1. Data type declarations for AST nodes
  2. Path types for rewrite rules
  3. Proof obligations for roundtrip properties

  RedTT syntax reference:
    data (A : type) ⊢ list where
    | nil
    | cons (x : A) (xs : list)

    def f : A → B = elim [...]
-/

import Cubical.SExpr

namespace Cubical.ToRedTT

open SExpr

/-! ## RedTT Code Generation -/

/-- RedTT data constructor -/
structure RedTTConstr where
  name : String
  args : List (String × String)  -- (argName, argType)
  boundary : Option String       -- HIT boundary conditions
  deriving Repr

/-- RedTT data type declaration -/
structure RedTTData where
  name   : String
  params : List (String × String)  -- (paramName, paramType)
  constrs : List RedTTConstr
  deriving Repr

/-- RedTT definition -/
structure RedTTDef where
  name : String
  ty   : String
  body : String
  deriving Repr

/-- Generated RedTT module -/
structure RedTTModule where
  imports  : List String
  dataTypes : List RedTTData
  defs     : List RedTTDef
  deriving Repr

/-! ## Grammar to RedTT Data Type Conversion -/

/-- Extract constructor info from a grammar production.
    Productions like Term.lam become constructors of Term. -/
def productionToConstr (prod : GrammarProd) : Option (String × RedTTConstr) := do
  let parts := prod.name.splitOn "."
  match parts with
  | [typeName, constrName] =>
    -- Extract arguments from the grammar expression
    let args := extractArgs prod.expr
    some (typeName, { name := constrName, args, boundary := none })
  | _ => none
where
  extractArgs : SExpr → List (String × String)
    | .list (.atom "seq" :: rest) => rest.flatMap extractArgs
    | .list [.atom "bind", .str x, typeExpr] => [(x, exprToType typeExpr)]
    | .list [.atom "bind", .atom x, typeExpr] => [(x, exprToType typeExpr)]
    | .list [.atom "node", _, inner] => extractArgs inner
    | _ => []

  exprToType : SExpr → String
    | .list [.atom "ref", .str name] => refToType name
    | .list [.atom "ref", .atom name] => refToType name
    | .list [.atom "star", inner] => s!"list ({exprToType inner})"
    | .str s => "string"  -- literal becomes string
    | _ => "term"

  refToType (name : String) : String :=
    let parts := name.splitOn "."
    match parts with
    | [_, localName] => localName
    | _ => name

/-- Group productions by type name -/
def groupByType (prods : List GrammarProd) : List (String × List RedTTConstr) :=
  let pairs := prods.filterMap productionToConstr
  let grouped := pairs.foldl (fun acc (ty, constr) =>
    match acc.find? (·.1 == ty) with
    | some (_, constrs) =>
      acc.map (fun (t, cs) => if t == ty then (t, cs ++ [constr]) else (t, cs))
    | none => acc ++ [(ty, [constr])]) []
  grouped

/-- Convert grouped productions to RedTT data types -/
def toDataTypes (groups : List (String × List RedTTConstr)) : List RedTTData :=
  groups.map fun (name, constrs) => {
    name
    params := []
    constrs
  }

/-! ## RedTT Code Emission -/

/-- Emit a single constructor -/
def emitConstr (c : RedTTConstr) : String :=
  let argsStr := c.args.map (fun (x, ty) => s!"({x} : {ty})") |> " ".intercalate
  let boundaryStr := match c.boundary with
    | some b => s!" [{b}]"
    | none => ""
  s!"| {c.name}{if argsStr.isEmpty then "" else " " ++ argsStr}{boundaryStr}"

/-- Emit a data type declaration -/
def emitData (d : RedTTData) : String :=
  let paramsStr := d.params.map (fun (x, ty) => s!"({x} : {ty})") |> " ".intercalate
  let header := if paramsStr.isEmpty
    then s!"data {d.name} where"
    else s!"data {paramsStr} ⊢ {d.name} where"
  let constrs := d.constrs.map emitConstr |> "\n".intercalate
  s!"{header}\n{constrs}"

/-- Emit a definition -/
def emitDef (d : RedTTDef) : String :=
  s!"def {d.name} : {d.ty} =\n  {d.body}"

/-- Emit a complete module -/
def emitModule (m : RedTTModule) : String :=
  let imports := m.imports.map (s!"import {·}") |> "\n".intercalate
  let dataTypes := m.dataTypes.map emitData |> "\n\n".intercalate
  let defs := m.defs.map emitDef |> "\n\n".intercalate
  s!"{imports}\n\n{dataTypes}\n\n{defs}"

/-! ## Main Generation Entry Point -/

/-- Generate RedTT module from Grammar.sexpr content -/
def generateFromSExpr (sexpr : SExpr) : Option String := do
  let prods ← SExpr.extractGrammar sexpr
  let groups := groupByType prods
  let dataTypes := toDataTypes groups

  -- Add standard definitions
  let roundtripProof : RedTTDef := {
    name := "parse-print-roundtrip"
    ty := "(t : term) → path term (parse (print t)) t"
    body := "-- TODO: prove by induction on term structure\n  elim [...]"
  }

  let module : RedTTModule := {
    imports := ["prelude", "data.list", "data.string"]
    dataTypes
    defs := [roundtripProof]
  }

  some (emitModule module)

/-- Generate RedTT from Grammar.sexpr file content -/
def generate (content : String) : Option String := do
  let sexpr ← SExpr.parseAll content
  generateFromSExpr sexpr

/-! ## Core Lego Types in RedTT -/

/-- Pre-defined RedTT code for Lego core types -/
def coreTypes : String := "
-- Lego Core Types for RedTT
-- Generated from single source of truth

import prelude
import data.list

-- Option type
data (A : type) ⊢ option where
| none
| some (x : A)

-- Partial isomorphism (the core Lego abstraction)
-- In CTT, this becomes an equivalence when total!
def iso (A B : type) : type =
  (fwd : A → option B) × (bwd : B → option A)

-- Universal term representation
data term where
| var (name : string)
| lit (value : string)
| con (head : string) (args : list term)

-- Grammar expression (Kleene algebra)
data grammar where
| empty                              -- ε
| lit (s : string)                   -- \"...\"
| ref (name : string)                -- production reference
| seq (g1 g2 : grammar)              -- g1 g2
| alt (g1 g2 : grammar)              -- g1 | g2
| star (g : grammar)                 -- g*
| bind (x : string) (g : grammar)    -- x ← g
| node (n : string) (g : grammar)    -- AST wrapper

-- Rewrite rule as a path!
-- In CTT, a rule a ~> b is literally path term a b
def rule : type = (lhs rhs : term) × path term lhs rhs

-- The key insight: bidirectional parsing/printing
-- is an equivalence when the grammar is unambiguous
def bidirectional (g : grammar)
  : iso (list token) term
  = -- grammar interpretation gives iso
    _

-- Roundtrip property: parse ∘ print = id
def roundtrip-fwd (g : grammar) (t : term)
  : path term ((bidirectional g).fwd ((bidirectional g).bwd t)) t
  = -- provable from grammar structure
    _

-- Roundtrip property: print ∘ parse = id (when successful)
def roundtrip-bwd (g : grammar) (toks : list token) (t : term)
  (p : path _ ((bidirectional g).fwd toks) (some t))
  : path _ ((bidirectional g).bwd t) (some toks)
  = -- provable from grammar structure
    _
"

end Cubical.ToRedTT
