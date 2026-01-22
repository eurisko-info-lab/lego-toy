/-
  Lego.CodeGen.ToCoolTT: Generate CoolTT code from Grammar.sexpr

  CoolTT is a more recent implementation with better usability.
  Key differences from RedTT:
  - Uses `sig` for record types
  - Different syntax for HITs
  - Better error messages

  CoolTT syntax reference:
    def nat : type := data [
    | zero
    | suc (n : nat)
    ]

    def list (A : type) : type := data [
    | nil
    | cons (x : A) (xs : list A)
    ]
-/

import Cubical.SExpr

namespace Cubical.ToCoolTT

open SExpr

/-! ## CoolTT Code Generation -/

/-- CoolTT constructor -/
structure CoolTTConstr where
  name : String
  args : List (String × String)
  boundary : Option String
  deriving Repr

/-- CoolTT data type -/
structure CoolTTData where
  name   : String
  params : List (String × String)
  constrs : List CoolTTConstr
  deriving Repr

/-- CoolTT definition -/
structure CoolTTDef where
  name : String
  ty   : String
  body : String
  deriving Repr

/-- CoolTT signature (record type) -/
structure CoolTTSig where
  name   : String
  fields : List (String × String)
  deriving Repr

/-- Generated CoolTT module -/
structure CoolTTModule where
  imports   : List String
  dataTypes : List CoolTTData
  sigs      : List CoolTTSig
  defs      : List CoolTTDef
  deriving Repr

/-! ## Grammar to CoolTT Conversion -/

/-- Extract constructor from production -/
def productionToConstr (prod : GrammarProd) : Option (String × CoolTTConstr) := do
  let parts := prod.name.splitOn "."
  match parts with
  | [typeName, constrName] =>
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
    | .str _ => "string"
    | _ => "term"

  refToType (name : String) : String :=
    let parts := name.splitOn "."
    match parts with
    | [_, localName] => localName
    | _ => name

/-- Group by type name -/
def groupByType (prods : List GrammarProd) : List (String × List CoolTTConstr) :=
  let pairs := prods.filterMap productionToConstr
  pairs.foldl (fun acc (ty, constr) =>
    match acc.find? (·.1 == ty) with
    | some (_, constrs) =>
      acc.map (fun (t, cs) => if t == ty then (t, cs ++ [constr]) else (t, cs))
    | none => acc ++ [(ty, [constr])]) []

/-- Convert to CoolTT data types -/
def toDataTypes (groups : List (String × List CoolTTConstr)) : List CoolTTData :=
  groups.map fun (name, constrs) => { name, params := [], constrs }

/-! ## CoolTT Code Emission -/

/-- Emit constructor -/
def emitConstr (c : CoolTTConstr) : String :=
  let argsStr := c.args.map (fun (x, ty) => s!"({x} : {ty})") |> " ".intercalate
  let boundaryStr := match c.boundary with
    | some b => s!" [{b}]"
    | none => ""
  s!"| {c.name}{if argsStr.isEmpty then "" else " " ++ argsStr}{boundaryStr}"

/-- Emit data type -/
def emitData (d : CoolTTData) : String :=
  let paramsStr := d.params.map (fun (x, ty) => s!"({x} : {ty})") |> " ".intercalate
  let constrs := d.constrs.map emitConstr |> "\n  ".intercalate
  if paramsStr.isEmpty then
    s!"def {d.name} : type := data [\n  {constrs}\n  ]"
  else
    s!"def {d.name} {paramsStr} : type := data [\n  {constrs}\n  ]"

/-- Emit signature (record type) -/
def emitSig (s : CoolTTSig) : String :=
  let fields := s.fields.map (fun (x, ty) => s!"def {x} : {ty}") |> "\n  ".intercalate
  s!"def {s.name} : type := sig [\n  {fields}\n  ]"

/-- Emit definition -/
def emitDef (d : CoolTTDef) : String :=
  s!"def {d.name} : {d.ty} :=\n  {d.body}"

/-- Emit module -/
def emitModule (m : CoolTTModule) : String :=
  let imports := m.imports.map (s!"import {·}") |> "\n".intercalate
  let dataTypes := m.dataTypes.map emitData |> "\n\n".intercalate
  let sigs := m.sigs.map emitSig |> "\n\n".intercalate
  let defs := m.defs.map emitDef |> "\n\n".intercalate
  s!"{imports}\n\n{dataTypes}\n\n{sigs}\n\n{defs}"

/-! ## Main Entry Point -/

/-- Generate CoolTT from S-expression -/
def generateFromSExpr (sexpr : SExpr) : Option String := do
  let prods ← SExpr.extractGrammar sexpr
  let groups := groupByType prods
  let dataTypes := toDataTypes groups

  -- Iso as a signature type
  let isoSig : CoolTTSig := {
    name := "iso"
    fields := [("fwd", "A → option B"), ("bwd", "B → option A")]
  }

  let module : CoolTTModule := {
    imports := ["prelude"]
    dataTypes
    sigs := [isoSig]
    defs := []
  }

  some (emitModule module)

/-- Generate from file content -/
def generate (content : String) : Option String := do
  let sexpr ← SExpr.parseAll content
  generateFromSExpr sexpr

/-! ## Core Lego Types in CoolTT -/

def coreTypes : String := "
-- Lego Core Types for CoolTT
-- Single source of truth architecture

import prelude

-- Option type
def option (A : type) : type := data [
| none
| some (x : A)
]

-- List type
def list (A : type) : type := data [
| nil
| cons (x : A) (xs : list A)
]

-- Partial isomorphism
def iso (A B : type) : type := sig [
  def fwd : A → option B
  def bwd : B → option A
]

-- Universal term
def term : type := data [
| var (name : string)
| lit (value : string)
| con (head : string) (args : list term)
]

-- Grammar algebra
def grammar : type := data [
| empty
| lit (s : string)
| ref (name : string)
| seq (g1 g2 : grammar)
| alt (g1 g2 : grammar)
| star (g : grammar)
| bind (x : string) (g : grammar)
| node (n : string) (g : grammar)
]

-- Token type
def token : type := data [
| ident (s : string)
| lit (s : string)
| sym (s : string)
| number (s : string)
]

-- Rule = path in term space
-- a ~> b means path term a b
def rule : type := sig [
  def lhs : term
  def rhs : term
  def path : path term lhs rhs
]

-- Bidirectional parsing/printing from grammar
def bidirectional (g : grammar) : iso (list token) term :=
  -- grammar interpretation yields iso
  _

-- Roundtrip theorem
def roundtrip (g : grammar) (t : term)
  : path term (bidirectional g .fwd (bidirectional g .bwd t).get) t
  := _
"

end Cubical.ToCoolTT
