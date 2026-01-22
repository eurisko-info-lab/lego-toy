/-
  Lego.Attr: Attribute Grammars as Catamorphisms + Paramorphisms

  Mathematical Foundation:
    Synthesized (Syn) = Catamorphism: F-algebra A, cata alg : Fix F → A
    Inherited   (Inh) = Paramorphism: para coalg : (Fix F, A) → A
    Both        = Hylomorphism: ana ∘ cata

  Pushout Compatibility:
    (L₁, A₁) ⊔ (L₂, A₂) = (L₁ ⊔ L₂, A₁ ⋈ A₂)
    where A₁ ⋈ A₂ is the coproduct of attribute algebras

  The key insight: attributes are just named algebras over the grammar functor.
  - Grammar defines a functor F via GrammarF
  - Parse tree is Fix F (initial algebra)
  - Syn attr = F-algebra: F A → A
  - Inh attr = paramorphism with context
-/

import Lego.Algebra

namespace Lego

/-! ## Attribute Flow Direction -/

/-- Direction of attribute computation.
    Forms a lattice: SynInh ⊑ Syn, SynInh ⊑ Inh -/
inductive AttrFlow where
  | syn    : AttrFlow  -- Synthesized: bottom-up (children → parent)
  | inh    : AttrFlow  -- Inherited: top-down (parent → children)
  | synInh : AttrFlow  -- Both directions (for circular attributes)
  deriving Repr, BEq, Inhabited

/-! ## Attribute Paths -/

/-- Path to an attribute in the tree.
    [] = this node
    ["body"] = this.body
    ["body", "type"] = this.body.type (attribute on child) -/
abbrev AttrPath := List String

/-- An attribute reference in an expression.
    Either a local attribute ($type) or child attribute (body.$type) -/
structure AttrRef where
  path : AttrPath  -- [] for local, [child] for child.attr
  name : String
  deriving Repr, BEq

namespace AttrRef

def self (name : String) : AttrRef := ⟨[], name⟩
def child (c : String) (name : String) : AttrRef := ⟨[c], name⟩
def ofString (s : String) : AttrRef :=
  let parts := s.splitOn "."
  match parts.reverse with
  | name :: path => ⟨path.reverse, name⟩
  | [] => ⟨[], s⟩

end AttrRef

/-! ## Attribute Definitions -/

/-- An attribute equation.
    Syntax: Production.target = expr
    Example: Lam.type = (Arrow $param-type $body.type) -/
structure AttrRule where
  prod   : String     -- Production name (e.g., "Lam", "App")
  target : AttrPath   -- Target: [] = this.attr, [child] = child.attr
  expr   : Term       -- Expression to compute the attribute
  deriving Repr, BEq

/-- An attribute definition.
    Example: syn type : Type -/
structure AttrDef where
  name  : String          -- Attribute name
  flow  : AttrFlow        -- Direction: Syn | Inh | SynInh
  type  : Option Term     -- Optional type annotation
  rules : List AttrRule   -- Equations for computing this attribute
  deriving Repr, BEq

namespace AttrDef

def empty (name : String) (flow : AttrFlow) : AttrDef :=
  ⟨name, flow, none, []⟩

def addRule (def_ : AttrDef) (rule : AttrRule) : AttrDef :=
  { def_ with rules := def_.rules ++ [rule] }

end AttrDef

/-! ## Attribute Environment -/

/-- Attribute environment: maps (path, attr-name) to computed value.
    The path is relative to the current node:
    - ([], "type") = this node's type attribute
    - (["body"], "type") = child "body"'s type attribute -/
structure AttrEnv where
  values : List ((AttrPath × String) × Term)
  deriving Repr, BEq, Inhabited

namespace AttrEnv

def empty : AttrEnv := ⟨[]⟩

def lookup (env : AttrEnv) (path : AttrPath) (name : String) : Option Term :=
  env.values.find? (·.1 == (path, name)) |>.map (·.2)

def insert (env : AttrEnv) (path : AttrPath) (name : String) (val : Term) : AttrEnv :=
  ⟨((path, name), val) :: env.values⟩

/-- Get local attribute (path = []) -/
def getLocal (env : AttrEnv) (name : String) : Option Term :=
  env.lookup [] name

/-- Get child's attribute -/
def getChild (env : AttrEnv) (child : String) (name : String) : Option Term :=
  env.lookup [child] name

/-- Merge two environments (second wins on conflict) -/
def merge (env1 env2 : AttrEnv) : AttrEnv :=
  ⟨env2.values ++ env1.values⟩

end AttrEnv

/-! ## Catamorphism: Synthesized Attribute Evaluation -/

/-- Evaluate an attribute expression in an environment.
    Expressions can reference:
    - $name     → local attribute
    - child.$name → child's attribute
    - Constructors are preserved -/
partial def evalAttrExpr (expr : Term) (env : AttrEnv) : Term :=
  match expr with
  | .var name =>
    if name.startsWith "$" then
      let attrName := name.drop 1
      -- Check if it's a child reference (contains .)
      let ref := AttrRef.ofString attrName
      match env.lookup ref.path ref.name with
      | some v => v
      | none => Term.con "error" [Term.lit s!"undefined: {name}"]
    else
      .var name
  | .con c args =>
    .con c (args.map (evalAttrExpr · env))
  | .lit s => .lit s

/-- Find the rule for a production in an attribute definition -/
def findRule (prod : String) (target : AttrPath) (rules : List AttrRule) : Option AttrRule :=
  rules.find? (fun r => r.prod == prod && r.target == target)

/-- Helper: map with index -/
def mapWithIndex {α β : Type} (f : Nat → α → β) (xs : List α) : List β :=
  let rec go (i : Nat) : List α → List β
    | [] => []
    | x :: xs => f i x :: go (i + 1) xs
  go 0 xs

/-- Catamorphism: evaluate synthesized attribute bottom-up.

    Mathematical structure:
      cata alg : Fix F → A
      where alg : F A → A is the algebra

    For attribute grammars:
      alg takes constructor name + children's attribute values
      and produces this node's attribute value -/
partial def evalSyn (def_ : AttrDef) (term : Term) : AttrEnv :=
  match term with
  | .con prod children =>
    -- First, recursively compute children's attributes
    let childEnvs := mapWithIndex (fun i child =>
      let childEnv := evalSyn def_ child
      -- Prefix child's attributes with child name
      let childName := s!"child{i}"
      childEnv.values.map fun ((path, name), val) =>
        ((childName :: path, name), val)
    ) children

    -- Build environment with all children's attributes
    let env : AttrEnv := ⟨childEnvs.flatten⟩

    -- Find rule for this production
    match findRule prod [] def_.rules with
    | some rule =>
      let val := evalAttrExpr rule.expr env
      env.insert [] def_.name val
    | none =>
      -- No rule: attribute is undefined at this node
      env

  | .var _ => AttrEnv.empty
  | .lit _ => AttrEnv.empty

/-! ## Paramorphism: Inherited Attribute Evaluation -/

/-- Paramorphism: evaluate inherited attributes top-down.

    Mathematical structure:
      para coalg : (Fix F, A) → A
      where we have access to both the subtree and parent's attributes

    For attribute grammars:
      coalg takes parent's attributes + child position
      and produces child's inherited attributes -/
partial def evalInh (def_ : AttrDef) (term : Term) (parentEnv : AttrEnv) : AttrEnv :=
  match term with
  | .con prod children =>
    -- For each child, compute its inherited attributes
    let childEnvs := mapWithIndex (fun i child =>
      let childName := s!"child{i}"
      -- Find rule for this child's inherited attribute
      match findRule prod [childName] def_.rules with
      | some rule =>
        let val := evalAttrExpr rule.expr parentEnv
        let childEnv := AttrEnv.empty.insert [] def_.name val
        -- Recursively propagate to grandchildren
        evalInh def_ child childEnv
      | none =>
        -- No rule: child doesn't inherit, but recurse anyway
        evalInh def_ child parentEnv
    ) children

    -- Merge all child environments
    List.foldl AttrEnv.merge parentEnv childEnvs

  | _ => parentEnv

/-! ## Combined Attribute Evaluation -/

/-- Evaluate all attributes for a term.

    Two-pass algorithm:
    1. Top-down: compute inherited attributes (paramorphism)
    2. Bottom-up: compute synthesized attributes (catamorphism)

    For circular attributes, we'd use fixpoint iteration. -/
def evalAttrs (defs : List AttrDef) (term : Term) : AttrEnv :=
  let (synDefs, inhDefs) := defs.partition (·.flow == .syn)

  -- Pass 1: inherited (top-down)
  let inhEnv := inhDefs.foldl (fun env def_ => evalInh def_ term env) AttrEnv.empty

  -- Pass 2: synthesized (bottom-up)
  let synEnv := synDefs.foldl (fun env def_ => AttrEnv.merge env (evalSyn def_ term)) inhEnv

  synEnv

/-! ## Generic Catamorphism/Paramorphism -/

/-- Generic catamorphism over Term.
    cata alg t = alg (fmap (cata alg) (unTerm t)) -/
partial def cataT [Inhabited α] (alg : String → List α → α) : Term → α
  | .con c args => alg c (args.map (cataT alg))
  | .var x => alg x []
  | .lit s => alg s []

/-- Generic paramorphism over Term.
    para coalg t = coalg (fmap (λx. (x, para coalg x)) (unTerm t)) -/
partial def paraT [Inhabited α] (coalg : String → List (Term × α) → α) : Term → α
  | .con c args => coalg c (args.map fun a => (a, paraT coalg a))
  | .var x => coalg x []
  | .lit s => coalg s []

/-! ## Attribute Algebra for Languages -/

/-- A language with attribute definitions.
    Extends Language with attribute grammar support. -/
structure AttrLanguage extends Language where
  attrs : List AttrDef
  deriving Repr

namespace AttrLanguage

/-- Get all synthesized attribute definitions -/
def synAttrs (lang : AttrLanguage) : List AttrDef :=
  lang.attrs.filter (·.flow == .syn)

/-- Get all inherited attribute definitions -/
def inhAttrs (lang : AttrLanguage) : List AttrDef :=
  lang.attrs.filter (·.flow == .inh)

/-- Evaluate all attributes on a parsed term -/
def eval (lang : AttrLanguage) (term : Term) : AttrEnv :=
  evalAttrs lang.attrs term

/-- Pushout of attributed languages.
    (L₁, A₁) ⊔ (L₂, A₂) = (L₁ ⊔ L₂, A₁ ⋈ A₂) -/
def pushout (l1 l2 : AttrLanguage) : AttrLanguage :=
  { name := s!"{l1.name}_{l2.name}"
    pieces := l1.pieces ++ l2.pieces
    attrs := l1.attrs ++ l2.attrs }

infixr:65 " ⊔ " => pushout

end AttrLanguage

end Lego
