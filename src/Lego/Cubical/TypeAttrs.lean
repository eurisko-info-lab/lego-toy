/-
  Lego.TypeAttrs: Cubical Type Theory as Attribute Grammar

  Type checking via attribute grammars:
  - syn type : synthesized (bottom-up) type inference
  - inh ctx  : inherited (top-down) typing context
  - syn elab : elaborated Core IR term

  Mathematical structure:
    Type inference = catamorphism (F-algebra)
    Context propagation = paramorphism (F-coalgebra)
    Bidirectional = ana ∘ cata (hylomorphism)

  AST ↔ IR Conversion:
    Rewrite rules transform between:
    - AST (named variables, surface syntax)
    - IR  (de Bruijn indices, Core.Expr)
-/

import Lego.Attr
import Lego.AttrEval
import Lego.Cubical.Core
import Lego.Algebra

namespace Lego

/-! ## AST to IR Conversion Rules

    These rules transform surface AST (with named variables)
    into Core IR (with de Bruijn indices).

    Pattern: (ast-form args...) ~> (ir-form args'...)

    The rules are applied bottom-up after parsing.
-/

/-- AST to IR rewrite rules -/
def astToIRRules : List (Term × Term) := [
  -- === Variables ===
  -- (var "x") stays as-is; de Bruijn computed during elaboration

  -- === Universes ===
  -- (type) ~> (univ 0)
  (.con "type" [], .con "univ" [.lit "0"]),
  -- (typeLevel n) ~> (univ n)
  (.con "typeLevel" [.var "n"], .con "univ" [.var "n"]),
  -- (interval) ~> (I)
  (.con "interval" [], .con "I" []),

  -- === Functions ===
  -- (lam (binders (typedBinder x A)) body) ~> (lam x A body)
  (.con "lam" [.con "binders" [.con "typedBinder" [.var "x", .var "A"]], .var "body"],
   .con "lam" [.var "x", .var "A", .var "body"]),
  -- (lam (binders (simpleBinder x)) body) ~> (lam x _ body)
  (.con "lam" [.con "binders" [.con "simpleBinder" [.var "x"]], .var "body"],
   .con "lam" [.var "x", .con "hole" [], .var "body"]),

  -- (Arrow A B) ~> (Pi _ A B)
  (.con "Arrow" [.var "A", .var "B"],
   .con "Pi" [.lit "_", .var "A", .var "B"]),

  -- (Pi (cell x A) B) ~> (Pi x A B)
  (.con "Pi" [.con "cell" [.var "x", .var "A"], .var "B"],
   .con "Pi" [.var "x", .var "A", .var "B"]),

  -- (app f (arg x)) ~> (app f x)
  (.con "app" [.var "f", .con "arg" [.var "x"]],
   .con "app" [.var "f", .var "x"]),
  -- (app f) ~> f  (no arguments)
  (.con "app" [.var "f"], .var "f"),

  -- === Sigma Types ===
  -- (Sigma x A B) stays as-is
  -- (Prod A B) ~> (Sigma _ A B)
  (.con "Prod" [.var "A", .var "B"],
   .con "Sigma" [.lit "_", .var "A", .var "B"]),

  -- (pair a b) stays as-is

  -- === Path Types ===
  -- (path A a b) stays as-is
  -- (refl) ~> (refl _)
  (.con "refl" [], .con "refl" [.con "hole" []]),
  -- (pathAbs (dims i) body sys) ~> (pabs i body sys)
  (.con "pathAbs" [.con "dims" [.var "i"], .var "body", .var "sys"],
   .con "pabs" [.var "i", .var "body", .var "sys"]),
  -- (pathAbs (dims i) body) ~> (pabs i body [])
  (.con "pathAbs" [.con "dims" [.var "i"], .var "body"],
   .con "pabs" [.var "i", .var "body", .con "sys" []]),

  -- === Coercion ===
  -- (coe r r' a A) stays as-is

  -- === Composition ===
  -- (hcom r r' A cap sys) stays as-is
  -- (comp r r' A cap sys) stays as-is

  -- === Let ===
  -- (let x A v body) stays as-is

  -- === Eliminators ===
  -- (elim target cases) ~> (elim target cases)

  -- === Glue Types ===
  -- (Glue A phi T e) stays as-is
  -- (glue t a) stays as-is
  -- (unglue g) stays as-is

  -- === V-types ===
  -- (Vtype r A B e) stays as-is
  -- (Vin r a b) stays as-is
  -- (Vproj r v A B e) stays as-is

  -- === Circle ===
  -- (circle) ~> (S1)
  (.con "circle" [], .con "S1" []),
  -- (base) stays as-is
  -- (loop) stays as-is

  -- === Nat ===
  -- (nat) stays as-is
  -- (zero) stays as-is
  -- (suc n) stays as-is

  -- === Projections ===
  -- (proj e (field "fst")) ~> (fst e)
  (.con "proj" [.var "e", .con "field" [.lit "fst"]],
   .con "fst" [.var "e"]),
  -- (proj e (field "snd")) ~> (snd e)
  (.con "proj" [.var "e", .con "field" [.lit "snd"]],
   .con "snd" [.var "e"]),

  -- === Definition ===
  -- (def name args type body) stays as-is for top-level processing
  -- (defInfer name args body) ~> (def name args _ body)
  (.con "defInfer" [.var "name", .var "args", .var "body"],
   .con "def" [.var "name", .var "args", .con "hole" [], .var "body"])
]

/-- IR to AST rewrite rules (inverse direction) -/
def irToASTRules : List (Term × Term) := [
  -- === Universes ===
  (.con "univ" [.lit "0"], .con "type" []),
  (.con "univ" [.var "n"], .con "typeLevel" [.var "n"]),
  (.con "I" [], .con "interval" []),

  -- === Functions ===
  -- (Pi _ A B) ~> (Arrow A B) when non-dependent
  (.con "Pi" [.lit "_", .var "A", .var "B"],
   .con "Arrow" [.var "A", .var "B"]),

  -- (Sigma _ A B) ~> (Prod A B) when non-dependent
  (.con "Sigma" [.lit "_", .var "A", .var "B"],
   .con "Prod" [.var "A", .var "B"]),

  -- === Projections ===
  (.con "fst" [.var "e"], .con "proj" [.var "e", .con "field" [.lit "fst"]]),
  (.con "snd" [.var "e"], .con "proj" [.var "e", .con "field" [.lit "snd"]]),

  -- === Circle ===
  (.con "S1" [], .con "circle" [])
]

/-- Apply AST→IR transformation to a term -/
partial def astToIR (term : Term) : Term :=
  -- First transform children
  let term' := match term with
    | .con name args => .con name (args.map astToIR)
    | .var _ => term
    | .lit _ => term
  -- Then try each rule
  astToIRRules.foldl (fun t (pat, replacement) =>
    match Term.matchPattern pat t with
    | some subst => Term.substitute replacement subst
    | none => t
  ) term'

/-- Apply IR→AST transformation to a term -/
partial def irToAST (term : Term) : Term :=
  let term' := match term with
    | .con name args => .con name (args.map irToAST)
    | .var _ => term
    | .lit _ => term
  irToASTRules.foldl (fun t (pat, replacement) =>
    match Term.matchPattern pat t with
    | some subst => Term.substitute replacement subst
    | none => t
  ) term'

/-! ## Type Attribute Rules

    Each rule has form: Production.type = expr
    where expr can reference:
    - $child0.type, $child1.type, ... for children's types
    - $ctx for inherited context
    - Constructors like (Pi ...) for type formation
-/

/-- Build a type attribute rule -/
def typeRule (prod : String) (expr : Term) : AttrRule :=
  { prod := prod, target := [], expr := expr }

/-- Build a context inheritance rule (passes ctx to specific child) -/
def ctxRule (prod : String) (childIdx : Nat) (expr : Term) : AttrRule :=
  { prod := prod, target := [s!"child{childIdx}"], expr := expr }

/-! ## Cubical Type Theory Rules -/

/-- Type inference rules for cubical type theory.

    The rules follow bidirectional typing:
    - Inference (Syn): types flow up from leaves
    - Checking (Inh): expected types flow down

    Productions must match the grammar in Redtt.lego
-/
def cubicalTypeRules : List AttrRule := [
  -- === Universes ===
  -- type : Type^1
  typeRule "type" (.con "typeN" [.lit "1"]),
  -- univ n : Type^(n+1)  (after AST→IR transformation)
  typeRule "univ" (.con "typeN" [.con "suc" [.var "$child0"]]),
  -- typeN n : Type^(n+1)
  typeRule "typeN" (.con "typeN" [.con "suc" [.var "$child0"]]),
  -- I : Type (interval type, after AST→IR)
  typeRule "I" (.con "type" []),

  -- === Variables ===
  -- var x : lookup x in ctx (handled specially in evalSyn)

  -- === Function Types ===
  -- Pi x A B : Type^(max level(A) level(B))
  -- For simplicity: Pi _ A B : Type if A : Type and B : Type
  typeRule "Pi" (.con "type" []),

  -- Arrow A B : Type if A : Type and B : Type
  typeRule "Arrow" (.con "type" []),

  -- lam x A body : Pi x A (typeof body)
  -- type = (Pi $child0 $child1 $child2.type)
  typeRule "lam" (.con "Pi" [.var "$child0", .var "$child1", .var "$child2.type"]),

  -- app f x : B[x/a] where f : Pi a A B
  -- type = substitute $child0.type.codomain with $child1
  typeRule "app" (.con "app-result-type" [.var "$child0.type", .var "$child1"]),

  -- === Sigma Types ===
  -- Sigma x A B : Type
  typeRule "Sigma" (.con "type" []),

  -- pair a b : Sigma (typeof a) (typeof b) -- simplified
  typeRule "pair" (.con "Sigma" [.var "_", .var "$child0.type", .var "$child1.type"]),

  -- proj1 p : A where p : Sigma x A B
  typeRule "proj1" (.con "proj1-type" [.var "$child0.type"]),

  -- proj2 p : B[fst p/x] where p : Sigma x A B
  typeRule "proj2" (.con "proj2-type" [.var "$child0.type", .var "$child0"]),

  -- === Path Types ===
  -- path A a b : Type
  typeRule "path" (.con "type" []),
  typeRule "pathsugar" (.con "type" []),

  -- refl a : path (typeof a) a a
  typeRule "refl" (.con "path" [.var "$child0.type", .var "$child0", .var "$child0"]),
  typeRule "reflexpr" (.con "path" [.var "$ctx.expected", .var "$ctx.lhs", .var "$ctx.rhs"]),

  -- pabs i body : path (typeof body) (body[0/i]) (body[1/i])
  typeRule "pabs" (.con "path" [.var "$child1.type",
                                 .con "subst0" [.var "$child1"],
                                 .con "subst1" [.var "$child1"]]),

  -- papp p r : (p.type).A  (the line type at dimension r)
  typeRule "papp" (.con "papp-type" [.var "$child0.type", .var "$child1"]),

  -- === Coercion ===
  -- coe r r' a A : A(r')
  typeRule "coe" (.con "subst" [.var "$child3", .var "$child1"]),
  typeRule "coeexpr" (.con "subst" [.var "$child3", .var "$child1"]),

  -- === Homogeneous Composition ===
  -- hcom r r' A φ cap : A
  typeRule "hcom" (.var "$child2"),
  typeRule "hcomexpr" (.var "$child2"),

  -- === Natural Numbers ===
  -- nat : Type
  typeRule "nat" (.con "type" []),
  -- zero : nat
  typeRule "zero" (.con "nat" []),
  -- suc n : nat (if n : nat)
  typeRule "suc" (.con "nat" []),
  -- natrec/natelim P z s n : P n
  typeRule "natrec" (.con "app" [.var "$child0", .var "$child3"]),
  typeRule "natelim" (.con "app" [.var "$child0", .var "$child3"]),

  -- === Circle (S¹) ===
  -- circle : Type
  typeRule "circle" (.con "type" []),
  -- base : circle
  typeRule "base" (.con "circle" []),
  -- loop r : circle
  typeRule "loop" (.con "circle" []),
  -- circlerec P b l x : P x
  typeRule "circlerec" (.con "app" [.var "$child0", .var "$child3"]),

  -- === Let Bindings ===
  -- let x A v body : typeof body (with x:A in scope)
  typeRule "let" (.var "$child3.type"),
  typeRule "letexpr" (.var "$child3.type"),

  -- === Systems (Partial Elements) ===
  -- sys branches : common type of branches
  typeRule "sys" (.var "$child0.type"),
  typeRule "sysface" (.var "$child1.type"),

  -- === Glue Types ===
  -- glue A φ T e : Type
  typeRule "glue" (.con "type" []),
  typeRule "Glue" (.con "type" []),
  -- glueElem t a : Glue A φ T e
  typeRule "glueelem" (.var "$ctx.expected"),
  -- unglue g : A
  typeRule "unglue" (.con "unglue-type" [.var "$child0.type"]),

  -- === Cofibrations ===
  -- ⊤, ⊥, r=s, φ∧ψ, φ∨ψ : 𝔽 (cofibration type)
  typeRule "coftop" (.con "cof" []),
  typeRule "cofbot" (.con "cof" []),
  typeRule "cofeq" (.con "cof" []),
  typeRule "cofand" (.con "cof" []),
  typeRule "cofor" (.con "cof" []),

  -- === Dimensions ===
  -- 0, 1, i : 𝕀 (interval type)
  typeRule "dim0" (.con "interval" []),
  typeRule "dim1" (.con "interval" []),
  typeRule "dimvar" (.con "interval" [])
]

/-- Context inheritance rules.

    These rules specify how context flows to children.
    For binder productions, the body child gets extended context.
-/
def cubicalCtxRules : List AttrRule := [
  -- lam x A body: body gets ctx extended with x:A
  ctxRule "lam" 2 (.con "extend" [.var "$ctx", .var "$child0", .var "$child1"]),

  -- Pi x A B: B gets ctx extended with x:A
  ctxRule "Pi" 2 (.con "extend" [.var "$ctx", .var "$child0", .var "$child1"]),

  -- Sigma x A B: B gets ctx extended with x:A
  ctxRule "Sigma" 2 (.con "extend" [.var "$ctx", .var "$child0", .var "$child1"]),

  -- let x A v body: body gets ctx extended with x:A
  ctxRule "let" 3 (.con "extend" [.var "$ctx", .var "$child0", .var "$child1"]),
  ctxRule "letexpr" 3 (.con "extend" [.var "$ctx", .var "$child0", .var "$child1"]),

  -- pabs i body: body gets dimCtx extended with i
  ctxRule "pabs" 1 (.con "extendDim" [.var "$ctx", .var "$child0"])
]

/-! ## Type Attribute Definition -/

/-- Synthesized type attribute -/
def typeAttrDef : AttrDef := {
  name := "type"
  flow := .syn
  type := some (.var "Type")
  rules := cubicalTypeRules
}

/-- Inherited context attribute -/
def ctxAttrDef : AttrDef := {
  name := "ctx"
  flow := .inh
  type := some (.var "Ctx")
  rules := cubicalCtxRules
}

/-- Synthesized elaboration attribute (Core IR) -/
def elabAttrDef : AttrDef := {
  name := "elaborated"
  flow := .syn
  type := some (.var "Expr")
  rules := []  -- Elaboration rules defined elsewhere
}

/-- All cubical type theory attribute definitions -/
def cubicalAttrDefs : List AttrDef := [typeAttrDef, ctxAttrDef, elabAttrDef]

/-! ## High-Level Type Checking API -/

/-- Type check a term using attribute grammar.
    First transforms AST to IR form, then evaluates type attributes. -/
def typecheckAttr (term : Term) (ctx : Context := Context.empty) : EvalResult Term :=
  let irTerm := astToIR term
  typecheck cubicalAttrDefs irTerm ctx

/-- Elaborate a term using attribute grammar -/
def elaborateAttr (term : Term) (ctx : Context := Context.empty) : EvalResult Term :=
  let irTerm := astToIR term
  elaborateTerm cubicalAttrDefs irTerm ctx

/-- Type check and get both type and elaborated term -/
def typecheckAndElab (term : Term) (ctx : Context := Context.empty) : EvalResult (Term × Term) :=
  let irTerm := astToIR term
  let env := evalAllAttrs {} cubicalAttrDefs irTerm ctx
  match env.getAttr [] "type", env.getAttr [] "elaborated" with
  | some ty, some elabTerm =>
    if env.hasErrors then
      .failed env.errors
    else
      .ok (ty, elabTerm) env.errors
  | _, _ =>
    .failed (TypeError.error "type checking failed" :: env.errors)

/-- Type check a term after AST→IR conversion, returning IR result -/
def typecheckToIR (term : Term) (ctx : Context := Context.empty) : EvalResult Term :=
  let irTerm := astToIR term
  typecheck cubicalAttrDefs irTerm ctx

/-- Convert IR result back to AST form -/
def typecheckToAST (term : Term) (ctx : Context := Context.empty) : EvalResult Term :=
  match typecheckAttr term ctx with
  | .ok ty errs => .ok (irToAST ty) errs
  | .failed errs => .failed errs

end Lego
