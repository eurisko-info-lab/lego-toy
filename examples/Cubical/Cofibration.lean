/-
  Lego.Cubical.Cofibration: Cofibration algebra and theory

  Mathematical Structure:
  - Cofibrations: decidable propositions on the interval
  - Lattice structure: meet (∧), join (∨), top (⊤), bot (⊥)
  - Dimension equality: r = s as cofibration
  - Boundary: ∂r = (r = 0) ∨ (r = 1)
  - Restriction: working under a cofibration assumption

  Key features from cooltt:
  - CofBuilder: construct cofibrations from dimension expressions
  - Consistency checking: detect contradictions
  - Normalization: simplify cofibrations
  - Sequent testing: check if cof₁ ⊢ cof₂

  Algebra:
  - Distributive lattice with top (⊤) and bottom (⊥)
  - cof_and and cof_or distribute over each other
  - cof_eq is symmetric and satisfies interval axioms
-/

import Lego.Cubical.Core

namespace Lego.Cubical.Cofibration

open Lego.Core
open Lego.Core.Expr

/-! ## Dimension Expressions

    Dimensions are elements of the interval [0, 1].
    They support equality testing against endpoints.
-/

/-- Check if dimension is constant 0 -/
def isDim0 : Expr → Bool
  | .dim0 => true
  | _ => false

/-- Check if dimension is constant 1 -/
def isDim1 : Expr → Bool
  | .dim1 => true
  | _ => false

/-- Check if two dimensions are syntactically equal -/
def dimEq : Expr → Expr → Bool
  | .dim0, .dim0 => true
  | .dim1, .dim1 => true
  | .dimVar n, .dimVar m => n == m
  | _, _ => false

/-- Normalize a dimension expression -/
def normalizeDim : Expr → Expr
  | e => e  -- Already in normal form

/-! ## Cofibration Constructors

    Build cofibrations using the lattice operations.
-/

/-- Check if expression is a cofibration -/
def isCof : Expr → Bool
  | .cof_top => true
  | .cof_bot => true
  | .cof_eq _ _ => true
  | .cof_and _ _ => true
  | .cof_or _ _ => true
  | _ => false

/-- Top cofibration (always true) -/
def top : Expr := cof_top

/-- Bottom cofibration (always false) -/
def bot : Expr := cof_bot

/-- Dimension equality: r = s -/
def eq (r s : Expr) : Expr :=
  -- Optimize constant cases
  if dimEq r s then cof_top
  else match r, s with
    | .dim0, .dim1 => cof_bot
    | .dim1, .dim0 => cof_bot
    | _, _ => cof_eq r s

/-- Less-than-or-equal: r ≤ s (encoded as r = 0 ∨ s = 1) -/
def le (r s : Expr) : Expr :=
  cof_or (eq r dim0) (eq s dim1)

/-- Meet (conjunction): φ ∧ ψ -/
def meet (φ ψ : Expr) : Expr :=
  -- Optimize identity/annihilator
  match φ, ψ with
  | .cof_top, ψ => ψ
  | φ, .cof_top => φ
  | .cof_bot, _ => cof_bot
  | _, .cof_bot => cof_bot
  | _, _ => if φ == ψ then φ else cof_and φ ψ

/-- Join (disjunction): φ ∨ ψ -/
def join (φ ψ : Expr) : Expr :=
  -- Optimize identity/annihilator
  match φ, ψ with
  | .cof_bot, ψ => ψ
  | φ, .cof_bot => φ
  | .cof_top, _ => cof_top
  | _, .cof_top => cof_top
  | _, _ => if φ == ψ then φ else cof_or φ ψ

/-- Meet of a list of cofibrations -/
def meetAll (φs : List Expr) : Expr :=
  φs.foldl meet cof_top

/-- Join of a list of cofibrations -/
def joinAll (φs : List Expr) : Expr :=
  φs.foldl join cof_bot

/-- Boundary of a dimension: ∂r = (r = 0) ∨ (r = 1) -/
def boundary (r : Expr) : Expr :=
  join (eq r dim0) (eq r dim1)

/-- Equal to 0: r = 0 -/
def eq0 (r : Expr) : Expr := eq r dim0

/-- Equal to 1: r = 1 -/
def eq1 (r : Expr) : Expr := eq r dim1

/-! ## Cofibration Normalization

    Simplify cofibrations using lattice laws.
-/

/-- Normalize a cofibration to a canonical form -/
partial def normalize : Expr → Expr
  | .cof_top => cof_top
  | .cof_bot => cof_bot
  | .cof_eq r s =>
    let r' := normalizeDim r
    let s' := normalizeDim s
    eq r' s'
  | .cof_and φ ψ =>
    let φ' := normalize φ
    let ψ' := normalize ψ
    meet φ' ψ'
  | .cof_or φ ψ =>
    let φ' := normalize φ
    let ψ' := normalize ψ
    join φ' ψ'
  | e => e  -- Not a cofibration

/-! ## Consistency Checking

    Detect if a cofibration is inconsistent (equivalent to ⊥).
-/

/-- Check if a cofibration is definitely true (≡ ⊤) -/
def isTop : Expr → Bool
  | .cof_top => true
  | .cof_eq r s => dimEq r s
  | .cof_or φ ψ => isTop φ || isTop ψ
  | _ => false

/-- Check if a cofibration is definitely false (≡ ⊥) -/
def isBot : Expr → Bool
  | .cof_bot => true
  | .cof_eq .dim0 .dim1 => true
  | .cof_eq .dim1 .dim0 => true
  | .cof_and φ ψ => isBot φ || isBot ψ
  | _ => false

/-- Check consistency: is the cofibration satisfiable? -/
def isConsistent (φ : Expr) : Bool :=
  !isBot (normalize φ)

/-- Check if two cofibrations are definitely disjoint -/
def areDisjoint (φ ψ : Expr) : Bool :=
  isBot (meet φ ψ)

/-! ## Sequent Testing

    Check if φ₁, ..., φₙ ⊢ ψ (hypotheses entail conclusion).
    This is a simple syntactic check, not a full decision procedure.
-/

/-- Check if conclusion is entailed by hypotheses -/
def entails (hypotheses : List Expr) (conclusion : Expr) : Bool :=
  -- Simple cases
  if isTop conclusion then true
  else if hypotheses.any isBot then true  -- From contradiction, anything follows
  else if hypotheses.any (· == conclusion) then true  -- Direct match
  else
    -- Check if meetAll hypotheses ∧ ¬conclusion is inconsistent
    -- Simplified: just check structural inclusion
    match conclusion with
    | .cof_or φ ψ => entails hypotheses φ || entails hypotheses ψ
    | .cof_and φ ψ => entails hypotheses φ && entails hypotheses ψ
    | _ => false

/-- Test sequent: given context cofibrations, is the goal cofibration true? -/
def testSequent (context : List Expr) (goal : Expr) : Bool :=
  entails context goal

/-! ## Cofibration Context

    Track assumed cofibrations for working under restrictions.
-/

/-- Cofibration context: list of assumed cofibrations -/
structure CofContext where
  assumptions : List Expr
  deriving Repr, BEq

namespace CofContext

/-- Empty context -/
def empty : CofContext := { assumptions := [] }

/-- Add an assumption -/
def assume (ctx : CofContext) (φ : Expr) : CofContext :=
  { assumptions := normalize φ :: ctx.assumptions }

/-- Add multiple assumptions -/
def assumeAll (ctx : CofContext) (φs : List Expr) : CofContext :=
  { assumptions := φs.map normalize ++ ctx.assumptions }

/-- Get the combined assumption (meet of all) -/
def combined (ctx : CofContext) : Expr :=
  meetAll ctx.assumptions

/-- Check if context is consistent -/
def isConsistent (ctx : CofContext) : Bool :=
  Cofibration.isConsistent (combined ctx)

/-- Test if a cofibration follows from context -/
def entails (ctx : CofContext) (φ : Expr) : Bool :=
  Cofibration.entails ctx.assumptions φ

/-- Check if context is inconsistent (contradiction) -/
def isInconsistent (ctx : CofContext) : Bool :=
  !ctx.isConsistent

end CofContext

/-! ## Restriction Operations

    Working under a cofibration assumption.
-/

/-- Restrict an expression under a cofibration
    If φ is true, we can simplify certain expressions -/
def restrictExpr (φ : Expr) (e : Expr) : Expr :=
  -- If assuming φ = (r = 0), substitute r → 0
  -- If assuming φ = (r = 1), substitute r → 1
  match φ with
  | .cof_eq (.dimVar n) .dim0 => substDim n dim0 e
  | .cof_eq (.dimVar n) .dim1 => substDim n dim1 e
  | .cof_eq .dim0 (.dimVar n) => substDim n dim0 e
  | .cof_eq .dim1 (.dimVar n) => substDim n dim1 e
  | _ => e
where
  substDim (n : Nat) (val : Expr) : Expr → Expr
    | .dimVar m => if m == n then val else dimVar m
    | .cof_eq r s => cof_eq (substDim n val r) (substDim n val s)
    | .cof_and p q => cof_and (substDim n val p) (substDim n val q)
    | .cof_or p q => cof_or (substDim n val p) (substDim n val q)
    | e => e

/-- Apply restriction from context -/
def applyRestrictions (ctx : CofContext) (e : Expr) : Expr :=
  ctx.assumptions.foldl (fun e φ => restrictExpr φ e) e

/-! ## Forall Cofibration

    Universal quantification over a dimension: ∀i. φ(i)
-/

/-- Check if ∀i. φ(i) holds (φ must hold for i=0 and i=1) -/
def forallDim (_n : Nat) (φ : Expr) : Bool :=
  let φ0 := normalize (subst0 dim0 φ)
  let φ1 := normalize (subst0 dim1 φ)
  isTop φ0 && isTop φ1

/-- Build ∀i. φ(i) as (φ[0/i] ∧ φ[1/i]) -/
def mkForallDim (φ : Expr) : Expr :=
  let φ0 := normalize (subst0 dim0 φ)
  let φ1 := normalize (subst0 dim1 φ)
  meet φ0 φ1

/-! ## Boundary Condition Checking

    Check if an expression agrees with its boundary.
-/

/-- Structure representing boundary data -/
structure BoundaryData where
  cof : Expr        -- The cofibration (e.g., ∂r)
  value : Expr      -- The boundary value
  deriving Repr, BEq

/-- Check if expression matches boundary under cofibration -/
def checkBoundary (expr : Expr) (bdry : BoundaryData) : Bool :=
  -- Under the cofibration, expr should equal the boundary value
  -- This is a syntactic check; semantic equality requires normalization
  let restricted := restrictExpr bdry.cof expr
  let expected := restrictExpr bdry.cof bdry.value
  restricted == expected

/-- Build boundary constraint: x : A | φ → u
    Meaning: x equals u when φ is true -/
def mkBoundaryConstraint (_x u : Expr) (φ : Expr) : Expr :=
  -- Represents the constraint that x = u under φ
  -- In types, this is Sub A φ (λ_. u)
  sub (lit "type") φ (lam u)

/-! ## Split/Case Analysis on Cofibrations

    Build expressions that branch on cofibration cases.
-/

/-- Build a cofibration split: [φ₁ → e₁ | ... | φₙ → eₙ] -/
def mkSplit (branches : List (Expr × Expr)) : Expr :=
  sys branches

/-- Check if a split covers all cases under a context -/
def splitCovers (ctx : CofContext) (branches : List (Expr × Expr)) : Bool :=
  let cofs := branches.map (·.1)
  let combined := joinAll cofs
  ctx.entails combined

/-! ## Cofibration Builders (matching cooltt's CofBuilder) -/

namespace CofBuilder

def eq (r s : Expr) : Expr := Cofibration.eq r s
def eq0 (r : Expr) : Expr := Cofibration.eq0 r
def eq1 (r : Expr) : Expr := Cofibration.eq1 r
def le (r s : Expr) : Expr := Cofibration.le r s
def meet (φ ψ : Expr) : Expr := Cofibration.meet φ ψ
def join (φ ψ : Expr) : Expr := Cofibration.join φ ψ
def meetAll (φs : List Expr) : Expr := Cofibration.meetAll φs
def joinAll (φs : List Expr) : Expr := Cofibration.joinAll φs
def boundary (r : Expr) : Expr := Cofibration.boundary r
def top : Expr := Cofibration.top
def bot : Expr := Cofibration.bot

end CofBuilder

/-! ## Dimension Probe (for forall quantification) -/

/-- Fresh dimension variable for quantification -/
def freshDimVar (level : Nat) : Expr := dimVar level

/-- Bind a dimension variable -/
def bindDim (body : Expr → Expr) : Expr :=
  -- Create a fresh dimension variable at level 0
  -- and shift any references in the body
  let e := body (dimVar 0)
  -- The body is under a new binder
  plam e

/-! ## Boundary Satisfied Check -/

/-- Result of boundary satisfaction check -/
inductive BoundarySat
  | sat       -- Boundary is satisfied
  | unsat     -- Boundary is not satisfied
  | unknown   -- Cannot determine
  deriving Repr, BEq

/-- Check if term satisfies its boundary constraint -/
def checkBoundarySat (term : Expr) (_ty : Expr) (φ : Expr) (bdry : Expr) : BoundarySat :=
  if isBot φ then .sat  -- Vacuously true
  else
    -- Under φ, term should equal bdry
    let termAtBdry := restrictExpr φ term
    let expected := restrictExpr φ bdry
    if termAtBdry == expected then .sat
    else if isTop φ then .unsat  -- φ is always true but doesn't match
    else .unknown

/-! ## Pretty Printing -/

def cofToString : Expr → String
  | .cof_top => "⊤"
  | .cof_bot => "⊥"
  | .cof_eq r s => s!"({r} = {s})"
  | .cof_and φ ψ => s!"({cofToString φ} ∧ {cofToString ψ})"
  | .cof_or φ ψ => s!"({cofToString φ} ∨ {cofToString ψ})"
  | e => s!"{repr e}"

instance : ToString CofContext where
  toString ctx := s!"CofContext[{ctx.assumptions.map cofToString}]"

end Lego.Cubical.Cofibration
