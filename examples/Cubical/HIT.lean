/-
  Lego.Cubical.HIT: Higher Inductive Types (HITs) specialized Kan operations

  This module provides the specialized Kan operations for built-in HITs:
  - Nat: Natural numbers with zero and suc
  - Circle (S¹): Circle with base and loop

  Mathematical structure:
  - HITs are initial algebras with path constructors
  - Kan operations (coe, hcom) must respect the path constructors
  - For Nat: hcom returns an fhcom (fibrant hcom) wrapping the computation
  - For Circle: loop paths must be preserved under hcom

  Key insight: When computing hcom for a HIT, if the result isn't
  a canonical form, we wrap it in an fhcom to delay computation
  until more information is available.

  Based on cooltt's Semantics.ml and redtt's Desc.ml HIT handling
-/

import Lego.Cubical.Core
import Lego.Cubical.FHCom

namespace Lego.Cubical.HIT

open Lego.Core
open Lego.Cubical
open Lego.Cubical.FHCom

/-! ## HIT Information

    Track which types are HITs and their structure
-/

/-- Known HIT types -/
inductive HITKind
  | nat     -- Natural numbers
  | circle  -- Circle S¹
  deriving Repr, BEq, Inhabited

/-- Check if an expression is a HIT type -/
def isHIT? : Expr → Option HITKind
  | .nat => some .nat
  | .circle => some .circle
  | _ => none

/-- Get the eliminator type for a HIT -/
def hitElimType (kind : HITKind) (motive : Expr) : Expr :=
  match kind with
  | .nat =>
    -- Nat eliminator type: (n : Nat) → P n
    -- where P : Nat → Type, z : P 0, s : (n : Nat) → P n → P (suc n)
    .pi .nat (.app motive.shift (.ix 0))
  | .circle =>
    -- Circle eliminator type: (x : S¹) → P x
    -- where P : S¹ → Type, b : P base, l : PathP (i. P (loop i)) b b
    .pi .circle (.app motive.shift (.ix 0))

/-! ## Nat Kan Operations

    Kan operations for natural numbers.
    Natural numbers are a "discrete" HIT - paths are just equality.
-/

/-- Check if a Nat is in canonical form (zero or suc) -/
def isNatCanonical : Expr → Bool
  | .zero => true
  | .suc _ => true
  | _ => false

/-- Homogeneous composition for Nat (fuel-limited)
    hcom r r' Nat [(φ₁, tube₁), ...] cap : Nat

    For Nat, if the result is canonical (zero/suc), return it.
    Otherwise, wrap in fhcom to delay computation.
-/
def hcomNatAux (fuel : Nat) (r r' : Expr) (tubes : List (Expr × Expr)) (cap : Expr) : Expr :=
  if fuel == 0 then mkFHCom r r' cap tubes
  else
    -- First, try to evaluate the cap
    let capNorm := Expr.normalize 100 cap
    match capNorm with
    | .zero =>
      -- If cap is zero and tubes agree (when φ holds), result is zero
      -- For simplicity, if cap is zero, assume result is zero
      .zero
    | .suc n =>
      -- If cap is suc n, result is suc (hcom n ...)
      -- Recursively apply hcom to the predecessor
      let tubesInner := tubes.map fun (φ, tube) =>
        -- tube : (i : 𝕀) → Nat, extract the suc argument
        (φ, .lam (.natElim (.lam .nat)  -- P = λ_. Nat
                          .zero         -- zero case: 0
                          (.lam (.lam (.ix 1)))  -- suc case: λn. λih. n
                          (.app tube (.ix 0))))
      .suc (hcomNatAux (fuel - 1) r r' tubesInner n)
    | _ =>
      -- Not canonical, wrap in fhcom
      mkFHCom r r' cap tubes
termination_by fuel
decreasing_by
  simp_wf
  have h : fuel ≠ 0 := by simp_all
  omega

def hcomNat (r r' : Expr) (tubes : List (Expr × Expr)) (cap : Expr) : Expr :=
  hcomNatAux 100 r r' tubes cap

/-- Coercion for Nat (along constant type line)
    coe r r' (λi. Nat) n = n  (Nat is constant)
-/
def coeNat (_r _r' : Expr) (n : Expr) : Expr := n

/-! ## Circle Kan Operations

    Kan operations for the circle S¹.
    The circle has a non-trivial loop, so Kan operations are more complex.
-/

/-- Check if a Circle element is in canonical form -/
def isCircleCanonical : Expr → Bool
  | .base => true
  | .loop _ => true
  | _ => false

/-- Homogeneous composition for Circle
    hcom r r' S¹ [(φ₁, tube₁), ...] cap : S¹


    For Circle, we need to handle base and loop cases.
    If the result isn't canonical, wrap in fhcom.
-/
def hcomCircle (r r' : Expr) (tubes : List (Expr × Expr)) (cap : Expr) : Expr :=
  let capNorm := Expr.normalize 100 cap
  match capNorm with
  | .base =>
    -- If cap is base and all tubes return base when φ holds, result is base
    -- For simplicity, return base (full impl would check tubes)
    .base
  | .loop dimArg =>
    -- If cap is loop(i), we need to compute hcom along the loop
    -- This involves composing the dimension with the hcom structure
    -- For simplicity, return loop applied to composed dimension
    -- Full implementation would use com (heterogeneous composition)
    .loop (hcomDim r r' tubes dimArg)
  | _ =>
    -- Not canonical, wrap in fhcom tagged with circle
    mkFHCom r r' cap tubes
where
  /-- Compose dimensions for hcom inside loop -/
  hcomDim (_r _r' : Expr) (_tubes : List (Expr × Expr)) (dim : Expr) : Expr :=
    -- Simplified: just return the dimension
    -- Full impl would do proper composition
    dim

/-- Coercion for Circle (along constant type line)
    coe r r' (λi. S¹) x = x  (Circle is constant)
-/
def coeCircle (_r _r' : Expr) (x : Expr) : Expr := x

/-! ## Unified HIT Kan Operations -/

/-- Homogeneous composition for any HIT type -/
def hcomHIT (kind : HITKind) (r r' : Expr) (tubes : List (Expr × Expr)) (cap : Expr) : Expr :=
  match kind with
  | .nat => hcomNat r r' tubes cap
  | .circle => hcomCircle r r' tubes cap

/-- Coercion for any HIT type -/
def coeHIT (kind : HITKind) (r r' : Expr) (elem : Expr) : Expr :=
  match kind with
  | .nat => coeNat r r' elem
  | .circle => coeCircle r r' elem

/-! ## HIT Reduction Rules

    Additional step rules for HIT-specific reductions
-/

/-- Try to reduce HIT-specific expressions -/
def stepHIT : Expr → Option Expr
  -- coe for Nat (constant type)
  | .coe _ _ (.plam .nat) n => some n
  -- coe for Circle (constant type)
  | .coe _ _ (.plam .circle) x => some x
  -- hcom for Nat with canonical cap
  | .hcom r r' .nat phi cap =>
    if isNatCanonical cap then
      some (hcomNat r r' [(phi, .lam cap)] cap)
    else
      none
  -- hcom for Circle with canonical cap
  | .hcom r r' .circle phi cap =>
    if isCircleCanonical cap then
      some (hcomCircle r r' [(phi, .lam cap)] cap)
    else
      none
  | _ => none

/-! ## HIT Smart Constructors -/

/-- Create a natural number literal -/
def mkNatLit : Nat → Expr
  | 0 => .zero
  | n + 1 => .suc (mkNatLit n)

/-- Convert an Expr to a natural number (if possible) -/
def toNatLit? : Expr → Option Nat
  | .zero => some 0
  | .suc n => (toNatLit? n).map (· + 1)
  | _ => none

/-- Create an addition on naturals using natElim -/
def mkNatAdd (m n : Expr) : Expr :=
  -- add m n = natElim (λ_. Nat) m (λ_ ih. suc ih) n
  .natElim (.lam .nat) m (.lam (.lam (.suc (.ix 0)))) n

/-- Create multiplication on naturals using natElim -/
def mkNatMul (m n : Expr) : Expr :=
  -- mul m n = natElim (λ_. Nat) zero (λ_ ih. add m ih) n
  .natElim (.lam .nat) .zero (.lam (.lam (mkNatAdd m.shift.shift (.ix 0)))) n

/-! ## Circle Paths -/

/-- The loop path from base to base
    loop : PathP (λi. S¹) base base
-/
def loopPath : Expr :=
  .plam (.loop (.dimVar 0))

/-- Check if two circle elements are equal at boundary -/
def circleAgreeAtBoundary (e1 e2 : Expr) (dim : Expr) : Bool :=
  match dim with
  | .dim0 =>
    -- At 0, loop 0 = base
    let e1' := if e1 == .loop .dim0 then .base else e1
    let e2' := if e2 == .loop .dim0 then .base else e2
    e1' == e2'
  | .dim1 =>
    -- At 1, loop 1 = base
    let e1' := if e1 == .loop .dim1 then .base else e1
    let e2' := if e2 == .loop .dim1 then .base else e2
    e1' == e2'
  | _ => false

/-! ## HIT Info Structure -/

/-- Information about a HIT element -/
structure HITInfo where
  kind : HITKind
  isCanonical : Bool
  constructorName : String
  deriving Repr, BEq

/-- Analyze a HIT element -/
def analyzeHIT (e : Expr) : Option HITInfo :=
  match e with
  | .zero => some ⟨.nat, true, "zero"⟩
  | .suc _ => some ⟨.nat, true, "suc"⟩
  | .base => some ⟨.circle, true, "base"⟩
  | .loop _ => some ⟨.circle, true, "loop"⟩
  | .natElim _ _ _ _ => some ⟨.nat, false, "natElim"⟩
  | .circleElim _ _ _ _ => some ⟨.circle, false, "circleElim"⟩
  | _ => none

end Lego.Cubical.HIT
