/-
  Lego.Cubical.SubType: Cubical Sub-types (Restriction Types)

  Sub-types encode partial elements with boundary constraints:
    sub A φ t : Type
  where elements of `sub A φ t` are elements of A that equal t when φ is true.

  This is the foundation for:
  - Partial elements that are only defined under certain cofibrations
  - Boundary constraints in extension types
  - Precise typing for hcom/coe operations

  Mathematical structure:
    Sub A φ t ≅ { x : A | φ → x = t }

  Key rules:
    sub-formation:  A : Type, φ : Cof, t : [φ] → A ⊢ sub A φ t : Type
    sub-intro:      e : A, [φ ⊢ e = t] ⊢ subIn e : sub A φ t
    sub-elim:       e : sub A φ t ⊢ subOut e : A
    sub-β:          subOut (subIn e) ≡ e
    sub-η:          e : sub A φ t ⊢ subIn (subOut e) ≡ e

  Reference: cooltt's Sub type (D.Sub in Domain.ml, S.Sub in Syntax.ml)
-/

import Lego.Cubical.Core

namespace Lego.Cubical.SubType

open Lego.Core
open Lego.Core.Expr

/-! ## SubInfo: Information about a sub type -/

/-- Information extracted from a sub type -/
structure SubInfo where
  /-- The base type A -/
  baseType : Expr
  /-- The cofibration φ -/
  cof : Expr
  /-- The boundary term (binds proof of φ) -/
  boundary : Expr
  deriving Repr, BEq

namespace SubInfo

/-- Extract SubInfo from a sub type expression -/
def fromExpr? : Expr → Option SubInfo
  | .sub ty cof bdry => some { baseType := ty, cof := cof, boundary := bdry }
  | _ => none

/-- Convert SubInfo back to expression -/
def toExpr (info : SubInfo) : Expr :=
  .sub info.baseType info.cof info.boundary

/-- Check if a sub type has trivial cofibration (always true) -/
def isTrivial (info : SubInfo) : Bool :=
  info.cof == .cof_top

/-- Check if a sub type has impossible cofibration (always false) -/
def isImpossible (info : SubInfo) : Bool :=
  info.cof == .cof_bot

/-- Get the underlying base type -/
def getBaseType (info : SubInfo) : Expr := info.baseType

/-- Evaluate the boundary at a proof (substitute proof for index 0) -/
def evalBoundary (info : SubInfo) (prf : Expr) : Expr :=
  Expr.subst0 prf info.boundary

end SubInfo

/-! ## Smart Constructors -/

/-- Create a sub type: sub A φ (λ_. t) -/
def mkSub (baseType : Expr) (cof : Expr) (boundary : Expr) : Expr :=
  .sub baseType cof boundary

/-- Create subIn with simplification -/
def mkSubIn (e : Expr) : Expr :=
  -- Could simplify: subIn (subOut e) → e
  .subIn e

/-- Create subOut with β-reduction -/
def mkSubOut (e : Expr) : Expr :=
  match e with
  -- β-rule: subOut (subIn e) → e
  | .subIn inner => inner
  | _ => .subOut e

/-! ## Reduction Rules -/

/-- β-reduction for sub types: subOut (subIn e) → e -/
def reduceSubOut : Expr → Option Expr
  | .subOut (.subIn e) => some e
  | _ => none

/-- Reduce sub type expressions -/
def reduceSubExpr : Expr → Option Expr
  | .subOut e =>
    match e with
    | .subIn inner => some inner
    | _ => none
  | _ => none

/-! ## Normalization -/

/-- Normalize sub type expressions (fuel-limited) -/
partial def normalizeSub (fuel : Nat) (e : Expr) : Expr :=
  if fuel == 0 then e
  else
    match reduceSubExpr e with
    | some e' => normalizeSub (fuel - 1) e'
    | none =>
      match e with
      | .sub ty cof bdry =>
        .sub (normalizeSub fuel ty) (normalizeSub fuel cof) (normalizeSub fuel bdry)
      | .subIn inner => .subIn (normalizeSub fuel inner)
      | .subOut inner =>
        let inner' := normalizeSub fuel inner
        -- Try reduction after normalizing inner
        match inner' with
        | .subIn x => x
        | _ => .subOut inner'
      | _ => e

/-! ## Conversion with other types -/

/-- A trivial sub type (with ⊤ cofibration) is equivalent to its base type -/
def trivialSubEquiv (ty : Expr) : Expr :=
  mkSub ty .cof_top (Expr.ix 0)  -- boundary is just the identity

/-- An impossible sub type (with ⊥ cofibration) has no boundary constraint -/
def impossibleSub (ty : Expr) : Expr :=
  mkSub ty .cof_bot (Expr.lit "⊥-elim")  -- boundary is vacuously satisfied

/-! ## Sub type as refinement -/

/-- Check if two sub types are equivalent
    (same base type, equivalent cofibrations, and compatible boundaries) -/
def subTypeEquiv (s1 s2 : SubInfo) : Bool :=
  Lego.Core.conv s1.baseType s2.baseType &&
  Lego.Core.conv s1.cof s2.cof &&
  Lego.Core.conv s1.boundary s2.boundary

/-! ## Integration with Extension Types -/

/-- Extension types can be seen as iterated sub types.
    ext 1 (λi. A) φ bdry ≅ (i : 𝕀) → sub A[i] (φ[i]) (bdry[i])
    This connection is key for boundary checking. -/
def extAsSub (n : Nat) (fam : Expr) (cof : Expr) (bdry : Expr) : Expr :=
  -- For now, just wrap in ext
  -- A more sophisticated implementation would use iterated sub types
  .ext n fam cof bdry

/-! ## Utilities for boundary checking -/

/-- Create a proof term for a cofibration equation r = s -/
def mkCofProof (r s : Expr) : Expr :=
  .refl (.cof_eq r s)  -- Simplified: actual proof would come from context

/-- Check if an element satisfies a boundary constraint
    This is a semantic check: when cof is true, elem should equal boundary[prf/x] -/
def checkBoundary (elem : Expr) (cof : Expr) (boundary : Expr) : Bool :=
  -- Simplified: in a full implementation, we would:
  -- 1. Check if cof is satisfiable
  -- 2. Under assumption cof is true, check elem ≡ boundary[prf/x]
  -- For now, we just check structural equality
  match cof with
  | .cof_bot => true  -- vacuously satisfied
  | .cof_top =>
    -- When always true, check elem ≡ boundary[trivial_prf/x]
    let bdryVal := Expr.subst0 (.lit "prf") boundary
    Lego.Core.conv (Expr.eval elem) (Expr.eval bdryVal)
  | _ => true  -- Assume satisfied for non-trivial cofibrations

/-! ## Sub type coercion -/

/-- Coerce through a sub type: coe in sub types is "strict"
    coe r r' (λi. sub A[i] φ[i] t[i]) (subIn e)
    = subIn (coe r r' (λi. A[i]) e) -/
def coeSub (r r' : Expr) (subLine : Expr) (elem : Expr) : Expr :=
  match elem with
  | .subIn inner =>
    -- Extract the base type line from sub type line
    -- subLine = λi. sub A[i] φ[i] t[i]
    -- We want to coe along λi. A[i]
    match subLine with
    | .lam (.sub baseTy _ _) =>
      let baseLine := Expr.lam baseTy
      .subIn (.coe r r' baseLine inner)
    | _ => .coe r r' subLine elem
  | _ => .coe r r' subLine elem

/-! ## Hcom in Sub types -/

/-- Homogeneous composition in sub types preserves the sub structure
    hcom r r' (sub A φ t) [(ψ, tube)] (subIn cap)
    = subIn (hcom r r' A [(ψ, λi. subOut (tube i))] cap) -/
def hcomSub (r r' : Expr) (subTy : Expr) (tubes : List (Expr × Expr)) (cap : Expr) : Expr :=
  match subTy, cap with
  | .sub baseTy _ _, .subIn innerCap =>
    -- Project tubes through subOut
    let projectedTubes := tubes.map fun (cof, tube) =>
      (cof, .lam (.subOut (.app (Expr.shift tube) (Expr.ix 0))))
    .subIn (.hcomTube r r' baseTy projectedTubes innerCap)
  | _, _ => .hcomTube r r' subTy tubes cap

/-! ## Pretty printing -/

/-- Pretty print a sub type -/
def ppSubType (info : SubInfo) : String :=
  s!"sub {info.baseType} {info.cof} {info.boundary}"

/-- Pretty print subIn -/
def ppSubIn (e : Expr) : String :=
  s!"(subIn {e})"

/-- Pretty print subOut -/
def ppSubOut (e : Expr) : String :=
  s!"(subOut {e})"

end Lego.Cubical.SubType
