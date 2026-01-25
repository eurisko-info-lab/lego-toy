/-
  Lego.Cubical.ExtType: Extension Types for Cubical Type Theory

  Extension types allow specifying types with boundary constraints:
    ext n fam cof bdry : Type

  This represents types of the form:
    (i₁ ... iₙ : 𝕀) → A  with partial boundary when φ holds

  Key operations:
  - extLam: Introduction (binds n dimension variables)
  - extApp: Elimination (applies to n dimension arguments)

  Mathematical structure:
  - Extension types are like dependent products over the interval
  - But with a partial element specified on the boundary (cofibration)
  - Used for partial elements, higher-order paths, and fill operations

  redtt/cooltt reference:
  - Ext (NB (nms, (cod, sys))): extension type with named dimension binders
  - ExtLam: introduction form
  - ExtApp: elimination form
-/

import Cubical.Core

namespace Lego.Cubical.ExtType

open Lego.Core
open Lego.Core.Expr

/-! ## Extension Type Information

    An extension type `ext n fam cof bdry` has:
    - n: number of dimension variables bound
    - fam: the type family (λ i₁...iₙ. A)
    - cof: the cofibration (λ i₁...iₙ. φ)
    - bdry: the boundary (λ i₁...iₙ. partial element when φ)
-/

/-- Information about an extension type -/
structure ExtInfo where
  /-- Number of dimension variables bound -/
  arity : Nat
  /-- Type family (binds arity dimensions) -/
  family : Expr
  /-- Cofibration (binds arity dimensions) -/
  cof : Expr
  /-- Boundary term (binds arity dimensions) -/
  boundary : Expr
  deriving Repr, BEq

namespace ExtInfo

/-- Create ExtInfo from an extension type expression -/
def fromExpr? : Expr → Option ExtInfo
  | .ext n fam cof bdry => some ⟨n, fam, cof, bdry⟩
  | _ => none

/-- Convert back to an Expr -/
def toExpr (info : ExtInfo) : Expr :=
  .ext info.arity info.family info.cof info.boundary

/-- Check if extension type is nullary (0 dimensions) -/
def isNullary (info : ExtInfo) : Bool :=
  info.arity == 0

/-- Check if extension type has trivial boundary (cof = ⊥) -/
def hasTrivialBoundary (info : ExtInfo) : Bool :=
  match info.cof with
  | .cof_bot => true
  | _ => false

/-- Apply dimensions to the family, returning the instantiated type -/
def applyFamily (info : ExtInfo) (dims : List Expr) : Expr :=
  if dims.length != info.arity then
    info.family  -- Wrong arity, return unchanged
  else
    -- Substitute each dimension (right to left, since de Bruijn)
    dims.foldr (init := info.family) fun dim acc => subst0 dim acc

/-- Apply dimensions to the cofibration -/
def applyCof (info : ExtInfo) (dims : List Expr) : Expr :=
  if dims.length != info.arity then
    info.cof
  else
    dims.foldr (init := info.cof) fun dim acc => subst0 dim acc

/-- Apply dimensions to the boundary -/
def applyBoundary (info : ExtInfo) (dims : List Expr) : Expr :=
  if dims.length != info.arity then
    info.boundary
  else
    dims.foldr (init := info.boundary) fun dim acc => subst0 dim acc

end ExtInfo

/-! ## Smart Constructors -/

/-- Create an extension type with proper normalization -/
def mkExt (arity : Nat) (fam cof bdry : Expr) : Expr :=
  -- Simplify if cofibration is trivial
  match cof with
  | .cof_bot =>
    -- No boundary constraint: just a cube of type fam
    .ext arity fam cof bdry
  | .cof_top =>
    -- Full boundary constraint: bdry is total
    -- The type is a single point (bdry at any dimension)
    .ext arity fam cof bdry
  | _ =>
    .ext arity fam cof bdry

/-- Create extension lambda -/
def mkExtLam (arity : Nat) (body : Expr) : Expr :=
  .extLam arity body

/-- Create extension application -/
def mkExtApp (e : Expr) (dims : List Expr) : Expr :=
  match e with
  | .extLam n body =>
    if dims.length == n then
      -- β-reduction: (extLam n body) @ [r₁, ..., rₙ] → body[rᵢ/iᵢ]
      dims.foldr (init := body) fun dim acc => subst0 dim acc
    else
      .extApp e dims
  | _ => .extApp e dims

/-! ## Reduction Rules -/

/-- Reduce extension-related expressions -/
def reduceExtExpr : Expr → Option Expr
  -- β-rule: (extLam n body) @ [dims] → body[dims]
  | .extApp (.extLam n body) dims =>
    if dims.length == n then
      some (dims.foldr (init := body) fun dim acc => subst0 dim acc)
    else
      none
  | _ => none

/-- Normalize extension expressions -/
partial def normalizeExt (fuel : Nat) (e : Expr) : Expr :=
  if fuel == 0 then e
  else match reduceExtExpr e with
  | some e' => normalizeExt (fuel - 1) e'
  | none => e

/-! ## Path as Extension Type

    Path types are a special case of extension types:
    Path A a b ≅ ext 1 (λ_. A) (∂) (λi. if i=0 then a else b)

    where ∂ = (i=0 ∨ i=1)
-/

/-- Convert a path type to extension type form -/
def pathToExt (ty a b : Expr) : Expr :=
  let fam := shift ty  -- λi. A (A doesn't depend on i)
  let cof := .cof_or (.cof_eq (.dimVar 0) .dim0) (.cof_eq (.dimVar 0) .dim1)  -- i=0 ∨ i=1
  -- Boundary: at i=0 give a, at i=1 give b
  let bdry := .sys [(.cof_eq (.dimVar 0) .dim0, shift a),
                    (.cof_eq (.dimVar 0) .dim1, shift b)]
  .ext 1 fam cof bdry

/-- Check if an extension type is equivalent to a path type -/
def isPathLike (info : ExtInfo) : Bool :=
  info.arity == 1 &&
  match info.cof with
  | .cof_or (.cof_eq (.dimVar 0) .dim0) (.cof_eq (.dimVar 0) .dim1) => true
  | _ => false

/-! ## Coercion and Composition in Extension Types

    For coe in ext types:
    coe r r' (λi. ext n famᵢ cofᵢ bdryᵢ) e

    The coerced element applies dimension args, coerces the result,
    and must preserve the boundary.
-/

/-- Coercion through extension type line (simplified) -/
def coeExt (r r' : Expr) (tyLine : Expr) (el : Expr) : Expr :=
  -- Simplified: just return coe expression
  -- Full implementation would compute:
  -- extLam n (coe r r' (fam-line) (extApp el dims))
  .coe r r' tyLine el

/-- Hcom in extension types (simplified) -/
def hcomExt (r r' : Expr) (extTy : Expr) (phi : Expr) (cap : Expr) : Expr :=
  -- Simplified: just return hcom expression
  -- Full implementation would compute hcom pointwise on the cubes
  .hcom r r' extTy phi cap

/-! ## Boundary Checking

    For an element e : ext n fam cof bdry, we need to verify:
    - When cof holds, e agrees with bdry
    - That is: ∀ dims. cof(dims) → e @ dims ≡ bdry(dims)
-/

/-- Check if boundary is satisfied (simplified) -/
def boundaryCheck (_info : ExtInfo) (_el : Expr) : Bool :=
  -- Simplified: always return true
  -- Full implementation would verify boundary agreement
  true

/-! ## Tests -/

/-- Basic extension type creation -/
def testExtBasic : Bool :=
  let ext := mkExt 1 (.univ .zero) .cof_bot .zero
  match ExtInfo.fromExpr? ext with
  | some info => info.arity == 1
  | none => false

/-- Extension lambda reduction -/
def testExtLamReduce : Bool :=
  let e := mkExtApp (mkExtLam 1 (.ix 0)) [.dim0]
  e == .dim0

/-- Path to extension conversion -/
def testPathToExt : Bool :=
  let ext := pathToExt (.univ .zero) .zero .zero
  match ExtInfo.fromExpr? ext with
  | some info => info.arity == 1 && isPathLike info
  | none => false

end Lego.Cubical.ExtType
