/-
  Lego.Cubical.FHCom: Fibrant Homogeneous Composition

  FHCom (Fibrant HCom) is used for types in cubical type theory.
  When a type A is formed as an FHCom, elements of A are boxes (Box),
  and extraction from Box is via Cap.

  In redtt:
  - FHCom represents types as Kan-filled values
  - Box introduces elements of FHCom types
  - Cap eliminates FHCom types (extracts the "cap" from a box)

  The FHCom type formation:
    fhcom r r' cap [(φ₁, tube₁), ...] : Type

  When we have an element of FHCom type, it's a Box:
    box r r' cap [(φ₁, side₁), ...] : fhcom r r' cap [(φ₁, tube₁), ...]

  Cap extracts from a Box:
    cap r r' ty sys v : ty
      where v : fhcom r r' ty sys

  Mathematical structure:
  - FHCom implements composition of types in the universe
  - Box/Cap form an adjoint pair for FHCom types
  - This enables the universe to be Kan (have fillers)
-/

import Cubical.Core
import Cubical.Kan
import Cubical.Visitor

namespace Lego.Cubical.FHCom

open Lego.Core
open Lego.Core.Expr
open Lego.Cubical.Kan

/-! ## FHCom Type Formation

    fhcom r r' cap sys : Type

    Forms a type by "composing" in the universe.
    - r, r' : dimensions (source and target)
    - cap : the "cap" type (at dimension r)
    - sys : system of faces [(φ₁, tube₁), ...]
      where each tube is a path from r to r' in types

    When r = r', fhcom r r cap sys = cap.
    When φ is true, the type is the tube at the endpoint.
-/

/-- Information about an FHCom type -/
structure FHComInfo where
  r  : Expr      -- source dimension
  r' : Expr      -- target dimension
  cap : Expr     -- cap type (at dimension r)
  sys : List (Expr × Expr)  -- system of (cofibration, tube)
  deriving Repr, BEq

namespace FHComInfo

/-- Check if direction is degenerate -/
def isDegenerate (info : FHComInfo) : Bool :=
  info.r == info.r'

/-- Evaluate FHCom at endpoint r (gives cap) -/
def atR (info : FHComInfo) : Expr :=
  info.cap

/-- Evaluate FHCom at endpoint r' (gives result type) -/
def atR' (info : FHComInfo) : Expr :=
  -- When evaluating at r', if any face is active, use the tube endpoint
  -- Otherwise return cap
  -- Simplified: for degenerate case, return cap
  if info.isDegenerate then info.cap
  else info.cap  -- Full implementation would evaluate tubes at r'

/-- Try to reduce FHCom type -/
def reduce (info : FHComInfo) : Option Expr :=
  -- Rule 1: degenerate direction
  if info.isDegenerate then some info.cap
  else
    -- Rule 2: check if any face projects
    -- (Would check if any φ evaluates to true and return the corresponding tube at r')
    none

end FHComInfo

/-! ## Box Introduction

    box r r' cap sys : fhcom r r' capTy sysTy

    Introduces an element of an FHCom type.
    - cap : element of the cap type (at dimension r)
    - sys : system giving sides that must agree with cap

    A box packs together:
    - A cap element
    - Evidence that the cap agrees with the system boundaries
-/

/-- Information about a Box -/
structure BoxInfo where
  r  : Expr      -- source dimension
  r' : Expr      -- target dimension
  cap : Expr     -- cap element
  sys : List (Expr × Expr)  -- system of (cofibration, side)
  deriving Repr, BEq

namespace BoxInfo

/-- Check if direction is degenerate -/
def isDegenerate (info : BoxInfo) : Bool :=
  info.r == info.r'

/-- Get cap element -/
def getCap (info : BoxInfo) : Expr :=
  info.cap

/-- Try to reduce Box -/
def reduce (info : BoxInfo) : Option Expr :=
  -- Degenerate case: box r r cap sys = cap
  if info.isDegenerate then some info.cap
  else none

end BoxInfo

/-! ## Cap Elimination

    cap r r' ty sys v : ty

    Eliminates an FHCom element to get the cap.
    - v : fhcom r r' ty sys (an FHCom element)
    - Returns: the cap of v

    Key computation rules:
    1. cap r r' ty sys (box r r' cap sys) = cap  (β-rule)
    2. cap r r ty sys v = v  (degenerate direction)
-/

/-- Information about a Cap elimination -/
structure CapInfo where
  r  : Expr
  r' : Expr
  ty : Expr      -- expected cap type
  sys : List (Expr × Expr)  -- system
  el : Expr      -- element to eliminate
  deriving Repr, BEq

namespace CapInfo

/-- Check if direction is degenerate -/
def isDegenerate (info : CapInfo) : Bool :=
  info.r == info.r'

/-- Try to reduce Cap -/
def reduce (info : CapInfo) : Option Expr :=
  -- Rule 1: degenerate direction
  if info.isDegenerate then some info.el
  else
    -- Rule 2: β-rule - cap of box is cap
    match info.el with
    | .boxEl _r _r' cap _sys => some cap
    | _ => none

end CapInfo

/-! ## Smart Constructors -/

/-- Create FHCom type with immediate reduction -/
def mkFHCom (r r' cap : Expr) (sysList : List (Expr × Expr)) : Expr :=
  let info : FHComInfo := ⟨r, r', cap, sysList⟩
  match info.reduce with
  | some e => e
  | none => .fhcom r r' cap sysList

/-- Create Box with immediate reduction -/
def mkBox (r r' cap : Expr) (sysList : List (Expr × Expr)) : Expr :=
  let info : BoxInfo := ⟨r, r', cap, sysList⟩
  match info.reduce with
  | some e => e
  | none => .boxEl r r' cap sysList

/-- Create Cap elimination with immediate reduction -/
def mkCap (r r' ty : Expr) (sysList : List (Expr × Expr)) (el : Expr) : Expr :=
  let info : CapInfo := ⟨r, r', ty, sysList, el⟩
  match info.reduce with
  | some e => e
  | none => .capEl r r' ty sysList el

/-! ## Coercion in FHCom Types

    Coercing in an FHCom type is complex:
    coe r r' (λi. fhcom s s' cap[i] sys[i]) v

    The algorithm (from redtt Val.ml rigid_coe FHCom):
    1. Coerce the cap through the varying cap type line
    2. Compute recovery faces for the boundaries
    3. Build the result as an hcom
-/

/-- Coerce in FHCom type (simplified) -/
def coeFHCom (dir : Dir) (fhcomInfo : FHComInfo) (el : Expr) : Expr :=
  if dir.isDegenerate then el
  else
    -- Full implementation would follow redtt's algorithm
    -- For now, just wrap in coe
    .coe (dimOfDir dir.src) (dimOfDir dir.tgt)
         (.fhcom fhcomInfo.r fhcomInfo.r' fhcomInfo.cap fhcomInfo.sys)
         el
where
  dimOfDir : Dim → Expr
    | .i0 => .dim0
    | .i1 => .dim1
    | .dvar n => .dimVar n

/-! ## HCom in FHCom Types

    Composition in an FHCom type.
    hcom r r' (fhcom s s' cap sys) φ tube v

    This is where the fibrant structure comes in:
    the FHCom type has Kan structure by construction.
-/

/-- HCom in FHCom type (simplified) -/
def hcomFHCom (_dir : Dir) (fhcomInfo : FHComInfo) (_phi : Expr)
    (_tube : Expr) (cap : Expr) : Expr :=
  -- Full implementation would use the FHCom's Kan structure
  -- For now, just return the cap for degenerate cases
  if fhcomInfo.isDegenerate then cap
  else .hcom fhcomInfo.r fhcomInfo.r' fhcomInfo.cap .cof_bot cap

/-! ## Reduction -/

/-- Try to reduce FHCom expressions -/
def reduceFHComExpr (e : Expr) : Option Expr :=
  match e with
  | .fhcom r r' cap sysList =>
    let info : FHComInfo := ⟨r, r', cap, sysList⟩
    info.reduce
  | .boxEl r r' cap sysList =>
    let info : BoxInfo := ⟨r, r', cap, sysList⟩
    info.reduce
  | .capEl r r' ty sysList el =>
    let info : CapInfo := ⟨r, r', ty, sysList, el⟩
    info.reduce
  | _ => none

/-! ## Normalization -/

/-- Normalize FHCom-related expressions using visitor pattern -/
def normalizeFHCom (fuel : Nat) (e : Expr) : Expr :=
  e.normalizeStep fuel reduceFHComExpr Expr.subst (fun d body => Expr.subst 0 d body)

end Lego.Cubical.FHCom
