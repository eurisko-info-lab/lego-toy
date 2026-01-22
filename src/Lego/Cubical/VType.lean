/-
  Lego.Cubical.VType: V-Types (Glue Types) for Univalence

  V-types are the key construction for implementing univalence in cubical type theory.
  They allow constructing paths between types from equivalences.

  Mathematical structure:
  - V r A B e : Type when r : 𝕀, A B : Type, e : Equiv A B
  - At r=0, V r A B e ≡ A
  - At r=1, V r A B e ≡ B
  - This gives ua : Equiv A B → Path Type A B via λ i → V i A B e

  Key operations:
  - vin r a b : V r A B e   (introduction)
  - vproj : V r A B e → B   (elimination)

  Based on redtt's Val.ml V-type implementation and CCHM cubical type theory.
-/

import Lego.Cubical.Core
import Lego.Cubical.Quote
import Lego.Cubical.Kan
import Lego.Cubical.Visitor

namespace Lego.Cubical.VType

open Lego.Core
open Lego.Core.Expr
open Lego.Cubical.Kan

/-! ## V-Type Formation

    V r A B e is a type when:
    - r : 𝕀 (dimension)
    - A : Type (type at r=0)
    - B : Type (type at r=1)
    - e : Equiv A B (equivalence witnessing they're equivalent)

    The key insight: V i A B e degenerates to A when i=0 and to B when i=1.
-/

/-- Information about a V-type -/
structure VTypeInfo where
  dimExpr : Expr     -- The dimension r
  ty0 : Expr         -- Type A (at r=0)
  ty1 : Expr         -- Type B (at r=1)
  equiv : Expr       -- Equivalence e : Equiv A B
  deriving Repr, BEq

/-- Information about a VIn introduction -/
structure VInInfo where
  dimExpr : Expr     -- The dimension r
  tm0 : Expr         -- Element of A (at r=0)
  tm1 : Expr         -- Element of B (at r=1)
  deriving Repr, BEq

namespace VTypeInfo

/-- Check if V-type is at dimension 0 -/
def atDim0 (info : VTypeInfo) : Bool :=
  info.dimExpr == dim0

/-- Check if V-type is at dimension 1 -/
def atDim1 (info : VTypeInfo) : Bool :=
  info.dimExpr == dim1

/-- Reduce V-type when dimension is concrete -/
def reduce (info : VTypeInfo) : Option Expr :=
  if info.atDim0 then some info.ty0
  else if info.atDim1 then some info.ty1
  else none

end VTypeInfo

namespace VInInfo

/-- Check if VIn is at dimension 0 -/
def atDim0 (info : VInInfo) : Bool :=
  info.dimExpr == dim0

/-- Check if VIn is at dimension 1 -/
def atDim1 (info : VInInfo) : Bool :=
  info.dimExpr == dim1

/-- Reduce VIn when dimension is concrete -/
def reduce (info : VInInfo) : Option Expr :=
  if info.atDim0 then some info.tm0
  else if info.atDim1 then some info.tm1
  else none

end VInInfo

/-! ## Equivalence Structure

    An equivalence e : Equiv A B consists of:
    - e.fst : A → B (the function)
    - e.snd : IsEquiv e.fst (the proof it's an equivalence)

    For V-type operations, we primarily use e.fst (the function).
-/

/-- Extract the function from an equivalence (assumes e is a pair) -/
def equivFunc (e : Expr) : Expr :=
  fst e

/-- Extract the inverse from an equivalence -/
def equivInv (e : Expr) : Expr :=
  -- equiv.snd.fst gives the inverse in standard encoding
  fst (snd e)

/-! ## VProj: Projection from V-type to B

    vproj : V r A B e → B

    Computation rules:
    - vproj (vin 0 a b) = e.fst a  (apply equivalence)
    - vproj (vin 1 a b) = b        (identity)
    - vproj (vin r a b) = b        (when r is variable, returns B component)
-/

/-- Reduce vproj elimination -/
def reduceVProj (r ty0 ty1 equiv el : Expr) : Expr :=
  match r with
  | .dim0 =>
    -- At r=0, apply the equivalence function to the element
    app (equivFunc equiv) el
  | .dim1 =>
    -- At r=1, element is already in B
    el
  | _ =>
    -- General case: check if el is a vin
    match el with
    | .vin _ _ tm1 => tm1  -- Return the B component
    | _ => vproj r ty0 ty1 equiv el

/-! ## V-Type Kan Operations

    V-types must be Kan-complete. This requires defining:
    - Coercion through V-types
    - Homogeneous composition in V-types

    The key idea is that coercion through V i A B e:
    - Uses coercion in A when going toward i=0
    - Uses coercion in B plus the equivalence when going toward i=1
-/

/-- Coerce through a V-type path -/
def coeV (dir : Dir) (vinfo : VTypeInfo) (el : Expr) : Expr :=
  if dir.isDegenerate then el
  else
    -- The general structure follows redtt's rigid_coe for V types
    match VTypeInfo.reduce vinfo with
    | some ty =>
      -- Concrete dimension: use regular coercion
      coe (dimToExpr dir.src) (dimToExpr dir.tgt) ty el
    | none =>
      -- V-type with variable dimension requires special handling
      -- Simplified: create a coe through the vtype
      coe (dimToExpr dir.src) (dimToExpr dir.tgt) (vtype vinfo.dimExpr vinfo.ty0 vinfo.ty1 vinfo.equiv) el
where
  dimToExpr : Dim → Expr
    | .i0 => dim0
    | .i1 => dim1
    | .dvar n => dimVar n

/-- Homogeneous composition in a V-type -/
def hcomV (dir : Dir) (vinfo : VTypeInfo) (cap : Expr) (sys : List (Expr × Expr)) : Expr :=
  if dir.isDegenerate then cap
  else
    match VTypeInfo.reduce vinfo with
    | some ty =>
      -- V-type reduced to concrete type, use regular hcom
      hcomTube (dimToExpr dir.src) (dimToExpr dir.tgt) ty sys cap
    | none =>
      -- V-type with variable dimension
      hcomTube (dimToExpr dir.src) (dimToExpr dir.tgt)
        (vtype vinfo.dimExpr vinfo.ty0 vinfo.ty1 vinfo.equiv) sys cap
where
  dimToExpr : Dim → Expr
    | .i0 => dim0
    | .i1 => dim1
    | .dvar n => dimVar n

/-! ## Univalence from V-Types

    The key theorem: ua : Equiv A B → Path Type A B
    is implemented as: ua e = λ i → V i A B e

    This works because:
    - V 0 A B e ≡ A
    - V 1 A B e ≡ B
    - V provides the path in between via the equivalence
-/

/-- Construct ua : Equiv A B → Path Type A B -/
def mkUA (tyA tyB equiv : Expr) : Expr :=
  -- ua e = λ i → V i A B e
  plam (vtype (dimVar 0) (Expr.shift tyA) (Expr.shift tyB) (Expr.shift equiv))

/-- Construct path→equiv : Path Type A B → Equiv A B -/
def mkPathToEquiv (path : Expr) : Expr :=
  -- Transport the identity equivalence along the path
  -- path→equiv p = coe 0 1 id-equiv in λ i → Equiv A (p i)
  -- Simplified representation
  app (app (ix 0) (lit "path→equiv")) path

/-! ## Normalization with V-Types

    Extend the normalizer to handle V-type constructs.
-/

/-- Try to reduce V-type related expressions -/
def reduceVTypeExpr : Expr → Option Expr
  | .vtype r ty0 ty1 equiv =>
    let info : VTypeInfo := { dimExpr := r, ty0 := ty0, ty1 := ty1, equiv := equiv }
    info.reduce
  | .vin r tm0 tm1 =>
    let info : VInInfo := { dimExpr := r, tm0 := tm0, tm1 := tm1 }
    info.reduce
  | .vproj r _ty0 _ty1 equiv el =>
    -- Check for simple reduction cases
    match r with
    | .dim0 => some (app (equivFunc equiv) el)
    | .dim1 => some el
    | _ => match el with
      | .vin _ _ tm1 => some tm1
      | _ => none
  | _ => none

/-- Normalize V-type expression using visitor pattern -/
def normalizeVExpr (e : Expr) : Expr :=
  e.normalizeStep 1000 reduceVTypeExpr Expr.subst (fun d body => Expr.subst 0 d body)

/-! ## V-Type Constructors -/

/-- Make a V-type: V r A B e -/
def mkV (r tyA tyB equiv : Expr) : Expr :=
  -- Check for immediate reduction
  match r with
  | .dim0 => tyA
  | .dim1 => tyB
  | _ => vtype r tyA tyB equiv

/-- Make a vin introduction: vin r a b -/
def mkVIn (r tm0 tm1 : Expr) : Expr :=
  match r with
  | .dim0 => tm0
  | .dim1 => tm1
  | _ => vin r tm0 tm1

/-- Make a vproj elimination with reduction -/
def mkVProj (r ty0 ty1 equiv el : Expr) : Expr :=
  reduceVProj r ty0 ty1 equiv el

/-! ## Tests -/

def vtypeTests : List (String × Bool) := [
  -- V-type reduction at endpoints
  ("V at 0 reduces to A",
    mkV dim0 (ix 0) (ix 1) (ix 2) == ix 0),

  ("V at 1 reduces to B",
    mkV dim1 (ix 0) (ix 1) (ix 2) == ix 1),

  ("V at variable is preserved",
    match mkV (dimVar 0) (ix 0) (ix 1) (ix 2) with
    | .vtype _ _ _ _ => true
    | _ => false),

  -- VIn reduction at endpoints
  ("vin at 0 reduces to a",
    mkVIn dim0 (ix 0) (ix 1) == ix 0),

  ("vin at 1 reduces to b",
    mkVIn dim1 (ix 0) (ix 1) == ix 1),

  ("vin at variable is preserved",
    match mkVIn (dimVar 0) (ix 0) (ix 1) with
    | .vin _ _ _ => true
    | _ => false),

  -- VProj reduction
  ("vproj at 0 applies function",
    match reduceVProj dim0 (ix 0) (ix 1) (pair (ix 10) (ix 11)) (ix 5) with
    | .app (.fst _) (.ix 5) => true
    | _ => false),

  ("vproj at 1 is identity",
    reduceVProj dim1 (ix 0) (ix 1) (ix 2) (ix 5) == ix 5),

  -- VTypeInfo
  ("VTypeInfo.atDim0 true",
    VTypeInfo.atDim0 { dimExpr := dim0, ty0 := ix 0, ty1 := ix 1, equiv := ix 2 }),

  ("VTypeInfo.atDim0 false",
    !VTypeInfo.atDim0 { dimExpr := dimVar 0, ty0 := ix 0, ty1 := ix 1, equiv := ix 2 }),

  ("VTypeInfo.reduce at 0",
    VTypeInfo.reduce { dimExpr := dim0, ty0 := ix 0, ty1 := ix 1, equiv := ix 2 } == some (ix 0)),

  ("VTypeInfo.reduce at 1",
    VTypeInfo.reduce { dimExpr := dim1, ty0 := ix 0, ty1 := ix 1, equiv := ix 2 } == some (ix 1)),

  -- VInInfo
  ("VInInfo.atDim1 true",
    VInInfo.atDim1 { dimExpr := dim1, tm0 := ix 0, tm1 := ix 1 }),

  ("VInInfo.reduce at 1",
    VInInfo.reduce { dimExpr := dim1, tm0 := ix 0, tm1 := ix 1 } == some (ix 1)),

  -- UA construction
  ("ua produces plam of vtype",
    match mkUA (ix 0) (ix 1) (ix 2) with
    | .plam (.vtype _ _ _ _) => true
    | _ => false),

  -- Normalization
  ("normalizeVExpr reduces V at 0",
    normalizeVExpr (vtype dim0 (ix 0) (ix 1) (ix 2)) == ix 0),

  ("normalizeVExpr reduces vin at 1",
    normalizeVExpr (vin dim1 (ix 0) (ix 1)) == ix 1),

  -- Dir checks for coeV
  ("coeV degenerate returns element",
    coeV { src := .i0, tgt := .i0 }
      { dimExpr := dimVar 0, ty0 := ix 0, ty1 := ix 1, equiv := ix 2 }
      (ix 5) == ix 5),

  -- Equiv accessors
  ("equivFunc extracts fst",
    match equivFunc (pair (ix 0) (ix 1)) with
    | .fst _ => true
    | _ => false),

  ("equivInv extracts snd.fst",
    match equivInv (pair (ix 0) (ix 1)) with
    | .fst (.snd _) => true
    | _ => false)
]

end Lego.Cubical.VType
