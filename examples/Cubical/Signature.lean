/-
  Lego.Cubical.Signature: Signature types (records with named fields)

  Mathematical Structure:
  - Telescopes: dependent sequences of types (Γ ⊢ A₁, x₁:A₁ ⊢ A₂, ...)
  - Signatures: named telescopes forming record types
  - Structs: introduction form (record values)
  - Projections: elimination form (field access)

  Key features from cooltt:
  - Kan operations for signatures (mcoe, mcom)
  - Telescopic Kan structure
  - Include/embedding of sub-signatures

  Algebra:
  - Signatures form a category with morphisms being field projections
  - Structs are generalized n-ary products
  - Empty signature is the terminal object (Unit)
-/

import Lego.Cubical.Core

namespace Lego.Cubical.Signature

open Lego.Core
open Lego.Core.Expr

/-! ## Field Labels

    Labels identify fields in signatures/structs.
    Can be user-defined names or generated (anonymous).
-/

/-- Field label -/
inductive Label where
  | user : String → Label      -- Named field: `x`, `fst`, etc.
  | anon : Nat → Label         -- Anonymous field: _0, _1, etc.
  deriving Repr, BEq, Inhabited

namespace Label

def toString : Label → String
  | .user s => s
  | .anon n => s!"_{n}"

instance : ToString Label := ⟨toString⟩

def isAnon : Label → Bool
  | .anon _ => true
  | _ => false

end Label

/-! ## Telescopes

    A telescope is a dependent sequence of types:
      Γ ⊢ A₁ type
      Γ, x₁:A₁ ⊢ A₂ type
      Γ, x₁:A₁, x₂:A₂ ⊢ A₃ type
      ...

    Using de Bruijn: each type can reference all previous variables.
-/

/-- A telescope cell: (label, type) where type may depend on prior cells -/
structure Cell where
  label : Label
  ty    : Expr   -- May reference de Bruijn vars for prior fields
  deriving Repr, BEq

/-- Telescope: sequence of dependent (label, type) cells -/
abbrev Telescope := List Cell

namespace Telescope

/-- Empty telescope -/
def empty : Telescope := []

/-- Extend telescope with a new cell at the end -/
def extend (tele : Telescope) (lbl : Label) (ty : Expr) : Telescope :=
  tele ++ [{ label := lbl, ty := ty }]

/-- Number of fields -/
def length (tele : Telescope) : Nat := List.length tele

/-- Get labels in order -/
def labels (tele : Telescope) : List Label :=
  tele.map (·.label)

/-- Find cell by label -/
def findByLabel (tele : Telescope) (lbl : Label) : Option (Nat × Cell) :=
  let rec go (lst : List Cell) (idx : Nat) : Option (Nat × Cell) :=
    match lst with
    | [] => none
    | cell :: rest =>
      if cell.label == lbl then some (idx, cell) else go rest (idx + 1)
  go tele 0

/-- Get type at index (assuming prior fields are substituted) -/
def typeAt (tele : Telescope) (idx : Nat) : Option Expr :=
  if h : idx < List.length tele then some ((tele : List Cell)[idx]'h).ty else none

/-- Shift all types in telescope -/
def shiftAll (delta : Int) (tele : Telescope) : Telescope :=
  tele.map fun cell => { cell with ty := shiftAbove 0 delta cell.ty }

/-- Substitute into all types in telescope -/
def substAll (idx : Nat) (val : Expr) (tele : Telescope) : Telescope :=
  let indexed := (tele : List Cell).zip (List.range (List.length tele))
  indexed.map fun (cell, i) =>
    -- Each cell needs substitution adjusted for its position
    { cell with ty := subst (idx + i) val cell.ty }

end Telescope

/-! ## Kan Telescopes

    Telescopes where all types are given as codes in a universe.
    These support Kan operations (coe, com) through the telescope.

    KCell: (label, code, rest) where code : Type and rest depends on El(code)
-/

/-- Kan telescope cell: codes instead of types -/
structure KCell where
  label : Label
  code  : Expr   -- code : Type (a universe code)
  deriving Repr, BEq

/-- Kan telescope: for Kan operations on signatures -/
abbrev KTelescope := List KCell

namespace KTelescope

def empty : KTelescope := []

def extend (tele : KTelescope) (lbl : Label) (code : Expr) : KTelescope :=
  tele ++ [{ label := lbl, code := code }]

def length (tele : KTelescope) : Nat := List.length tele

def labels (tele : KTelescope) : List Label :=
  tele.map (·.label)

/-- Convert Kan telescope to regular telescope (El each code) -/
def toTelescope (ktele : KTelescope) : Telescope :=
  ktele.map fun kcell => { label := kcell.label, ty := kcell.code }

end KTelescope

/-! ## Signature Types

    Signature: named product type with dependent fields
      sig { x : A, y : B(x), z : C(x,y) }

    This is an n-ary generalization of Σ types with named projections.
-/

/-- Signature type representation -/
structure SignatureType where
  telescope : Telescope
  deriving Repr, BEq

namespace SignatureType

/-- Empty signature (unit type) -/
def empty : SignatureType := { telescope := [] }

/-- Single-field signature -/
def single (lbl : Label) (ty : Expr) : SignatureType :=
  { telescope := [{ label := lbl, ty := ty }] }

/-- Extend with a new field -/
def extend (sig : SignatureType) (lbl : Label) (ty : Expr) : SignatureType :=
  { telescope := sig.telescope.extend lbl ty }

/-- Number of fields -/
def numFields (sig : SignatureType) : Nat := sig.telescope.length

/-- Get all labels -/
def labels (sig : SignatureType) : List Label := sig.telescope.labels

/-- Find field index by label -/
def findField (sig : SignatureType) (lbl : Label) : Option Nat :=
  sig.telescope.findByLabel lbl |>.map (·.1)

/-- Get field type at index -/
def fieldType (sig : SignatureType) (idx : Nat) : Option Expr :=
  sig.telescope.typeAt idx

/-- Convert to nested sigma type -/
def toSigma (sig : SignatureType) : Expr :=
  match _h : sig.telescope with
  | [] => univ 0  -- Empty signature ~ Unit
  | [cell] => cell.ty
  | cell :: rest =>
    let restSig : SignatureType := { telescope := rest }
    sigma cell.ty (toSigma restSig)
termination_by List.length sig.telescope
decreasing_by simp_wf; simp_all [List.length_cons]

end SignatureType

/-! ## Struct Values

    Struct: named tuple / record value
      struct { x = a, y = b, z = c }

    Introduction form for signature types.
-/

/-- Field value in a struct -/
structure Field where
  label : Label
  value : Expr
  deriving Repr, BEq

/-- Struct: record value -/
structure Struct where
  fields : List Field
  deriving Repr, BEq

namespace Struct

/-- Empty struct (unit value) -/
def empty : Struct := { fields := [] }

/-- Single-field struct -/
def single (lbl : Label) (val : Expr) : Struct :=
  { fields := [{ label := lbl, value := val }] }

/-- Extend with a new field -/
def extend (s : Struct) (lbl : Label) (val : Expr) : Struct :=
  { fields := s.fields ++ [{ label := lbl, value := val }] }

/-- Number of fields -/
def numFields (s : Struct) : Nat := s.fields.length

/-- Get labels -/
def labels (s : Struct) : List Label := s.fields.map (·.label)

/-- Get values -/
def values (s : Struct) : List Expr := s.fields.map (·.value)

/-- Find field by label -/
def findField (s : Struct) (lbl : Label) : Option Field :=
  s.fields.find? fun f => f.label == lbl

/-- Get field value by label -/
def getField (s : Struct) (lbl : Label) : Option Expr :=
  s.findField lbl |>.map (·.value)

/-- Get field value by index -/
def getAt (s : Struct) (idx : Nat) : Option Expr :=
  if h : idx < s.fields.length then some (s.fields[idx].value) else none

/-- Convert to nested pair -/
def toPair (s : Struct) : Expr :=
  match _h : s.fields with
  | [] => lit "unit"  -- Empty struct ~ ()
  | [f] => f.value
  | f :: rest =>
    let restStruct : Struct := { fields := rest }
    pair f.value (toPair restStruct)
termination_by s.fields.length
decreasing_by
  simp_wf
  simp_all only [List.length_cons]
  omega

/-- Create struct from list of (label, value) pairs -/
def fromList (pairs : List (Label × Expr)) : Struct :=
  { fields := pairs.map fun (lbl, val) => { label := lbl, value := val } }

end Struct

/-! ## Projection Operations

    proj struct label idx : extract field from struct

    Reduces to nested fst/snd operations on pairs.
-/

/-- Project field at index from nested pair representation -/
def projAt (e : Expr) (idx : Nat) : Expr :=
  match idx with
  | 0 => fst e
  | n + 1 => projAt (snd e) n

/-- Build projection expression -/
def mkProj (struct : Expr) (_lbl : Label) (idx : Nat) : Expr :=
  -- For now, represent as nested fst/snd
  -- In cooltt, there's a dedicated Proj constructor
  projAt struct idx

/-! ## Unpack: Extract all fields from a struct -/

/-- Unpack struct into list of field values -/
def unpack (s : Struct) : List Expr :=
  s.values

/-- Unpack expression representing struct into field expressions -/
def unpackExpr (e : Expr) (numFields : Nat) : List Expr :=
  match numFields with
  | 0 => []
  | 1 => [e]
  | n + 1 => fst e :: unpackExpr (snd e) n

/-! ## Signature Equality

    Two signatures are equal if:
    - Same number of fields
    - Corresponding labels match
    - Corresponding types are equal (under substitution)
-/

/-- Check if two signatures have the same structure -/
def signaturesMatch (sig1 sig2 : SignatureType) : Bool :=
  sig1.telescope.length == sig2.telescope.length &&
  (sig1.telescope.zip sig2.telescope).all fun (c1, c2) =>
    c1.label == c2.label

/-! ## Kan Operations on Signatures

    Signatures support Kan operations telescopically:

    mcoe (coercion through signature type line):
      For a line of signature types: i ⊢ sig { x : A[i], y : B[i](x) }
      mcoe r r' line struct = struct { x = coe r r' A x, y = coe r r' B y }

    mcom (composition in signature type):
      Similar to mcoe but with hcom for each field
-/

/-- Build coercion through a signature (mcoe)
    Given: line : i → SignatureType, r, r', struct : sig(line r)
    Returns: struct' : sig(line r') with each field coerced -/
def buildMCoe (r r' : Expr) (struct : Expr) (ktele : KTelescope) : Expr :=
  let indexed := ktele.zip (List.range ktele.length)
  let fields := indexed.map fun (kcell, idx) =>
    let fieldVal := projAt struct idx
    let coercedVal := coe r r' (plam kcell.code) fieldVal
    { label := kcell.label, value := coercedVal : Field }
  (Struct.mk fields).toPair

/-- Build homogeneous composition in a signature (mcom)
    Given: sig type, r, r', phi, tubes, cap
    Returns: struct with each field composed -/
def buildMCom (r r' phi : Expr) (cap : Expr) (ktele : KTelescope) : Expr :=
  let indexed := ktele.zip (List.range ktele.length)
  let fields := indexed.map fun (kcell, idx) =>
    let fieldCap := projAt cap idx
    let composedVal := hcom r r' kcell.code phi fieldCap
    { label := kcell.label, value := composedVal : Field }
  (Struct.mk fields).toPair

/-! ## Type Checking Helpers -/

/-- Check if expression matches a struct with given labels -/
def isStructWith (e : Expr) (labels : List Label) : Bool :=
  -- For now, just check it's a nested pair with right number of fields
  match labels with
  | [] => true  -- Empty struct matches anything at unit
  | [_] => true  -- Single field struct
  | _ :: rest =>
    match e with
    | pair _ b => isStructWith b rest
    | _ => false

/-- Instantiate telescope with values (substitute all prior fields) -/
def instantiateTelescope (tele : Telescope) (vals : List Expr) : Option Telescope :=
  if vals.length < tele.length then none
  else
    let indexed := tele.zip (List.range tele.length)
    let instantiated := indexed.map fun (cell, idx) =>
      let priorVals := vals.take idx
      let priorIndexed := priorVals.zip (List.range priorVals.length)
      let ty' := priorIndexed.foldl (fun ty (v, i) => subst i v ty) cell.ty
      { cell with ty := ty' }
    some instantiated

/-! ## Signature Inclusion (Subtyping)

    One signature can include another if it has all the same fields
    (possibly with more fields added).
-/

/-- Check if sig2 extends sig1 (sig1 ⊆ sig2) -/
def isExtension (sig1 sig2 : SignatureType) : Bool :=
  let lbls1 := sig1.labels
  let lbls2 := sig2.labels
  lbls1.all fun lbl => lbls2.contains lbl

/-- Project signature extension to base signature -/
def projectToBase (sig1 sig2 : SignatureType) (struct2 : Expr) : Option Expr :=
  if !isExtension sig1 sig2 then none
  else
    let fields := sig1.labels.map fun lbl =>
      match sig2.findField lbl with
      | some idx => (lbl, projAt struct2 idx)
      | none => (lbl, lit "error")  -- Should not happen if isExtension is true
    some (Struct.fromList fields).toPair

/-! ## Pretty Printing -/

def labelToString (lbl : Label) : String := lbl.toString

def telescopeToString (tele : Telescope) : String :=
  let fields := tele.map fun cell => s!"{cell.label} : _"
  "{ " ++ ", ".intercalate fields ++ " }"

def signatureToString (sig : SignatureType) : String :=
  "sig " ++ telescopeToString sig.telescope

def structToString (s : Struct) : String :=
  let fields := s.fields.map fun f => s!"{f.label} = _"
  "struct { " ++ ", ".intercalate fields ++ " }"

/-! ## Building Helpers -/

/-- Create a simple non-dependent signature from list of (name, type) -/
def mkSimpleSignature (fields : List (String × Expr)) : SignatureType :=
  { telescope := fields.map fun (name, ty) => { label := .user name, ty := ty } }

/-- Create a struct from list of (name, value) -/
def mkSimpleStruct (fields : List (String × Expr)) : Struct :=
  { fields := fields.map fun (name, val) => { label := .user name, value := val } }

/-- Derive struct type from struct value (for type inference) -/
def inferStructType (s : Struct) (inferType : Expr → Expr) : SignatureType :=
  { telescope := s.fields.map fun f => { label := f.label, ty := inferType f.value } }

end Lego.Cubical.Signature
