/-
  Cubical.lean
  Generated Lean definitions for Cubical Type Theory

  Pipeline: CubicalTT.lego → cubical2rosetta → rosetta2lean → Cubical.lean
-/

namespace Cubical

/-! ## Dimensions: De Morgan algebra -/

inductive Dim where
  | i0
  | i1
  | var : String → Dim
  | meet : Dim → Dim → Dim
  | join : Dim → Dim → Dim
  | neg : Dim → Dim
  deriving Repr, BEq, Inhabited

/-! ## Cofibrations: Face lattice -/

inductive Cof where
  | top
  | bot
  | eq : Dim → Dim → Cof
  | and : Cof → Cof → Cof
  | or : Cof → Cof → Cof
  deriving Repr, BEq, Inhabited

/-! ## Types and Terms -/

mutual
  inductive Ty where
    | univ : Nat → Ty
    | pi : String → Ty → Ty → Ty
    | sigma : String → Ty → Ty → Ty
    | path : Ty → Term → Term → Ty
    | pathP : String → Ty → Term → Term → Ty
    | sub : Ty → Cof → Term → Ty
    | glue : Ty → Cof → Ty → Term → Ty
    | vtype : Dim → Ty → Ty → Term → Ty
    | nat
    | circle
    deriving Repr

  inductive Term where
    | var : String → Term
    | lam : String → Term → Term
    | app : Term → Term → Term
    | pair : Term → Term → Term
    | fst : Term → Term
    | snd : Term → Term
    | plam : String → Term → Term
    | papp : Term → Dim → Term
    | coe : Dim → Dim → String → Ty → Term → Term
    | hcom : Ty → Dim → Dim → Cof → Term → Term → Term
    | com : String → Ty → Dim → Dim → Cof → Term → Term → Term
    | subIn : Term → Term
    | subOut : Term → Term
    | glueIn : Term → Term → Term
    | unglue : Cof → Term → Term → Term
    | vin : Dim → Term → Term → Term
    | vproj : Dim → Term → Ty → Ty → Term → Term
    | zero
    | suc : Term → Term
    | base
    | loop : Dim → Term
    deriving Repr
end

/-! ## System: Partial elements -/

structure Branch where
  cof : Cof
  term : Term
  deriving Repr

abbrev System := List Branch

/-! ## De Morgan laws -/

def Dim.normalize : Dim → Dim
  | .neg .i0 => .i1
  | .neg .i1 => .i0
  | .neg (.neg d) => d.normalize
  | .meet .i0 _ => .i0
  | .meet _ .i0 => .i0
  | .meet .i1 d => d.normalize
  | .meet d .i1 => d.normalize
  | .join .i0 d => d.normalize
  | .join d .i0 => d.normalize
  | .join .i1 _ => .i1
  | .join _ .i1 => .i1
  | d => d

def Cof.normalize : Cof → Cof
  | .and .bot _ => .bot
  | .and _ .bot => .bot
  | .and .top φ => φ.normalize
  | .and φ .top => φ.normalize
  | .or .top _ => .top
  | .or _ .top => .top
  | .or .bot φ => φ.normalize
  | .or φ .bot => φ.normalize
  | .eq d1 d2 =>
    let d1' := d1.normalize
    let d2' := d2.normalize
    if d1' == d2' then .top else .eq d1' d2'
  | φ => φ

end Cubical
