/-
  Lego.Cubical.Domain: Semantic Domain Types for NbE

  This module defines the semantic domain used for Normalization by Evaluation (NbE).
  The domain consists of:
  - D.Con: Semantic values (evaluated terms)
  - D.Tp: Semantic types
  - D.Cut: Neutral terms with their types
  - D.Env: Evaluation environments
  - D.Clo: Closures for delayed evaluation

  Mathematical Structure:
  - The domain forms a partial equivalence relation (PER) model
  - Evaluation maps syntax to semantics: ⟦_⟧ : Expr → D.Con
  - Quotation maps semantics back to syntax: ↓ : D.Con → Expr (at type)
  - NbE: normalize(e) = ↓⟦e⟧

  Based on cooltt's Domain.ml and redtt's Val.ml
-/

import Lego.Cubical.Core

namespace Lego.Cubical.Domain

open Lego.Core

/-! ## Level for Universe Hierarchy

    Semantic levels for universe polymorphism.
-/

/-- Semantic universe level -/
inductive DLevel where
  | const : Nat → DLevel           -- Concrete level
  | lvar  : Nat → DLevel           -- Level variable
  | max   : DLevel → DLevel → DLevel  -- Maximum
  | suc   : DLevel → DLevel        -- Successor
  deriving Repr, BEq, Inhabited

namespace DLevel

def zero : DLevel := .const 0
def one : DLevel := .const 1

def ofLevel : Level → DLevel
  | .zero => .const 0
  | .suc l => .suc (ofLevel l)
  | .max l1 l2 => .max (ofLevel l1) (ofLevel l2)
  | .lvar n => .lvar n

end DLevel

/-! ## Dimension Values

    Semantic dimensions (interval endpoints and variables).
-/

/-- Semantic dimension value -/
inductive Dim where
  | dim0 : Dim                     -- 0 endpoint
  | dim1 : Dim                     -- 1 endpoint
  | dvar : Nat → Dim               -- Dimension variable
  deriving Repr, BEq, Inhabited

namespace Dim

def ofExpr : Expr → Option Dim
  | .dim0 => some .dim0
  | .dim1 => some .dim1
  | .dimVar n => some (.dvar n)
  | _ => none

def toExpr : Dim → Expr
  | .dim0 => .dim0
  | .dim1 => .dim1
  | .dvar n => .dimVar n

def eq (d1 d2 : Dim) : Bool := d1 == d2

end Dim

/-! ## Cofibration Values

    Semantic cofibrations (conditions on dimensions).
-/

/-- Semantic cofibration -/
inductive Cof where
  | top : Cof                      -- ⊤ (always true)
  | bot : Cof                      -- ⊥ (always false)
  | eq  : Dim → Dim → Cof          -- r = s
  | join : Cof → Cof → Cof         -- φ ∨ ψ
  | meet : Cof → Cof → Cof         -- φ ∧ ψ
  deriving Repr, BEq, Inhabited

namespace Cof

/-- Check if cofibration is definitely true -/
partial def isTrue : Cof → Bool
  | .top => true
  | .eq d1 d2 => Dim.eq d1 d2
  | .join φ ψ => isTrue φ || isTrue ψ
  | _ => false

/-- Check if cofibration is definitely false -/
partial def isFalse : Cof → Bool
  | .bot => true
  | .eq .dim0 .dim1 => true
  | .eq .dim1 .dim0 => true
  | .meet φ ψ => isFalse φ || isFalse ψ
  | _ => false

/-- Boundary cofibration: r = 0 ∨ r = 1 -/
def boundary (r : Dim) : Cof :=
  .join (.eq r .dim0) (.eq r .dim1)

end Cof

/-! ## Closures

    Closures represent delayed computations - a term paired with its environment.
-/

-- Forward declarations for mutual recursion
mutual
/-- Semantic value (evaluated term) -/
inductive Con where
  | lam    : Clo → Con                           -- λ-abstraction
  | pair   : Con → Con → Con                     -- Pair (a, b)
  | zero   : Con                                 -- Nat zero
  | suc    : Con → Con                           -- Nat successor
  | base   : Con                                 -- Circle base
  | loop   : Dim → Con                           -- Circle loop at dimension
  | refl   : Con → Con                           -- Reflexivity path
  | plam   : DimClo → Con                        -- Path lambda
  | vin    : Dim → Con → Con → Con               -- V-type intro
  | glueEl : Con → Con → Con                     -- Glue element
  | extLam : Nat → Clo → Con                     -- Extension lambda
  | subIn  : Con → Con                           -- Sub type intro
  | struct : List (String × Con) → Con           -- Struct value
  | box    : Dim → Dim → Con → List (Cof × Con) → Con  -- FHCom box
  | neu    : Cut → Con                           -- Neutral (blocked)
  deriving Repr, BEq, Inhabited

/-- Semantic type -/
inductive Tp where
  | univ   : DLevel → Tp                         -- Universe
  | pi     : Tp → TpClo → Tp                     -- Π type
  | sigma  : Tp → TpClo → Tp                     -- Σ type
  | path   : TpDimClo → Con → Con → Tp           -- Path type
  | nat    : Tp                                  -- Natural numbers
  | circle : Tp                                  -- Circle S¹
  | vtype  : Dim → Tp → Tp → Con → Tp            -- V-type
  | glue   : Tp → Cof → Tp → Con → Tp            -- Glue type
  | ext    : Nat → TpDimClo → CofDimClo → Clo → Tp  -- Extension type
  | sub    : Tp → Cof → Con → Tp                 -- Sub type
  | sig    : List (String × Tp) → Tp             -- Signature type
  | data   : String → List Con → Tp              -- Datatype
  | fhcom  : Dim → Dim → Tp → List (Cof × TpDimClo) → Tp  -- FHCom type
  | neu    : Cut → Tp                            -- Neutral type
  deriving Repr, BEq, Inhabited

/-- Neutral term with its type -/
inductive Cut where
  | var    : Nat → Tp → Cut                      -- Variable with type
  | app    : Cut → Con → Cut                     -- Application to value
  | fst    : Cut → Cut                           -- First projection
  | snd    : Cut → Cut                           -- Second projection
  | papp   : Cut → Dim → Cut                     -- Path application
  | natElim : TpClo → Con → Con → Cut → Cut      -- Nat eliminator
  | circleElim : TpClo → Con → Con → Cut → Cut   -- Circle eliminator
  | coe    : Dim → Dim → TpDimClo → Cut → Cut    -- Coercion
  | hcom   : Dim → Dim → Tp → Cof → List (Cof × Clo) → Cut → Cut  -- HCom
  | vproj  : Dim → Tp → Tp → Con → Cut → Cut     -- V projection
  | unglue : Cut → Cut                           -- Unglue
  | extApp : Cut → List Dim → Cut                -- Extension application
  | subOut : Cut → Cut                           -- Sub elimination
  | proj   : Cut → String → Cut                  -- Signature projection
  | elim   : String → List Con → TpClo → List (String × Clo) → Cut → Cut  -- Datatype elim
  deriving Repr, BEq, Inhabited

/-- Term closure: (env, term) -/
inductive Clo where
  | clo : Env → Expr → Clo
  deriving Repr, BEq

/-- Type closure: (env, type term) -/
inductive TpClo where
  | clo : Env → Expr → TpClo
  deriving Repr, BEq

/-- Dimension closure: (env, term with dimension binding) -/
inductive DimClo where
  | clo : Env → Expr → DimClo
  deriving Repr, BEq

/-- Type dimension closure -/
inductive TpDimClo where
  | clo : Env → Expr → TpDimClo
  deriving Repr, BEq

/-- Cofibration dimension closure -/
inductive CofDimClo where
  | clo : Env → Expr → CofDimClo
  deriving Repr, BEq

/-- Evaluation environment -/
inductive Env where
  | empty : Env
  | extend : Env → Con → Env
  | extendDim : Env → Dim → Env
  deriving Repr, BEq
end

/-! ## Environment Operations -/

namespace Env

/-- Lookup value at de Bruijn index -/
def lookup (env : Env) (idx : Nat) : Option Con :=
  match env, idx with
  | .empty, _ => none
  | .extend _ v, 0 => some v
  | .extend e _, n + 1 => lookup e n
  | .extendDim e _, n => lookup e n

/-- Lookup dimension at de Bruijn index -/
def lookupDim (env : Env) (idx : Nat) : Option Dim :=
  match env, idx with
  | .empty, _ => none
  | .extendDim _ d, 0 => some d
  | .extendDim e _, n + 1 => lookupDim e n
  | .extend e _, n => lookupDim e n

/-- Length of environment -/
def length : Env → Nat
  | .empty => 0
  | .extend e _ => 1 + length e
  | .extendDim e _ => 1 + length e

end Env

/-! ## Closure Application

    Applying closures to values.
-/

namespace Clo

/-- Get the body of a closure -/
def body : Clo → Expr
  | .clo _ e => e

/-- Get the environment of a closure -/
def env : Clo → Env
  | .clo e _ => e

end Clo

namespace TpClo

def body : TpClo → Expr
  | .clo _ e => e

def env : TpClo → Env
  | .clo e _ => e

end TpClo

namespace DimClo

def body : DimClo → Expr
  | .clo _ e => e

def env : DimClo → Env
  | .clo e _ => e

end DimClo

/-! ## Smart Constructors for Semantic Values -/

namespace Con

/-- Create neutral from cut -/
def ofCut (cut : Cut) : Con := .neu cut

/-- Check if value is neutral -/
def isNeutral : Con → Bool
  | .neu _ => true
  | _ => false

/-- Extract cut from neutral, if any -/
def getCut : Con → Option Cut
  | .neu c => some c
  | _ => none

end Con

namespace Tp

/-- Create neutral type from cut -/
def ofCut (cut : Cut) : Tp := .neu cut

/-- Check if type is neutral -/
def isNeutral : Tp → Bool
  | .neu _ => true
  | _ => false

/-- Arrow type (non-dependent Pi) -/
def arrow (dom cod : Tp) : Tp :=
  .pi dom (.clo .empty (Expr.shift (toExpr cod)))
where
  toExpr : Tp → Expr
    | .univ l => .univ (levelToCore l)
    | .nat => .nat
    | .circle => .circle
    | _ => .lit "?"  -- Placeholder
  levelToCore : DLevel → Level
    | .const n => Level.ofNat n
    | _ => .zero

end Tp

/-! ## Kan Telescopes (Semantic)

    Telescopes with Kan structure for signatures.
-/

/-- Semantic Kan telescope entry -/
structure KanTelEntry where
  name : String
  tpClo : TpDimClo  -- Type varies over dimension
  deriving Repr, BEq

/-- Semantic Kan telescope -/
abbrev KanTel := List KanTelEntry

/-! ## System/Tube Representation

    For hcom and partial elements.
-/

/-- A system is a list of (cofibration, value) pairs -/
abbrev System := List (Cof × Con)

/-- A tube system for types -/
abbrev TubeSystem := List (Cof × TpDimClo)

/-! ## Splice Frame

    For working under binders during evaluation.
-/

/-- Splice frame: information needed to reconstruct terms -/
inductive Frame where
  | app : Con → Frame              -- Applied to value
  | fst : Frame                    -- First projection
  | snd : Frame                    -- Second projection
  | papp : Dim → Frame             -- Path application
  deriving Repr, BEq, Inhabited

/-- Splice: stack of frames for reconstruction -/
abbrev Splice := List Frame

/-! ## Pretty Printing -/

def dimToString : Dim → String
  | .dim0 => "0"
  | .dim1 => "1"
  | .dvar n => s!"i{n}"

mutual
partial def conToString : Con → String
  | .lam _ => "λ..."
  | .pair a b => s!"({conToString a}, {conToString b})"
  | .zero => "zero"
  | .suc n => s!"suc({conToString n})"
  | .base => "base"
  | .loop d => s!"loop({dimToString d})"
  | .refl a => s!"refl({conToString a})"
  | .plam _ => "λi...."
  | .vin d a b => s!"vin({dimToString d}, {conToString a}, {conToString b})"
  | .glueEl t a => s!"glue({conToString t}, {conToString a})"
  | .extLam n _ => s!"extLam({n}, ...)"
  | .subIn a => s!"subIn({conToString a})"
  | .struct _ => "struct{...}"
  | .box _ _ _ _ => "box(...)"
  | .neu cut => s!"[{cutToString cut}]"

partial def cutToString : Cut → String
  | .var n _ => s!"x{n}"
  | .app f a => s!"{cutToString f}({conToString a})"
  | .fst p => s!"fst({cutToString p})"
  | .snd p => s!"snd({cutToString p})"
  | .papp p d => s!"{cutToString p}@{dimToString d}"
  | _ => "..."

partial def tpToString : Tp → String
  | .univ _ => s!"Type"
  | .pi dom _ => s!"Π({tpToString dom})...."
  | .sigma dom _ => s!"Σ({tpToString dom})...."
  | .path _ a b => s!"Path _ {conToString a} {conToString b}"
  | .nat => "Nat"
  | .circle => "S¹"
  | .vtype d a b _ => s!"V({dimToString d}, {tpToString a}, {tpToString b}, ...)"
  | .glue a _ t _ => s!"Glue({tpToString a}, _, {tpToString t}, ...)"
  | .ext n _ _ _ => s!"Ext({n}, ...)"
  | .sub a _ _ => s!"Sub({tpToString a}, ...)"
  | .sig _ => "sig{...}"
  | .data dlbl _ => s!"data.{dlbl}"
  | .fhcom _ _ _ _ => "fhcom(...)"
  | .neu cut => s!"[{cutToString cut}]"
end

end Lego.Cubical.Domain
