/-
  Lego.Core: De Bruijn indexed Core IR with substitution engine

  The foundation for computational type theory:
  - De Bruijn indices for capture-avoiding substitution
  - Shifting for correct variable handling under binders
  - β-reduction rules for computation

  Mathematical structure:
  - Presheaf model: terms indexed by context length
  - Substitution: functorial action on terms
  - Weakening: natural transformation between context extensions
-/

import Lego.Algebra

namespace Lego.Core

/-! ## Universe Levels

    Universe polymorphism via level expressions:
    - Concrete levels: 0, 1, 2, ...
    - Level variables: α, β, ...  (for polymorphism)
    - Level successor: suc ℓ
    - Level maximum: max ℓ₁ ℓ₂

    Key equations:
    - max ℓ ℓ = ℓ
    - max ℓ (suc ℓ) = suc ℓ
    - max (suc ℓ₁) (suc ℓ₂) = suc (max ℓ₁ ℓ₂)
-/

/-- Universe level expressions -/
inductive Level where
  | zero  : Level                    -- Level 0
  | suc   : Level → Level            -- ℓ + 1
  | max   : Level → Level → Level    -- max ℓ₁ ℓ₂
  | lvar  : Nat → Level              -- Level variable (de Bruijn)
  deriving Repr, BEq, Inhabited

namespace Level

/-- Convert Nat to Level -/
def ofNat : Nat → Level
  | 0 => zero
  | n + 1 => suc (ofNat n)

/-- Try to convert Level to Nat (fails if contains variables) -/
def toNat? : Level → Option Nat
  | zero => some 0
  | suc l => (toNat? l).map (· + 1)
  | max l1 l2 => do
    let n1 ← toNat? l1
    let n2 ← toNat? l2
    some (Nat.max n1 n2)
  | lvar _ => none

/-- Normalize level expression -/
partial def normalize : Level → Level
  | zero => zero
  | suc l => suc (normalize l)
  | max l1 l2 =>
    let l1' := normalize l1
    let l2' := normalize l2
    match l1', l2' with
    | zero, l => l
    | l, zero => l
    | l1, l2 => if l1 == l2 then l1 else max l1 l2
  | lvar n => lvar n

/-- Check if two levels are equal (after normalization) -/
def levelEq (l1 l2 : Level) : Bool :=
  normalize l1 == normalize l2

/-- Check if l1 ≤ l2 (for cumulativity) -/
partial def leq (l1 l2 : Level) : Bool :=
  let l1' := normalize l1
  let l2' := normalize l2
  match l1', l2' with
  | zero, _ => true
  | suc l1, suc l2 => leq l1 l2
  | l, max l2a l2b => leq l l2a || leq l l2b
  | max l1a l1b, l => leq l1a l && leq l1b l
  | lvar n, lvar m => n == m
  | _, _ => l1' == l2'

/-- Pretty print level -/
def toString : Level → String
  | zero => "0"
  | suc l =>
    match toNat? (suc l) with
    | some n => s!"{n}"
    | none => s!"(suc {toString l})"
  | max l1 l2 => s!"(max {toString l1} {toString l2})"
  | lvar n => s!"ℓ{n}"

instance : ToString Level := ⟨toString⟩

/-- Allow numeric literals for concrete levels -/
instance : OfNat Level n where
  ofNat := ofNat n

end Level

/-! ## De Bruijn Indexed Terms -/

/-- Core term: de Bruijn indexed for substitution.
    Surface terms use names; Core terms use indices.

    Index 0 = most recently bound variable
    Index n = variable bound n binders ago
-/
inductive Expr where
  | ix    : Nat → Expr                     -- de Bruijn index
  | lit   : String → Expr                  -- literal
  | lam   : Expr → Expr                    -- λ. body (binds index 0)
  | app   : Expr → Expr → Expr             -- application
  | pi    : Expr → Expr → Expr             -- Π A. B (binds index 0 in B)
  | sigma : Expr → Expr → Expr             -- Σ A. B (binds index 0 in B)
  | pair  : Expr → Expr → Expr             -- (a, b)
  | fst   : Expr → Expr                    -- π₁
  | snd   : Expr → Expr                    -- π₂
  | letE  : Expr → Expr → Expr → Expr      -- let x : A = v in body
  | univ  : Level → Expr                   -- Type^ℓ (universe polymorphism)
  -- Interval and dimension operations
  | dim0  : Expr                           -- 0 : 𝕀 (left endpoint)
  | dim1  : Expr                           -- 1 : 𝕀 (right endpoint)
  | dimVar : Nat → Expr                    -- dimension variable (de Bruijn)
  -- Cofibrations
  | cof_top : Expr                         -- ⊤ (always true)
  | cof_bot : Expr                         -- ⊥ (always false)
  | cof_eq  : Expr → Expr → Expr           -- r = s (dimension equality)
  | cof_and : Expr → Expr → Expr           -- φ ∧ ψ (conjunction)
  | cof_or  : Expr → Expr → Expr           -- φ ∨ ψ (disjunction)
  -- Cubical operations
  | path  : Expr → Expr → Expr → Expr      -- path A a b
  | plam  : Expr → Expr                    -- path lambda: λi. body (binds dim var)
  | papp  : Expr → Expr → Expr             -- path application: p @ r
  | refl  : Expr → Expr                    -- refl a : path A a a
  | coe   : Expr → Expr → Expr → Expr → Expr  -- coe r r' (λi.A) a
  | hcom  : Expr → Expr → Expr → Expr → Expr → Expr  -- hcom r r' A φ cap (tube implicit when φ true)
  | hcomTube : Expr → Expr → Expr → List (Expr × Expr) → Expr → Expr  -- hcom r r' A [(φ,tube)...] cap with explicit tubes
  -- Heterogeneous composition: com r r' (λi.A[i]) cap sys
  -- This is the key operation for transport in dependent types.
  -- com = coe + hcom: coerce the cap and system, then compose homogeneously.
  | com   : Expr → Expr → Expr → List (Expr × Expr) → Expr → Expr  -- com r r' (λi.A) [(φ,tube)...] cap
  -- Generalized homogeneous composition (ghcom): expands hcom when type doesn't have strict Kan structure
  | ghcom : Expr → Expr → Expr → List (Expr × Expr) → Expr → Expr  -- ghcom r r' A [(φ,tube)...] cap
  -- Generalized heterogeneous composition (gcom): ghcom with varying type
  | gcom  : Expr → Expr → Expr → List (Expr × Expr) → Expr → Expr  -- gcom r r' (λi.A) [(φ,tube)...] cap
  -- FHCom: fibrant homogeneous composition (types as Kan-filled values)
  -- fhcom r r' cap sys : Type (when used at type level)
  | fhcom : Expr → Expr → Expr → List (Expr × Expr) → Expr  -- fhcom r r' cap [(φ,tube)...]
  -- Box: introduction for FHCom types
  | boxEl : Expr → Expr → Expr → List (Expr × Expr) → Expr  -- box r r' cap [(φ,side)...]
  -- Cap: elimination for FHCom types (extract the cap from a box)
  | capEl : Expr → Expr → Expr → List (Expr × Expr) → Expr → Expr  -- cap r r' ty [(φ,tube)...] box
  -- Systems (partial elements): list of (cof, term) branches
  | sys   : List (Expr × Expr) → Expr      -- [(φ₁, t₁), (φ₂, t₂), ...]
  -- V-types (Glue types for univalence)
  -- V r A B equiv : when r=0 gives A, when r=1 gives B
  | vtype : Expr → Expr → Expr → Expr → Expr  -- V r A B equiv
  | vin   : Expr → Expr → Expr → Expr      -- vin r a b : V r A B e (when r=0 gives a, r=1 gives b)
  | vproj : Expr → Expr → Expr → Expr → Expr → Expr  -- vproj r A B equiv v : projects out of V-type
  -- Natural numbers (for HIT treatment)
  | nat   : Expr                           -- Nat type
  | zero  : Expr                           -- zero
  | suc   : Expr → Expr                    -- suc n
  | natElim : Expr → Expr → Expr → Expr → Expr  -- natElim P z s n
  -- Circle (HIT)
  | circle : Expr                          -- S¹ type
  | base   : Expr                          -- base : S¹
  | loop   : Expr → Expr                   -- loop r : S¹ (at dimension r)
  | circleElim : Expr → Expr → Expr → Expr → Expr  -- circleElim P b ℓ x
  -- Extension types (partial elements with boundary constraints)
  -- ext n fam cof bdry : Type
  -- Represents types of the form (i₁ ... iₙ : 𝕀) → A with partial boundary
  -- - n: number of dimension variables bound
  -- - fam: the family (λ i₁...iₙ. A)
  -- - cof: the cofibration under which boundary is specified (λ i₁...iₙ. φ)
  -- - bdry: the boundary term (λ i₁...iₙ. partial element)
  | ext     : Nat → Expr → Expr → Expr → Expr  -- ext n fam cof bdry
  -- extLam: introduction for extension types
  -- extLam n body : ext n fam cof bdry
  -- Binds n dimension variables in body
  | extLam  : Nat → Expr → Expr                -- extLam n body
  -- extApp: elimination for extension types
  -- extApp e [r₁, ..., rₙ] : fam[r₁/i₁, ..., rₙ/iₙ]
  -- Applies e to n dimension arguments
  | extApp  : Expr → List Expr → Expr          -- extApp e [r₁, ..., rₙ]
  -- Sub types (cubical subtypes / restriction types)
  -- sub A φ t : Type where A : Type, φ : Cof, t : [φ] → A
  -- Elements of sub A φ t are elements of A that equal t when φ is true
  | sub     : Expr → Expr → Expr → Expr        -- sub A φ (λ _. t)
  -- subIn: introduction for Sub types
  -- subIn e : sub A φ t when e : A and e = t[prf/x] when φ
  | subIn   : Expr → Expr                      -- subIn e
  -- subOut: elimination for Sub types
  -- subOut e : A when e : sub A φ t
  | subOut  : Expr → Expr                      -- subOut e
  deriving Repr, BEq, Inhabited

namespace Expr

/-! ## Shifting (Weakening)

    shift k e = e with all free variables >= k incremented by 1

    Essential for substitution under binders:
    - When we go under a binder, the context extends
    - Free variables must be adjusted to account for the new binding
-/

/-- Shift free variables at or above cutoff by delta -/
partial def shiftAbove (cutoff : Nat) (delta : Int) : Expr → Expr
  | ix n =>
    if n >= cutoff then
      -- Free variable: shift it
      let n' := (n : Int) + delta
      if n' >= 0 then ix n'.toNat else ix 0  -- Guard against negative
    else
      -- Bound variable: unchanged
      ix n
  | lit s => lit s
  | lam body => lam (shiftAbove (cutoff + 1) delta body)
  | app f x => app (shiftAbove cutoff delta f) (shiftAbove cutoff delta x)
  | pi dom cod => pi (shiftAbove cutoff delta dom) (shiftAbove (cutoff + 1) delta cod)
  | sigma dom cod => sigma (shiftAbove cutoff delta dom) (shiftAbove (cutoff + 1) delta cod)
  | pair a b => pair (shiftAbove cutoff delta a) (shiftAbove cutoff delta b)
  | fst e => fst (shiftAbove cutoff delta e)
  | snd e => snd (shiftAbove cutoff delta e)
  | letE ty val body =>
    letE (shiftAbove cutoff delta ty)
         (shiftAbove cutoff delta val)
         (shiftAbove (cutoff + 1) delta body)
  | univ n => univ n
  -- Dimension terms
  | dim0 => dim0
  | dim1 => dim1
  | dimVar n =>
    if n >= cutoff then
      let n' := (n : Int) + delta
      if n' >= 0 then dimVar n'.toNat else dimVar 0
    else dimVar n
  -- Cofibrations
  | cof_top => cof_top
  | cof_bot => cof_bot
  | cof_eq r s => cof_eq (shiftAbove cutoff delta r) (shiftAbove cutoff delta s)
  | cof_and phi psi => cof_and (shiftAbove cutoff delta phi) (shiftAbove cutoff delta psi)
  | cof_or phi psi => cof_or (shiftAbove cutoff delta phi) (shiftAbove cutoff delta psi)
  -- Path operations
  | path ty a b => path (shiftAbove cutoff delta ty)
                       (shiftAbove cutoff delta a)
                       (shiftAbove cutoff delta b)
  | plam body => plam (shiftAbove (cutoff + 1) delta body)  -- binds dim var
  | papp p r => papp (shiftAbove cutoff delta p) (shiftAbove cutoff delta r)
  | refl a => refl (shiftAbove cutoff delta a)
  | coe r r' ty a => coe (shiftAbove cutoff delta r)
                         (shiftAbove cutoff delta r')
                         (shiftAbove (cutoff + 1) delta ty)  -- ty binds dimension
                         (shiftAbove cutoff delta a)
  | hcom r r' ty phi cap => hcom (shiftAbove cutoff delta r)
                                 (shiftAbove cutoff delta r')
                                 (shiftAbove cutoff delta ty)
                                 (shiftAbove cutoff delta phi)
                                 (shiftAbove cutoff delta cap)
  | hcomTube r r' ty tubes cap =>
    hcomTube (shiftAbove cutoff delta r)
             (shiftAbove cutoff delta r')
             (shiftAbove cutoff delta ty)
             (tubes.map fun (φ, tube) => (shiftAbove cutoff delta φ, shiftAbove (cutoff + 1) delta tube))  -- tube binds dim
             (shiftAbove cutoff delta cap)
  | com r r' ty tubes cap =>
    com (shiftAbove cutoff delta r)
        (shiftAbove cutoff delta r')
        (shiftAbove (cutoff + 1) delta ty)  -- ty binds dimension
        (tubes.map fun (φ, tube) => (shiftAbove cutoff delta φ, shiftAbove (cutoff + 1) delta tube))  -- tube binds dim
        (shiftAbove cutoff delta cap)
  -- ghcom: generalized hcom
  | ghcom r r' ty tubes cap =>
    ghcom (shiftAbove cutoff delta r)
          (shiftAbove cutoff delta r')
          (shiftAbove cutoff delta ty)
          (tubes.map fun (φ, tube) => (shiftAbove cutoff delta φ, shiftAbove (cutoff + 1) delta tube))
          (shiftAbove cutoff delta cap)
  -- gcom: generalized com (heterogeneous)
  | gcom r r' ty tubes cap =>
    gcom (shiftAbove cutoff delta r)
         (shiftAbove cutoff delta r')
         (shiftAbove (cutoff + 1) delta ty)  -- ty binds dimension
         (tubes.map fun (φ, tube) => (shiftAbove cutoff delta φ, shiftAbove (cutoff + 1) delta tube))
         (shiftAbove cutoff delta cap)
  -- fhcom: fibrant hcom (for types)
  | fhcom r r' cap tubes =>
    fhcom (shiftAbove cutoff delta r)
          (shiftAbove cutoff delta r')
          (shiftAbove cutoff delta cap)
          (tubes.map fun (φ, tube) => (shiftAbove cutoff delta φ, shiftAbove (cutoff + 1) delta tube))
  -- box: introduction for fhcom types
  | boxEl r r' cap sysList =>
    boxEl (shiftAbove cutoff delta r)
        (shiftAbove cutoff delta r')
        (shiftAbove cutoff delta cap)
        (sysList.map fun (φ, side) => (shiftAbove cutoff delta φ, shiftAbove cutoff delta side))
  -- cap: elimination for fhcom types
  | capEl r r' ty tubes e =>
    capEl (shiftAbove cutoff delta r)
        (shiftAbove cutoff delta r')
        (shiftAbove cutoff delta ty)
        (tubes.map fun (φ, tube) => (shiftAbove cutoff delta φ, shiftAbove (cutoff + 1) delta tube))
        (shiftAbove cutoff delta e)
  -- Systems
  | sys branches => sys (branches.map fun (cof, tm) =>
      (shiftAbove cutoff delta cof, shiftAbove cutoff delta tm))
  -- V-types
  | vtype r a b equiv => vtype (shiftAbove cutoff delta r)
                               (shiftAbove cutoff delta a)
                               (shiftAbove cutoff delta b)
                               (shiftAbove cutoff delta equiv)
  | vin r el0 el1 => vin (shiftAbove cutoff delta r)
                         (shiftAbove cutoff delta el0)
                         (shiftAbove cutoff delta el1)
  | vproj r a b equiv v => vproj (shiftAbove cutoff delta r)
                                 (shiftAbove cutoff delta a)
                                 (shiftAbove cutoff delta b)
                                 (shiftAbove cutoff delta equiv)
                                 (shiftAbove cutoff delta v)
  -- Nat
  | nat => nat
  | zero => zero
  | suc n => suc (shiftAbove cutoff delta n)
  | natElim p z s n => natElim (shiftAbove cutoff delta p)
                               (shiftAbove cutoff delta z)
                               (shiftAbove (cutoff + 2) delta s)  -- s binds n and ih
                               (shiftAbove cutoff delta n)
  -- Circle
  | circle => circle
  | base => base
  | loop r => loop (shiftAbove cutoff delta r)
  | circleElim p b l x => circleElim (shiftAbove cutoff delta p)
                                     (shiftAbove cutoff delta b)
                                     (shiftAbove (cutoff + 1) delta l)  -- l binds dim
                                     (shiftAbove cutoff delta x)
  -- Extension types
  | ext n fam cof bdry =>
    ext n (shiftAbove (cutoff + n) delta fam)    -- fam binds n dims
          (shiftAbove (cutoff + n) delta cof)    -- cof binds n dims
          (shiftAbove (cutoff + n) delta bdry)   -- bdry binds n dims
  | extLam n body => extLam n (shiftAbove (cutoff + n) delta body)  -- binds n dims
  | extApp e dims => extApp (shiftAbove cutoff delta e) (dims.map (shiftAbove cutoff delta))
  -- Sub types
  | sub ty cof bdry => sub (shiftAbove cutoff delta ty)
                           (shiftAbove cutoff delta cof)
                           (shiftAbove (cutoff + 1) delta bdry)  -- bdry binds 1 (prf of cof)
  | subIn e => subIn (shiftAbove cutoff delta e)
  | subOut e => subOut (shiftAbove cutoff delta e)

/-- Shift all free variables by 1 (standard weakening) -/
def shift (e : Expr) : Expr := shiftAbove 0 1 e

/-- Shift all free variables by n -/
def shiftN (n : Nat) (e : Expr) : Expr := shiftAbove 0 n e

/-! ## Substitution

    subst e idx val = e[idx := val]

    The core operation: replace index `idx` with `val`.
    - Variables < idx: unchanged (bound in inner scope)
    - Variable = idx: replaced with val
    - Variables > idx: decremented (outer variables shift down)
-/

/-- Substitute value for index in expression -/
partial def subst (idx : Nat) (val : Expr) : Expr → Expr
  | ix n =>
    if n < idx then
      ix n          -- Inner bound variable: unchanged
    else if n == idx then
      val           -- This is the variable: substitute
    else
      ix (n - 1)    -- Outer variable: shift down
  | lit s => lit s
  | lam body =>
    -- Under binder: shift val, increment target index
    lam (subst (idx + 1) (shift val) body)
  | app f x => app (subst idx val f) (subst idx val x)
  | pi dom cod =>
    pi (subst idx val dom) (subst (idx + 1) (shift val) cod)
  | sigma dom cod =>
    sigma (subst idx val dom) (subst (idx + 1) (shift val) cod)
  | pair a b => pair (subst idx val a) (subst idx val b)
  | fst e => fst (subst idx val e)
  | snd e => snd (subst idx val e)
  | letE ty v body =>
    letE (subst idx val ty)
         (subst idx val v)
         (subst (idx + 1) (shift val) body)
  | univ n => univ n
  -- Dimension terms
  | dim0 => dim0
  | dim1 => dim1
  | dimVar n =>
    if n < idx then dimVar n
    else if n == idx then val  -- substitute dimension variable
    else dimVar (n - 1)
  -- Cofibrations
  | cof_top => cof_top
  | cof_bot => cof_bot
  | cof_eq r s => cof_eq (subst idx val r) (subst idx val s)
  | cof_and phi psi => cof_and (subst idx val phi) (subst idx val psi)
  | cof_or phi psi => cof_or (subst idx val phi) (subst idx val psi)
  -- Path operations
  | path ty a b => path (subst idx val ty)
                       (subst idx val a)
                       (subst idx val b)
  | plam body => plam (subst (idx + 1) (shift val) body)
  | papp p r => papp (subst idx val p) (subst idx val r)
  | refl a => refl (subst idx val a)
  | coe r r' ty a =>
    coe (subst idx val r)
        (subst idx val r')
        (subst (idx + 1) (shift val) ty)  -- ty binds dimension
        (subst idx val a)
  | hcom r r' ty phi cap =>
    hcom (subst idx val r)
         (subst idx val r')
         (subst idx val ty)
         (subst idx val phi)
         (subst idx val cap)
  | hcomTube r r' ty tubes cap =>
    hcomTube (subst idx val r)
             (subst idx val r')
             (subst idx val ty)
             (tubes.map fun (φ, tube) => (subst idx val φ, subst (idx + 1) (shift val) tube))  -- tube binds dim
             (subst idx val cap)
  | com r r' ty tubes cap =>
    com (subst idx val r)
        (subst idx val r')
        (subst (idx + 1) (shift val) ty)  -- ty binds dimension
        (tubes.map fun (φ, tube) => (subst idx val φ, subst (idx + 1) (shift val) tube))  -- tube binds dim
        (subst idx val cap)
  -- ghcom: generalized hcom
  | ghcom r r' ty tubes cap =>
    ghcom (subst idx val r)
          (subst idx val r')
          (subst idx val ty)
          (tubes.map fun (φ, tube) => (subst idx val φ, subst (idx + 1) (shift val) tube))
          (subst idx val cap)
  -- gcom: generalized com
  | gcom r r' ty tubes cap =>
    gcom (subst idx val r)
         (subst idx val r')
         (subst (idx + 1) (shift val) ty)
         (tubes.map fun (φ, tube) => (subst idx val φ, subst (idx + 1) (shift val) tube))
         (subst idx val cap)
  -- fhcom
  | fhcom r r' cap tubes =>
    fhcom (subst idx val r)
          (subst idx val r')
          (subst idx val cap)
          (tubes.map fun (φ, tube) => (subst idx val φ, subst (idx + 1) (shift val) tube))
  -- box
  | boxEl r r' cap sysList =>
    boxEl (subst idx val r)
        (subst idx val r')
        (subst idx val cap)
        (sysList.map fun (φ, side) => (subst idx val φ, subst idx val side))
  -- cap
  | capEl r r' ty tubes e =>
    capEl (subst idx val r)
        (subst idx val r')
        (subst idx val ty)
        (tubes.map fun (φ, tube) => (subst idx val φ, subst (idx + 1) (shift val) tube))
        (subst idx val e)
  -- Systems
  | sys branches => sys (branches.map fun (cof, tm) =>
      (subst idx val cof, subst idx val tm))
  -- V-types
  | vtype r a b equiv =>
    vtype (subst idx val r) (subst idx val a) (subst idx val b) (subst idx val equiv)
  | vin r el0 el1 =>
    vin (subst idx val r) (subst idx val el0) (subst idx val el1)
  | vproj r a b equiv v =>
    vproj (subst idx val r) (subst idx val a) (subst idx val b) (subst idx val equiv) (subst idx val v)
  -- Nat
  | nat => nat
  | zero => zero
  | suc n => suc (subst idx val n)
  | natElim p z s n =>
    natElim (subst idx val p)
            (subst idx val z)
            (subst (idx + 2) (shiftN 2 val) s)  -- s binds n and ih
            (subst idx val n)
  -- Circle
  | circle => circle
  | base => base
  | loop r => loop (subst idx val r)
  | circleElim p b l x =>
    circleElim (subst idx val p)
               (subst idx val b)
               (subst (idx + 1) (shift val) l)  -- l binds dim
               (subst idx val x)
  -- Extension types
  | ext n fam cof bdry =>
    let val' := shiftN n val  -- shift val under n binders
    ext n (subst (idx + n) val' fam)
          (subst (idx + n) val' cof)
          (subst (idx + n) val' bdry)
  | extLam n body =>
    extLam n (subst (idx + n) (shiftN n val) body)
  | extApp e dims =>
    extApp (subst idx val e) (dims.map (subst idx val))
  -- Sub types
  | sub ty cof bdry =>
    sub (subst idx val ty)
        (subst idx val cof)
        (subst (idx + 1) (shift val) bdry)  -- bdry binds 1
  | subIn e => subIn (subst idx val e)
  | subOut e => subOut (subst idx val e)

/-- Substitute at index 0 (most common case: β-reduction) -/
def subst0 (val : Expr) (body : Expr) : Expr := subst 0 val body

/-! ## Free Variable Checking -/

-- Large pattern match requires more time to elaborate
set_option maxHeartbeats 200000 in
/-- Check if index n is free in expression -/
partial def freeIn (n : Nat) : Expr → Bool
  | ix m => m == n
  | lit _ => false
  | lam body => freeIn (n + 1) body
  | app f x => freeIn n f || freeIn n x
  | pi dom cod => freeIn n dom || freeIn (n + 1) cod
  | sigma dom cod => freeIn n dom || freeIn (n + 1) cod
  | pair a b => freeIn n a || freeIn n b
  | fst e => freeIn n e
  | snd e => freeIn n e
  | letE ty val body => freeIn n ty || freeIn n val || freeIn (n + 1) body
  | univ _ => false
  -- Dimensions
  | dim0 => false
  | dim1 => false
  | dimVar m => m == n
  -- Cofibrations
  | cof_top => false
  | cof_bot => false
  | cof_eq r s => freeIn n r || freeIn n s
  | cof_and phi psi => freeIn n phi || freeIn n psi
  | cof_or phi psi => freeIn n phi || freeIn n psi
  -- Paths
  | path ty a b => freeIn n ty || freeIn n a || freeIn n b
  | plam body => freeIn (n + 1) body
  | papp p r => freeIn n p || freeIn n r
  | refl a => freeIn n a
  | coe r r' ty a => freeIn n r || freeIn n r' || freeIn (n + 1) ty || freeIn n a
  | hcom r r' ty phi cap => freeIn n r || freeIn n r' || freeIn n ty || freeIn n phi || freeIn n cap
  | hcomTube r r' ty tubes cap =>
    freeIn n r || freeIn n r' || freeIn n ty ||
    tubes.any (fun (φ, tube) => freeIn n φ || freeIn (n + 1) tube) ||  -- tube binds dim
    freeIn n cap
  | com r r' ty tubes cap =>
    freeIn n r || freeIn n r' || freeIn (n + 1) ty ||  -- ty is a type line (binds dimension)
    tubes.any (fun (φ, tube) => freeIn n φ || freeIn (n + 1) tube) ||  -- tube binds dim
    freeIn n cap
  -- ghcom
  | ghcom r r' ty tubes cap =>
    freeIn n r || freeIn n r' || freeIn n ty ||
    tubes.any (fun (φ, tube) => freeIn n φ || freeIn (n + 1) tube) ||
    freeIn n cap
  -- gcom
  | gcom r r' ty tubes cap =>
    freeIn n r || freeIn n r' || freeIn (n + 1) ty ||
    tubes.any (fun (φ, tube) => freeIn n φ || freeIn (n + 1) tube) ||
    freeIn n cap
  -- fhcom
  | fhcom r r' cap tubes =>
    freeIn n r || freeIn n r' || freeIn n cap ||
    tubes.any (fun (φ, tube) => freeIn n φ || freeIn (n + 1) tube)
  -- box
  | boxEl r r' cap sysList =>
    freeIn n r || freeIn n r' || freeIn n cap ||
    sysList.any (fun (φ, side) => freeIn n φ || freeIn n side)
  -- cap
  | capEl r r' ty tubes e =>
    freeIn n r || freeIn n r' || freeIn n ty ||
    tubes.any (fun (φ, tube) => freeIn n φ || freeIn (n + 1) tube) ||
    freeIn n e
  -- Systems
  | sys branches => branches.any fun (cof, tm) => freeIn n cof || freeIn n tm
  -- V-types
  | vtype r a b equiv => freeIn n r || freeIn n a || freeIn n b || freeIn n equiv
  | vin r el0 el1 => freeIn n r || freeIn n el0 || freeIn n el1
  | vproj r a b equiv v => freeIn n r || freeIn n a || freeIn n b || freeIn n equiv || freeIn n v
  -- Nat
  | nat => false
  | zero => false
  | suc e => freeIn n e
  | natElim p z s e => freeIn n p || freeIn n z || freeIn (n + 2) s || freeIn n e
  -- Circle
  | circle => false
  | base => false
  | loop r => freeIn n r
  | circleElim p b l x => freeIn n p || freeIn n b || freeIn (n + 1) l || freeIn n x
  -- Extension types
  | ext m fam cof bdry => freeIn (n + m) fam || freeIn (n + m) cof || freeIn (n + m) bdry
  | extLam m body => freeIn (n + m) body
  | extApp e dims => freeIn n e || dims.any (freeIn n)
  -- Sub types
  | sub ty cof bdry => freeIn n ty || freeIn n cof || freeIn (n + 1) bdry
  | subIn e => freeIn n e
  | subOut e => freeIn n e

/-- Check if variable 0 is free (for eta-expansion detection) -/
def freeIn0 (e : Expr) : Bool := freeIn 0 e

/-! ## β-Reduction -/

-- Large pattern match requires more time to elaborate
set_option maxHeartbeats 600000 in
/-- Single-step reduction (outermost first) -/
partial def step : Expr → Option Expr
  -- β-reduction: (λ. body) x → body[0 := x]
  | app (lam body) arg => some (subst0 arg body)

  -- let-reduction: let x = v in body → body[0 := v]
  | letE _ val body => some (subst0 val body)

  -- Projection reductions
  | fst (pair a _) => some a
  | snd (pair _ b) => some b

  -- Path application: (λi. body) @ r → body[0 := r]
  | papp (plam body) r => some (subst0 r body)

  -- Refl application: (refl a) @ r → a  (for any r)
  | papp (refl a) _ => some a

  -- Cofibration simplification
  | cof_eq dim0 dim0 => some cof_top
  | cof_eq dim1 dim1 => some cof_top
  | cof_eq dim0 dim1 => some cof_bot
  | cof_eq dim1 dim0 => some cof_bot
  | cof_eq (dimVar n) (dimVar m) => if n == m then some cof_top else none
  | cof_and cof_top phi => some phi
  | cof_and phi cof_top => some phi
  | cof_and cof_bot _ => some cof_bot
  | cof_and _ cof_bot => some cof_bot
  | cof_or cof_top _ => some cof_top
  | cof_or _ cof_top => some cof_top
  | cof_or cof_bot phi => some phi
  | cof_or phi cof_bot => some phi

  -- Coercion reflexivity: coe r r A a → a (when r = r')
  | coe dim0 dim0 _ a => some a
  | coe dim1 dim1 _ a => some a
  | coe (dimVar n) (dimVar m) _ a => if n == m then some a else none

  -- Kan Operations: coe through type formers
  --
  -- coe r r' (Π(x:A). B) f = λ a. coe r r' (B[coe r' r A a]) (f (coe r' r A a))
  --
  -- The key insight: we coerce the argument BACKWARDS (r' to r) to feed f,
  -- then coerce the result FORWARDS (r to r').

  -- coe through Pi: coe r r' (λi. Π A. B) f = λ a. coe r r' (B[coerced-arg]) (f (coe r' r A a))
  -- Here ty = (λi. Π dom. cod) so ty binds dimension i
  | coe r r' (plam (pi dom cod)) f =>
    some <|
      lam <|  -- λ a.
        let arg := ix 0  -- the argument 'a'
        let argAtR := coe (shift r') (shift r) (plam (shift dom)) arg
        let appResult := app (shift f) argAtR
        coe (shift r) (shift r') (plam (subst0 argAtR (shift cod))) appResult

  -- coe through Sigma: coe r r' (λi. Σ A. B) (a, b) = (coe r r' A a, coe r r' B[...] b)
  | coe r r' (plam (sigma dom cod)) (pair a b) =>
    let fstCoerced := coe r r' (plam dom) a
    let sndCoerced := coe r r' (plam (subst0 (coe r (dimVar 0) (plam (shift dom)) (shift a)) cod)) b
    some <| pair fstCoerced sndCoerced

  -- coe through Nat: coe r r' Nat n → n (Nat is coercion-stable)
  | coe _ _ (plam nat) a => some a

  -- coe through Circle: coe r r' S¹ x → x (Circle is coercion-stable)
  | coe _ _ (plam circle) a => some a

  -- hcom reflexivity: hcom r r A φ cap → cap (when r = r')
  | hcom dim0 dim0 _ _ cap => some cap
  | hcom dim1 dim1 _ _ cap => some cap
  | hcom (dimVar n) (dimVar m) _ _ cap => if n == m then some cap else none

  -- hcom through Pi: hcom r r' (Π A. B) φ f → λ a. hcom r r' (B a) φ (f a)
  | hcom r r' (pi _dom cod) phi f =>
    some <|
      lam <|  -- λ a.
        let arg := ix 0
        let fibTy := subst0 arg (shift cod)
        let appCap := app (shift f) arg
        hcom (shift r) (shift r') fibTy (shift phi) appCap

  -- hcom through Sigma: hcom r r' (Σ A. B) φ (a, b)
  | hcom r r' (sigma dom cod) phi (pair a b) =>
    let fstHcom := hcom r r' dom phi a
    let sndHcom := hcom r r' (subst0 a cod) phi b
    some <| pair fstHcom sndHcom

  -- hcom in Nat: stays as is (Nat is hcom-stable)
  -- hcom in Circle: stays as is (handled by circle eliminator)

  -- Nat elimination
  | natElim _ z _ zero => some z
  | natElim p z s (suc n) =>
    -- s expects: n, then ih = natElim P z s n
    let ih := natElim p z s n
    some <| subst0 ih (subst0 n s)

  -- Circle elimination
  -- base case: circleElim P b l base → b
  | circleElim _ b _ base => some b
  -- loop case: circleElim P b l (loop r) → l @ r
  -- But l is λi. ... so we need l[r] = body[0 := r]
  | circleElim _ _ l (loop r) => some (papp l r)

  -- System extraction (when cof is true)
  | sys ((cof_top, tm) :: _) => some tm

  -- hcomTube reflexivity: hcom r r A tubes cap → cap (when r = r')
  | hcomTube dim0 dim0 _ _ cap => some cap
  | hcomTube dim1 dim1 _ _ cap => some cap
  | hcomTube (dimVar n) (dimVar m) _ _ cap => if n == m then some cap else none

  -- hcomTube: when all cofibrations are ⊥, reduces to cap
  | hcomTube _ _ _ tubes cap =>
    if tubes.all (fun (φ, _) => φ == cof_bot) then some cap else none

  -- ===== com (heterogeneous composition) =====
  -- com r r' (λi.A) tubes cap = hcomTube r r' A[r'] (coerced-tubes) (coe r r' (λi.A) cap)
  -- This is the fundamental operation for transport in dependent types.
  --
  -- Key insight: com combines coercion and composition
  -- - First coerce the cap from A[r] to A[r']
  -- - Then compose in the target type A[r']
  -- - The tubes must also be coerced to match

  -- com reflexivity: com r r (λi.A) tubes cap → cap
  | com dim0 dim0 _ _ cap => some cap
  | com dim1 dim1 _ _ cap => some cap
  | com (dimVar n) (dimVar m) _ _ cap => if n == m then some cap else none

  -- com through constant type line: com r r' (λi.A) tubes cap → hcomTube r r' A tubes cap
  -- When the type doesn't depend on i, com reduces to hcom
  | com r r' (plam ty) tubes cap =>
    if !freeIn 0 ty then
      -- Type doesn't depend on dimension, so coe is identity
      some (hcomTube r r' ty tubes cap)
    else
      -- General case: convert to hcomTube with coerced cap and tubes
      -- The cap is coerced: coe r r' (λi.A) cap
      let coercedCap := coe r r' (plam ty) cap
      -- The type at r': A[r'/i]
      let tyAtR' := subst0 r' ty
      -- Each tube needs to be coerced from j to r'
      -- tube : (j : 𝕀) → A[j], we need: (j : 𝕀) → A[r']
      -- So: λj. coe j r' (λi.A) (tube j)
      let coercedTubes := tubes.map fun (φ, tube) =>
        (φ, coe (dimVar 0) (shift r') (shift (plam ty)) tube)
      some (hcomTube r r' tyAtR' coercedTubes coercedCap)

  -- ===== V-type computation rules =====
  -- V 0 A B equiv → A
  | vtype dim0 a _ _ => some a
  -- V 1 A B equiv → B
  | vtype dim1 _ b _ => some b

  -- vin 0 a b → a
  | vin dim0 a _ => some a
  -- vin 1 a b → b
  | vin dim1 _ b => some b

  -- vproj 0 A B equiv v → equiv v (apply the equivalence when r=0)
  | vproj dim0 _ _ equiv v => some (app equiv v)
  -- vproj 1 A B equiv v → v (identity projection when r=1)
  | vproj dim1 _ _ _ v => some v

  -- vproj r A B equiv (vin r' a b) → b when r = r' (extract second component)
  | vproj _ _ _ _ (vin _ _ b) => some b

  -- No reduction at this level
  | _ => none

/-- Reduce inside subterms (single step, leftmost-outermost) -/
partial def stepDeep : Expr → Option Expr
  | e =>
    -- Try at root first
    match step e with
    | some e' => some e'
    | none =>
      -- Try in subterms
      match e with
      | app f x =>
        match stepDeep f with
        | some f' => some (app f' x)
        | none =>
          match stepDeep x with
          | some x' => some (app f x')
          | none => none
      | lam body =>
        match stepDeep body with
        | some body' => some (lam body')
        | none => none
      | pi dom cod =>
        match stepDeep dom with
        | some dom' => some (pi dom' cod)
        | none =>
          match stepDeep cod with
          | some cod' => some (pi dom cod')
          | none => none
      | sigma dom cod =>
        match stepDeep dom with
        | some dom' => some (sigma dom' cod)
        | none =>
          match stepDeep cod with
          | some cod' => some (sigma dom cod')
          | none => none
      | pair a b =>
        match stepDeep a with
        | some a' => some (pair a' b)
        | none =>
          match stepDeep b with
          | some b' => some (pair a b')
          | none => none
      | fst e =>
        match stepDeep e with
        | some e' => some (fst e')
        | none => none
      | snd e =>
        match stepDeep e with
        | some e' => some (snd e')
        | none => none
      | letE ty val body =>
        match stepDeep ty with
        | some ty' => some (letE ty' val body)
        | none =>
          match stepDeep val with
          | some val' => some (letE ty val' body)
          | none =>
            match stepDeep body with
            | some body' => some (letE ty val body')
            | none => none
      -- Path operations
      | plam body =>
        match stepDeep body with
        | some body' => some (plam body')
        | none => none
      | papp p r =>
        match stepDeep p with
        | some p' => some (papp p' r)
        | none =>
          match stepDeep r with
          | some r' => some (papp p r')
          | none => none
      | path ty a b =>
        match stepDeep ty with
        | some ty' => some (path ty' a b)
        | none =>
          match stepDeep a with
          | some a' => some (path ty a' b)
          | none =>
            match stepDeep b with
            | some b' => some (path ty a b')
            | none => none
      | refl a =>
        match stepDeep a with
        | some a' => some (refl a')
        | none => none
      | coe r r' ty a =>
        -- Try each subterm left-to-right
        match stepDeep r with
        | some r'' => some (coe r'' r' ty a)
        | none =>
          match stepDeep r' with
          | some r'' => some (coe r r'' ty a)
          | none =>
            match stepDeep ty with
            | some ty' => some (coe r r' ty' a)
            | none =>
              match stepDeep a with
              | some a' => some (coe r r' ty a')
              | none => none
      | hcom r r' ty phi cap =>
        match stepDeep r with
        | some r'' => some (hcom r'' r' ty phi cap)
        | none =>
          match stepDeep r' with
          | some r'' => some (hcom r r'' ty phi cap)
          | none =>
            match stepDeep ty with
            | some ty' => some (hcom r r' ty' phi cap)
            | none =>
              match stepDeep phi with
              | some phi' => some (hcom r r' ty phi' cap)
              | none =>
                match stepDeep cap with
                | some cap' => some (hcom r r' ty phi cap')
                | none => none
      | hcomTube r r' ty tubes cap =>
        match stepDeep r with
        | some r'' => some (hcomTube r'' r' ty tubes cap)
        | none =>
          match stepDeep r' with
          | some r'' => some (hcomTube r r'' ty tubes cap)
          | none =>
            match stepDeep ty with
            | some ty' => some (hcomTube r r' ty' tubes cap)
            | none =>
              match stepDeep cap with
              | some cap' => some (hcomTube r r' ty tubes cap')
              | none => none  -- tubes reduction omitted for simplicity
      | com r r' ty tubes cap =>
        match stepDeep r with
        | some r'' => some (com r'' r' ty tubes cap)
        | none =>
          match stepDeep r' with
          | some r'' => some (com r r'' ty tubes cap)
          | none =>
            match stepDeep ty with
            | some ty' => some (com r r' ty' tubes cap)
            | none =>
              match stepDeep cap with
              | some cap' => some (com r r' ty tubes cap')
              | none => none  -- tubes reduction omitted for simplicity
      -- Cofibrations
      | cof_eq r s =>
        match stepDeep r with
        | some r' => some (cof_eq r' s)
        | none =>
          match stepDeep s with
          | some s' => some (cof_eq r s')
          | none => none
      | cof_and phi psi =>
        match stepDeep phi with
        | some phi' => some (cof_and phi' psi)
        | none =>
          match stepDeep psi with
          | some psi' => some (cof_and phi psi')
          | none => none
      | cof_or phi psi =>
        match stepDeep phi with
        | some phi' => some (cof_or phi' psi)
        | none =>
          match stepDeep psi with
          | some psi' => some (cof_or phi psi')
          | none => none
      -- Nat operations
      | suc n =>
        match stepDeep n with
        | some n' => some (suc n')
        | none => none
      | natElim p z s n =>
        match stepDeep p with
        | some p' => some (natElim p' z s n)
        | none =>
          match stepDeep z with
          | some z' => some (natElim p z' s n)
          | none =>
            match stepDeep s with
            | some s' => some (natElim p z s' n)
            | none =>
              match stepDeep n with
              | some n' => some (natElim p z s n')
              | none => none
      -- Circle operations
      | loop r =>
        match stepDeep r with
        | some r' => some (loop r')
        | none => none
      | circleElim p b l x =>
        match stepDeep p with
        | some p' => some (circleElim p' b l x)
        | none =>
          match stepDeep b with
          | some b' => some (circleElim p b' l x)
          | none =>
            match stepDeep l with
            | some l' => some (circleElim p b l' x)
            | none =>
              match stepDeep x with
              | some x' => some (circleElim p b l x')
              | none => none
      -- V-type operations
      | vtype r a b equiv =>
        match stepDeep r with
        | some r' => some (vtype r' a b equiv)
        | none =>
          match stepDeep a with
          | some a' => some (vtype r a' b equiv)
          | none =>
            match stepDeep b with
            | some b' => some (vtype r a b' equiv)
            | none =>
              match stepDeep equiv with
              | some equiv' => some (vtype r a b equiv')
              | none => none
      | vin r el0 el1 =>
        match stepDeep r with
        | some r' => some (vin r' el0 el1)
        | none =>
          match stepDeep el0 with
          | some el0' => some (vin r el0' el1)
          | none =>
            match stepDeep el1 with
            | some el1' => some (vin r el0 el1')
            | none => none
      | vproj r a b equiv v =>
        match stepDeep r with
        | some r' => some (vproj r' a b equiv v)
        | none =>
          match stepDeep a with
          | some a' => some (vproj r a' b equiv v)
          | none =>
            match stepDeep b with
            | some b' => some (vproj r a b' equiv v)
            | none =>
              match stepDeep equiv with
              | some equiv' => some (vproj r a b equiv' v)
              | none =>
                match stepDeep v with
                | some v' => some (vproj r a b equiv v')
                | none => none
      -- Systems - try to reduce each branch
      | sys branches =>
        let rec tryBranches : List (Expr × Expr) → List (Expr × Expr) → Option Expr
          | [], _ => none
          | (cof, tm) :: rest, acc =>
            match stepDeep cof with
            | some cof' => some (sys (acc.reverse ++ [(cof', tm)] ++ rest))
            | none =>
              match stepDeep tm with
              | some tm' => some (sys (acc.reverse ++ [(cof, tm')] ++ rest))
              | none => tryBranches rest ((cof, tm) :: acc)
        tryBranches branches []
      | _ => none

/-- Normalize with fuel (prevent infinite loops) -/
partial def normalize (fuel : Nat) (e : Expr) : Expr :=
  match fuel with
  | 0 => e
  | n + 1 =>
    match stepDeep e with
    | some e' => normalize n e'
    | none => e  -- Normal form

/-- Default normalization with reasonable fuel -/
def eval (e : Expr) : Expr := normalize 1000 e

/-! ## Pretty Printing -/

/-- Convert to readable string (with de Bruijn indices) -/
partial def toString : Expr → String
  | ix n => s!"#{n}"
  | lit s => s
  | lam body => s!"(λ. {toString body})"
  | app f x => s!"({toString f} {toString x})"
  | pi dom cod => s!"(Π {toString dom}. {toString cod})"
  | sigma dom cod => s!"(Σ {toString dom}. {toString cod})"
  | pair a b => s!"({toString a}, {toString b})"
  | fst e => s!"{toString e}.1"
  | snd e => s!"{toString e}.2"
  | letE ty val body => s!"(let : {toString ty} = {toString val} in {toString body})"
  | univ l => match l with
    | .zero => "Type"
    | _ => s!"Type^{Level.toString l}"
  -- Dimensions
  | dim0 => "0"
  | dim1 => "1"
  | dimVar n => s!"i{n}"
  -- Cofibrations
  | cof_top => "⊤"
  | cof_bot => "⊥"
  | cof_eq r s => s!"({toString r} = {toString s})"
  | cof_and phi psi => s!"({toString phi} ∧ {toString psi})"
  | cof_or phi psi => s!"({toString phi} ∨ {toString psi})"
  -- Paths
  | path ty a b => s!"(path {toString ty} {toString a} {toString b})"
  | plam body => s!"(λi. {toString body})"
  | papp p r => s!"({toString p} @ {toString r})"
  | refl a => s!"(refl {toString a})"
  | coe r r' ty a => s!"(coe {toString r} {toString r'} {toString ty} {toString a})"
  | hcom r r' ty phi cap => s!"(hcom {toString r} {toString r'} {toString ty} [{toString phi}] {toString cap})"
  | hcomTube r r' ty tubes cap =>
    let tubeStrs := tubes.map fun (φ, tube) => s!"{toString φ} ↦ {toString tube}"
    s!"(hcom {toString r} {toString r'} {toString ty} [{String.intercalate ", " tubeStrs}] {toString cap})"
  | com r r' ty tubes cap =>
    let tubeStrs := tubes.map fun (φ, tube) => s!"{toString φ} ↦ {toString tube}"
    s!"(com {toString r} {toString r'} {toString ty} [{String.intercalate ", " tubeStrs}] {toString cap})"
  -- ghcom and gcom
  | ghcom r r' ty tubes cap =>
    let tubeStrs := tubes.map fun (φ, tube) => s!"{toString φ} ↦ {toString tube}"
    s!"(ghcom {toString r} {toString r'} {toString ty} [{String.intercalate ", " tubeStrs}] {toString cap})"
  | gcom r r' ty tubes cap =>
    let tubeStrs := tubes.map fun (φ, tube) => s!"{toString φ} ↦ {toString tube}"
    s!"(gcom {toString r} {toString r'} {toString ty} [{String.intercalate ", " tubeStrs}] {toString cap})"
  -- FHCom, Box, Cap
  | fhcom r r' cap tubes =>
    let tubeStrs := tubes.map fun (φ, tube) => s!"{toString φ} ↦ {toString tube}"
    s!"(fhcom {toString r} {toString r'} {toString cap} [{String.intercalate ", " tubeStrs}])"
  | boxEl r r' cap sysList =>
    let sideStrs := sysList.map fun (φ, side) => s!"{toString φ} ↦ {toString side}"
    s!"(box {toString r} {toString r'} {toString cap} [{String.intercalate ", " sideStrs}])"
  | capEl r r' ty tubes el =>
    let tubeStrs := tubes.map fun (φ, tube) => s!"{toString φ} ↦ {toString tube}"
    s!"(cap {toString r} {toString r'} {toString ty} [{String.intercalate ", " tubeStrs}] {toString el})"
  -- Systems
  | sys branches =>
    let branchStrs := branches.map fun (cof, tm) => s!"{toString cof} ↦ {toString tm}"
    s!"[{String.intercalate ", " branchStrs}]"
  -- V-types
  | vtype r a b equiv => s!"(V {toString r} {toString a} {toString b} {toString equiv})"
  | vin r el0 el1 => s!"(vin {toString r} {toString el0} {toString el1})"
  | vproj r a b equiv v => s!"(vproj {toString r} {toString a} {toString b} {toString equiv} {toString v})"
  -- Nat
  | nat => "ℕ"
  | zero => "0"
  | suc n => s!"S({toString n})"
  | natElim p z s n => s!"(ℕ-elim {toString p} {toString z} {toString s} {toString n})"
  -- Circle
  | circle => "S¹"
  | base => "base"
  | loop r => s!"(loop {toString r})"
  | circleElim p b l x => s!"(S¹-elim {toString p} {toString b} {toString l} {toString x})"
  -- Extension types
  | ext n fam cof bdry => s!"(ext {n} {toString fam} {toString cof} {toString bdry})"
  | extLam n body => s!"(extLam {n} {toString body})"
  | extApp e dims =>
    let dimStrs := dims.map toString
    s!"(extApp {toString e} [{String.intercalate ", " dimStrs}])"
  -- Sub types
  | sub ty cof bdry => s!"(sub {toString ty} {toString cof} {toString bdry})"
  | subIn e => s!"(subIn {toString e})"
  | subOut e => s!"(subOut {toString e})"

instance : ToString Expr := ⟨toString⟩

end Expr

/-! ## Bidirectional Type Checking

    Based on cooltt's approach:
    - infer: synthesize a type for an expression
    - check: verify expression has expected type

    The context is a list of types (de Bruijn style, most recent first)
-/

/-- Typing context: list of types (index 0 = most recent binding) -/
abbrev Ctx := List Expr

/-- Type error information -/
inductive TypeError where
  | unbound : Nat → TypeError
  | mismatch : Expr → Expr → Expr → TypeError  -- expr, expected, actual
  | notFunction : Expr → Expr → TypeError      -- expr, type
  | notPair : Expr → Expr → TypeError
  | notPath : Expr → Expr → TypeError
  | cannotInfer : Expr → TypeError
  | notType : Expr → TypeError
  | pathBoundaryMismatch : Expr → Expr → Expr → TypeError  -- body, expected endpoint, actual
  | tubeAgreement : Expr → Expr → Expr → TypeError  -- hcom, face1 value, face2 value
  | cofibrationError : String → TypeError
  deriving Repr

instance : ToString TypeError where
  toString
  | .unbound n => s!"Unbound variable #{n}"
  | .mismatch e exp act => s!"Type mismatch in {e}: expected {exp}, got {act}"
  | .notFunction e ty => s!"Expected function type, got {ty} in {e}"
  | .notPair e ty => s!"Expected sigma type, got {ty} in {e}"
  | .notPath e ty => s!"Expected path type, got {ty} in {e}"
  | .cannotInfer e => s!"Cannot infer type of {e}"
  | .notType e => s!"Expected a type, got {e}"
  | .pathBoundaryMismatch body exp act => s!"Path boundary mismatch in {body}: expected {exp}, got {act}"
  | .tubeAgreement hc v1 v2 => s!"Tube agreement failure in {hc}: {v1} ≠ {v2}"
  | .cofibrationError msg => s!"Cofibration error: {msg}"

/-- Type checking result -/
abbrev TCResult := Except TypeError

/-! ## Conversion Checking

    Definitional equality for cubical type theory:
    - β-reduction (function application)
    - η-expansion (functions, pairs, paths)
    - Cubical computation (coe, hcom)

    Key principle: two terms are convertible if they have the same
    normal form, or if they are extensionally equal via η-laws.

    η-laws:
    - Functions: f ≡ λx. f x
    - Pairs:     p ≡ (fst p, snd p)
    - Paths:     p ≡ λi. p @ i
-/

/-- Normalize for type comparison -/
def nfEq (a b : Expr) : Bool :=
  Expr.eval a == Expr.eval b

/-- Check if a term is a neutral (stuck) term that can't reduce further -/
def isNeutral : Expr → Bool
  | .ix _ => true
  | .app f _ => isNeutral f
  | .fst e => isNeutral e
  | .snd e => isNeutral e
  | .papp p _ => isNeutral p
  | .coe _ _ _ e => isNeutral e  -- coe stuck on neutral
  | .hcom _ _ _ _ e => isNeutral e  -- hcom stuck on neutral
  | .natElim _ _ _ n => isNeutral n
  | .circleElim _ _ _ x => isNeutral x
  | _ => false

/-- Conversion checking with η-expansion.
    More sophisticated than nfEq - handles extensional equality.

    Strategy:
    1. Normalize both terms
    2. If syntactically equal, done
    3. Try η-expansion based on head constructors
    4. Recurse structurally on matching constructors
    5. For neutrals, compare head and spine
-/
partial def conv (a b : Expr) : Bool :=
  let a' := Expr.eval a
  let b' := Expr.eval b
  if a' == b' then true
  else match a', b' with
  -- ===== η for functions: f ≡ λx. f x =====
  | .lam body1, .lam body2 => conv body1 body2
  | f, .lam body =>
    -- η-expand f to λx. f x and compare bodies
    -- Under the binder, f becomes (shift f), applied to (ix 0)
    conv (.app (Expr.shift f) (.ix 0)) body
  | .lam body, f =>
    conv body (.app (Expr.shift f) (.ix 0))

  -- ===== η for pairs: p ≡ (fst p, snd p) =====
  | .pair a1 b1, .pair a2 b2 => conv a1 a2 && conv b1 b2
  | p, .pair a2 b2 =>
    -- η-expand p to (fst p, snd p)
    conv (.fst p) a2 && conv (.snd p) b2
  | .pair a1 b1, p =>
    conv a1 (.fst p) && conv b1 (.snd p)

  -- ===== η for paths: p ≡ λi. p @ i =====
  | .plam body1, .plam body2 => conv body1 body2

  -- ===== refl: refl a ≡ λi. a (must come before generic plam η) =====
  | .refl a1, .refl a2 => conv a1 a2
  | .refl a, .plam body =>
    -- refl a = λi. a (constant path)
    conv (Expr.shift a) body
  | .plam body, .refl a =>
    conv body (Expr.shift a)

  -- ===== η for paths (generic): p ≡ λi. p @ i =====
  | p, .plam body =>
    -- η-expand p to λi. p @ i
    -- Under the binder, p becomes (shift p), applied to (dimVar 0)
    conv (.papp (Expr.shift p) (.dimVar 0)) body
  | .plam body, p =>
    conv body (.papp (Expr.shift p) (.dimVar 0))

  -- ===== Type formers: structural =====
  | .pi dom1 cod1, .pi dom2 cod2 => conv dom1 dom2 && conv cod1 cod2
  | .sigma dom1 cod1, .sigma dom2 cod2 => conv dom1 dom2 && conv cod1 cod2
  | .path ty1 a1 b1, .path ty2 a2 b2 => conv ty1 ty2 && conv a1 a2 && conv b1 b2
  | .univ l1, .univ l2 => Level.levelEq l1 l2

  -- ===== Applications and projections: structural =====
  | .app f1 x1, .app f2 x2 => conv f1 f2 && conv x1 x2
  | .papp p1 r1, .papp p2 r2 => conv p1 p2 && conv r1 r2
  | .fst e1, .fst e2 => conv e1 e2
  | .snd e1, .snd e2 => conv e1 e2

  -- ===== Let: should be reduced, but handle structurally =====
  | .letE ty1 v1 b1, .letE ty2 v2 b2 => conv ty1 ty2 && conv v1 v2 && conv b1 b2

  -- ===== Dimensions =====
  | .dim0, .dim0 => true
  | .dim1, .dim1 => true
  | .dimVar n1, .dimVar n2 => n1 == n2

  -- ===== Cofibrations =====
  | .cof_top, .cof_top => true
  | .cof_bot, .cof_bot => true
  | .cof_eq r1 s1, .cof_eq r2 s2 => conv r1 r2 && conv s1 s2
  | .cof_and φ1 ψ1, .cof_and φ2 ψ2 => conv φ1 φ2 && conv ψ1 ψ2
  | .cof_or φ1 ψ1, .cof_or φ2 ψ2 => conv φ1 φ2 && conv ψ1 ψ2

  -- ===== Coercion: structural when stuck =====
  | .coe r1 r1' ty1 a1, .coe r2 r2' ty2 a2 =>
    conv r1 r2 && conv r1' r2' && conv ty1 ty2 && conv a1 a2

  -- ===== Composition: structural when stuck =====
  | .hcom r1 r1' ty1 φ1 cap1, .hcom r2 r2' ty2 φ2 cap2 =>
    conv r1 r2 && conv r1' r2' && conv ty1 ty2 && conv φ1 φ2 && conv cap1 cap2

  | .hcomTube r1 r1' ty1 tubes1 cap1, .hcomTube r2 r2' ty2 tubes2 cap2 =>
    conv r1 r2 && conv r1' r2' && conv ty1 ty2 && conv cap1 cap2 &&
    tubes1.length == tubes2.length &&
    (tubes1.zip tubes2).all fun ((φ1, t1), (φ2, t2)) => conv φ1 φ2 && conv t1 t2

  | .com r1 r1' ty1 tubes1 cap1, .com r2 r2' ty2 tubes2 cap2 =>
    conv r1 r2 && conv r1' r2' && conv ty1 ty2 && conv cap1 cap2 &&
    tubes1.length == tubes2.length &&
    (tubes1.zip tubes2).all fun ((φ1, t1), (φ2, t2)) => conv φ1 φ2 && conv t1 t2

  -- ===== Natural numbers =====
  | .nat, .nat => true
  | .zero, .zero => true
  | .suc n1, .suc n2 => conv n1 n2
  | .natElim p1 z1 s1 n1, .natElim p2 z2 s2 n2 =>
    conv p1 p2 && conv z1 z2 && conv s1 s2 && conv n1 n2

  -- ===== Circle =====
  | .circle, .circle => true
  | .base, .base => true
  | .loop r1, .loop r2 => conv r1 r2
  | .circleElim p1 b1 l1 x1, .circleElim p2 b2 l2 x2 =>
    conv p1 p2 && conv b1 b2 && conv l1 l2 && conv x1 x2

  -- ===== Extension types =====
  | .ext n1 fam1 cof1 bdry1, .ext n2 fam2 cof2 bdry2 =>
    n1 == n2 && conv fam1 fam2 && conv cof1 cof2 && conv bdry1 bdry2
  | .extLam n1 body1, .extLam n2 body2 =>
    n1 == n2 && conv body1 body2
  | .extApp e1 dims1, .extApp e2 dims2 =>
    conv e1 e2 && dims1.length == dims2.length &&
    (dims1.zip dims2).all fun (d1, d2) => conv d1 d2

  -- ===== V-types =====
  | .vtype r1 a1 b1 e1, .vtype r2 a2 b2 e2 =>
    conv r1 r2 && conv a1 a2 && conv b1 b2 && conv e1 e2
  | .vin r1 el01 el11, .vin r2 el02 el12 =>
    conv r1 r2 && conv el01 el02 && conv el11 el12
  | .vproj r1 a1 b1 e1 v1, .vproj r2 a2 b2 e2 v2 =>
    conv r1 r2 && conv a1 a2 && conv b1 b2 && conv e1 e2 && conv v1 v2

  -- ===== Systems: compare branches =====
  | .sys bs1, .sys bs2 =>
    bs1.length == bs2.length &&
    (bs1.zip bs2).all fun ((φ1, t1), (φ2, t2)) => conv φ1 φ2 && conv t1 t2

  -- ===== Sub types =====
  | .sub ty1 cof1 bdry1, .sub ty2 cof2 bdry2 =>
    conv ty1 ty2 && conv cof1 cof2 && conv bdry1 bdry2
  | .subIn e1, .subIn e2 => conv e1 e2
  | .subOut e1, .subOut e2 => conv e1 e2

  -- ===== Variables and literals =====
  | .ix n1, .ix n2 => n1 == n2
  | .lit s1, .lit s2 => s1 == s2

  -- ===== No match =====
  | _, _ => false

/-- Check if two types are convertible (for type checking) -/
def typeConv (ty1 ty2 : Expr) : Bool := conv ty1 ty2

/-- Lookup type in context -/
def lookupCtx (ctx : Ctx) (n : Nat) : TCResult Expr :=
  match ctx[n]? with
  | some ty => .ok (Expr.shiftN (n + 1) ty)  -- Shift to account for bindings
  | none => .error (.unbound n)

/-- Check tube agreement for hcomTube.
    For each (φ, tube), verify that tube(r) ≡ cap when φ might hold.
    Returns the type on success, or a tubeAgreement error. -/
def checkTubeAgreement (r : Expr) (ty : Expr) (tubes : List (Expr × Expr)) (cap : Expr) : TCResult Expr :=
  let rec go : List (Expr × Expr) → TCResult Expr
    | [] => .ok ty
    | (phi, tube) :: rest =>
      -- tube binds a dimension variable j
      -- tube(r) should equal cap when phi holds
      let tubeAtR := Expr.subst0 r tube  -- tube[r/j]
      let tubeAtR_nf := Expr.eval tubeAtR
      let cap_nf := Expr.eval cap
      -- Only check agreement when phi might be satisfiable
      if Expr.eval phi != .cof_bot then
        if !conv tubeAtR_nf cap_nf then
          .error (.tubeAgreement (.hcomTube r .dim1 ty tubes cap) tubeAtR_nf cap_nf)
        else
          go rest
      else
        go rest
  go tubes

mutual
/-- Infer the type of an expression -/
partial def infer (ctx : Ctx) : Expr → TCResult Expr
  -- Variable: lookup in context
  | .ix n => lookupCtx ctx n

  -- Literals are untyped (for now, treat as their own type)
  | .lit s => .ok (.lit s)

  -- Universe hierarchy
  | .univ n => .ok (.univ (.suc n))

  -- Pi type formation: if A : Type_i and B : Type_j then (Π A B) : Type_{max i j}
  | .pi dom cod => do
    let domTy ← infer ctx dom
    match Expr.eval domTy with
    | .univ i =>
      let codTy ← infer (dom :: ctx) cod
      match Expr.eval codTy with
      | .univ j => .ok (.univ (Level.normalize (.max i j)))
      | _ => .error (.notType cod)
    | _ => .error (.notType dom)

  -- Sigma type formation
  | .sigma dom cod => do
    let domTy ← infer ctx dom
    match Expr.eval domTy with
    | .univ i =>
      let codTy ← infer (dom :: ctx) cod
      match Expr.eval codTy with
      | .univ j => .ok (.univ (Level.normalize (.max i j)))
      | _ => .error (.notType cod)
    | _ => .error (.notType dom)

  -- Application: infer function type, check argument
  | .app f a => do
    let fTy ← infer ctx f
    match Expr.eval fTy with
    | .pi dom cod =>
      let _ ← check ctx a dom  -- Check argument has domain type
      .ok (Expr.subst0 a cod)  -- Result type with arg substituted
    | ty => .error (.notFunction (.app f a) ty)

  -- Projections
  | .fst p => do
    let pTy ← infer ctx p
    match Expr.eval pTy with
    | .sigma dom _ => .ok dom
    | ty => .error (.notPair (.fst p) ty)

  | .snd p => do
    let pTy ← infer ctx p
    match Expr.eval pTy with
    | .sigma _ cod => .ok (Expr.subst0 (.fst p) cod)
    | ty => .error (.notPair (.snd p) ty)

  -- Path type formation
  | .path ty a b => do
    let tyTy ← infer ctx ty
    match Expr.eval tyTy with
    | .univ n =>
      let _ ← check ctx a ty
      let _ ← check ctx b ty
      .ok (.univ n)
    | _ => .error (.notType ty)

  -- Path application
  | .papp p _ => do
    let pTy ← infer ctx p
    match Expr.eval pTy with
    | .path ty _ _ => .ok ty
    | ty => .error (.notPath (.papp p .dim0) ty)

  -- Refl: infer type from the argument
  | .refl a => do
    let aTy ← infer ctx a
    .ok (.path aTy a a)

  -- Coe: coerce through type line
  | .coe _ r' ty _ => do
    -- ty binds a dimension variable, evaluate at r' to get result type
    .ok (Expr.subst0 r' ty)

  -- Dimensions
  | .dim0 => .ok (.lit "𝕀")
  | .dim1 => .ok (.lit "𝕀")
  | .dimVar _ => .ok (.lit "𝕀")

  -- Cofibrations
  | .cof_top => .ok (.lit "𝔽")
  | .cof_bot => .ok (.lit "𝔽")
  | .cof_eq _ _ => .ok (.lit "𝔽")
  | .cof_and _ _ => .ok (.lit "𝔽")
  | .cof_or _ _ => .ok (.lit "𝔽")

  -- Nat type
  | .nat => .ok (.univ .zero)
  | .zero => .ok .nat
  | .suc n => do
    let _ ← check ctx n .nat
    .ok .nat

  -- Circle type
  | .circle => .ok (.univ .zero)
  | .base => .ok .circle
  | .loop _ => .ok .circle

  -- Let: infer body type with binding
  | .letE ty val body => do
    let _ ← check ctx val ty
    infer (ty :: ctx) body

  -- Lambda and pair require annotation to infer
  | e@(.lam _) => .error (.cannotInfer e)
  | e@(.pair _ _) => .error (.cannotInfer e)
  | e@(.plam _) => .error (.cannotInfer e)

  -- HCom with tube agreement checking
  -- hcom r r' A φ cap : A
  -- Requirement: when φ holds, tube values must agree with cap at r
  | .hcom _r _r' ty phi cap => do
    -- Check cap has type ty
    let _ ← check ctx cap ty
    -- Check phi is a cofibration (simplified: just infer it)
    let _ ← infer ctx phi
    -- The result type is ty at r'
    .ok ty

  -- HComTube with explicit tubes and agreement checking
  -- hcomTube r r' A [(φ₁, tube₁), ...] cap : A
  -- Requirements:
  -- 1. cap : A
  -- 2. For each (φᵢ, tubeᵢ): tubeᵢ : (j : 𝕀) → A  (tube binds dimension j)
  -- 3. TUBE AGREEMENT: tubeᵢ(r) ≡ cap when φᵢ holds
  | .hcomTube r _r' ty tubes cap => do
    -- Check cap has type ty
    let _ ← check ctx cap ty
    -- Check each tube and verify agreement
    checkTubeAgreement r ty tubes cap

  -- Com (heterogeneous composition)
  -- com r r' (λi.A) [(φ₁, tube₁), ...] cap : A[r']
  -- Requirements:
  -- 1. cap : A[r] (cap lives in the type at the source dimension)
  -- 2. For each (φᵢ, tubeᵢ): tubeᵢ(j) : A[j] (tube varies with the type line)
  -- 3. TUBE AGREEMENT: tubeᵢ(r) ≡ cap when φᵢ holds
  | .com _ r' ty _ cap => do
    -- ty is a type line (λi.A), the cap should have type A[r]
    let _ ← infer ctx cap  -- simplified: just infer cap type
    -- The result type is A[r'] - substitute r' for the bound dimension in ty
    .ok (Expr.subst0 r' ty)

  -- GHCom (generalized homogeneous composition)
  -- ghcom r r' A [(φ₁, tube₁), ...] cap : A
  | .ghcom _ _ ty _ cap => do
    let _ ← check ctx cap ty
    .ok ty

  -- GCom (generalized heterogeneous composition)
  -- gcom r r' (λi.A) [(φ₁, tube₁), ...] cap : A[r']
  | .gcom _ r' ty _ cap => do
    let _ ← infer ctx cap
    .ok (Expr.subst0 r' ty)

  -- FHCom (fibrant hcom - for types)
  -- fhcom r r' cap sys : Type
  | .fhcom _ _ _ _ => .ok (.univ .zero)  -- Simplified: FHCom produces a type

  -- Box (introduction for FHCom types)
  -- box r r' cap sys : fhcom r r' cap sys
  | .boxEl r r' cap sysList => .ok (.fhcom r r' cap sysList)

  -- Cap (elimination for FHCom types)
  -- cap r r' ty sys el : ty
  | .capEl _ _ ty _ el => do
    let _ ← infer ctx el
    .ok ty

  | .natElim p _ _ n => .ok (.app p n)
  | .circleElim p _ _ x => .ok (.app p x)

  -- Extension types
  -- ext n fam cof bdry : Type
  | .ext _ _ _ _ => .ok (.univ .zero)  -- Extension type formation is a type

  -- extLam: cannot infer without annotation
  | e@(.extLam _ _) => .error (.cannotInfer e)

  -- extApp: apply extension element to dimensions
  -- extApp e [r₁, ..., rₙ] : fam[r₁/i₁, ..., rₙ/iₙ]
  | .extApp e dims => do
    let eTy ← infer ctx e
    match Expr.eval eTy with
    | .ext n fam _ _ =>
      -- fam binds n dimensions, substitute each dimension
      if dims.length == n then
        let result := dims.foldl (init := fam) fun acc dim => Expr.subst0 dim acc
        .ok result
      else
        .error (.cannotInfer (.extApp e dims))
    | _ => .error (.cannotInfer (.extApp e dims))

  -- V-types
  -- V r A B equiv : Type (when equiv : A → B is an equivalence at r=0)
  | .vtype _ _ _ _ => .ok (.univ .zero)  -- Simplified: assumes small types
  -- vin r a b : V r A B equiv (when a : A and b : B)
  | .vin _r a b => do
    let _ ← infer ctx a  -- a : A
    let tyB ← infer ctx b  -- b : B
    .ok tyB  -- Result is in B (simplified)
  -- vproj r A B equiv v : B
  | .vproj _ _ b _ v => do
    let _ ← infer ctx v
    .ok b

  -- Sub types
  -- sub A φ t : Type (when A : Type, φ : Cof, t : [φ] → A)
  | .sub _ _ _ => .ok (.univ .zero)  -- Sub type formation is a type

  -- subIn: cannot infer, needs type annotation (element could have many sub types)
  | e@(.subIn _) => .error (.cannotInfer e)

  -- subOut e : A when e : sub A φ t
  | .subOut e => do
    let eTy ← infer ctx e
    match Expr.eval eTy with
    | .sub ty _ _ => .ok ty
    | _ => .error (.cannotInfer (.subOut e))

  -- Systems
  | .sys ((_, tm) :: _) => infer ctx tm
  | .sys [] => .error (.cannotInfer (.sys []))

/-- Check that expression has expected type -/
partial def check (ctx : Ctx) (e : Expr) (expected : Expr) : TCResult Unit := do
  match e with
  -- Lambda introduction: check against Pi type
  | .lam body =>
    match Expr.eval expected with
    | .pi dom cod =>
      check (dom :: ctx) body cod
    | _ => .error (.notFunction e expected)

  -- Pair introduction: check against Sigma type
  | .pair a b =>
    match Expr.eval expected with
    | .sigma dom cod =>
      let _ ← check ctx a dom
      check ctx b (Expr.subst0 a cod)
    | _ => .error (.notPair e expected)

  -- Path lambda: check against Path type with boundary verification
  | .plam body =>
    match Expr.eval expected with
    | .path ty lhs rhs =>
      -- Check body has type ty (with dimension variable in scope)
      let _ ← infer (ty :: ctx) body
      -- Verify boundaries: body[0/i] ≡ lhs, body[1/i] ≡ rhs
      let body0 := Expr.eval (Expr.subst0 .dim0 body)  -- body at i=0
      let body1 := Expr.eval (Expr.subst0 .dim1 body)  -- body at i=1
      if !conv body0 lhs then
        .error (.pathBoundaryMismatch body lhs body0)
      else if !conv body1 rhs then
        .error (.pathBoundaryMismatch body rhs body1)
      else
        .ok ()
    | _ => .error (.notPath e expected)

  -- ExtLam introduction: check against extension type
  | .extLam n body =>
    match Expr.eval expected with
    | .ext m fam cof bdry =>
      if n == m then
        -- Body should have type fam (with n dimension variables in scope)
        -- Simplified: just infer body type, proper checking would verify boundary
        let _ ← infer ctx body
        -- TODO: verify that when cof holds, body agrees with bdry
        .ok ()
      else
        .error (.mismatch e expected (.ext n fam cof bdry))
    | _ => .error (.cannotInfer e)

  -- SubIn introduction: check against sub type
  | .subIn elem =>
    match Expr.eval expected with
    | .sub ty cof bdry =>
      -- elem should have type ty
      let _ ← check ctx elem ty
      -- TODO: verify that when cof holds, elem agrees with bdry[prf/x]
      -- For now, simplified: just check the element has the base type
      -- The boundary condition would be: conv (eval elem) (subst0 prf bdry) when cof is true
      let _ := (cof, bdry)  -- silence unused warning
      .ok ()
    | _ => .error (.cannotInfer e)

  -- Fallback: infer and compare
  | _ => do
    let inferred ← infer ctx e
    if nfEq inferred expected then
      .ok ()
    else
      .error (.mismatch e expected inferred)
end

/-- Type check an expression in empty context -/
def typecheck (e : Expr) : TCResult Expr := infer [] e

/-- Type check with expected type -/
def typecheckAgainst (e : Expr) (ty : Expr) : TCResult Unit := check [] e ty

/-! ## Elaboration: Named → De Bruijn -/

/-- Environment mapping names to de Bruijn levels -/
abbrev NameEnv := List String

/-- Resolve a name to de Bruijn index.
    The environment is a list with most recent binding at the front.
    Position in list = de Bruijn index (0 = most recent)
-/
def resolveName (env : NameEnv) (name : String) : Option Nat :=
  let rec go (i : Nat) : List String → Option Nat
    | [] => none
    | n :: rest => if n == name then some i else go (i + 1) rest
  go 0 env

open Lego in
/-- Elaborate a surface Term to Core Expr.
    Converts named variables to de Bruijn indices.
-/
partial def elaborate (env : NameEnv) : Lego.Term → Option Expr
  -- Named variable → index
  | Lego.Term.var name =>
    match resolveName env name with
    | some idx => some (.ix idx)
    | none => some (.lit name)  -- Free variable becomes literal (or error?)

  -- Literal
  | Lego.Term.lit s => some (.lit s)

  -- Lambda: (lam x body) or (lam x A body)
  | Lego.Term.con "lam" [Lego.Term.var x, body] => do
    let body' ← elaborate (x :: env) body
    some (.lam body')
  | Lego.Term.con "lam" [Lego.Term.var x, _, body] => do
    let body' ← elaborate (x :: env) body
    some (.lam body')

  -- Application: (app f x)
  | Lego.Term.con "app" [f, x] => do
    let f' ← elaborate env f
    let x' ← elaborate env x
    some (.app f' x')

  -- Pi: (Pi x A B) or (pi x A B)
  | Lego.Term.con "Pi" [Lego.Term.var x, dom, cod] => do
    let dom' ← elaborate env dom
    let cod' ← elaborate (x :: env) cod
    some (.pi dom' cod')
  | Lego.Term.con "pi" [Lego.Term.var x, dom, cod] => do
    let dom' ← elaborate env dom
    let cod' ← elaborate (x :: env) cod
    some (.pi dom' cod')

  -- Arrow: (Arrow A B) - non-dependent
  | Lego.Term.con "Arrow" [dom, cod] => do
    let dom' ← elaborate env dom
    let cod' ← elaborate ("_" :: env) cod
    some (.pi dom' cod')
  | Lego.Term.con "arr" [dom, cod] => do
    let dom' ← elaborate env dom
    let cod' ← elaborate ("_" :: env) cod
    some (.pi dom' cod')

  -- Sigma: (Sigma x A B)
  | Lego.Term.con "Sigma" [Lego.Term.var x, dom, cod] => do
    let dom' ← elaborate env dom
    let cod' ← elaborate (x :: env) cod
    some (.sigma dom' cod')
  | Lego.Term.con "sigma" [Lego.Term.var x, dom, cod] => do
    let dom' ← elaborate env dom
    let cod' ← elaborate (x :: env) cod
    some (.sigma dom' cod')

  -- Pair: (pair a b)
  | Lego.Term.con "pair" [a, b] => do
    let a' ← elaborate env a
    let b' ← elaborate env b
    some (.pair a' b')

  -- Projections
  | Lego.Term.con "proj1" [e] => do
    let e' ← elaborate env e
    some (.fst e')
  | Lego.Term.con "fst" [e] => do
    let e' ← elaborate env e
    some (.fst e')
  | Lego.Term.con "proj2" [e] => do
    let e' ← elaborate env e
    some (.snd e')
  | Lego.Term.con "snd" [e] => do
    let e' ← elaborate env e
    some (.snd e')

  -- Let: (let x A v body)
  | Lego.Term.con "let" [Lego.Term.var x, ty, val, body] => do
    let ty' ← elaborate env ty
    let val' ← elaborate env val
    let body' ← elaborate (x :: env) body
    some (.letE ty' val' body')
  | Lego.Term.con "letexpr" [Lego.Term.var x, ty, val, body] => do
    let ty' ← elaborate env ty
    let val' ← elaborate env val
    let body' ← elaborate (x :: env) body
    some (.letE ty' val' body')

  -- Universe
  | Lego.Term.con "type" [] => some (.univ .zero)
  | Lego.Term.con "typeN" [Lego.Term.lit n] => some (.univ (Level.ofNat n.toNat!))
  | Lego.Term.con "Univ" [Lego.Term.lit n] => some (.univ (Level.ofNat n.toNat!))

  -- Path: (path A a b) or (pathsugar A a b)
  | Lego.Term.con "path" [ty, a, b] => do
    let ty' ← elaborate env ty
    let a' ← elaborate env a
    let b' ← elaborate env b
    some (.path ty' a' b')
  | Lego.Term.con "pathsugar" [ty, a, b] => do
    let ty' ← elaborate env ty
    let a' ← elaborate env a
    let b' ← elaborate env b
    some (.path ty' a' b')

  -- Refl: (refl a) or (reflexpr)
  | Lego.Term.con "refl" [a] => do
    let a' ← elaborate env a
    some (.refl a')
  | Lego.Term.con "reflexpr" [] => some (.refl (.ix 0))  -- implicit

  -- Coe: (coeexpr r r' a A)
  | Lego.Term.con "coeexpr" [r, r', a, ty] => do
    let r1 ← elaborate env r
    let r2 ← elaborate env r'
    let a' ← elaborate env a
    let ty' ← elaborate ("_i" :: env) ty  -- ty binds dimension var
    some (.coe r1 r2 ty' a')
  | Lego.Term.con "coe" [r, r', a, ty] => do
    let r1 ← elaborate env r
    let r2 ← elaborate env r'
    let a' ← elaborate env a
    let ty' ← elaborate ("_i" :: env) ty  -- ty binds dimension var
    some (.coe r1 r2 ty' a')

  -- HCom: (hcomexpr r r' ty phi cap)
  | Lego.Term.con "hcomexpr" [r, r', ty, phi, cap] => do
    let r1 ← elaborate env r
    let r2 ← elaborate env r'
    let ty' ← elaborate env ty
    let phi' ← elaborate env phi
    let cap' ← elaborate env cap
    some (.hcom r1 r2 ty' phi' cap')
  | Lego.Term.con "hcom" [r, r', ty, phi, cap] => do
    let r1 ← elaborate env r
    let r2 ← elaborate env r'
    let ty' ← elaborate env ty
    let phi' ← elaborate env phi
    let cap' ← elaborate env cap
    some (.hcom r1 r2 ty' phi' cap')
  -- Simplified hcom with implicit ⊤ cofibration
  | Lego.Term.con "hcomexpr" [r, r', ty, cap] => do
    let r1 ← elaborate env r
    let r2 ← elaborate env r'
    let ty' ← elaborate env ty
    let cap' ← elaborate env cap
    some (.hcom r1 r2 ty' .cof_top cap')
  | Lego.Term.con "hcom" [r, r', ty, cap] => do
    let r1 ← elaborate env r
    let r2 ← elaborate env r'
    let ty' ← elaborate env ty
    let cap' ← elaborate env cap
    some (.hcom r1 r2 ty' .cof_top cap')

  -- Zero-arg constructor → literal
  | Lego.Term.con name [] => some (.lit name)

  -- Generic constructor → try to elaborate args
  | Lego.Term.con "var" [Lego.Term.var name] =>
    match resolveName env name with
    | some idx => some (.ix idx)
    | none => some (.lit name)

  | _ => none

end Lego.Core
