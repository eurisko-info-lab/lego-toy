/-
  Lego.Cubical.Kan: Kan Operations for Cubical Type Theory

  Implements the key transport operations:
  - Coercion (coe): transport along a path in the universe
  - Homogeneous Composition (hcom): fill a cube with compatible boundaries
  - Heterogeneous Composition (com): combine coe + hcom for dependent types

  Mathematical structure:
  - These operations witness that types form a Kan complex
  - coe: functorial action of paths on elements
  - hcom: existence of fillers for open boxes
  - com: composition in dependent types via pullback

  Based on redtt's Val.ml Kan operations and CCHM cubical type theory.
-/

import Lego.Cubical.Core
import Lego.Cubical.Quote
import Lego.Cubical.Visitor

namespace Lego.Cubical.Kan

open Lego.Core
open Lego.Core.Expr

/-! ## Dimension Values

    Dimensions are elements of the interval 𝕀 = {0, 1}.
    In cubical type theory, we track:
    - Concrete endpoints: 0 and 1
    - Variables: dimension variables bound by path lambdas
-/

/-- Dimension values -/
inductive Dim where
  | i0 : Dim               -- 0 endpoint
  | i1 : Dim               -- 1 endpoint
  | dvar : Nat → Dim       -- dimension variable
  deriving Repr, BEq, Inhabited

/-- Direction: pair of dimensions for coercion/composition -/
structure Dir where
  src : Dim
  tgt : Dim
  deriving Repr, BEq

namespace Dir
/-- Check if direction is degenerate (src = tgt) -/
def isDegenerate (d : Dir) : Bool :=
  d.src == d.tgt

/-- Create direction from expressions -/
def ofExpr (r r' : Expr) : Dir :=
  let toDim : Expr → Dim
    | .dim0 => .i0
    | .dim1 => .i1
    | .dimVar n => .dvar n
    | _ => .i0  -- fallback
  { src := toDim r, tgt := toDim r' }
end Dir

/-! ## Cofibration Evaluation

    Cofibrations are propositions that can be decided on the interval:
    - ⊤: always true
    - ⊥: always false
    - r = s: dimension equality
    - φ ∧ ψ: conjunction
    - φ ∨ ψ: disjunction
-/

/-- Evaluate cofibration to boolean given dimension substitution -/
partial def evalCof (subst : Nat → Option Dim) : Expr → Bool
  | .cof_top => true
  | .cof_bot => false
  | .cof_eq r s =>
    let evalDim : Expr → Option Dim
      | .dim0 => some .i0
      | .dim1 => some .i1
      | .dimVar n => subst n
      | _ => none
    match evalDim r, evalDim s with
    | some d1, some d2 => d1 == d2
    | _, _ => false  -- Unknown
  | .cof_and φ ψ => evalCof subst φ && evalCof subst ψ
  | .cof_or φ ψ => evalCof subst φ || evalCof subst ψ
  | _ => false

/-! ## Dimension Substitution in Expressions

    Now using visitor-based implementation from Lego.Cubical.Visitor.
-/

/-- Substitute a dimension expression for dimVar 0 (visitor-based) -/
def substDim0 (d : Expr) (e : Expr) : Expr :=
  e.substDim0' d

/-! ## Coercion

    coe r r' (λi.A[i]) a : A[r'/i]

    Transport an element a : A[r/i] to A[r'/i] along the line of types.

    Key computation rules:
    1. coe r r A a = a  (when r = r', identity)
    2. coe r r' (λi.Type) a = a  (universe is constant)
    3. coe r r' (λi.Π(x:A[i]).B[i,x]) f = λx. coe r r' ... (f ...)
    4. coe r r' (λi.Σ(x:A[i]).B[i,x]) (a,b) = (coe r r' A a, coe r r' ... b)
-/

/-- Try to reduce coercion -/
partial def reduceCoe (fuel : Nat) (r r' : Expr) (ty : Expr) (a : Expr) : Option Expr :=
  if fuel == 0 then none
  else
  -- Rule 1: degenerate direction
  if r == r' then some a
  else match ty with
  -- Rule 2: universe is stable under coercion
  | .univ _ => some a
  -- Rule 3: coercion in Pi type (simplified)
  | .pi _dom _cod =>
    -- Full implementation would build the transport function
    -- For now, just recognize the pattern
    some (.lam (.coe r r' ty (.app (Expr.shift a) (.ix 0))))
  -- Rule 4: coercion in Sigma type (simplified)
  | .sigma _dom _cod =>
    some (.pair (.coe r r' ty (.fst a)) (.coe r r' ty (.snd a)))
  -- Path type: transport the path pointwise
  | .path tyA _ _ =>
    some (.plam (.coe r r' tyA (.papp (Expr.shift a) (.dimVar 0))))
  | _ => none

/-! ## Homogeneous Composition (HCom)

    hcom r r' A φ u a : A

    Key computation rules:
    1. hcom r r A φ u a = a  (degenerate direction)
    2. hcom r r' A ⊤ u a = u r'  (when cofibration is true, use tube at endpoint)
    3. hcom r r' A ⊥ u a = a  (when cofibration is false, return cap)
-/

/-- Try to reduce homogeneous composition -/
partial def reduceHCom (fuel : Nat) (r r' : Expr) (_ty : Expr) (phi : Expr) (cap : Expr) : Option Expr :=
  if fuel == 0 then none
  else
  -- Rule 1: degenerate direction
  if r == r' then some cap
  else match phi with
  -- Rule 2: ⊤ - would need tube
  | .cof_top => some cap  -- Simplified
  -- Rule 3: ⊥ - no tube constraint, return cap
  | .cof_bot => some cap
  | _ => none

/-- Try to reduce hcom with explicit tubes -/
partial def reduceHComTube (fuel : Nat) (r r' : Expr) (_ty : Expr)
    (tubes : List (Expr × Expr)) (cap : Expr) : Option Expr :=
  if fuel == 0 then none
  else
  -- Rule 1: degenerate direction
  if r == r' then some cap
  else
    -- Check if any tube is active
    let subst : Nat → Option Dim := fun _ => none  -- No substitution context
    match tubes.find? (fun (φ, _) => evalCof subst φ) with
    | some (_, tube) =>
      -- Substitute r' for the dimension variable in tube
      some (substDim0 r' tube)
    | none =>
      if tubes.isEmpty then some cap
      else none

/-! ## Heterogeneous Composition (Com)

    com r r' (λi.A[i]) φ u a : A[r']

    Like hcom but the type varies along the dimension.
-/

/-- Try to reduce heterogeneous composition -/
partial def reduceCom (fuel : Nat) (r r' : Expr) (ty : Expr)
    (tubes : List (Expr × Expr)) (cap : Expr) : Option Expr :=
  if fuel == 0 then none
  else
  -- Rule 1: degenerate direction
  if r == r' then some cap
  else
    -- Basic reduction: coe the cap, then hcom
    let tyAtR' := substDim0 r' ty
    let coeCap := Expr.coe r r' ty cap
    let coeTubes := tubes.map fun (φ, tube) =>
      let coeTube := Expr.coe (.dimVar 0) r' ty tube
      (φ, coeTube)
    some (.hcomTube r r' tyAtR' coeTubes coeCap)

/-! ## Kan Reduction

    Main entry point for reducing Kan operations.
-/

/-- Fuel for reduction (prevent infinite loops) -/
def defaultFuel : Nat := 1000

/-- Try to reduce a Kan operation -/
def reduceKan (e : Expr) : Option Expr :=
  match e with
  | .coe r r' ty a => reduceCoe defaultFuel r r' ty a
  | .hcom r r' ty phi cap => reduceHCom defaultFuel r r' ty phi cap
  | .hcomTube r r' ty tubes cap => reduceHComTube defaultFuel r r' ty tubes cap
  | .com r r' ty tubes cap => reduceCom defaultFuel r r' ty tubes cap
  | _ => none

/-- Normalize expression including Kan operations.
    Uses Expr.normalizeStep which handles beta reduction generically.
    Kan-specific reductions are passed as the extraReduce parameter. -/
def normalizeKan (fuel : Nat) (e : Expr) : Expr :=
  e.normalizeStep fuel reduceKan (Expr.subst) substDim0

/-! ## Transport (Special Case)

    transport : path Type A B → A → B
    transport p a = coe 0 1 (λi. p @ i) a

    This is the standard transport operation derived from coercion.
-/

/-- Create transport term -/
def mkTransport (pathTy : Expr) (a : Expr) : Expr :=
  .coe .dim0 .dim1 (.papp (Expr.shift pathTy) (.dimVar 0)) a

/-! ## Path Operations via Kan

    Many path operations can be defined using Kan operations:
    - symm : path A a b → path A b a
    - trans : path A a b → path A b c → path A a c
    - ap : (f : A → B) → path A x y → path B (f x) (f y)
-/

/-- Symmetry: flip a path (simplified) -/
def mkSymm (p : Expr) : Expr :=
  -- symm p i = p (1-i)
  -- Simplified representation
  .plam (.papp (Expr.shift p) (.dimVar 0))

/-- Transitivity via composition -/
def mkTrans (tyA : Expr) (p q : Expr) : Expr :=
  .hcomTube .dim0 .dim1 tyA
    [ (.cof_eq (.dimVar 0) .dim0, .papp (Expr.shift p) .dim0)
    , (.cof_eq (.dimVar 0) .dim1, Expr.shift q)
    ]
    (.papp p .dim1)

/-- Apply function to path -/
def mkAp (f : Expr) (p : Expr) : Expr :=
  .plam (.app (Expr.shift f) (.papp (Expr.shift p) (.dimVar 0)))

end Lego.Cubical.Kan
