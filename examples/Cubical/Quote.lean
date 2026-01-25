import Cubical.Core

/-!
# Quotation: Reading Back Semantic Values to Syntax

This module implements quotation (read-back) for cubical type theory.
Given a semantic value (in normal form), quotation produces a syntactic term.

## Key Operations

1. **quote** - Convert a value to syntax at a given type
2. **quoteNeu** - Convert a neutral term to syntax
3. **quoteTy** - Convert a type (value) to syntax

## De Bruijn Levels vs Indices

During quotation, we track de Bruijn *levels* (counting from the bottom of
the context) rather than indices (counting from the top). This simplifies
handling of binders:
- Level of a variable = position where it was introduced
- To convert level to index: index = envSize - level - 1

## Algorithm (NbE style)

Quotation is the right adjoint to evaluation in NbE:
- eval : Syntax → Value
- quote : Value → Syntax
- quote (eval t) ≡ t (up to β-normalization)

Reference: "Normalization by Evaluation for Cubical Type Theory" (Sterling)
-/

namespace Lego.Cubical

open Lego.Core
open Lego.Core.Expr

/-! ## Quotation Environment

Track the current de Bruijn level (size of context).
-/

/-- Quotation environment: tracks current de Bruijn level -/
structure QuoteEnv where
  /-- Current de Bruijn level (size of context) -/
  level : Nat
  /-- Dimension variable level (separate from term variables) -/
  dimLevel : Nat := 0
  deriving Repr

namespace QuoteEnv

def empty : QuoteEnv := ⟨0, 0⟩

def succ (env : QuoteEnv) : QuoteEnv :=
  { env with level := env.level + 1 }

def succDim (env : QuoteEnv) : QuoteEnv :=
  { env with dimLevel := env.dimLevel + 1 }

/-- Convert de Bruijn level to index -/
def levelToIndex (env : QuoteEnv) (lvl : Nat) : Nat :=
  env.level - lvl - 1

/-- Convert dimension level to index -/
def dimLevelToIndex (env : QuoteEnv) (lvl : Nat) : Nat :=
  env.dimLevel - lvl - 1

end QuoteEnv

/-! ## Generic Values (Semantic Variables)

When quoting under a binder, we need to create a "generic" value
that represents a fresh variable at the current level.
-/

/-- Create a generic variable at the current level -/
def generic (env : QuoteEnv) : Expr :=
  Expr.ix env.level

/-- Create a generic dimension variable -/
def genericDim (env : QuoteEnv) : Expr :=
  Expr.dimVar env.dimLevel

/-! ## Substitution and Shifting

Helpers for manipulating de Bruijn indices.
-/

/-- Shift free variables (≥ cutoff) by n -/
partial def shiftFrom (term : Expr) (n : Nat) (cutoff : Nat) : Expr :=
  match term with
  | Expr.ix k =>
    if k >= cutoff then Expr.ix (k + n) else Expr.ix k
  | Expr.lam body => Expr.lam (shiftFrom body n (cutoff + 1))
  | Expr.app f a => Expr.app (shiftFrom f n cutoff) (shiftFrom a n cutoff)
  | Expr.pi dom cod => Expr.pi (shiftFrom dom n cutoff) (shiftFrom cod n (cutoff + 1))
  | Expr.sigma dom cod => Expr.sigma (shiftFrom dom n cutoff) (shiftFrom cod n (cutoff + 1))
  | Expr.pair a b => Expr.pair (shiftFrom a n cutoff) (shiftFrom b n cutoff)
  | Expr.fst p => Expr.fst (shiftFrom p n cutoff)
  | Expr.snd p => Expr.snd (shiftFrom p n cutoff)
  | Expr.path ty a b => Expr.path (shiftFrom ty n cutoff) (shiftFrom a n cutoff) (shiftFrom b n cutoff)
  | Expr.plam body => Expr.plam (shiftFrom body n cutoff)
  | Expr.papp p r => Expr.papp (shiftFrom p n cutoff) r
  | Expr.refl a => Expr.refl (shiftFrom a n cutoff)
  | Expr.letE ty v body =>
    Expr.letE (shiftFrom ty n cutoff) (shiftFrom v n cutoff) (shiftFrom body n (cutoff + 1))
  | Expr.suc m => Expr.suc (shiftFrom m n cutoff)
  | e => e

/-- Shift all free variables by n -/
def shift (term : Expr) (n : Nat) : Expr :=
  shiftFrom term n 0

/-- Substitute val for index 0 in term, with depth tracking -/
partial def substAt (term : Expr) (val : Expr) (depth : Nat) : Expr :=
  match term with
  | Expr.ix n =>
    if n == depth then
      shift val depth  -- Shift the substituted value
    else if n > depth then
      Expr.ix (n - 1)  -- Adjust for removed binder
    else
      Expr.ix n        -- Bound above, unchanged

  | Expr.lam body => Expr.lam (substAt body val (depth + 1))
  | Expr.app f a => Expr.app (substAt f val depth) (substAt a val depth)
  | Expr.pi dom cod => Expr.pi (substAt dom val depth) (substAt cod val (depth + 1))
  | Expr.sigma dom cod => Expr.sigma (substAt dom val depth) (substAt cod val (depth + 1))
  | Expr.pair a b => Expr.pair (substAt a val depth) (substAt b val depth)
  | Expr.fst p => Expr.fst (substAt p val depth)
  | Expr.snd p => Expr.snd (substAt p val depth)
  | Expr.path ty a b => Expr.path (substAt ty val depth) (substAt a val depth) (substAt b val depth)
  | Expr.plam body => Expr.plam (substAt body val depth)  -- Dim binder, term depth unchanged
  | Expr.papp p r => Expr.papp (substAt p val depth) r
  | Expr.refl a => Expr.refl (substAt a val depth)
  | Expr.coe r r' ty a => Expr.coe r r' (substAt ty val depth) (substAt a val depth)
  | Expr.hcom r r' ty phi cap =>
    Expr.hcom r r' (substAt ty val depth) phi (substAt cap val depth)
  | Expr.hcomTube r r' ty tubes cap =>
    Expr.hcomTube r r' (substAt ty val depth)
      (tubes.map fun (c, t) => (c, substAt t val depth))
      (substAt cap val depth)
  | Expr.com r r' ty tubes cap =>
    Expr.com r r' (substAt ty val depth)
      (tubes.map fun (c, t) => (c, substAt t val depth))
      (substAt cap val depth)
  | Expr.letE ty v body =>
    Expr.letE (substAt ty val depth) (substAt v val depth) (substAt body val (depth + 1))
  | Expr.suc n => Expr.suc (substAt n val depth)
  | Expr.natElim p z s n =>
    Expr.natElim (substAt p val depth) (substAt z val depth) (substAt s val depth) (substAt n val depth)
  | Expr.circleElim p b l x =>
    Expr.circleElim (substAt p val depth) (substAt b val depth) (substAt l val depth) (substAt x val depth)
  | Expr.loop r => Expr.loop r
  | Expr.vtype r a b e =>
    Expr.vtype r (substAt a val depth) (substAt b val depth) (substAt e val depth)
  | Expr.vin r m n => Expr.vin r (substAt m val depth) (substAt n val depth)
  | Expr.vproj r a b e v =>
    Expr.vproj r (substAt a val depth) (substAt b val depth) (substAt e val depth) (substAt v val depth)
  | Expr.sys branches =>
    Expr.sys (branches.map fun (c, t) => (c, substAt t val depth))
  | e => e  -- Atoms unchanged

/-! ## Core Quotation

Quote semantic values back to syntax.
-/

mutual

/-- Quote a dimension -/
partial def quoteDim (env : QuoteEnv) : Expr → Expr
  | Expr.dim0 => Expr.dim0
  | Expr.dim1 => Expr.dim1
  | Expr.dimVar n =>
    -- Convert level to index
    Expr.dimVar (env.dimLevelToIndex n)
  | e => e  -- Already a dimension expression

/-- Quote a cofibration -/
partial def quoteCof (env : QuoteEnv) : Expr → Expr
  | Expr.cof_top => Expr.cof_top
  | Expr.cof_bot => Expr.cof_bot
  | Expr.cof_eq a b => Expr.cof_eq (quoteDim env a) (quoteDim env b)
  | Expr.cof_and a b => Expr.cof_and (quoteCof env a) (quoteCof env b)
  | Expr.cof_or a b => Expr.cof_or (quoteCof env a) (quoteCof env b)
  | e => e

/-- Quote a type (value in universe) back to syntax -/
partial def quoteTy (env : QuoteEnv) : Expr → Expr
  | Expr.univ l => Expr.univ l
  | Expr.nat => Expr.nat
  | Expr.circle => Expr.circle

  | Expr.pi dom cod =>
    let qdom := quoteTy env dom
    -- Quote codomain with a fresh variable
    let var := generic env
    let env' := env.succ
    let cod' := substAt cod var 0  -- Instantiate with the generic
    let qcod := quoteTy env' cod'
    Expr.pi qdom qcod

  | Expr.sigma dom cod =>
    let qdom := quoteTy env dom
    let var := generic env
    let env' := env.succ
    let cod' := substAt cod var 0
    let qcod := quoteTy env' cod'
    Expr.sigma qdom qcod

  | Expr.path ty a b =>
    Expr.path (quoteTy env ty) (quote env ty a) (quote env ty b)

  -- Cubical types
  | Expr.vtype r a b e =>
    Expr.vtype (quoteDim env r) (quoteTy env a) (quoteTy env b) (quote env (Expr.univ Level.zero) e)

  -- Neutral types get quoted as neutrals
  | e => quoteNeu env e

/-- Quote a value at a given type -/
partial def quote (env : QuoteEnv) (ty : Expr) : Expr → Expr
  | e =>
    let ty' := eval ty
    let e' := eval e
    match ty', e' with
    -- Introduction forms: quote structurally based on type

    | Expr.pi _dom cod, f =>
      -- η-expand: λx. f x
      let var := generic env
      let env' := env.succ
      let cod' := substAt cod var 0
      let app := eval (Expr.app f var)
      Expr.lam (quote env' cod' app)

    | Expr.sigma dom cod, p =>
      -- η-expand: (fst p, snd p)
      let fstP := eval (Expr.fst p)
      let sndP := eval (Expr.snd p)
      let cod' := substAt cod fstP 0
      Expr.pair (quote env dom fstP) (quote env cod' sndP)

    | Expr.path ty' _a _b, p =>
      -- η-expand: λi. p @ i
      let dim := genericDim env
      let env' := env.succDim
      let app := eval (Expr.papp p dim)
      Expr.plam (quote env' ty' app)

    | Expr.nat, Expr.zero => Expr.zero
    | Expr.nat, Expr.suc n => Expr.suc (quote env Expr.nat n)

    | Expr.circle, Expr.base => Expr.base
    | Expr.circle, Expr.loop r => Expr.loop (quoteDim env r)

    -- V-type introductions
    | Expr.vtype _ a b _e, Expr.vin r' m n =>
      Expr.vin (quoteDim env r') (quote env a m) (quote env b n)

    -- Neutrals and other forms
    | _, _ => quoteNeu env e'

/-- Quote a neutral term -/
partial def quoteNeu (env : QuoteEnv) : Expr → Expr
  | Expr.ix n =>
    -- Variable: convert level to index if needed
    if n < env.level then
      Expr.ix (env.levelToIndex n)
    else
      Expr.ix n  -- Free variable, keep as-is

  | Expr.lit s => Expr.lit s

  | Expr.app f a =>
    Expr.app (quoteNeu env f) (quoteNeu env a)

  | Expr.fst p => Expr.fst (quoteNeu env p)
  | Expr.snd p => Expr.snd (quoteNeu env p)

  | Expr.papp p r => Expr.papp (quoteNeu env p) (quoteDim env r)

  | Expr.coe r r' ty a =>
    Expr.coe (quoteDim env r) (quoteDim env r') (quoteTy env ty) (quoteNeu env a)

  | Expr.hcom r r' ty phi cap =>
    Expr.hcom (quoteDim env r) (quoteDim env r')
      (quoteTy env ty) (quoteCof env phi) (quoteNeu env cap)

  | Expr.hcomTube r r' ty tubes cap =>
    Expr.hcomTube (quoteDim env r) (quoteDim env r')
      (quoteTy env ty)
      (tubes.map fun (c, t) => (quoteCof env c, quoteNeu env t))
      (quoteNeu env cap)

  | Expr.com r r' ty tubes cap =>
    Expr.com (quoteDim env r) (quoteDim env r')
      (quoteTy env ty)
      (tubes.map fun (c, t) => (quoteCof env c, quoteNeu env t))
      (quoteNeu env cap)

  | Expr.vproj r a b e v =>
    Expr.vproj (quoteDim env r) (quoteTy env a) (quoteTy env b)
      (quoteNeu env e) (quoteNeu env v)

  | Expr.natElim p z s n =>
    Expr.natElim (quoteTy env p) (quoteNeu env z) (quoteNeu env s) (quoteNeu env n)

  | Expr.circleElim p b l x =>
    Expr.circleElim (quoteTy env p) (quoteNeu env b) (quoteNeu env l) (quoteNeu env x)

  | Expr.refl a => Expr.refl (quoteNeu env a)

  | Expr.letE ty val body =>
    Expr.letE (quoteTy env ty) (quoteNeu env val) (quoteNeu env.succ body)

  | Expr.sys branches =>
    Expr.sys (branches.map fun (c, t) => (quoteCof env c, quoteNeu env t))

  | Expr.lam body => Expr.lam (quoteNeu env.succ body)

  | Expr.plam body => Expr.plam (quoteNeu env.succDim body)

  | Expr.pair a b => Expr.pair (quoteNeu env a) (quoteNeu env b)

  | e => e  -- Already in normal form (atoms)

end

/-! ## High-Level Interface -/

/-- Quote a closed value at a given type -/
def quoteClosed (ty : Expr) (val : Expr) : Expr :=
  quote QuoteEnv.empty ty val

/-- Quote a closed type -/
def quoteClosedTy (ty : Expr) : Expr :=
  quoteTy QuoteEnv.empty ty

/-- Normalize and quote (NbE) -/
def nbe (ty : Expr) (val : Expr) : Expr :=
  quoteClosed (eval ty) (eval val)

/-- Normalize a type -/
def nbeTy (ty : Expr) : Expr :=
  quoteClosedTy (eval ty)

/-- Check if two values are equal by quoting (definitional equality via NbE) -/
def equalByNbe (ty : Expr) (v1 v2 : Expr) : Bool :=
  let q1 := nbe ty v1
  let q2 := nbe ty v2
  -- Syntactic equality of quoted forms
  conv q1 q2

end Lego.Cubical
