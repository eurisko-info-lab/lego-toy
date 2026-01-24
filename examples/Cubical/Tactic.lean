/-
  Lego.Cubical.Tactic: Bidirectional type checking tactics

  Mathematical Structure:
  - Bidirectional typing: synthesis (↑) and checking (↓)
  - Tactics as computations over typing goals
  - Based on cooltt's Tactic module design

  Key insight from cooltt:
  "Tactics are monadic computations that produce syntax given typing information.
   Checking tactics are given a goal type, synthesis tactics return both
   the term and its type."

  This module provides:
  - Tp: Type-level tactics (formation rules)
  - Chk: Checking tactics (introduction rules)
  - Syn: Synthesis tactics (elimination rules)
  - Var: Variable handling in contexts
  - Abstraction helpers for binding

  The key invariant is that checking tactics produce well-typed terms
  of the given type, while synthesis tactics produce both term and type.
-/

import Lego.Cubical.Core
import Lego.Cubical.Cofibration
import Lego.Cubical.Splice

namespace Lego.Cubical.Tactic

open Lego.Core
open Lego.Core.Expr
open Cofibration

/-! ## Tactic Result Type

    Tactics can succeed with a value or fail with an error.
-/

inductive TacResult (α : Type) where
  | ok : α → TacResult α
  | error : String → TacResult α
  deriving Repr, BEq

namespace TacResult

def map (f : α → β) : TacResult α → TacResult β
  | ok a => ok (f a)
  | error msg => error msg

def bind (ma : TacResult α) (f : α → TacResult β) : TacResult β :=
  match ma with
  | ok a => f a
  | error msg => error msg

def pure (a : α) : TacResult α := ok a

instance : Monad TacResult where
  pure := pure
  bind := bind

instance : MonadExcept String TacResult where
  throw := error
  tryCatch ma handler :=
    match ma with
    | ok a => ok a
    | error msg => handler msg

def isOk : TacResult α → Bool
  | ok _ => true
  | error _ => false

def getOrElse (ma : TacResult α) (default : α) : α :=
  match ma with
  | ok a => a
  | error _ => default

end TacResult

/-! ## Typing Context

    A context maps de Bruijn indices to types.
-/

structure TpCtx where
  /-- List of types for bound variables (most recent first) -/
  types : List Expr
  /-- Current cofibration assumptions -/
  cofAssumptions : List Expr
  deriving Repr, BEq

namespace TpCtx

/-- Empty typing context -/
def empty : TpCtx := { types := [], cofAssumptions := [] }

/-- Extend context with a new type -/
def extend (ctx : TpCtx) (ty : Expr) : TpCtx :=
  { ctx with types := ty :: ctx.types }

/-- Look up type of variable by de Bruijn index -/
def lookup (ctx : TpCtx) (n : Nat) : Option Expr :=
  ctx.types[n]?

/-- Size of context -/
def size (ctx : TpCtx) : Nat := ctx.types.length

/-- Add a cofibration assumption -/
def assume (ctx : TpCtx) (φ : Expr) : TpCtx :=
  { ctx with cofAssumptions := φ :: ctx.cofAssumptions }

/-- Check if context is consistent -/
def isConsistent (ctx : TpCtx) : Bool :=
  -- Check no contradictions in cofibration assumptions
  let combined := meetAll ctx.cofAssumptions
  Cofibration.isConsistent combined

end TpCtx

/-! ## Checking Goal

    A checking goal includes the expected type and boundary constraints.
    In cubical type theory, we often check terms at boundary types.
-/

structure ChkGoal where
  /-- Expected type -/
  tp : Expr
  /-- Cofibration constraint (when to match boundary) -/
  cof : Expr := cof_top
  /-- Boundary term (value when cof is satisfied) -/
  boundary : Expr := lit "unit"
  deriving Repr, BEq

namespace ChkGoal

/-- Simple goal with just a type -/
def simple (ty : Expr) : ChkGoal :=
  { tp := ty, cof := cof_top, boundary := lit "unit" }

/-- Goal with boundary constraint -/
def withBoundary (ty : Expr) (φ : Expr) (bdry : Expr) : ChkGoal :=
  { tp := ty, cof := φ, boundary := bdry }

end ChkGoal

/-! ## Type Formation Tactics (Tp)

    Tactics for constructing types (introduction for universes).
-/

/-- A type formation tactic produces a type expression -/
abbrev TpTac := TpCtx → TacResult Expr

namespace Tp

/-- Create a tactic from a computation -/
def rule (_name : String) (m : TpCtx → TacResult Expr) : TpTac := m

/-- Run a type tactic -/
def run (tac : TpTac) (ctx : TpCtx) : TacResult Expr := tac ctx

/-- Return a constant type -/
def pure (e : Expr) : TpTac := fun _ => TacResult.ok e

/-- Formation rule for Nat -/
def nat : TpTac := pure .nat

/-- Formation rule for Circle -/
def circle : TpTac := pure .circle

/-- Formation rule for Universe -/
def univ : TpTac := pure (Expr.univ 0)

/-- Formation rule for Dim (interval type) -/
def dim : TpTac := pure (lit "𝕀")

/-- Formation rule for Cof -/
def cof : TpTac := pure (lit "Cof")  -- Represent Cof as a literal for now

/-- Pi type formation -/
def pi (dom : TpTac) (cod : Expr → TpTac) : TpTac := fun ctx => do
  let domTy ← dom ctx
  let ctx' := ctx.extend domTy
  let codTy ← cod (ix 0) ctx'
  TacResult.ok (Expr.pi domTy codTy)

/-- Sigma type formation -/
def sigma (base : TpTac) (fam : Expr → TpTac) : TpTac := fun ctx => do
  let baseTy ← base ctx
  let ctx' := ctx.extend baseTy
  let famTy ← fam (ix 0) ctx'
  TacResult.ok (Expr.sigma baseTy famTy)

/-- Path type formation -/
def path (tyLine : TpTac) (left : Expr) (right : Expr) : TpTac := fun ctx => do
  let ty ← tyLine ctx
  -- Path A a b is represented with plam internally
  TacResult.ok (lit s!"Path({ty},{left},{right})")

/-- Sub type formation -/
def sub (ty : TpTac) (φ : Expr) (tm : Expr) : TpTac := fun ctx => do
  let t ← ty ctx
  TacResult.ok (Expr.sub t φ tm)

/-- Proof type formation -/
def prf (φ : Expr) : TpTac := pure (lit s!"Prf({φ})")

/-- Map over result -/
def map (f : Expr → Expr) (tac : TpTac) : TpTac := fun ctx => do
  let e ← tac ctx
  TacResult.ok (f e)

end Tp

/-! ## Checking Tactics (Chk)

    Tactics for checking terms against types (introduction rules).
-/

/-- A checking tactic produces a term given a goal -/
abbrev ChkTac := TpCtx → ChkGoal → TacResult Expr

/-! ## Helper Functions for Type Matching

    These helpers work around pattern matching issues with Expr constructors.
-/

/-- Helper to extract sigma components -/
def isSigma (e : Expr) : Option (Expr × Expr) :=
  match e with
  | Expr.sigma a b => some (a, b)
  | _ => none

/-- Helper to extract pi components -/
def isPi (e : Expr) : Option (Expr × Expr) :=
  match e with
  | Expr.pi dom cod => some (dom, cod)
  | _ => none

/-- Helper to check for Nat -/
def isNat (e : Expr) : Bool :=
  match e with
  | Expr.nat => true
  | _ => false

/-- Helper to check for Circle -/
def isCircle (e : Expr) : Bool :=
  match e with
  | Expr.circle => true
  | _ => false

/-- Helper to extract sub components -/
def isSub (e : Expr) : Option (Expr × Expr × Expr) :=
  match e with
  | Expr.sub a φ t => some (a, φ, t)
  | _ => none

namespace Chk

/-- Create a checking tactic from a computation -/
def rule (_name : String) (m : TpCtx → ChkGoal → TacResult Expr) : ChkTac := m

/-- Create a boundary-aware checking tactic -/
def brule (_name : String) (m : TpCtx → Expr → Expr → Expr → TacResult Expr) : ChkTac :=
  fun ctx goal => m ctx goal.tp goal.cof goal.boundary

/-- Run a checking tactic -/
def run (tac : ChkTac) (ctx : TpCtx) (tp : Expr) : TacResult Expr :=
  tac ctx (ChkGoal.simple tp)

/-- Run a checking tactic with boundary -/
def brun (tac : ChkTac) (ctx : TpCtx) (tp : Expr) (φ : Expr) (bdry : Expr) : TacResult Expr :=
  tac ctx (ChkGoal.withBoundary tp φ bdry)

/-- Return a constant term -/
def pure (e : Expr) : ChkTac := fun _ _ => TacResult.ok e

/-- Zero introduction -/
def zero : ChkTac := rule "Nat.zero" fun _ctx goal =>
  if isNat goal.tp then TacResult.ok Expr.zero
  else TacResult.error "expected Nat"

/-- Successor introduction -/
def suc (tac : ChkTac) : ChkTac := rule "Nat.suc" fun ctx goal =>
  if isNat goal.tp then
    match tac ctx (ChkGoal.simple Expr.nat) with
    | TacResult.ok n => TacResult.ok (Expr.suc n)
    | TacResult.error msg => TacResult.error msg
  else TacResult.error "expected Nat"

/-- Lambda introduction -/
def lam (body : Expr → ChkTac) : ChkTac := rule "Pi.intro" fun ctx goal =>
  let piResult := isPi goal.tp
  if h : piResult.isSome then
    let p := piResult.get h
    let dom := p.1
    let cod := p.2
    let ctx' := ctx.extend dom
    let goalCod := ChkGoal.simple cod
    match body (ix 0) ctx' goalCod with
    | TacResult.ok bodySyn => TacResult.ok (Expr.lam bodySyn)
    | TacResult.error msg => TacResult.error msg
  else TacResult.error "expected Pi type"

/-- Pair introduction -/
def pair (fstTac : ChkTac) (sndTac : ChkTac) : ChkTac := rule "Sg.intro" fun ctx goal =>
  let sigResult := isSigma goal.tp
  if h : sigResult.isSome then
    let p := sigResult.get h
    let sigBase := p.1
    let fam := p.2
    match fstTac ctx (ChkGoal.simple sigBase) with
    | TacResult.ok fstVal =>
      -- Substitute fst into family
      let famSubst := subst 0 fstVal fam
      match sndTac ctx (ChkGoal.simple famSubst) with
      | TacResult.ok sndVal => TacResult.ok (Expr.pair fstVal sndVal)
      | TacResult.error msg => TacResult.error msg
    | TacResult.error msg => TacResult.error msg
  else
    TacResult.error "expected Sigma type"

/-- Path lambda introduction -/
def plam (body : Expr → ChkTac) : ChkTac := rule "Path.intro" fun ctx goal =>
  -- Path types are introduced by path lambdas
  let ctx' := ctx.extend (lit "𝕀")  -- Add interval variable
  do
    let bodyTerm ← body (dimVar ctx.size) ctx' (ChkGoal.simple goal.tp)
    TacResult.ok (Expr.plam bodyTerm)

/-- Base introduction for Circle -/
def base : ChkTac := rule "Circle.base" fun _ goal =>
  if isCircle goal.tp then TacResult.ok Expr.base
  else TacResult.error "expected Circle"

/-- Loop introduction for Circle -/
def loop (dimTac : ChkTac) : ChkTac := rule "Circle.loop" fun ctx goal =>
  if isCircle goal.tp then
    match dimTac ctx (ChkGoal.simple (lit "𝕀")) with
    | TacResult.ok r => TacResult.ok (Expr.loop r)
    | TacResult.error msg => TacResult.error msg
  else TacResult.error "expected Circle"

/-- SubIn introduction -/
def subIn (tac : ChkTac) : ChkTac := rule "Sub.intro" fun ctx goal =>
  let subResult := isSub goal.tp
  if h : subResult.isSome then
    let triple := subResult.get h
    let a := triple.1
    match tac ctx (ChkGoal.simple a) with
    | TacResult.ok tm => TacResult.ok (Expr.subIn tm)
    | TacResult.error msg => TacResult.error msg
  else TacResult.error "expected Sub type"

/-- Convert synthesis tactic to checking tactic -/
def syn (synTac : TpCtx → TacResult (Expr × Expr)) : ChkTac := rule "Syn.to.Chk" fun ctx _goal => do
  let (tm, _inferredTy) ← synTac ctx
  -- Should check that inferredTy converts to goal.tp
  TacResult.ok tm

/-- Catch errors with a handler -/
def tryCatch (tac : ChkTac) (handler : String → ChkTac) : ChkTac := fun ctx goal =>
  match tac ctx goal with
  | TacResult.ok e => TacResult.ok e
  | TacResult.error msg => handler msg ctx goal

end Chk

/-! ## Synthesis Tactics (Syn)

    Tactics for inferring types of terms (elimination rules).
-/

/-- A synthesis tactic produces a term and its type -/
abbrev SynTac := TpCtx → TacResult (Expr × Expr)

namespace Syn

/-- Create a synthesis tactic from a computation -/
def rule (_name : String) (m : TpCtx → TacResult (Expr × Expr)) : SynTac := m

/-- Run a synthesis tactic -/
def run (tac : SynTac) (ctx : TpCtx) : TacResult (Expr × Expr) := tac ctx

/-- Variable lookup -/
def var (n : Nat) : SynTac := rule "Var" fun ctx =>
  match ctx.lookup n with
  | some ty => TacResult.ok (ix n, ty)
  | none => TacResult.error s!"variable {n} not in scope"

/-- Application elimination -/
def app (fnTac : SynTac) (argTac : ChkTac) : SynTac := rule "Pi.elim" fun ctx => do
  let (fn, fnTy) ← fnTac ctx
  let piResult := isPi fnTy
  if h : piResult.isSome then
    let pair := piResult.get h
    let dom := pair.1
    let cod := pair.2
    let arg ← argTac ctx (ChkGoal.simple dom)
    let resultTy := subst 0 arg cod
    pure (Expr.app fn arg, resultTy)
  else TacResult.error "expected function type"

/-- First projection elimination -/
def fst (pairTac : SynTac) : SynTac := rule "Sg.pi1" fun ctx => do
  let (p, pTy) ← pairTac ctx
  let sigResult := isSigma pTy
  if h : sigResult.isSome then
    let pair := sigResult.get h
    TacResult.ok (Expr.fst p, pair.1)
  else
    TacResult.error "expected Sigma type"

/-- Second projection elimination -/
def snd (pairTac : SynTac) : SynTac := rule "Sg.pi2" fun ctx => do
  let (p, pTy) ← pairTac ctx
  let sigResult := isSigma pTy
  if h : sigResult.isSome then
    let pair := sigResult.get h
    let fam := pair.2
    let fstVal := Expr.fst p
    let famSubst := subst 0 fstVal fam
    TacResult.ok (Expr.snd p, famSubst)
  else
    TacResult.error "expected Sigma type"

/-- Path application elimination -/
def papp (pathTac : SynTac) (dimTac : ChkTac) : SynTac := rule "Path.elim" fun ctx => do
  let (p, _pTy) ← pathTac ctx
  let r ← dimTac ctx (ChkGoal.simple (lit "𝕀"))
  -- Result type is the path type at dimension r
  pure (Expr.papp p r, Expr.univ 0)  -- Simplified: would need path type info

/-- SubOut elimination -/
def subOut (subTac : SynTac) : SynTac := rule "Sub.elim" fun ctx => do
  let (tm, ty) ← subTac ctx
  let subResult := isSub ty
  if h : subResult.isSome then
    let triple := subResult.get h
    let a := triple.1
    pure (Expr.subOut tm, a)
  else TacResult.error "expected Sub type"

/-- Annotate a checking tactic with a type -/
def ann (chkTac : ChkTac) (tpTac : TpTac) : SynTac := rule "Ann" fun ctx => do
  let ty ← tpTac ctx
  let tm ← chkTac ctx (ChkGoal.simple ty)
  pure (tm, ty)

/-- Catch errors with a handler -/
def tryCatch (tac : SynTac) (handler : String → SynTac) : SynTac := fun ctx =>
  match tac ctx with
  | TacResult.ok e => TacResult.ok e
  | TacResult.error msg => handler msg ctx

end Syn

/-! ## Variable Handling

    Track variables in scope with their types.
-/

structure Var where
  /-- Type of the variable -/
  tp : Expr
  /-- Value (semantic) of the variable -/
  con : Expr
  deriving Repr, BEq

namespace Var

/-- Create a variable for proof -/
def prf (φ : Expr) : Var :=
  { tp := lit s!"Prf({φ})", con := lit "prf" }

/-- Get the type of a variable -/
def getTp (v : Var) : Expr := v.tp

/-- Get the term representation of a variable -/
def getTerm (v : Var) : Expr := v.con

/-- Convert variable to synthesis tactic -/
def syn (v : Var) : SynTac := fun _ =>
  TacResult.ok (v.con, v.tp)

end Var

/-! ## Abstraction

    Helper for introducing binders.
-/

/-- Abstract over a variable of given type -/
def abstract (tp : Expr) (k : Var → TpCtx → TacResult α) : TpCtx → TacResult α := fun ctx =>
  let lvl := ctx.size
  let v : Var := { tp := tp, con := ix lvl }
  let ctx' := ctx.extend tp
  k v ctx'

/-- Abstract over a proof variable -/
def abstractPrf (φ : Expr) (k : Var → TpCtx → TacResult α) : TpCtx → TacResult α := fun ctx =>
  let v := Var.prf φ
  let ctx' := ctx.assume φ
  k v ctx'

/-! ## Nat Elimination -/

namespace Nat

/-- Nat elimination tactic -/
def elim (motTac : ChkTac) (zeroTac : ChkTac) (sucTac : ChkTac) (scrutTac : SynTac) : SynTac :=
  Syn.rule "Nat.elim" fun ctx => do
    let (scrut, scrutTy) ← scrutTac ctx
    if isNat scrutTy then
      -- motTac should produce Nat → Type
      let mot ← motTac ctx (ChkGoal.simple (Expr.pi .nat (Expr.univ 0)))
      let zeroCase ← zeroTac ctx (ChkGoal.simple (Expr.app mot .zero))
      let sucCase ← sucTac ctx (ChkGoal.simple
        (Expr.pi .nat (Expr.pi (Expr.app mot (ix 0)) (Expr.app mot (Expr.suc (ix 1))))))
      let resultTy := Expr.app mot scrut
      pure (natElim mot zeroCase sucCase scrut, resultTy)
    else TacResult.error "expected Nat scrutinee"

end Nat

/-! ## Circle Elimination -/

namespace Circle

/-- Circle elimination tactic -/
def elim (motTac : ChkTac) (baseTac : ChkTac) (loopTac : ChkTac) (scrutTac : SynTac) : SynTac :=
  Syn.rule "Circle.elim" fun ctx => do
    let (scrut, scrutTy) ← scrutTac ctx
    if isCircle scrutTy then
      let mot ← motTac ctx (ChkGoal.simple (Expr.pi .circle (Expr.univ 0)))
      let baseCase ← baseTac ctx (ChkGoal.simple (Expr.app mot .base))
      -- loopCase should be a path in the fiber over loop
      let loopCase ← loopTac ctx (ChkGoal.simple (Expr.pi (lit "𝕀") (Expr.app mot (Expr.loop (ix 0)))))
      let resultTy := Expr.app mot scrut
      pure (circleElim mot baseCase loopCase scrut, resultTy)
    else TacResult.error "expected Circle scrutinee"

end Circle

/-! ## Coercion and Composition Tactics -/

namespace Coe

/-- Coercion tactic -/
def coe (famTac : ChkTac) (srcTac : ChkTac) (trgTac : ChkTac) (tmTac : ChkTac) : SynTac :=
  Syn.rule "Coe" fun ctx => do
    -- famTac should produce I → Type
    let fam ← famTac ctx (ChkGoal.simple (Expr.pi (lit "𝕀") (Expr.univ 0)))
    let src ← srcTac ctx (ChkGoal.simple (lit "𝕀"))
    let trg ← trgTac ctx (ChkGoal.simple (lit "𝕀"))
    let famSrc := Expr.app fam src
    let tm ← tmTac ctx (ChkGoal.simple famSrc)
    let resultTy := Expr.app fam trg
    pure (Expr.coe fam src trg tm, resultTy)

end Coe

namespace Hcom

/-- Homogeneous composition tactic -/
def hcom (tyTac : ChkTac) (srcTac : ChkTac) (trgTac : ChkTac) (cofTac : ChkTac)
         (capTac : ChkTac) : SynTac :=
  Syn.rule "HCom" fun ctx => do
    let ty ← tyTac ctx (ChkGoal.simple (Expr.univ 0))
    let src ← srcTac ctx (ChkGoal.simple (lit "𝕀"))
    let trg ← trgTac ctx (ChkGoal.simple (lit "𝕀"))
    let φ ← cofTac ctx (ChkGoal.simple (lit "Cof"))
    let cap ← capTac ctx (ChkGoal.simple ty)
    pure (Expr.hcom src trg ty φ cap, ty)

end Hcom

/-! ## Cofibration Tactics (Cof)

    Tactics for constructing cofibrations.
    Based on cooltt's Cof module.
-/

namespace Cof

/-- Cof formation rule -/
def formation : TpTac := Tp.pure (lit "𝔽")

/-- Dimension equality cofibration: r = s -/
def eq (tac0 : ChkTac) (tac1 : ChkTac) : ChkTac :=
  Chk.rule "Cof.eq" fun ctx goal =>
    match goal.tp with
    | Expr.lit "𝔽" =>
      do
        let r0 ← tac0 ctx (ChkGoal.simple (lit "𝕀"))
        let r1 ← tac1 ctx (ChkGoal.simple (lit "𝕀"))
        TacResult.ok (Expr.cof_eq r0 r1)
    | _ => TacResult.error "expected Cof type"

/-- Dimension inequality cofibration: r ≤ s (encoded as (r = 0) ∨ (s = 1)) -/
def le (tac0 : ChkTac) (tac1 : ChkTac) : ChkTac :=
  Chk.rule "Cof.le" fun ctx goal =>
    match goal.tp with
    | Expr.lit "𝔽" =>
      do
        let r0 ← tac0 ctx (ChkGoal.simple (lit "𝕀"))
        let r1 ← tac1 ctx (ChkGoal.simple (lit "𝕀"))
        -- r ≤ s means r=0 ∨ s=1
        TacResult.ok (Expr.cof_or (Expr.cof_eq r0 .dim0) (Expr.cof_eq r1 .dim1))
    | _ => TacResult.error "expected Cof type"

/-- Join (disjunction) of cofibrations -/
def join (tacs : List ChkTac) : ChkTac :=
  Chk.rule "Cof.join" fun ctx goal =>
    match goal.tp with
    | Expr.lit "𝔽" =>
      match tacs with
      | [] => TacResult.ok Expr.cof_bot
      | [t] => t ctx (ChkGoal.simple (lit "𝔽"))
      | t :: ts => do
        let first ← t ctx (ChkGoal.simple (lit "𝔽"))
        let rest ← (join ts) ctx goal
        TacResult.ok (Expr.cof_or first rest)
    | _ => TacResult.error "expected Cof type"

/-- Meet (conjunction) of cofibrations -/
def meet (tacs : List ChkTac) : ChkTac :=
  Chk.rule "Cof.meet" fun ctx goal =>
    match goal.tp with
    | Expr.lit "𝔽" =>
      match tacs with
      | [] => TacResult.ok Expr.cof_top
      | [t] => t ctx (ChkGoal.simple (lit "𝔽"))
      | t :: ts => do
        let first ← t ctx (ChkGoal.simple (lit "𝔽"))
        let rest ← (meet ts) ctx goal
        TacResult.ok (Expr.cof_and first rest)
    | _ => TacResult.error "expected Cof type"

/-- Boundary cofibration: r = 0 ∨ r = 1 -/
def boundary (dimTac : ChkTac) : ChkTac :=
  join [eq dimTac (Chk.pure .dim0), eq dimTac (Chk.pure .dim1)]

/-- Assert a cofibration is true -/
def assertTrue (φ : Expr) : TpCtx → TacResult Unit := fun _ctx =>
  if Cofibration.isTop φ then TacResult.ok ()
  else TacResult.error s!"expected true cofibration: {repr φ}"

/-- Split on cofibrations -/
structure SplitBranch where
  cof : ChkTac
  bdy : Var → ChkTac

def split (branches : List SplitBranch) : ChkTac :=
  Chk.brule "Cof.split" fun ctx tp φ bdry => do
    -- Collect all the cofibrations
    let cofs ← branches.mapM fun b => b.cof ctx (ChkGoal.simple (lit "𝔽"))
    -- Check the disjunction is true
    let _disjunction := cofs.foldl Expr.cof_or Expr.cof_bot
    -- For each branch, check the body under the assumption
    let indexed := cofs.zip branches
    let bodies ← indexed.mapM fun (cofVal, b) => do
      let ctx' := ctx.assume cofVal
      let v : Var := { tp := lit s!"Prf({cofVal})", con := lit "prf" }
      b.bdy v ctx' (ChkGoal.withBoundary tp φ bdry)
    -- Construct split term
    let pairs := cofs.zip bodies
    TacResult.ok (Expr.lit s!"split({pairs.length})")  -- Placeholder

end Cof

/-! ## Proof Tactics (Prf)

    Tactics for proof terms (evidence of cofibration truth).
-/

namespace Prf

/-- Proof type formation -/
def formation (φTac : ChkTac) : TpTac :=
  Tp.rule "Prf.formation" fun ctx => do
    let φ ← φTac ctx (ChkGoal.simple (lit "𝔽"))
    TacResult.ok (lit s!"Prf({φ})")

/-- Proof introduction (when cofibration is true) -/
def intro : ChkTac :=
  Chk.rule "Prf.intro" fun _ctx goal =>
    match goal.tp with
    | Expr.lit s =>
      if s.startsWith "Prf(" then
        -- Extract the cofibration and check it's true in context
        TacResult.ok (lit "prf")
      else TacResult.error "expected Prf type"
    | _ => TacResult.error "expected Prf type"

end Prf

/-! ## Path Tactics (Path)

    Tactics for path types and terms.
-/

namespace Path

/-- Path type formation -/
def formation (tyTac : TpTac) (leftTac : ChkTac) (rightTac : ChkTac) : TpTac :=
  Tp.rule "Path.formation" fun ctx => do
    let ty ← tyTac ctx
    let left ← leftTac ctx (ChkGoal.simple ty)
    let right ← rightTac ctx (ChkGoal.simple ty)
    TacResult.ok (Expr.path ty left right)

/-- Path introduction -/
def intro (bodyTac : Var → ChkTac) : ChkTac :=
  Chk.rule "Path.intro" fun ctx goal =>
    match goal.tp with
    | Expr.path ty _ _ =>
      let lvl := ctx.size
      let v : Var := { tp := lit "𝕀", con := ix lvl }
      let ctx' := ctx.extend (lit "𝕀")
      do
        let body ← bodyTac v ctx' (ChkGoal.simple ty)
        TacResult.ok (Expr.plam body)
    | _ => TacResult.error "expected Path type"

/-- Path elimination (application) -/
def elim (pathTac : SynTac) (dimTac : ChkTac) : SynTac :=
  Syn.rule "Path.elim" fun ctx => do
    let (p, pTy) ← pathTac ctx
    match pTy with
    | Expr.path ty _ _ =>
      let r ← dimTac ctx (ChkGoal.simple (lit "𝕀"))
      TacResult.ok (Expr.papp p r, ty)
    | _ => TacResult.error "expected Path type"

end Path

/-! ## El Tactics (El)

    Tactics for element types (decoding universe codes).
-/

namespace El

/-- El type formation -/
def formation (codeTac : ChkTac) : TpTac :=
  Tp.rule "El.formation" fun ctx => do
    let code ← codeTac ctx (ChkGoal.simple (Expr.univ 0))
    TacResult.ok code  -- In our setup, codes are types directly

/-- El introduction (wrap value) -/
def intro (tac : ChkTac) : ChkTac :=
  Chk.rule "El.intro" fun ctx goal =>
    tac ctx goal  -- Pass through, El is definitionally equal to the type

/-- El elimination (unwrap value) -/
def elim (tac : SynTac) : SynTac :=
  Syn.rule "El.elim" fun ctx =>
    tac ctx  -- Pass through

end El

/-! ## Structural Tactics

    Tactics for let-bindings, variable lookup, and other structural operations.
-/

namespace Structural

/-- Let binding in checking context -/
def let_ (synTac : SynTac) (bodyTac : Var → ChkTac) : ChkTac :=
  Chk.rule "Structural.let" fun ctx goal => do
    let (tm, ty) ← synTac ctx
    let lvl := ctx.size
    let v : Var := { tp := ty, con := tm }
    let ctx' := ctx.extend ty
    let body ← bodyTac v ctx' goal
    -- Substitute the definition into the body
    TacResult.ok (subst lvl tm body)

/-- Let binding in synthesis context -/
def let_syn (synTac : SynTac) (bodyTac : Var → SynTac) : SynTac :=
  Syn.rule "Structural.let_syn" fun ctx => do
    let (tm, ty) ← synTac ctx
    let lvl := ctx.size
    let v : Var := { tp := ty, con := tm }
    let ctx' := ctx.extend ty
    let (body, bodyTy) ← bodyTac v ctx'
    TacResult.ok (subst lvl tm body, subst lvl tm bodyTy)

/-- Variable lookup by name (simplified: by index) -/
def lookupVar (idx : Nat) : SynTac :=
  Syn.var idx

/-- Generalize: abstract over a free variable -/
def generalize (idx : Nat) (bodyTac : ChkTac) : ChkTac :=
  Chk.rule "Structural.generalize" fun ctx goal => do
    match ctx.lookup idx with
    | some ty =>
      let ctx' := ctx.extend ty
      let body ← bodyTac ctx' (ChkGoal.simple goal.tp)
      TacResult.ok (Expr.lam body)
    | none => TacResult.error s!"cannot generalize: variable {idx} not in scope"

/-- Abstract over a variable of given type -/
def abstract_ (ident : String) (tpTac : TpTac) (bodyTac : Var → ChkTac) : ChkTac :=
  Chk.rule s!"Structural.abstract[{ident}]" fun ctx goal => do
    let tp ← tpTac ctx
    let lvl := ctx.size
    let v : Var := { tp := tp, con := ix lvl }
    let ctx' := ctx.extend tp
    let body ← bodyTac v ctx' goal
    TacResult.ok body

end Structural

/-! ## Hole/Probe Tactics

    Tactics for debugging and creating holes.
-/

namespace Hole

/-- Create a hole (metavariable) -/
def hole (name : Option String) : ChkTac :=
  Chk.rule s!"Hole[{name.getD "?"}]" fun _ctx _goal =>
    TacResult.ok (Expr.lit s!"?{name.getD "hole"}")  -- Placeholder for hole

/-- Silent hole (no output) -/
def silent (name : Option String) : ChkTac :=
  hole name

/-- Synthesizing hole -/
def synHole (name : Option String) : SynTac :=
  Syn.rule s!"Hole.syn[{name.getD "?"}]" fun _ctx =>
    TacResult.ok (Expr.lit s!"?{name.getD "hole"}", Expr.univ 0)  -- Placeholder

end Hole

namespace Probe

/-- Probe the goal (for debugging) -/
def probeChk (name : Option String) (tac : ChkTac) : ChkTac :=
  Chk.rule s!"Probe[{name.getD "?"}]" fun ctx goal => do
    -- In a real implementation, would print the goal
    tac ctx goal

/-- Probe synthesis goal -/
def probeSyn (name : Option String) (tac : SynTac) : SynTac :=
  Syn.rule s!"Probe.syn[{name.getD "?"}]" fun ctx => do
    tac ctx

end Probe

/-! ## Helper: Run with simple context -/

def runChk (tac : ChkTac) (ty : Expr) : TacResult Expr :=
  Chk.run tac TpCtx.empty ty

def runSyn (tac : SynTac) : TacResult (Expr × Expr) :=
  Syn.run tac TpCtx.empty

def runTp (tac : TpTac) : TacResult Expr :=
  Tp.run tac TpCtx.empty

/-! ## Univ Tactics (Universe Type Codes)

    Tactics for V-types, extension types, and Kan operations at the type level.
    Based on cooltt's Univ module.
-/

namespace Univ

/-- V-type code formation: V r A B equiv
    When r=0 gives A, when r=1 gives B. -/
def code_v (dimTac : ChkTac) (aTac : TpTac) (bTac : TpTac) (equivTac : ChkTac) : TpTac :=
  Tp.rule "Univ.code_v" fun ctx => do
    let r ← dimTac ctx (ChkGoal.simple (lit "𝕀"))
    let a ← aTac ctx
    let b ← bTac ctx
    -- equiv : Equiv A B
    let equiv ← equivTac ctx (ChkGoal.simple (lit s!"Equiv({a},{b})"))
    TacResult.ok (Expr.vtype r a b equiv)

/-- FHCom type formation: fhcom r r' cap [(φ,tube)...]
    Fibrant homogeneous composition at type level. -/
def code_fhcom (rTac r'Tac capTac : ChkTac) (tubes : List (ChkTac × ChkTac)) : TpTac :=
  Tp.rule "Univ.code_fhcom" fun ctx => do
    let r ← rTac ctx (ChkGoal.simple (lit "𝕀"))
    let r' ← r'Tac ctx (ChkGoal.simple (lit "𝕀"))
    let cap ← capTac ctx (ChkGoal.simple (Expr.univ 0))
    let tubeExprs ← tubes.mapM fun (φtac, ttac) => do
      let φ ← φtac ctx (ChkGoal.simple (lit "𝔽"))
      let t ← ttac ctx (ChkGoal.simple (Expr.univ 0))
      pure (φ, t)
    TacResult.ok (Expr.fhcom r r' cap tubeExprs)

/-- Extension type formation: ext n fam cof bdry
    Types with partial boundary constraints. -/
def ext (n : Nat) (famTac cofTac bdryTac : ChkTac) : TpTac :=
  Tp.rule "Univ.ext" fun ctx => do
    let fam ← famTac ctx (ChkGoal.simple (Expr.univ 0))
    let cof ← cofTac ctx (ChkGoal.simple (lit "𝔽"))
    let bdry ← bdryTac ctx (ChkGoal.simple fam)  -- Simplified: should match partial
    TacResult.ok (Expr.ext n fam cof bdry)

/-- HCom type code: hcom at the universe level (checking variant) -/
def hcom_chk (rTac r'Tac tyTac capTac : ChkTac) (tubes : List (ChkTac × ChkTac)) : TpTac :=
  Tp.rule "Univ.hcom_chk" fun ctx => do
    let r ← rTac ctx (ChkGoal.simple (lit "𝕀"))
    let r' ← r'Tac ctx (ChkGoal.simple (lit "𝕀"))
    let ty ← tyTac ctx (ChkGoal.simple (Expr.univ 0))
    let cap ← capTac ctx (ChkGoal.simple ty)
    let tubeExprs ← tubes.mapM fun (φtac, ttac) => do
      let φ ← φtac ctx (ChkGoal.simple (lit "𝔽"))
      let t ← ttac ctx (ChkGoal.simple ty)
      pure (φ, t)
    TacResult.ok (Expr.hcomTube r r' ty tubeExprs cap)

/-- Com type code: heterogeneous composition (checking variant) -/
def com_chk (rTac r'Tac famTac capTac : ChkTac) (tubes : List (ChkTac × ChkTac)) : TpTac :=
  Tp.rule "Univ.com_chk" fun ctx => do
    let r ← rTac ctx (ChkGoal.simple (lit "𝕀"))
    let r' ← r'Tac ctx (ChkGoal.simple (lit "𝕀"))
    let fam ← famTac ctx (ChkGoal.simple (Expr.univ 0))  -- λi.A type family
    let cap ← capTac ctx (ChkGoal.simple (Expr.univ 0))  -- Simplified
    let tubeExprs ← tubes.mapM fun (φtac, ttac) => do
      let φ ← φtac ctx (ChkGoal.simple (lit "𝔽"))
      let t ← ttac ctx (ChkGoal.simple (Expr.univ 0))
      pure (φ, t)
    TacResult.ok (Expr.com r r' fam tubeExprs cap)

/-- Coe type code: coercion (checking variant) -/
def coe_chk (rTac r'Tac famTac termTac : ChkTac) : TpTac :=
  Tp.rule "Univ.coe_chk" fun ctx => do
    let r ← rTac ctx (ChkGoal.simple (lit "𝕀"))
    let r' ← r'Tac ctx (ChkGoal.simple (lit "𝕀"))
    let fam ← famTac ctx (ChkGoal.simple (Expr.univ 0))
    let term ← termTac ctx (ChkGoal.simple (Expr.univ 0))
    TacResult.ok (Expr.coe fam r r' term)

/-- Sub type formation: sub A φ t
    Cubical subtype / restriction type. -/
def sub (aTac φTac tTac : ChkTac) : TpTac :=
  Tp.rule "Univ.sub" fun ctx => do
    let a ← aTac ctx (ChkGoal.simple (Expr.univ 0))
    let φ ← φTac ctx (ChkGoal.simple (lit "𝔽"))
    let t ← tTac ctx (ChkGoal.simple a)  -- Partial: should be under φ
    TacResult.ok (Expr.sub a φ t)

end Univ

/-! ## V-Type Element Tactics (ElV)

    Tactics for introducing and eliminating V-type elements.
-/

namespace ElV

/-- V-type element introduction: vin r a b -/
def intro (dimTac aTac bTac : ChkTac) : ChkTac :=
  Chk.rule "ElV.intro" fun ctx goal =>
    match goal.tp with
    | Expr.vtype _r tyA tyB _ =>
      do
        let dim ← dimTac ctx (ChkGoal.simple (lit "𝕀"))
        let a ← aTac ctx (ChkGoal.simple tyA)
        let b ← bTac ctx (ChkGoal.simple tyB)
        TacResult.ok (Expr.vin dim a b)
    | _ => TacResult.error "expected V-type"

/-- V-type projection: vproj r A B equiv v -/
def proj (dimTac : ChkTac) (termTac : SynTac) : SynTac :=
  Syn.rule "ElV.proj" fun ctx => do
    let dim ← dimTac ctx (ChkGoal.simple (lit "𝕀"))
    let (tm, ty) ← termTac ctx
    match ty with
    | Expr.vtype _r tyA tyB equiv =>
      let result := Expr.vproj dim tyA tyB equiv tm
      -- Result type depends on dimension
      TacResult.ok (result, tyB)  -- Simplified: should depend on dim
    | _ => TacResult.error "expected V-type"

end ElV

/-! ## Extension Type Element Tactics (ElExt)

    Tactics for extension type elements.
-/

namespace ElExt

/-- Extension type element introduction: extLam n body -/
def intro (n : Nat) (bodyTac : ChkTac) : ChkTac :=
  Chk.rule "ElExt.intro" fun ctx goal =>
    match goal.tp with
    | Expr.ext m fam _cof _bdry =>
      if n == m then do
        -- Bind n dimension variables
        let body ← bodyTac ctx (ChkGoal.simple fam)  -- Simplified
        TacResult.ok (Expr.extLam n body)
      else TacResult.error s!"dimension mismatch: expected {m}, got {n}"
    | _ => TacResult.error "expected extension type"

/-- Extension type elimination: extApp e [r₁, ..., rₙ] -/
def elim (termTac : SynTac) (dimTacs : List ChkTac) : SynTac :=
  Syn.rule "ElExt.elim" fun ctx => do
    let (tm, ty) ← termTac ctx
    match ty with
    | Expr.ext n fam _cof _bdry =>
      if dimTacs.length == n then do
        let dims ← dimTacs.mapM fun dtac => dtac ctx (ChkGoal.simple (lit "𝕀"))
        let result := Expr.extApp tm dims
        -- Result type is fam with dims substituted
        TacResult.ok (result, fam)  -- Simplified
      else TacResult.error s!"wrong number of dimension arguments: expected {n}"
    | _ => TacResult.error "expected extension type"

end ElExt

/-! ## FHCom Element Tactics (ElFHCom)

    Tactics for FHCom elements (box/cap).
-/

namespace ElFHCom

/-- FHCom introduction: boxEl r r' cap [(φ,side)...] -/
def intro (rTac r'Tac capTac : ChkTac) (sides : List (ChkTac × ChkTac)) : ChkTac :=
  Chk.rule "ElFHCom.intro" fun ctx goal =>
    match goal.tp with
    | Expr.fhcom _r _r' cap _tubes =>
      do
        let rVal ← rTac ctx (ChkGoal.simple (lit "𝕀"))
        let r'Val ← r'Tac ctx (ChkGoal.simple (lit "𝕀"))
        let capVal ← capTac ctx (ChkGoal.simple cap)
        let sideExprs ← sides.mapM fun (φtac, stac) => do
          let φ ← φtac ctx (ChkGoal.simple (lit "𝔽"))
          let s ← stac ctx (ChkGoal.simple cap)  -- Simplified
          pure (φ, s)
        TacResult.ok (Expr.boxEl rVal r'Val capVal sideExprs)
    | _ => TacResult.error "expected fhcom type"

/-- FHCom elimination: capEl r r' ty [(φ,tube)...] box -/
def elim (rTac r'Tac tyTac boxTac : ChkTac) (tubes : List (ChkTac × ChkTac)) : SynTac :=
  Syn.rule "ElFHCom.elim" fun ctx => do
    let r ← rTac ctx (ChkGoal.simple (lit "𝕀"))
    let r' ← r'Tac ctx (ChkGoal.simple (lit "𝕀"))
    let ty ← tyTac ctx (ChkGoal.simple (Expr.univ 0))
    let box ← boxTac ctx (ChkGoal.simple (Expr.fhcom r r' ty []))  -- Simplified
    let tubeExprs ← tubes.mapM fun (φtac, ttac) => do
      let φ ← φtac ctx (ChkGoal.simple (lit "𝔽"))
      let t ← ttac ctx (ChkGoal.simple ty)
      pure (φ, t)
    TacResult.ok (Expr.capEl r r' ty tubeExprs box, ty)

end ElFHCom

/-! ## Telescope Tactics

    Tactics for working with dependent telescopes (lists of dependent types).
    Based on cooltt's telescope infrastructure.
-/

/-- A telescope is a list of named types where each can depend on previous -/
structure TelEntry where
  name : String
  tpTac : TpTac
  deriving Inhabited

/-- Telescope representation -/
abbrev Telescope := List TelEntry

namespace Telescope

/-- Empty telescope -/
def empty : Telescope := []

/-- Extend telescope with a new entry -/
def extend (tel : Telescope) (name : String) (tpTac : TpTac) : Telescope :=
  tel ++ [TelEntry.mk name tpTac]

/-- Elaborate a telescope to get a list of types -/
def elaborate (tel : Telescope) (ctx : TpCtx) : TacResult (List Expr) :=
  tel.foldlM (init := []) fun acc entry => do
    let ty ← entry.tpTac ctx  -- Simplified: should thread context
    TacResult.ok (acc ++ [ty])

/-- Create a Pi type from telescope and result type -/
def toPi (tel : Telescope) (resultTac : TpTac) : TpTac :=
  Tp.rule "Telescope.toPi" fun ctx => do
    let types ← elaborate tel ctx
    let result ← resultTac ctx
    -- Build nested Pi: (x₁ : A₁) → (x₂ : A₂) → ... → R
    let piType := types.foldr (init := result) fun ty acc =>
      Expr.pi ty acc
    TacResult.ok piType

/-- Create a Sigma type from telescope (dependent product) -/
def toSigma (tel : Telescope) : TpTac :=
  Tp.rule "Telescope.toSigma" fun ctx => do
    let types ← elaborate tel ctx
    match types with
    | [] => TacResult.ok (lit "Unit")  -- Empty telescope = unit
    | [t] => TacResult.ok t
    | t :: ts =>
      -- Build nested Sigma: Σ(x₁ : A₁), Σ(x₂ : A₂), ...
      let sigmaType := ts.foldl (init := t) fun acc ty =>
        Expr.sigma acc ty
      TacResult.ok sigmaType

/-- Apply a term to all telescope arguments -/
def applyTo (tel : Telescope) (termTac : SynTac) (argTacs : List ChkTac) : SynTac :=
  Syn.rule "Telescope.applyTo" fun ctx => do
    if argTacs.length != tel.length then
      TacResult.error s!"wrong number of arguments: expected {tel.length}, got {argTacs.length}"
    else do
      let types ← elaborate tel ctx
      let args ← (argTacs.zip types).mapM fun (argTac, ty) =>
        argTac ctx (ChkGoal.simple ty)
      let (fn, fnTy) ← termTac ctx
      -- Apply all arguments
      let result := args.foldl (init := fn) Expr.app
      -- Compute result type (simplified: just return the last codomain)
      TacResult.ok (result, fnTy)

end Telescope

/-! ## Kan Telescope Tactics

    Telescopes equipped with Kan structure (for paths, transport, etc.).
-/

/-- A Kan telescope has types that vary over an interval dimension -/
structure KanTelEntry where
  name : String
  tpTac : ChkTac → TpTac  -- Takes dimension variable, produces type

/-- Kan telescope representation -/
abbrev KanTelescope := List KanTelEntry

namespace KanTelescope

/-- Empty Kan telescope -/
def empty : KanTelescope := []

/-- Extend Kan telescope -/
def extend (ktel : KanTelescope) (name : String) (tpTac : ChkTac → TpTac) : KanTelescope :=
  ktel ++ [KanTelEntry.mk name tpTac]

/-- Evaluate Kan telescope at a dimension -/
def atDim (ktel : KanTelescope) (dimTac : ChkTac) : Telescope :=
  ktel.map fun entry =>
    TelEntry.mk entry.name (entry.tpTac dimTac)

/-- Create type family from Kan telescope: λi. Σ(x₁ : A₁ i), Σ(x₂ : A₂ i), ... -/
def toFamily (ktel : KanTelescope) : TpTac :=
  Tp.rule "KanTelescope.toFamily" fun ctx => do
    -- Create a dimension abstraction
    let body := Telescope.toSigma (atDim ktel (Chk.pure (ix 0)))  -- Dimension var at index 0
    let bodyTy ← body ctx
    TacResult.ok (Expr.plam bodyTy)

/-- Transport along Kan telescope -/
def coe (ktel : KanTelescope) (srcDim trgDim termTac : ChkTac) : ChkTac :=
  Chk.rule "KanTelescope.coe" fun ctx goal => do
    let src ← srcDim ctx (ChkGoal.simple (lit "𝕀"))
    let trg ← trgDim ctx (ChkGoal.simple (lit "𝕀"))
    let fam ← toFamily ktel ctx
    let term ← termTac ctx (ChkGoal.simple goal.tp)  -- Simplified
    TacResult.ok (Expr.coe fam src trg term)

end KanTelescope

end Lego.Cubical.Tactic
