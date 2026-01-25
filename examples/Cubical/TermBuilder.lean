/-
  Lego.Cubical.TermBuilder: De Bruijn-Free Term Construction

  Mathematical Structure:
  - HOAS-style term building
  - Automatic de Bruijn index management
  - Combinators for common patterns

  Based on cooltt's TermBuilder.ml module.

  Key insight from cooltt:
  "TermBuilder provides a HOAS-style interface for building terms without
   manually managing de Bruijn indices. Functions like `lam` and `pi` take
   Lean functions and convert them to de Bruijn-indexed terms."
-/

import Cubical.Core

namespace Lego.Cubical.TermBuilder

open Lego.Core
open Lego.Core.Expr

/-! ## Building Context -/

/-- Context tracking the current de Bruijn level -/
structure BuildCtx where
  level : Nat := 0
  deriving Repr

namespace BuildCtx

def empty : BuildCtx := {}

def next (ctx : BuildCtx) : BuildCtx :=
  { ctx with level := ctx.level + 1 }

/-- Create a fresh variable at the current level -/
def freshVar (ctx : BuildCtx) : Expr := .ix ctx.level

end BuildCtx

/-! ## The Build Monad -/

/-- Simple reader monad for tracking level -/
def BuildM (α : Type) : Type := BuildCtx → α

namespace BuildM

def pure (a : α) : BuildM α := fun _ => a

def bind (ma : BuildM α) (f : α → BuildM β) : BuildM β := fun ctx =>
  f (ma ctx) ctx

instance : Monad BuildM where
  pure := pure
  bind := bind

def getCtx : BuildM BuildCtx := fun ctx => ctx

def getLevel : BuildM Nat := fun ctx => ctx.level

def withBinder (k : Expr → BuildM α) : BuildM α := fun ctx =>
  let var := ctx.freshVar
  k var ctx.next

def run (ma : BuildM α) : α := ma BuildCtx.empty

end BuildM

/-! ## Basic Term Builders -/

/-- Build a lambda abstraction -/
def lam (k : Expr → BuildM Expr) : BuildM Expr := fun ctx =>
  let body := k (ctx.freshVar) ctx.next
  .lam body

/-- Build a pi type -/
def pi (dom : BuildM Expr) (k : Expr → BuildM Expr) : BuildM Expr := fun ctx =>
  let d := dom ctx
  let cod := k (ctx.freshVar) ctx.next
  .pi d cod

/-- Build a sigma type -/
def sigma (fst : BuildM Expr) (k : Expr → BuildM Expr) : BuildM Expr := fun ctx =>
  let a := fst ctx
  let b := k (ctx.freshVar) ctx.next
  .sigma a b

/-- Build a path type -/
def path (tp : BuildM Expr) (l : BuildM Expr) (r : BuildM Expr) : BuildM Expr := fun ctx =>
  .path (tp ctx) (l ctx) (r ctx)

/-- Build a path lambda (over the interval) -/
def plam (k : Expr → BuildM Expr) : BuildM Expr := fun ctx =>
  let body := k (ctx.freshVar) ctx.next
  .plam body

/-- Build a sub type -/
def sub (tp : BuildM Expr) (φ : BuildM Expr) (k : Expr → BuildM Expr) : BuildM Expr := fun ctx =>
  let a := tp ctx
  let phi := φ ctx
  let t := k (ctx.freshVar) ctx.next
  .sub a phi t

/-! ## Application Builders -/

/-- Apply a function to an argument -/
def ap (f : BuildM Expr) (args : List (BuildM Expr)) : BuildM Expr := fun ctx =>
  args.foldl (fun acc arg => .app acc (arg ctx)) (f ctx)

/-- Path application -/
def papp (p : BuildM Expr) (r : BuildM Expr) : BuildM Expr := fun ctx =>
  .papp (p ctx) (r ctx)

/-- First projection -/
def fst (p : BuildM Expr) : BuildM Expr := fun ctx => .fst (p ctx)

/-- Second projection -/
def snd (p : BuildM Expr) : BuildM Expr := fun ctx => .snd (p ctx)

/-! ## Dimension Builders -/

/-- Dimension 0 -/
def dim0 : BuildM Expr := fun _ => .dim0

/-- Dimension 1 -/
def dim1 : BuildM Expr := fun _ => .dim1

/-! ## Cofibration Builders -/

/-- Top cofibration (true) -/
def top : BuildM Expr := fun _ => .cof_top

/-- Bottom cofibration (false) -/
def bot : BuildM Expr := fun _ => .cof_bot

/-- Dimension equality -/
def eq (r s : BuildM Expr) : BuildM Expr := fun ctx =>
  .cof_eq (r ctx) (s ctx)

/-- Conjunction of cofibrations -/
def cof_and (φ ψ : BuildM Expr) : BuildM Expr := fun ctx =>
  .cof_and (φ ctx) (ψ ctx)

/-- Disjunction of cofibrations -/
def cof_or (φ ψ : BuildM Expr) : BuildM Expr := fun ctx =>
  .cof_or (φ ctx) (ψ ctx)

/-- Join (big disjunction) -/
def cof_join (cofs : List (BuildM Expr)) : BuildM Expr := fun ctx =>
  match cofs with
  | [] => .cof_bot
  | [φ] => φ ctx
  | _φ :: _rest => cofs.foldl (fun acc c => .cof_or acc (c ctx)) .cof_bot

/-- Meet (big conjunction) -/
def cof_meet (cofs : List (BuildM Expr)) : BuildM Expr := fun ctx =>
  match cofs with
  | [] => .cof_top
  | [φ] => φ ctx
  | _ => cofs.foldl (fun acc c => .cof_and acc (c ctx)) .cof_top

/-- Boundary cofibration: r=0 ∨ r=1 -/
def boundary (r : BuildM Expr) : BuildM Expr := fun ctx =>
  let rv := r ctx
  .cof_or (.cof_eq rv .dim0) (.cof_eq rv .dim1)

/-! ## Type Builders -/

/-- Universe type -/
def univ : BuildM Expr := fun _ => .univ 0

/-- Nat type -/
def nat : BuildM Expr := fun _ => .nat

/-- Circle type -/
def circle : BuildM Expr := fun _ => .circle

/-- Dimension type -/
def tp_dim : BuildM Expr := fun _ => .lit "𝕀"

/-- Cofibration type -/
def tp_cof : BuildM Expr := fun _ => .lit "𝔽"

/-! ## Value Builders -/

/-- Zero -/
def zero : BuildM Expr := fun _ => .zero

/-- Successor -/
def suc (n : BuildM Expr) : BuildM Expr := fun ctx => .suc (n ctx)

/-- Natural number literal -/
def natLit (n : Nat) : BuildM Expr := fun _ =>
  let rec go : Nat → Expr
    | 0 => .zero
    | n + 1 => .suc (go n)
  go n

/-- Circle base point -/
def base : BuildM Expr := fun _ => .base

/-- Circle loop -/
def loop (r : BuildM Expr) : BuildM Expr := fun ctx => .loop (r ctx)

/-! ## Pair and Subtype Builders -/

/-- Build a pair -/
def pair (a b : BuildM Expr) : BuildM Expr := fun ctx =>
  .pair (a ctx) (b ctx)

/-- Subtype intro -/
def subIn (t : BuildM Expr) : BuildM Expr := fun ctx =>
  .subIn (t ctx)

/-- Subtype elimination -/
def subOut (t : BuildM Expr) : BuildM Expr := fun ctx =>
  .subOut (t ctx)

/-- Proof term for cofibration -/
def prf : BuildM Expr := fun _ => .lit "prf"

/-! ## Kan Operations -/

/-- Coercion along a line of types -/
def coe (line : BuildM Expr) (r s : BuildM Expr) (t : BuildM Expr) : BuildM Expr := fun ctx =>
  .coe (line ctx) (r ctx) (s ctx) (t ctx)

/-- Homogeneous composition -/
def hcom (tp : BuildM Expr) (r s : BuildM Expr) (φ : BuildM Expr) (u : BuildM Expr) : BuildM Expr := fun ctx =>
  .hcom (tp ctx) (r ctx) (s ctx) (φ ctx) (u ctx)

/-- Composition (derived) -/
def com (line : BuildM Expr) (r s : BuildM Expr) (φ : BuildM Expr) (u : BuildM Expr) : BuildM Expr := fun ctx =>
  -- com A r s φ u = coe A r s (hcom (A s) r s φ (λ i → coe A i s (u i)))
  let a := line ctx
  let rv := r ctx
  let sv := s ctx
  let phiv := φ ctx
  let uv := u ctx
  -- Simplified: just use the core syntax
  .coe a rv sv (.hcom (.app a sv) rv sv phiv uv)

/-! ## Split/Case -/

/-- Cofibration split -/
def cof_split (branches : List (BuildM Expr × BuildM Expr)) : BuildM Expr := fun ctx =>
  let bs := branches.map fun (φ, t) => (φ ctx, t ctx)
  .lit s!"cof-split({bs.length})"  -- Placeholder

/-! ## V Type Builders -/

/-- V type introduction -/
def v (r : BuildM Expr) (a b : BuildM Expr) (e : BuildM Expr) : BuildM Expr := fun ctx =>
  .vtype (r ctx) (a ctx) (b ctx) (e ctx)

/-- Vin constructor -/
def vIn (r : BuildM Expr) (part : BuildM Expr) (tot : BuildM Expr) : BuildM Expr := fun ctx =>
  .vin (r ctx) (part ctx) (tot ctx)

/-- Vproj elimination -/
def vProj (r : BuildM Expr) (a b : BuildM Expr) (e : BuildM Expr) (v : BuildM Expr) : BuildM Expr := fun ctx =>
  .vproj (r ctx) (a ctx) (b ctx) (e ctx) (v ctx)

/-! ## El (Universe Decode) -/

/-- Decode a universe code -/
def el (code : BuildM Expr) : BuildM Expr := fun ctx =>
  .app (.lit "El") (code ctx)

/-! ## Running Builders -/

/-- Run a builder and get the resulting term -/
def build (b : BuildM Expr) : Expr := b BuildCtx.empty

/-- Run a builder at a given level -/
def buildAt (level : Nat) (b : BuildM Expr) : Expr :=
  b { level }

/-! ## Helper Combinators -/

/-- Build a term from a pure expression -/
def const (e : Expr) : BuildM Expr := fun _ => e

/-- Sequence of lambdas -/
def lams (n : Nat) (k : List Expr → BuildM Expr) : BuildM Expr :=
  let rec go (i : Nat) (acc : List Expr) : BuildM Expr :=
    if i >= n then k acc.reverse
    else lam fun x => go (i + 1) (x :: acc)
  go 0 []

/-- Sequence of pis -/
def pis (doms : List (BuildM Expr)) (k : List Expr → BuildM Expr) : BuildM Expr :=
  let rec go (ds : List (BuildM Expr)) (acc : List Expr) : BuildM Expr :=
    match ds with
    | [] => k acc.reverse
    | d :: rest => pi d fun x => go rest (x :: acc)
  go doms []

end Lego.Cubical.TermBuilder
