/-
  Lego.Cubical.Conversion: Equality and Subtyping Checking

  Mathematical Structure:
  - Definitional equality via normalization
  - Type-directed equality checking
  - Cofibration-aware comparison under restrictions

  Based on cooltt's Conversion.ml module.

  Key insight from cooltt:
  "Conversion checking works by first normalizing both sides to WHNF,
   then comparing structurally. For types like Pi and Sigma, we compare
   under binders. For neutral terms, we compare the head and spine."

  This module provides:
  - Type equality: equate_tp
  - Term equality: equate_con
  - Dimension equality: equate_dim
  - Cofibration equality: equate_cof
  - Neutral term equality: equate_cut
-/

import Cubical.Core
import Cubical.Cofibration
import Cubical.Visitor

namespace Lego.Cubical.Conversion

open Lego.Core
open Lego.Core.Expr
open Cofibration

/-! ## Conversion Result Type

    Conversion can succeed, fail, or be blocked on a meta.
-/

inductive ConvResult where
  | ok : ConvResult
  | fail : String → ConvResult
  | blocked : Nat → ConvResult  -- Blocked on meta variable
  deriving Repr, BEq, Inhabited

namespace ConvResult

def isOk : ConvResult → Bool
  | ok => true
  | _ => false

def andThen (r1 : ConvResult) (r2 : Unit → ConvResult) : ConvResult :=
  match r1 with
  | ok => r2 ()
  | fail msg => fail msg
  | blocked n => blocked n

end ConvResult

/-! ## Conversion Context

    Tracks the current cofibration context and size for de Bruijn.
-/

structure ConvCtx where
  /-- Current size (number of bound variables) -/
  size : Nat
  /-- Current cofibration assumptions -/
  cof : Expr
  deriving Repr

namespace ConvCtx

def empty : ConvCtx := { size := 0, cof := Expr.cof_top }

def extend (ctx : ConvCtx) : ConvCtx :=
  { ctx with size := ctx.size + 1 }

def assume (ctx : ConvCtx) (φ : Expr) : ConvCtx :=
  { ctx with cof := Expr.cof_and ctx.cof φ }

end ConvCtx

/-! ## Weak Head Normal Form

    Reduce to weak head normal form for comparison.
    Uses visitor-based whnf from Visitor.lean.
-/

/-- Check if an expression is in weak head normal form -/
def isWhnf (e : Expr) : Bool :=
  (e.whnfStep Expr.subst (fun d body => Expr.subst 0 d body)).isNone

/-- Reduce to weak head normal form -/
def whnf (fuel : Nat) (e : Expr) : Expr :=
  e.whnf' fuel Expr.subst (fun d body => Expr.subst 0 d body)

/-- Default fuel for WHNF computation -/
def defaultFuel : Nat := 1000

/-! ## Dimension Equality

    Dimensions are equal if they normalize to the same value.
-/

/-- Check if two dimensions are equal -/
def equate_dim (_ctx : ConvCtx) (r1 r2 : Expr) : ConvResult :=
  let r1' := whnf defaultFuel r1
  let r2' := whnf defaultFuel r2
  if r1' == r2' then ConvResult.ok
  else
    -- Check if equal under current cofibration
    match r1', r2' with
    | .dim0, .dim0 => ConvResult.ok
    | .dim1, .dim1 => ConvResult.ok
    | .ix n1, .ix n2 => if n1 == n2 then ConvResult.ok
                        else ConvResult.fail s!"dimensions differ: {n1} vs {n2}"
    | _, _ => ConvResult.fail s!"dimensions not equal: {repr r1'} vs {repr r2'}"

/-! ## Type, Term, Cofibration, and Neutral Equality

    Types are equal if they have the same structure after normalization.
    Terms are equal if they have the same normal form at a given type.
    Cofibrations are equal if they are logically equivalent.
    Note: equate_tp, equate_con, equate_cof and equate_neutral are mutually recursive.
-/

mutual

/-- Check if two cofibrations are equal -/
partial def equate_cof (ctx : ConvCtx) (φ1 φ2 : Expr) : ConvResult :=
  let φ1' := whnf defaultFuel φ1
  let φ2' := whnf defaultFuel φ2
  if φ1' == φ2' then ConvResult.ok
  else
    -- Structural comparison
    match φ1', φ2' with
    | .cof_top, .cof_top => ConvResult.ok
    | .cof_bot, .cof_bot => ConvResult.ok
    | .cof_eq r1 s1, .cof_eq r2 s2 =>
      match equate_dim ctx r1 r2, equate_dim ctx s1 s2 with
      | .ok, .ok => ConvResult.ok
      | .fail msg, _ => ConvResult.fail msg
      | _, .fail msg => ConvResult.fail msg
      | .blocked n, _ => ConvResult.blocked n
      | _, .blocked n => ConvResult.blocked n
    | .cof_and φ1a φ1b, .cof_and φ2a φ2b =>
      match equate_cof ctx φ1a φ2a with
      | .ok => equate_cof ctx φ1b φ2b
      | r => r
    | .cof_or φ1a φ1b, .cof_or φ2a φ2b =>
      match equate_cof ctx φ1a φ2a with
      | .ok => equate_cof ctx φ1b φ2b
      | r => r
    | _, _ => ConvResult.fail s!"cofibrations not equal: {repr φ1'} vs {repr φ2'}"

/-- Check if two types are equal -/
partial def equate_tp (ctx : ConvCtx) (tp1 tp2 : Expr) : ConvResult :=
  let tp1' := whnf defaultFuel tp1
  let tp2' := whnf defaultFuel tp2
  if tp1' == tp2' then ConvResult.ok
  else
    match tp1', tp2' with
    -- Base types
    | .nat, .nat => ConvResult.ok
    | .circle, .circle => ConvResult.ok
    | .univ n1, .univ n2 => if n1 == n2 then ConvResult.ok
                           else ConvResult.fail s!"universe levels differ: {n1} vs {n2}"

    -- Dimension and cofibration types
    | .lit "𝕀", .lit "𝕀" => ConvResult.ok
    | .lit "𝔽", .lit "𝔽" => ConvResult.ok

    -- Pi types
    | .pi dom1 cod1, .pi dom2 cod2 =>
      match equate_tp ctx dom1 dom2 with
      | .ok =>
        let ctx' := ctx.extend
        equate_tp ctx' cod1 cod2
      | r => r

    -- Sigma types
    | .sigma a1 b1, .sigma a2 b2 =>
      match equate_tp ctx a1 a2 with
      | .ok =>
        let ctx' := ctx.extend
        equate_tp ctx' b1 b2
      | r => r

    -- Path types
    | .path a1 l1 r1, .path a2 l2 r2 =>
      match equate_tp ctx a1 a2 with
      | .ok =>
        match equate_con ctx a1 l1 l2 with
        | .ok => equate_con ctx a1 r1 r2
        | r => r
      | r => r

    -- Sub types
    | .sub a1 φ1 t1, .sub a2 φ2 t2 =>
      match equate_tp ctx a1 a2 with
      | .ok =>
        match equate_cof ctx φ1 φ2 with
        | .ok =>
          let ctx' := ctx.assume φ1
          equate_con ctx' a1 t1 t2
        | r => r
      | r => r

    -- V types
    | .vtype r1 a1 b1 e1, .vtype r2 a2 b2 e2 =>
      match equate_dim ctx r1 r2 with
      | .ok =>
        match equate_tp ctx a1 a2 with
        | .ok =>
          match equate_tp ctx b1 b2 with
          | .ok => equate_con ctx (Expr.lit "Equiv") e1 e2  -- Simplified equiv type
          | r => r
        | r => r
      | r => r

    -- Literals (for now, just check equality)
    | .lit s1, .lit s2 => if s1 == s2 then ConvResult.ok
                          else ConvResult.fail s!"type literals differ: {s1} vs {s2}"

    | _, _ => ConvResult.fail s!"types not equal: {repr tp1'} vs {repr tp2'}"

/-- Check if two terms are equal at a type -/
partial def equate_con (ctx : ConvCtx) (tp : Expr) (t1 t2 : Expr) : ConvResult :=
  let t1' := whnf defaultFuel t1
  let t2' := whnf defaultFuel t2
  if t1' == t2' then ConvResult.ok
  else
    let tp' := whnf defaultFuel tp
    match tp' with
    -- Pi types: compare under abstraction
    | .pi _dom cod =>
      let ctx' := ctx.extend
      let var := Expr.ix 0
      let app1 := Expr.app (shift t1') var
      let app2 := Expr.app (shift t2') var
      equate_con ctx' cod app1 app2

    -- Sigma types: compare components
    | .sigma a b =>
      let fst1 := Expr.fst t1'
      let fst2 := Expr.fst t2'
      match equate_con ctx a fst1 fst2 with
      | .ok =>
        let snd1 := Expr.snd t1'
        let snd2 := Expr.snd t2'
        let b' := subst 0 fst1 b
        equate_con ctx b' snd1 snd2
      | r => r

    -- Path types: compare at fresh dimension
    | .path a _ _ =>
      let ctx' := ctx.extend
      let var := Expr.ix 0
      let papp1 := Expr.papp (shift t1') var
      let papp2 := Expr.papp (shift t2') var
      equate_con ctx' a papp1 papp2

    -- Sub types: compare base
    | .sub a _ _ =>
      let out1 := Expr.subOut t1'
      let out2 := Expr.subOut t2'
      equate_con ctx a out1 out2

    -- Nat: structural comparison
    | .nat =>
      match t1', t2' with
      | .zero, .zero => ConvResult.ok
      | .suc n1, .suc n2 => equate_con ctx .nat n1 n2
      | _, _ => equate_neutral ctx t1' t2'

    -- Circle: structural comparison
    | .circle =>
      match t1', t2' with
      | .base, .base => ConvResult.ok
      | .loop r1, .loop r2 => equate_dim ctx r1 r2
      | _, _ => equate_neutral ctx t1' t2'

    -- Dimension type
    | .lit "𝕀" => equate_dim ctx t1' t2'

    -- Cofibration type
    | .lit "𝔽" => equate_cof ctx t1' t2'

    -- Universe: compare as types
    | .univ _ => equate_tp ctx t1' t2'

    -- Default: neutral comparison
    | _ => equate_neutral ctx t1' t2'

/-- Check if two neutral terms are equal -/
partial def equate_neutral (ctx : ConvCtx) (t1 t2 : Expr) : ConvResult :=
  match t1, t2 with
  -- Variables
  | .ix n1, .ix n2 => if n1 == n2 then ConvResult.ok
                      else ConvResult.fail s!"variables differ: {n1} vs {n2}"

  -- Application
  | .app f1 a1, .app f2 a2 =>
    match equate_neutral ctx f1 f2 with
    | .ok => equate_neutral ctx a1 a2  -- Simplified: should use inferred type
    | r => r

  -- Path application
  | .papp p1 r1, .papp p2 r2 =>
    match equate_neutral ctx p1 p2 with
    | .ok => equate_dim ctx r1 r2
    | r => r

  -- Projections
  | .fst p1, .fst p2 => equate_neutral ctx p1 p2
  | .snd p1, .snd p2 => equate_neutral ctx p1 p2

  -- Coe
  | .coe a1 r1 s1 t1, .coe a2 r2 s2 t2 =>
    match equate_neutral ctx a1 a2 with
    | .ok =>
      match equate_dim ctx r1 r2 with
      | .ok =>
        match equate_dim ctx s1 s2 with
        | .ok => equate_neutral ctx t1 t2
        | r => r
      | r => r
    | r => r

  -- HCom
  | .hcom a1 r1 s1 φ1 u1, .hcom a2 r2 s2 φ2 u2 =>
    match equate_neutral ctx a1 a2 with
    | .ok =>
      match equate_dim ctx r1 r2 with
      | .ok =>
        match equate_dim ctx s1 s2 with
        | .ok =>
          match equate_cof ctx φ1 φ2 with
          | .ok => equate_neutral ctx u1 u2
          | r => r
        | r => r
      | r => r
    | r => r

  -- Literals
  | .lit s1, .lit s2 => if s1 == s2 then ConvResult.ok
                        else ConvResult.fail s!"literals differ: {s1} vs {s2}"

  | _, _ => ConvResult.fail s!"neutral terms not equal: {repr t1} vs {repr t2}"

end  -- mutual

/-! ## Top-level Conversion Functions -/

/-- Check type equality -/
def checkTpEq (tp1 tp2 : Expr) : ConvResult :=
  equate_tp ConvCtx.empty tp1 tp2

/-- Check term equality at a type -/
def checkEq (tp t1 t2 : Expr) : ConvResult :=
  equate_con ConvCtx.empty tp t1 t2

/-- Check if t1 converts to t2 (subtyping) -/
def checkSubtype (tp1 tp2 : Expr) : ConvResult :=
  -- For now, just equality. Full subtyping would include universe cumulativity
  equate_tp ConvCtx.empty tp1 tp2

/-! ## Helpers for integration with tactics -/

/-- Convert ConvResult to Bool -/
def ConvResult.toBool : ConvResult → Bool
  | .ok => true
  | _ => false

/-- Check equality, returning Bool -/
def equal (tp t1 t2 : Expr) : Bool :=
  (checkEq tp t1 t2).toBool

/-- Check type equality, returning Bool -/
def equalTp (tp1 tp2 : Expr) : Bool :=
  (checkTpEq tp1 tp2).toBool

end Lego.Cubical.Conversion
