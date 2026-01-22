/-
  Lego.Cubical.RefineMonad: Elaboration/Refinement Monad

  Mathematical Structure:
  - Reader-State-Error monad for elaboration
  - Carries: global state, local environment, cofibration context

  Based on cooltt's RefineMonad.ml / Monads.ml architecture.

  This module provides the core monad used for:
  - Type checking and elaboration
  - Quotation of semantic values back to syntax
  - Constraint solving and unification
  - Error reporting with source locations

  Key insight from cooltt:
  "The refine monad provides access to both global state (definitions, holes)
   and local context (variables in scope, cofibration assumptions)."
-/

import Lego.Cubical.Core
import Lego.Cubical.Cofibration
import Lego.Cubical.Conversion

namespace Lego.Cubical.RefineMonad

open Lego.Core
open Lego.Core.Expr
open Cofibration
open Conversion

/-! ## Error Types -/

/-- Refinement error with location information -/
inductive RefineError where
  | unboundVariable : String → RefineError
  | expectedType : Expr → RefineError
  | typeMismatch : Expr → Expr → RefineError
  | expectedConnective : String → Expr → RefineError
  | conversionFailed : String → RefineError
  | unboundMeta : Nat → RefineError
  | other : String → RefineError
  deriving Repr, BEq

/-! ## Identifiers -/

/-- Identifier types: anonymous, user-defined, or machine-generated -/
inductive Ident where
  | anon : Ident
  | user : String → Ident
  | machine : String → Ident
  deriving Repr, BEq, Hashable, Inhabited

namespace Ident

def name : Ident → Option String
  | anon => none
  | user s => some s
  | machine s => some s

def toString : Ident → String
  | anon => "_"
  | user s => s
  | machine s => s

instance : ToString Ident := ⟨toString⟩

end Ident

/-! ## Local Environment -/

/-- A cell in the local environment: contains type and optional value -/
structure Cell where
  ident : Ident
  tp : Expr
  value : Option Expr := none
  deriving Repr

/-- Local environment for bound variables -/
structure LocalEnv where
  cells : Array Cell := #[]
  cofCtx : Expr := .cof_top  -- Current cofibration assumptions
  deriving Repr

namespace LocalEnv

def empty : LocalEnv := { cells := #[], cofCtx := .cof_top }

def size (env : LocalEnv) : Nat := env.cells.size

def extend (env : LocalEnv) (ident : Ident) (tp : Expr) (value : Option Expr := none) : LocalEnv :=
  { env with cells := env.cells.push { ident, tp, value } }

def getLocal (env : LocalEnv) (ix : Nat) : Option Cell :=
  if ix < env.cells.size then
    env.cells[env.cells.size - 1 - ix]?
  else none

def getLocalTp (env : LocalEnv) (ix : Nat) : Option Expr :=
  (env.getLocal ix).map Cell.tp

def resolve (env : LocalEnv) (name : String) : Option Nat :=
  -- Search from end to beginning (most recent first)
  let rec go (i : Nat) : Option Nat :=
    if i >= env.cells.size then none
    else
      let idx := env.cells.size - 1 - i
      match env.cells[idx]? with
      | some cell =>
        match cell.ident.name with
        | some n => if n == name then some i else go (i + 1)
        | none => go (i + 1)
      | none => none
  go 0

def assume (env : LocalEnv) (φ : Expr) : LocalEnv :=
  { env with cofCtx := .cof_and env.cofCtx φ }

end LocalEnv

/-! ## Global Environment -/

/-- A global definition -/
structure GlobalDef where
  name : String
  tp : Expr
  value : Option Expr  -- None for axioms/postulates
  deriving Repr

/-- Global state for refinement -/
structure GlobalEnv where
  defs : Array GlobalDef := #[]
  holes : Array (Nat × Expr × Option Expr) := #[]  -- (id, type, solution)
  nextHoleId : Nat := 0
  nextMetaId : Nat := 0
  deriving Repr

namespace GlobalEnv

def empty : GlobalEnv := {}

def addDef (env : GlobalEnv) (name : String) (tp : Expr) (value : Option Expr) : GlobalEnv :=
  { env with defs := env.defs.push { name, tp, value } }

def lookupDef (env : GlobalEnv) (name : String) : Option GlobalDef :=
  env.defs.find? (fun d => d.name == name)

def addHole (env : GlobalEnv) (tp : Expr) : GlobalEnv × Nat :=
  let id := env.nextHoleId
  ({ env with
     holes := env.holes.push (id, tp, none),
     nextHoleId := id + 1 }, id)

def freshMeta (env : GlobalEnv) : GlobalEnv × Nat :=
  let id := env.nextMetaId
  ({ env with nextMetaId := id + 1 }, id)

def solveHole (env : GlobalEnv) (id : Nat) (sol : Expr) : GlobalEnv :=
  let holes := env.holes.map fun (hid, tp, _) =>
    if hid == id then (hid, tp, some sol) else (hid, tp, none)
  { env with holes }

def getHoleSolution (env : GlobalEnv) (id : Nat) : Option Expr :=
  match env.holes.find? (fun (hid, _, _) => hid == id) with
  | some (_, _, sol) => sol
  | none => none

end GlobalEnv

/-! ## Refine Monad -/

/-- Source location for error reporting -/
structure SourceLoc where
  file : String := ""
  line : Nat := 0
  column : Nat := 0
  deriving Repr

/-- The refinement monad context -/
structure RefineCtx where
  localEnv : LocalEnv := {}
  location : Option SourceLoc := none
  deriving Repr

/-- The refinement monad state -/
structure RefineState where
  globalEnv : GlobalEnv := {}
  deriving Repr

/-- Result of refinement -/
inductive RefineResult (α : Type) where
  | ok : α → RefineState → RefineResult α
  | error : RefineError → Option SourceLoc → RefineResult α
  deriving Repr

/-- The refinement monad: Reader (ctx) + State (global) + Error -/
def RefineM (α : Type) : Type :=
  RefineCtx → RefineState → RefineResult α

namespace RefineM

def pure (a : α) : RefineM α := fun _ st => .ok a st

def bind (ma : RefineM α) (f : α → RefineM β) : RefineM β := fun ctx st =>
  match ma ctx st with
  | .ok a st' => f a ctx st'
  | .error e loc => .error e loc

instance : Monad RefineM where
  pure := pure
  bind := bind

instance : MonadExcept RefineError RefineM where
  throw e := fun ctx _ => .error e ctx.location
  tryCatch ma f := fun ctx st =>
    match ma ctx st with
    | .ok a st' => .ok a st'
    | .error e _ => f e ctx st

/-! ## Basic Operations -/

/-- Get the local environment -/
def getLocalEnv : RefineM LocalEnv := fun ctx st => .ok ctx.localEnv st

/-- Get the global environment -/
def getGlobalEnv : RefineM GlobalEnv := fun _ st => .ok st.globalEnv st

/-- Modify the global environment -/
def modifyGlobalEnv (f : GlobalEnv → GlobalEnv) : RefineM Unit := fun _ st =>
  .ok () { st with globalEnv := f st.globalEnv }

/-- Run with modified local context -/
def withLocalEnv (f : LocalEnv → LocalEnv) (ma : RefineM α) : RefineM α := fun ctx st =>
  ma { ctx with localEnv := f ctx.localEnv } st

/-- Run with updated location -/
def withLocation (loc : SourceLoc) (ma : RefineM α) : RefineM α := fun ctx st =>
  ma { ctx with location := some loc } st

/-- Throw an error -/
def refineError (e : RefineError) : RefineM α := throw e

/-! ## Variable Operations -/

/-- Extend the context with a new variable -/
def abstract (ident : Ident) (tp : Expr) (k : Expr → RefineM α) : RefineM α := fun ctx st =>
  let var := Expr.ix ctx.localEnv.size
  let newEnv := ctx.localEnv.extend ident tp none
  k var { ctx with localEnv := newEnv } st

/-- Get the type of a local variable by index -/
def getLocalTp (ix : Nat) : RefineM Expr := do
  let env ← getLocalEnv
  match env.getLocalTp ix with
  | some tp => pure tp
  | none => throw (.unboundVariable s!"index {ix}")

/-- Resolve a name to a local or global binding -/
def resolveName (name : String) : RefineM (Sum Nat GlobalDef) := do
  let localEnv ← getLocalEnv
  let localResult := localEnv.resolve name
  if h : localResult.isSome then
    return Sum.inl (localResult.get h)
  else
    let globalEnv ← getGlobalEnv
    let globalResult := globalEnv.lookupDef name
    if h2 : globalResult.isSome then
      return Sum.inr (globalResult.get h2)
    else
      throw (.unboundVariable name)

/-! ## Hole Operations -/

/-- Create a new hole.
    Returns (holeId, placeholder expression).
    The placeholder is a literal "?{id}" since Expr has no hole constructor. -/
def freshHole (tp : Expr) : RefineM (Nat × Expr) := do
  let env ← getGlobalEnv
  let (env', id) := env.addHole tp
  modifyGlobalEnv (fun _ => env')
  pure (id, .lit s!"?{id}")

/-- Create a fresh metavariable -/
def freshMeta : RefineM Nat := do
  let env ← getGlobalEnv
  let (env', id) := env.freshMeta
  modifyGlobalEnv (fun _ => env')
  pure id

/-- Solve a hole -/
def solveHole (id : Nat) (sol : Expr) : RefineM Unit :=
  modifyGlobalEnv (·.solveHole id sol)

/-- Get hole solution -/
def getHoleSolution (id : Nat) : RefineM (Option Expr) := do
  let env ← getGlobalEnv
  pure (env.getHoleSolution id)

/-! ## Global Definition Operations -/

/-- Add a global definition -/
def addGlobal (name : String) (tp : Expr) (value : Option Expr) : RefineM Unit :=
  modifyGlobalEnv (·.addDef name tp value)

/-- Lookup a global definition -/
def lookupGlobal (name : String) : RefineM (Option GlobalDef) := do
  let env ← getGlobalEnv
  pure (env.lookupDef name)

/-! ## Cofibration Operations -/

/-- Run under a cofibration assumption -/
def assume (φ : Expr) (ma : RefineM α) : RefineM α :=
  withLocalEnv (·.assume φ) ma

/-- Get current cofibration context -/
def getCofCtx : RefineM Expr := do
  let env ← getLocalEnv
  pure env.cofCtx

/-! ## Conversion/Equality -/

/-- Check type equality -/
def equateTp (tp1 tp2 : Expr) : RefineM Unit := do
  match Conversion.checkTpEq tp1 tp2 with
  | .ok => pure ()
  | .fail msg => throw (.conversionFailed msg)
  | .blocked n => throw (.unboundMeta n)

/-- Check term equality at a type -/
def equate (tp : Expr) (t1 t2 : Expr) : RefineM Unit := do
  match Conversion.checkEq tp t1 t2 with
  | .ok => pure ()
  | .fail msg => throw (.conversionFailed msg)
  | .blocked n => throw (.unboundMeta n)

/-! ## Running the Monad -/

/-- Run the refine monad with initial state -/
def run (ma : RefineM α) : RefineResult α :=
  ma {} {}

/-- Run the refine monad with initial context -/
def runWith (ctx : RefineCtx) (st : RefineState) (ma : RefineM α) : RefineResult α :=
  ma ctx st

/-- Convert result to Except -/
def toExcept (r : RefineResult α) : Except (RefineError × Option SourceLoc) (α × RefineState) :=
  match r with
  | .ok a st => .ok (a, st)
  | .error e loc => .error (e, loc)

end RefineM

/-! ## Quotation -/

/-- Quote context for normalization -/
structure QuoteCtx where
  size : Nat := 0
  normalize : Bool := true
  deriving Repr

/-- Quote a term back to syntax (identity for now) -/
def quote (_ctx : QuoteCtx) (e : Expr) : Expr := e

/-- Quote a type back to syntax -/
def quoteTp (ctx : QuoteCtx) (tp : Expr) : Expr := quote ctx tp

/-! ## Lift Operations -/

/-- Lift a conversion check into RefineM -/
def RefineM.liftConv (r : ConvResult) : RefineM Unit := do
  match r with
  | .ok => pure ()
  | .fail msg => throw (.conversionFailed msg)
  | .blocked n => throw (.unboundMeta n)

end Lego.Cubical.RefineMonad
