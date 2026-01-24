/-
  Lego.Cubical.GlobalEnv: Global Environment for definitions and datatypes

  The global environment holds:
  - Type definitions: `def name : Type := value`
  - Datatype declarations: `data Name : Type where ...`
  - Dimension variables (for cubical operations)
  - Meta-variables (for unification)

  Mathematical structure:
  - The global env forms a category of contexts
  - Definitions are morphisms (substitutions)
  - Datatypes are inductive types in the initial algebra

  Based on redtt's GlobalEnv.ml
-/

import Lego.Algebra
import Lego.Cubical.Core
import Lego.Cubical.Visitor
import Std.Data.HashMap

namespace Lego.Cubical

open Lego.Core

/-! ## Names

    Global names with optional source location.
    Uses strings for simplicity (redtt uses abstract Name.t)
-/

/-- A global name with optional metadata -/
structure GName where
  name : String
  source : Option String := none  -- file/location info
  deriving Repr, BEq, Hashable, Inhabited

instance : ToString GName where
  toString n := n.name

namespace GName

def fresh (base : String) (counter : Nat) : GName :=
  { name := s!"{base}_{counter}" }

def named (s : String) : GName := { name := s }

def anonymous : GName := { name := "_" }

end GName

/-! ## Datatype Descriptors

    Description of an inductive datatype:
    - Parameters (e.g., `List (A : Type)`)
    - Constructors with their argument telescopes
    - Boundary constraints (for HITs)
-/

/-- Argument specification in a constructor telescope -/
inductive GArgSpec where
  | const : Expr → GArgSpec          -- A constant type argument
  | recursive : GArgSpec             -- Recursive occurrence (Self)
  | dim   : GArgSpec                  -- Dimension argument (for HITs)
  deriving Repr, BEq

/-- A constructor definition -/
structure GConstructor where
  name : String
  args : List (String × GArgSpec)    -- Named arguments
  boundary : List (Expr × Expr)      -- [(cofib, term)] for HITs
  deriving Repr

/-- A datatype descriptor -/
structure GDataDesc where
  name : GName
  params : List (String × Expr)      -- Type parameters
  level : Level                       -- Universe level
  constrs : List GConstructor         -- Constructors
  deriving Repr

/-! ## Global Environment Entries -/

/-- Entry types in the global environment -/
inductive GEntry where
  | param : Expr → GEntry                       -- Type parameter (postulated)
  | defn  : Expr → Expr → GEntry                -- Definition: (type, value)
  | datatype : GDataDesc → GEntry               -- Inductive datatype
  | dimVar : GEntry                             -- Dimension variable
  | metaVar : Expr → Option Expr → GEntry       -- Meta-variable: (type, solution?)
  deriving Repr

/-! ## Global Environment -/

/-- The global environment -/
structure GlobalEnv where
  entries : Std.HashMap GName GEntry
  insertOrder : List GName  -- Track insertion order for printing

instance : Inhabited GlobalEnv where
  default := { entries := {}, insertOrder := [] }

namespace GlobalEnv

/-- Empty environment -/
def empty : GlobalEnv := { entries := {}, insertOrder := [] }

/-- Extend environment with a new entry -/
def extend (env : GlobalEnv) (nm : GName) (entry : GEntry) : GlobalEnv :=
  { entries := env.entries.insert nm entry
    insertOrder := nm :: env.insertOrder }

/-- Define a new term -/
def define (env : GlobalEnv) (nm : GName) (ty : Expr) (tm : Expr) : GlobalEnv :=
  env.extend nm (GEntry.defn ty tm)

/-- Declare a type parameter (axiom/postulate) -/
def declareParam (env : GlobalEnv) (nm : GName) (ty : Expr) : GlobalEnv :=
  env.extend nm (GEntry.param ty)

/-- Declare a dimension variable -/
def declareDim (env : GlobalEnv) (nm : GName) : GlobalEnv :=
  env.extend nm GEntry.dimVar

/-- Declare a datatype -/
def declareDatatype (env : GlobalEnv) (desc : GDataDesc) : GlobalEnv :=
  env.extend desc.name (GEntry.datatype desc)

/-- Create a meta-variable -/
def createMeta (env : GlobalEnv) (nm : GName) (ty : Expr) : GlobalEnv :=
  env.extend nm (GEntry.metaVar ty none)

/-- Solve a meta-variable -/
def solveMeta (env : GlobalEnv) (nm : GName) (solution : Expr) : GlobalEnv :=
  match env.entries[nm]? with
  | some (GEntry.metaVar ty _) =>
    { env with entries := env.entries.insert nm (GEntry.metaVar ty (some solution)) }
  | _ => env  -- Silently ignore if not a meta

/-- Lookup an entry -/
def lookup (env : GlobalEnv) (nm : GName) : Option GEntry :=
  env.entries[nm]?

/-- Lookup the type of an entry -/
def lookupType (env : GlobalEnv) (nm : GName) : Option Expr :=
  match env.entries[nm]? with
  | some (GEntry.param ty) => some ty
  | some (GEntry.defn ty _) => some ty
  | some (GEntry.datatype desc) => some (.univ desc.level)
  | some GEntry.dimVar => some (.lit "𝕀")
  | some (GEntry.metaVar ty _) => some ty
  | none => none

/-- Lookup type and optional value -/
def lookupWithValue (env : GlobalEnv) (nm : GName) : Option (Expr × Option Expr) :=
  match env.entries[nm]? with
  | some (GEntry.param ty) => some (ty, none)
  | some (GEntry.defn ty tm) => some (ty, some tm)
  | some (GEntry.datatype desc) => some (.univ desc.level, none)
  | some GEntry.dimVar => some (.lit "𝕀", none)
  | some (GEntry.metaVar ty sol) => some (ty, sol)
  | none => none

/-- Lookup a datatype descriptor -/
def lookupDatatype (env : GlobalEnv) (nm : GName) : Option GDataDesc :=
  match env.entries[nm]? with
  | some (GEntry.datatype desc) => some desc
  | _ => none

/-- Check if a name is defined -/
def isDefined (env : GlobalEnv) (nm : GName) : Bool :=
  env.entries.contains nm

/-- Get all dimension variables -/
def getDimVars (env : GlobalEnv) : List GName :=
  env.insertOrder.filter fun nm =>
    match env.entries[nm]? with
    | some GEntry.dimVar => true
    | _ => false

/-- Get all unsolved meta-variables -/
def getUnsolvedMetas (env : GlobalEnv) : List (GName × Expr) :=
  env.insertOrder.filterMap fun nm =>
    match env.entries[nm]? with
    | some (GEntry.metaVar ty none) => some (nm, ty)
    | _ => none

/-- Pretty print the environment -/
def toString (env : GlobalEnv) : String :=
  let entries := env.insertOrder.reverse.filterMap fun nm =>
    match env.entries[nm]? with
    | some (GEntry.param ty) => some s!"{nm} : {Expr.toString ty}"
    | some (GEntry.defn ty tm) => some s!"{nm} : {Expr.toString ty} := {Expr.toString tm}"
    | some (GEntry.datatype desc) => some s!"data {desc.name}"
    | some GEntry.dimVar => some s!"{nm} : 𝕀"
    | some (GEntry.metaVar ty none) => some s!"?{nm} : {Expr.toString ty}"
    | some (GEntry.metaVar ty (some sol)) => some s!"?{nm} : {Expr.toString ty} := {Expr.toString sol}"
    | none => none
  String.intercalate "\n" entries

instance : ToString GlobalEnv where
  toString := GlobalEnv.toString

end GlobalEnv

/-! ## Extended Typing Context

    Combines global environment with local context for type checking.
-/

/-- Combined typing context -/
structure TypingCtx where
  global : GlobalEnv
  local_ : Ctx              -- Local de Bruijn context
  dimCtx : List GName       -- Dimension variables in scope

instance : Inhabited TypingCtx where
  default := { global := default, local_ := [], dimCtx := [] }

namespace TypingCtx

/-- Empty context -/
def empty : TypingCtx :=
  { global := GlobalEnv.empty
    local_ := []
    dimCtx := [] }

/-- With a global environment -/
def withGlobal (env : GlobalEnv) : TypingCtx :=
  { global := env
    local_ := []
    dimCtx := [] }

/-- Extend local context with a type binding -/
def extendLocal (ctx : TypingCtx) (ty : Expr) : TypingCtx :=
  { ctx with local_ := ty :: ctx.local_ }

/-- Extend with a dimension variable -/
def extendDim (ctx : TypingCtx) (nm : GName) : TypingCtx :=
  { ctx with dimCtx := nm :: ctx.dimCtx }

/-- Lookup a local variable by de Bruijn index -/
def lookupLocal (ctx : TypingCtx) (idx : Nat) : Option Expr :=
  ctx.local_[idx]?

/-- Lookup a global name -/
def lookupGlobal (ctx : TypingCtx) (nm : GName) : Option GEntry :=
  ctx.global.lookup nm

/-- Local context depth -/
def depth (ctx : TypingCtx) : Nat := ctx.local_.length

end TypingCtx

/-! ## Evaluation with Global Definitions

    Extend the evaluator to unfold global definitions.
-/

/-- Unfold a global definition if present -/
def unfoldGlobal (env : GlobalEnv) (nm : GName) : Option Expr :=
  match env.lookupWithValue nm with
  | some (_, some tm) => some tm
  | _ => none

/-- Get the head literal of an application spine -/
private def getHeadLit : Expr → Option String
  | .lit name => some name
  | .app f _ => getHeadLit f
  | _ => none

/-- Unfold head literal in an expression if it's a global -/
private def unfoldHead (env : GlobalEnv) : Expr → Option Expr
  | .lit name => unfoldGlobal env (GName.named name)
  | .app f a =>
    match unfoldHead env f with
    | some f' => some (.app f' a)
    | none => none
  | _ => none

/-- Step with global unfolding -/
def stepWithGlobals (env : GlobalEnv) (e : Expr) : Option Expr :=
  -- First try visitor-based whnf step
  match e.whnfStep Expr.subst (fun d body => Expr.subst 0 d body) with
  | some e' => some e'
  | none =>
    -- Try to unfold a global at the head
    unfoldHead env e

/-- Normalize with global unfolding using visitor-based whnf -/
def normalizeWithGlobals (env : GlobalEnv) (fuel : Nat) (e : Expr) : Expr :=
  match fuel with
  | 0 => e
  | n + 1 =>
    match stepWithGlobals env e with
    | some e' => normalizeWithGlobals env n e'
    | none => e

/-- Evaluate with global definitions -/
def evalWithGlobals (env : GlobalEnv) (e : Expr) : Expr :=
  normalizeWithGlobals env 1000 e

/-! ## Type Checking with Global Environment -/

/-- Extended type checking result -/
inductive TCResultG (α : Type) where
  | ok : α → TCResultG α
  | error : TypeError → TCResultG α
  | unsolvedMeta : GName → Expr → TCResultG α  -- Meta needs solving

namespace TCResultG

def pure (a : α) : TCResultG α := ok a

def bind (x : TCResultG α) (f : α → TCResultG β) : TCResultG β :=
  match x with
  | ok a => f a
  | error e => error e
  | unsolvedMeta nm ty => unsolvedMeta nm ty

instance : Monad TCResultG where
  pure := pure
  bind := bind

end TCResultG

mutual

/-- Infer type in extended context -/
partial def inferG (ctx : TypingCtx) : Expr → TCResultG Expr
  -- Variable: try local first, then global
  | .ix n =>
    match ctx.lookupLocal n with
    | some ty => .ok (Expr.shiftN (n + 1) ty)
    | none => .error (.unbound n)

  -- Literal: might be a global reference
  | .lit name =>
    match ctx.global.lookupType (GName.named name) with
    | some ty => .ok ty
    | none => .ok (.lit name)  -- Unknown literal

  -- Universe
  | .univ n => .ok (.univ (.suc n))

  -- Pi type
  | .pi dom cod => do
    let domTy ← inferG ctx dom
    match evalWithGlobals ctx.global domTy with
    | .univ i =>
      let codTy ← inferG (ctx.extendLocal dom) cod
      match evalWithGlobals ctx.global codTy with
      | .univ j => .ok (.univ (Level.normalize (.max i j)))
      | _ => .error (.notType cod)
    | _ => .error (.notType dom)

  -- Sigma type
  | .sigma dom cod => do
    let domTy ← inferG ctx dom
    match evalWithGlobals ctx.global domTy with
    | .univ i =>
      let codTy ← inferG (ctx.extendLocal dom) cod
      match evalWithGlobals ctx.global codTy with
      | .univ j => .ok (.univ (Level.normalize (.max i j)))
      | _ => .error (.notType cod)
    | _ => .error (.notType dom)

  -- Application
  | .app f a => do
    let fTy ← inferG ctx f
    match evalWithGlobals ctx.global fTy with
    | .pi dom cod =>
      let _ ← checkG ctx a dom
      .ok (Expr.subst0 a cod)
    | ty => .error (.notFunction (.app f a) ty)

  -- Projections
  | .fst p => do
    let pTy ← inferG ctx p
    match evalWithGlobals ctx.global pTy with
    | .sigma dom _ => .ok dom
    | ty => .error (.notPair (.fst p) ty)

  | .snd p => do
    let pTy ← inferG ctx p
    match evalWithGlobals ctx.global pTy with
    | .sigma _ cod => .ok (Expr.subst0 (.fst p) cod)
    | ty => .error (.notPair (.snd p) ty)

  -- Path type
  | .path ty a b => do
    let tyTy ← inferG ctx ty
    match evalWithGlobals ctx.global tyTy with
    | .univ n =>
      let _ ← checkG ctx a ty
      let _ ← checkG ctx b ty
      .ok (.univ n)
    | _ => .error (.notType ty)

  -- Path application
  | .papp p _ => do
    let pTy ← inferG ctx p
    match evalWithGlobals ctx.global pTy with
    | .path ty _ _ => .ok ty
    | ty => .error (.notPath (.papp p .dim0) ty)

  -- Refl
  | .refl a => do
    let aTy ← inferG ctx a
    .ok (.path aTy a a)

  -- Coe
  | .coe _ r' ty _ =>
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

  -- Nat
  | .nat => .ok (.univ .zero)
  | .zero => .ok .nat
  | .suc n => do
    let _ ← checkG ctx n .nat
    .ok .nat

  -- Circle
  | .circle => .ok (.univ .zero)
  | .base => .ok .circle
  | .loop _ => .ok .circle

  -- Let
  | .letE ty val body => do
    let _ ← checkG ctx val ty
    inferG (ctx.extendLocal ty) body

  -- Can't infer
  | e@(.lam _) => .error (.cannotInfer e)
  | e@(.pair _ _) => .error (.cannotInfer e)
  | e@(.plam _) => .error (.cannotInfer e)

  -- HCom
  | .hcom _ _ ty _ cap => do
    let _ ← checkG ctx cap ty
    .ok ty

  -- HComTube
  | .hcomTube _ _ ty _ cap => do
    let _ ← checkG ctx cap ty
    .ok ty

  -- Com
  | .com _ r' ty _ _ =>
    .ok (Expr.subst0 r' ty)

  -- GHCom
  | .ghcom _ _ ty _ cap => do
    let _ ← checkG ctx cap ty
    .ok ty

  -- GCom
  | .gcom _ r' ty _ _ =>
    .ok (Expr.subst0 r' ty)

  -- FHCom
  | .fhcom _ _ _ _ => .ok (.univ .zero)

  -- Box
  | .boxEl r r' cap sysList => .ok (.fhcom r r' cap sysList)

  -- Cap
  | .capEl _ _ ty _ el => do
    let _ ← inferG ctx el
    .ok ty

  -- Nat/Circle eliminators
  | .natElim p _ _ n => .ok (.app p n)
  | .circleElim p _ _ x => .ok (.app p x)

  -- Extension types
  | .ext _ _ _ _ => .ok (.univ .zero)  -- ext n fam cof bdry : Type
  | e@(.extLam _ _) => .error (.cannotInfer e)  -- needs annotation
  | .extApp e dims => do
    let eTy ← inferG ctx e
    match evalWithGlobals ctx.global eTy with
    | .ext n fam _ _ =>
      if dims.length == n then
        -- Substitute dimensions into family
        let result := dims.foldl (init := fam) fun acc dim => Expr.subst0 dim acc
        .ok result
      else
        .error (.cannotInfer (.extApp e dims))
    | _ => .error (.cannotInfer (.extApp e dims))

  -- Sub types
  | .sub _ _ _ => .ok (.univ .zero)  -- sub A φ t : Type
  | e@(.subIn _) => .error (.cannotInfer e)  -- needs annotation
  | .subOut e => do
    let eTy ← inferG ctx e
    match evalWithGlobals ctx.global eTy with
    | .sub ty _ _ => .ok ty
    | _ => .error (.cannotInfer (.subOut e))

  -- V-types
  | .vtype _ _ _ _ => .ok (.univ .zero)
  | .vin _ _ b => inferG ctx b
  | .vproj _ _ b _ _ => .ok b

  -- Systems
  | .sys ((_, tm) :: _) => inferG ctx tm
  | .sys [] => .error (.cannotInfer (.sys []))

/-- Check type in extended context -/
partial def checkG (ctx : TypingCtx) (e : Expr) (expected : Expr) : TCResultG Unit := do
  match e with
  | .lam body =>
    match evalWithGlobals ctx.global expected with
    | .pi dom cod =>
      checkG (ctx.extendLocal dom) body cod
    | _ => .error (.notFunction e expected)

  | .pair a b =>
    match evalWithGlobals ctx.global expected with
    | .sigma dom cod =>
      let _ ← checkG ctx a dom
      checkG ctx b (Expr.subst0 a cod)
    | _ => .error (.notPair e expected)

  | .plam body =>
    match evalWithGlobals ctx.global expected with
    | .path ty lhs rhs =>
      let _ ← inferG (ctx.extendLocal ty) body
      let body0 := evalWithGlobals ctx.global (Expr.subst0 .dim0 body)
      let body1 := evalWithGlobals ctx.global (Expr.subst0 .dim1 body)
      if !conv body0 lhs then
        .error (.pathBoundaryMismatch body lhs body0)
      else if !conv body1 rhs then
        .error (.pathBoundaryMismatch body rhs body1)
      else
        .ok ()
    | _ => .error (.notPath e expected)

  | .extLam n body =>
    match evalWithGlobals ctx.global expected with
    | .ext m _fam _cof _bdry =>
      if n == m then
        -- Check body (simplified: just infer type)
        let _ ← inferG ctx body
        .ok ()
      else
        .error (.mismatch e expected (.ext n _fam _cof _bdry))
    | _ => .error (.cannotInfer e)

  | .subIn elem =>
    match evalWithGlobals ctx.global expected with
    | .sub ty _cof _bdry =>
      -- Check element has base type
      checkG ctx elem ty
    | _ => .error (.cannotInfer e)

  | _ => do
    let inferred ← inferG ctx e
    let infNf := evalWithGlobals ctx.global inferred
    let expNf := evalWithGlobals ctx.global expected
    if conv infNf expNf then
      .ok ()
    else
      .error (.mismatch e expected inferred)

end -- mutual

/-! ## Standard Library Entries -/

/-- Create a standard library with basic definitions -/
def standardLib : GlobalEnv := Id.run do
  let mut env := GlobalEnv.empty

  -- Type : Type₁
  env := env.declareParam (GName.named "Type") (.univ (.suc .zero))

  -- Unit type
  env := env.declareParam (GName.named "Unit") (.univ .zero)
  env := env.declareParam (GName.named "tt") (.lit "Unit")

  -- Bool type
  env := env.declareParam (GName.named "Bool") (.univ .zero)
  env := env.declareParam (GName.named "true") (.lit "Bool")
  env := env.declareParam (GName.named "false") (.lit "Bool")

  -- Nat type (as parameter, not yet as data)
  env := env.declareParam (GName.named "Nat") (.univ .zero)

  -- Identity function
  -- id : (A : Type) → A → A
  -- id A x = x
  let idTy := Expr.pi (.univ .zero) (Expr.pi (.ix 0) (.ix 1))
  let idTm := Expr.lam (Expr.lam (.ix 0))
  env := env.define (GName.named "id") idTy idTm

  -- Const function
  -- const : (A B : Type) → A → B → A
  -- const A B x y = x
  let constTy := Expr.pi (.univ .zero) (Expr.pi (.univ .zero) (Expr.pi (.ix 1) (Expr.pi (.ix 1) (.ix 1))))
  let constTm := Expr.lam (Expr.lam (Expr.lam (Expr.lam (.ix 1))))
  env := env.define (GName.named "const") constTy constTm

  return env

end Lego.Cubical
