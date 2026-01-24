/-
  Lego.Cubical.Elaborate: Bidirectional elaboration from surface to core

  Elaboration bridges surface syntax with names to core IR with de Bruijn.
  Key features:
  - Bidirectional type checking (infer/check modes)
  - Implicit argument insertion via meta-variables
  - Hole filling for incomplete terms
  - Name resolution and scope management

  Mathematical structure:
  - Elaboration as a partial function: Surface × Ctx → Core × Type
  - Bidirectionality: splitting elaboration into infer (↑) and check (↓)
  - Implicit arguments via unification constraints

  Based on redtt's Elaborator.ml
-/

import Lego.Cubical.Core
import Lego.Cubical.GlobalEnv
import Lego.Cubical.Unify
import Lego.Cubical.Quote
import Lego.Cubical.Datatype

namespace Lego.Cubical.Elaborate

open Lego.Core
open Lego.Cubical
open Lego.Cubical.Datatype

/-! ## Surface Syntax

    Surface terms use names and support implicit arguments.
-/

/-- Surface term with names -/
inductive Surface where
  | var    : String → Surface                           -- Named variable
  | lit    : String → Surface                           -- Literal
  | lam    : String → Surface → Surface                 -- λx. body
  | app    : Surface → Surface → Surface                -- f x
  | appImpl : Surface → Surface → Surface               -- f {x} (implicit)
  | pi     : String → Surface → Surface → Surface       -- (x : A) → B
  | piImpl : String → Surface → Surface → Surface       -- {x : A} → B (implicit Pi)
  | sigma  : String → Surface → Surface → Surface       -- (x : A) × B
  | pair   : Surface → Surface → Surface                -- (a, b)
  | fst    : Surface → Surface                          -- π₁
  | snd    : Surface → Surface                          -- π₂
  | letIn  : String → Surface → Surface → Surface → Surface  -- let x : A = v in body
  | univ   : Nat → Surface                              -- Type^n
  | hole   : Option String → Surface                    -- _ or ?name
  | ann    : Surface → Surface → Surface                -- (t : A)
  -- Cubical
  | dim0   : Surface                                    -- 0
  | dim1   : Surface                                    -- 1
  | path   : Surface → Surface → Surface → Surface      -- Path A a b
  | plam   : String → Surface → Surface                 -- λi. body (path lambda)
  | papp   : Surface → Surface → Surface                -- p @ r
  | refl   : Surface → Surface                          -- refl a
  -- Datatypes
  | data   : String → List Surface → Surface            -- D params
  | intro  : String → String → List Surface → Surface   -- C args (constructor)
  | elim   : Surface → Surface → List (String × List String × Surface) → Surface  -- elim scrut with mot | clauses
  deriving Repr, BEq, Inhabited

/-! ## Meta-Variable Tracking

    Simple meta-variable context for elaboration.
-/

/-- Meta-variable info -/
structure MetaEntry where
  ty : Expr
  solution : Option Expr := none
  deriving Repr, Inhabited

/-- Meta-variable context (id → info) -/
abbrev MetaCtx := Std.HashMap Nat MetaEntry

/-! ## Elaboration Context

    Tracks local bindings and their types during elaboration.
-/

/-- Local binding info -/
structure LocalBinding where
  name : String
  ty : Expr              -- Type in core
  isDim : Bool := false  -- Is this a dimension variable?
  deriving Repr, Inhabited

/-- Elaboration context -/
structure ElabCtx where
  locals : List LocalBinding := []
  global : GlobalEnv := GlobalEnv.empty
  metaCtx : MetaCtx := Std.HashMap.emptyWithCapacity
  nextMeta : Nat := 0

instance : Inhabited ElabCtx where
  default := { locals := [], global := GlobalEnv.empty, metaCtx := Std.HashMap.emptyWithCapacity, nextMeta := 0 }

namespace ElabCtx

/-- Empty context with globals -/
def withGlobals (env : GlobalEnv) : ElabCtx :=
  { locals := [], global := env, metaCtx := Std.HashMap.emptyWithCapacity, nextMeta := 0 }

/-- Extend with a local binding -/
def extend (ctx : ElabCtx) (name : String) (ty : Expr) : ElabCtx :=
  { ctx with locals := { name := name, ty := ty } :: ctx.locals }

/-- Extend with a dimension variable -/
def extendDim (ctx : ElabCtx) (name : String) : ElabCtx :=
  { ctx with locals := { name := name, ty := .lit "𝕀", isDim := true } :: ctx.locals }

/-- Lookup a local variable by name, return de Bruijn index -/
def lookupLocal (ctx : ElabCtx) (name : String) : Option (Nat × Expr) :=
  let rec go (bindings : List LocalBinding) (idx : Nat) : Option (Nat × Expr) :=
    match bindings with
    | [] => none
    | b :: bs =>
      if b.name == name then some (idx, b.ty)
      else go bs (idx + 1)
  go ctx.locals 0

/-- Number of local bindings -/
def depth (ctx : ElabCtx) : Nat := ctx.locals.length

/-- Create a fresh meta-variable -/
def freshMeta (ctx : ElabCtx) (ty : Expr) : ElabCtx × Expr :=
  let metaId := ctx.nextMeta
  let entry : MetaEntry := { ty := ty, solution := none }
  let newCtx := { ctx with
    nextMeta := ctx.nextMeta + 1
    metaCtx := ctx.metaCtx.insert metaId entry
  }
  (newCtx, Expr.lit s!"meta.{metaId}")

end ElabCtx

/-! ## Elaboration Monad

    Tracks context, can fail, and accumulates constraints.
-/

/-- Elaboration result -/
abbrev ElabM := StateT ElabCtx (Except String)

/-- Run elaboration -/
def runElab (ctx : ElabCtx) (m : ElabM α) : Except String (α × ElabCtx) :=
  m.run ctx

/-- Get current context -/
def getCtx : ElabM ElabCtx := get

/-- Modify context -/
def modifyCtx (f : ElabCtx → ElabCtx) : ElabM Unit := modify f

/-- Fail with error -/
def elabError (msg : String) : ElabM α := throw msg

/-- Lookup local variable -/
def lookupVar (name : String) : ElabM (Option (Nat × Expr)) := do
  let ctx ← getCtx
  return ctx.lookupLocal name

/-- Extend context with binding -/
def withBinding (name : String) (ty : Expr) (m : ElabM α) : ElabM α := do
  modifyCtx (·.extend name ty)
  let result ← m
  modifyCtx fun ctx => { ctx with locals := ctx.locals.tail! }
  return result

/-- Extend context with multiple bindings -/
def withBindings (bindings : List (String × Expr)) (m : ElabM α) : ElabM α := do
  match bindings with
  | [] => m
  | (name, ty) :: rest =>
    withBinding name ty (withBindings rest m)

/-- Extend context with dimension -/
def withDim (name : String) (m : ElabM α) : ElabM α := do
  modifyCtx (·.extendDim name)
  let result ← m
  modifyCtx fun ctx => { ctx with locals := ctx.locals.tail! }
  return result

/-- Create fresh meta -/
def freshMeta (ty : Expr) : ElabM Expr := do
  let ctx ← getCtx
  let (newCtx, metaExpr) := ctx.freshMeta ty
  set newCtx
  return metaExpr

/-! ## Bidirectional Elaboration

    Two modes:
    - infer: given term, produce type
    - check: given term and expected type, check compatibility
-/

mutual
/-- Infer mode: elaborate and return type -/
partial def infer (s : Surface) : ElabM (Expr × Expr) := do
  match s with
  | .var name => do
    match ← lookupVar name with
    | some (idx, ty) =>
      -- Shift type to current context depth
      return (.ix idx, ty)
    | none =>
      -- Try global lookup
      let ctx ← getCtx
      match ctx.global.lookupType (GName.named name) with
      | some ty => return (.lit name, ty)
      | none => elabError s!"Unknown variable: {name}"

  | .lit s => return (.lit s, .univ .zero)  -- Literals are opaque

  | .univ n => return (.univ (.ofNat n), .univ (.ofNat (n + 1)))

  | .pi x dom cod => do
    let (domCore, domTy) ← infer dom
    let (codCore, codTy) ← withBinding x domCore (infer cod)
    -- Pi type: if dom : Type^i and cod : Type^j, then Pi : Type^max(i,j)
    let level := match (domTy, codTy) with
      | (.univ i, .univ j) => Level.max i j
      | _ => Level.zero  -- Fallback
    return (.pi domCore codCore, .univ level)

  | .sigma x dom cod => do
    let (domCore, domTy) ← infer dom
    let (codCore, codTy) ← withBinding x domCore (infer cod)
    let level := match (domTy, codTy) with
      | (.univ i, .univ j) => Level.max i j
      | _ => Level.zero
    return (.sigma domCore codCore, .univ level)

  | .ann tm ty => do
    let (tyCore, _) ← infer ty
    let tmCore ← check tm tyCore
    return (tmCore, tyCore)

  | .app f x => do
    let (fCore, fTy) ← infer f
    match fTy with
    | .pi dom cod =>
      let xCore ← check x dom
      let resultTy := Expr.subst 0 xCore cod
      return (.app fCore xCore, resultTy)
    | _ => elabError s!"Expected function type, got {fTy}"

  | .fst p => do
    let (pCore, pTy) ← infer p
    match pTy with
    | .sigma dom _ => return (.fst pCore, dom)
    | _ => elabError "Expected sigma type for fst"

  | .snd p => do
    let (pCore, pTy) ← infer p
    match pTy with
    | .sigma _ cod =>
      let fstVal := Expr.fst pCore
      let resultTy := Expr.subst 0 fstVal cod
      return (.snd pCore, resultTy)
    | _ => elabError "Expected sigma type for snd"

  | .pair a b => do
    let (aCore, aTy) ← infer a
    let (bCore, bTy) ← infer b
    -- Infer non-dependent sigma
    let sigTy := Expr.sigma aTy (Expr.shiftN 1 bTy)
    return (.pair aCore bCore, sigTy)

  | .papp p r => do
    let (pCore, pTy) ← infer p
    match pTy with
    | .path tyLine _a __b =>
      let (rCore, _) ← infer r
      -- At endpoints: r=0 → a, r=1 → b
      return (.papp pCore rCore, tyLine)
    | _ => elabError "Expected path type for @"

  | .refl a => do
    let (aCore, aTy) ← infer a
    let pathTy := Expr.path aTy aCore aCore
    return (.refl aCore, pathTy)

  | .hole _name => do
    -- Create a meta for the type, then the term
    let typeMeta ← freshMeta (.univ .zero)
    let termMeta ← freshMeta typeMeta
    return (termMeta, typeMeta)

  | .dim0 => return (.dim0, .lit "𝕀")
  | .dim1 => return (.dim1, .lit "𝕀")

  | .path tyS a b => do
    let (tyCore, tyTy) ← infer tyS
    let (aCore, _) ← infer a
    let (bCore, _) ← infer b
    let level := match tyTy with
      | .univ l => l
      | _ => Level.zero
    return (.path tyCore aCore bCore, .univ level)

  | .data dlbl params => do
    let paramsCore ← params.mapM (fun p => do let (c, _) ← infer p; return c)
    let dataTy := mkData dlbl paramsCore
    let ctx ← getCtx
    match ctx.global.lookupDatatype (GName.named dlbl) with
    | some desc => return (dataTy, .univ desc.level)
    | none => return (dataTy, .univ .zero)  -- Assume level 0 if not found

  | .intro dlbl clbl args => do
    let ctx ← getCtx
    -- Look up datatype descriptor
    match ctx.global.lookupDatatype (GName.named dlbl) with
    | some desc =>
      -- Find the constructor
      match desc.constrs.find? (·.name == clbl) with
      | some constr =>
        -- Check args match constructor arity
        if args.length != constr.args.length then
          elabError s!"Constructor {clbl} expects {constr.args.length} args, got {args.length}"
        else do
          -- Elaborate args with expected types from constructor signature
          let mut argsCore : List Expr := []
          let mut argIdx := 0
          for (argS, (_, spec)) in args.zip constr.args do
            match spec with
            | .const ty =>
              -- Non-recursive arg: check against declared type
              let argCore ← check argS ty
              argsCore := argsCore ++ [argCore]
            | .recursive =>
              -- Recursive arg: check against the datatype itself
              let argCore ← check argS (mkData dlbl (desc.params.map Prod.snd))
              argsCore := argsCore ++ [argCore]
            | .dim =>
              -- Dimension arg: infer and expect dimension
              let (argCore, _) ← infer argS
              argsCore := argsCore ++ [argCore]
            argIdx := argIdx + 1
          -- Build intro expression with datatype params
          let params := desc.params.map Prod.snd
          let introExpr := mkIntro dlbl clbl params argsCore
          let resultTy := mkData dlbl params
          return (introExpr, resultTy)
      | none =>
        elabError s!"Constructor {clbl} not found in datatype {dlbl}"
    | none =>
      -- Datatype not registered - fall back to simple inference
      let argsCore ← args.mapM (fun a => do let (c, _) ← infer a; return c)
      let introExpr := mkIntro dlbl clbl [] argsCore
      let resultTy := mkData dlbl []
      return (introExpr, resultTy)

  | _ => elabError s!"Cannot infer type for: {repr s}"

/-- Check mode: elaborate against expected type -/
partial def check (s : Surface) (expected : Expr) : ElabM Expr := do
  match s, expected with
  -- Lambda checks against Pi
  | .lam x body, .pi dom cod => do
    let bodyCore ← withBinding x dom do
      check body cod
    return .lam bodyCore

  -- Path lambda checks against Path
  | .plam i body, .path tyLine _ _ => do
    let bodyCore ← withDim i do
      check body tyLine
    return .plam bodyCore

  -- Pair checks against Sigma
  | .pair a b, .sigma dom cod => do
    let aCore ← check a dom
    let codSubst := Expr.subst 0 aCore cod
    let bCore ← check b codSubst
    return .pair aCore bCore

  -- Let binding
  | .letIn x tyS val body, expected => do
    let (tyCore, _) ← infer tyS
    let valCore ← check val tyCore
    let bodyCore ← withBinding x tyCore do
      check body expected
    return .letE tyCore valCore bodyCore

  -- Hole: create meta of expected type
  | .hole _, expected => do
    freshMeta expected

  -- Refl checks against Path
  | .refl a, .path tyLine lhs rhs => do
    let aCore ← check a tyLine
    -- Check that endpoints are convertible: lhs ≡ aCore and rhs ≡ aCore
    let aVal := Expr.eval aCore
    let lhsVal := Expr.eval lhs
    let rhsVal := Expr.eval rhs
    if !conv aVal lhsVal then
      elabError s!"refl endpoint mismatch: expected {lhs}, got {aCore}"
    else if !conv aVal rhsVal then
      elabError s!"refl endpoint mismatch: expected {rhs}, got {aCore}"
    else
      return .refl aCore

  -- Elim checks by inferring scrutinee
  | .elim scrut mot clauses, _expected => do
    let (scrutCore, scrutTy) ← infer scrut
    let (motCore, _) ← infer mot
    let ctx ← getCtx
    -- Get datatype info for looking up constructor arg types
    let dataInfo := isData scrutTy
    -- Build clauses with binders in scope
    let clausesCore ← clauses.mapM fun (clbl, binders, body) => do
      -- Look up constructor arg types from datatype if available
      let argTypes : List Expr ← match dataInfo with
        | some (dlbl, params) =>
          match ctx.global.lookupDatatype (GName.named dlbl) with
          | some desc =>
            match desc.constrs.find? (·.name == clbl) with
            | some constr =>
              -- Get types from constructor signature
              pure <| constr.args.map fun (_, spec) =>
                match spec with
                | .const ty => ty
                | .recursive => mkData dlbl params
                | .dim => .lit "𝕀"
            | none => pure <| binders.map (fun _ => .univ .zero)  -- fallback
          | none => pure <| binders.map (fun _ => .univ .zero)  -- fallback
        | none => pure <| binders.map (fun _ => .univ .zero)  -- fallback
      -- Extend context with binders
      let bodyCore ← withBindings (binders.zip argTypes) do
        let (c, _) ← infer body
        pure c
      return { clbl := clbl, body := bodyCore : ElimClause }
    -- Get datatype label from scrutTy
    match dataInfo with
    | some (dlbl, params) =>
      return mkElim dlbl params motCore clausesCore scrutCore
    | none => elabError "Elim scrutinee must be a datatype"

  -- Fall back to infer + convert
  | s, expected => do
    let (core, inferred) ← infer s
    -- Check convertibility
    if conv inferred expected then
      return core
    else
      elabError s!"Type mismatch: expected {expected}, got {inferred}"
end

/-! ## Conversion Checking

    Check if two types are definitionally equal.
-/

/-- Simple conversion check (structural equality after normalization) -/
def conv (t1 t2 : Expr) : Bool :=
  let t1' := Expr.normalize 100 t1
  let t2' := Expr.normalize 100 t2
  t1' == t2'

/-! ## Top-Level Elaboration -/

/-- Elaborate a surface term in check mode -/
def elaborate (env : GlobalEnv) (s : Surface) (ty : Expr) : Except String Expr := do
  let ctx := ElabCtx.withGlobals env
  let (result, _) ← runElab ctx (check s ty)
  return result

/-- Elaborate and infer type -/
def elaborateInfer (env : GlobalEnv) (s : Surface) : Except String (Expr × Expr) := do
  let ctx := ElabCtx.withGlobals env
  let (result, _) ← runElab ctx (infer s)
  return result

/-! ## Type Elaboration (chk_tp)

    Check that a surface term is a valid type.
    Returns the elaborated type and its universe level.
-/

/-- Check that a surface term is a valid type -/
def checkType (s : Surface) : ElabM (Expr × Level) := do
  let (tyCore, tyTy) ← infer s
  match tyTy with
  | .univ level => return (tyCore, level)
  | _ => elabError s!"Expected a type, got {tyTy}"

/-- Check type with expected universe level -/
def checkTypeAtLevel (s : Surface) (expected : Level) : ElabM Expr := do
  let (tyCore, level) ← checkType s
  -- Check universe level compatibility
  if Level.leq level expected then
    return tyCore
  else
    elabError s!"Universe level mismatch: expected ≤ {expected}, got {level}"

/-! ## Telescopic Elaboration (chk_tp_in_tele)

    Elaborate types inside a telescope, threading context through.
-/

/-- Telescope entry for elaboration -/
structure TeleEntry where
  name : String
  surface : Surface
  deriving Repr, Inhabited

/-- Elaborate a telescope of types -/
def checkTelescope (entries : List TeleEntry) : ElabM (List (String × Expr)) := do
  entries.foldlM (init := []) fun acc entry => do
    let (tyCore, _) ← checkType entry.surface
    let result := acc ++ [(entry.name, tyCore)]
    -- Extend context for subsequent entries
    modifyCtx (·.extend entry.name tyCore)
    return result

/-- Elaborate a type in a telescope context -/
def checkTypeInTele (tele : List TeleEntry) (s : Surface) : ElabM (List (String × Expr) × Expr) := do
  let teleCore ← checkTelescope tele
  let (tyCore, _) ← checkType s
  return (teleCore, tyCore)

/-- Build Pi type from telescope -/
def teleToPi (tele : List (String × Expr)) (cod : Expr) : Expr :=
  tele.foldr (fun (_, dom) acc => .pi dom acc) cod

/-! ## Extended Surface Syntax (Cubical)

    Additional surface constructors for cubical features.
-/

/-- Extended surface syntax with full cubical constructs -/
inductive SurfaceExt where
  | base     : Surface → SurfaceExt                    -- Embed basic surface
  -- Cofibrations
  | cof_eq   : SurfaceExt → SurfaceExt → SurfaceExt    -- r = s
  | cof_and  : SurfaceExt → SurfaceExt → SurfaceExt    -- φ ∧ ψ
  | cof_or   : SurfaceExt → SurfaceExt → SurfaceExt    -- φ ∨ ψ
  | cof_top  : SurfaceExt                              -- ⊤
  | cof_bot  : SurfaceExt                              -- ⊥
  | boundary : SurfaceExt → SurfaceExt                 -- ∂r = (r = 0) ∨ (r = 1)
  -- Kan operations
  | coe      : SurfaceExt → SurfaceExt → SurfaceExt → SurfaceExt → SurfaceExt  -- coe r r' (λi.A) a
  | hcom     : SurfaceExt → SurfaceExt → SurfaceExt → SurfaceExt → SurfaceExt → SurfaceExt  -- hcom r r' A φ cap
  | com      : SurfaceExt → SurfaceExt → SurfaceExt → List (SurfaceExt × SurfaceExt) → SurfaceExt → SurfaceExt  -- com r r' (λi.A) sys cap
  -- V-types
  | vtype    : SurfaceExt → SurfaceExt → SurfaceExt → SurfaceExt → SurfaceExt  -- V r A B equiv
  | vin      : SurfaceExt → SurfaceExt → SurfaceExt → SurfaceExt               -- vin r a b
  | vproj    : SurfaceExt → SurfaceExt → SurfaceExt                            -- vproj r v
  -- Extension types
  | ext      : Nat → SurfaceExt → SurfaceExt → SurfaceExt → SurfaceExt          -- ext n fam cof bdry
  | extLam   : Nat → SurfaceExt → SurfaceExt                                    -- extLam n body
  | extApp   : SurfaceExt → List SurfaceExt → SurfaceExt                        -- extApp e dims
  -- Sub types
  | sub      : SurfaceExt → SurfaceExt → SurfaceExt → SurfaceExt               -- sub A φ t
  | subIn    : SurfaceExt → SurfaceExt                                         -- subIn e
  | subOut   : SurfaceExt → SurfaceExt                                         -- subOut e
  deriving Repr, Inhabited

mutual
/-- Convert extended surface to core expression (checking mode) -/
partial def checkExt (s : SurfaceExt) (expected : Expr) : ElabM Expr := do
  match s with
  | .base surf => check surf expected

  | .cof_eq r s => do
    let rCore ← checkExt r (.lit "𝕀")
    let sCore ← checkExt s (.lit "𝕀")
    return .cof_eq rCore sCore

  | .cof_and φ ψ => do
    let φCore ← checkExt φ (.lit "𝔽")
    let ψCore ← checkExt ψ (.lit "𝔽")
    return .cof_and φCore ψCore

  | .cof_or φ ψ => do
    let φCore ← checkExt φ (.lit "𝔽")
    let ψCore ← checkExt ψ (.lit "𝔽")
    return .cof_or φCore ψCore

  | .cof_top => return .cof_top
  | .cof_bot => return .cof_bot

  | .boundary r => do
    let rCore ← checkExt r (.lit "𝕀")
    return .cof_or (.cof_eq rCore .dim0) (.cof_eq rCore .dim1)

  | .coe rS r'S famS aS => do
    let rCore ← checkExt rS (.lit "𝕀")
    let r'Core ← checkExt r'S (.lit "𝕀")
    let (famCore, _) ← inferExt famS  -- λi. A, produces type family
    let aCore ← checkExt aS expected  -- Simplified: should be fam @ r
    return .coe famCore rCore r'Core aCore

  | .hcom rS r'S tyS φS capS => do
    let rCore ← checkExt rS (.lit "𝕀")
    let r'Core ← checkExt r'S (.lit "𝕀")
    let tyCore ← checkExt tyS (.univ 0)
    let φCore ← checkExt φS (.lit "𝔽")
    let capCore ← checkExt capS tyCore
    return .hcom rCore r'Core tyCore φCore capCore

  | .com rS r'S famS sysS capS => do
    let rCore ← checkExt rS (.lit "𝕀")
    let r'Core ← checkExt r'S (.lit "𝕀")
    let (famCore, _) ← inferExt famS
    let sysCore ← sysS.mapM fun (φ, t) => do
      let φCore ← checkExt φ (.lit "𝔽")
      let (tCore, _) ← inferExt t
      pure (φCore, tCore)
    let (capCore, _) ← inferExt capS
    return .com rCore r'Core famCore sysCore capCore

  | .vtype rS aS bS equivS => do
    let rCore ← checkExt rS (.lit "𝕀")
    let aCore ← checkExt aS (.univ 0)
    let bCore ← checkExt bS (.univ 0)
    let (equivCore, _) ← inferExt equivS
    return Expr.vtype rCore aCore bCore equivCore

  | .vin rS aS bS =>
    match expected with
    | .vtype _ tyA tyB _ => do
      let rCore ← checkExt rS (.lit "𝕀")
      let aCore ← checkExt aS tyA
      let bCore ← checkExt bS tyB
      return .vin rCore aCore bCore
    | _ => elabError "Expected V-type for vin"

  | .vproj rS vS => do
    let rCore ← checkExt rS (.lit "𝕀")
    let (vCore, vTy) ← inferExt vS
    match vTy with
    | .vtype _ tyA tyB equiv =>
      return .vproj rCore tyA tyB equiv vCore
    | _ => elabError "Expected V-type for vproj"

  | .ext n famS cofS bdryS => do
    let (famCore, _) ← inferExt famS
    let cofCore ← checkExt cofS (.lit "𝔽")
    let (bdryCore, _) ← inferExt bdryS
    return Expr.ext n famCore cofCore bdryCore

  | .extLam n bodyS =>
    match expected with
    | .ext m fam _cof _bdry =>
      if n == m then do
        let bodyCore ← checkExt bodyS fam
        return .extLam n bodyCore
      else elabError s!"Dimension mismatch: expected {m}, got {n}"
    | _ => elabError "Expected extension type for extLam"

  | .extApp eS dimsS => do
    let (eCore, eTy) ← inferExt eS
    match eTy with
    | .ext n _fam _cof _bdry =>
      if dimsS.length == n then do
        let dimsCore ← dimsS.mapM fun d => checkExt d (.lit "𝕀")
        return .extApp eCore dimsCore
      else elabError s!"Wrong number of dimension arguments"
    | _ => elabError "Expected extension type for extApp"

  | .sub aS φS tS => do
    let aCore ← checkExt aS (.univ 0)
    let φCore ← checkExt φS (.lit "𝔽")
    let tCore ← checkExt tS aCore
    return Expr.sub aCore φCore tCore

  | .subIn eS =>
    match expected with
    | .sub a _φ _t => do
      let eCore ← checkExt eS a
      return .subIn eCore
    | _ => elabError "Expected sub type for subIn"

  | .subOut eS => do
    let (eCore, eTy) ← inferExt eS
    match eTy with
    | .sub _a _φ _t => return .subOut eCore
    | _ => elabError "Expected sub type for subOut"

/-- Infer mode for extended surface -/
partial def inferExt (s : SurfaceExt) : ElabM (Expr × Expr) := do
  match s with
  | .base surf => infer surf
  | .cof_top => return (.cof_top, .lit "𝔽")
  | .cof_bot => return (.cof_bot, .lit "𝔽")
  | .cof_eq r s' => do
    let rCore ← checkExt r (.lit "𝕀")
    let sCore ← checkExt s' (.lit "𝕀")
    return (.cof_eq rCore sCore, .lit "𝔽")
  | .cof_and φ ψ => do
    let φCore ← checkExt φ (.lit "𝔽")
    let ψCore ← checkExt ψ (.lit "𝔽")
    return (.cof_and φCore ψCore, .lit "𝔽")
  | .cof_or φ ψ => do
    let φCore ← checkExt φ (.lit "𝔽")
    let ψCore ← checkExt ψ (.lit "𝔽")
    return (.cof_or φCore ψCore, .lit "𝔽")
  | .boundary r => do
    let rCore ← checkExt r (.lit "𝕀")
    return (.cof_or (.cof_eq rCore .dim0) (.cof_eq rCore .dim1), .lit "𝔽")
  | .vtype rS aS bS equivS => do
    let rCore ← checkExt rS (.lit "𝕀")
    let (aCore, aTy) ← inferExt aS
    let (bCore, _) ← inferExt bS
    let (equivCore, _) ← inferExt equivS
    let level := match aTy with
      | .univ l => l
      | _ => Level.zero
    return (Expr.vtype rCore aCore bCore equivCore, .univ level)
  | .ext n famS cofS bdryS => do
    let (famCore, famTy) ← inferExt famS
    let cofCore ← checkExt cofS (.lit "𝔽")
    let (bdryCore, _) ← inferExt bdryS
    let level := match famTy with
      | .univ l => l
      | _ => Level.zero
    return (Expr.ext n famCore cofCore bdryCore, .univ level)
  | .sub aS φS tS => do
    let (aCore, aTy) ← inferExt aS
    let φCore ← checkExt φS (.lit "𝔽")
    let tCore ← checkExt tS aCore
    return (Expr.sub aCore φCore tCore, aTy)
  | _ => elabError s!"Cannot infer type for extended surface term"
end

/-! ## Convenience: Parse-like Surface Constructors -/

/-- Build a function type from a list of bindings -/
def mkPi (bindings : List (String × Surface)) (cod : Surface) : Surface :=
  bindings.foldr (fun (x, ty) acc => .pi x ty acc) cod

/-- Build a lambda from a list of parameters -/
def mkLam (params : List String) (body : Surface) : Surface :=
  params.foldr .lam body

/-- Build nested applications -/
def mkApps (f : Surface) (args : List Surface) : Surface :=
  args.foldl .app f

/-! ## Examples -/

/-- Surface term for identity function: λx. x -/
def idSurface : Surface := .lam "x" (.var "x")

/-- Surface term for identity type: (A : Type) → A → A -/
def idTypeSurface : Surface :=
  .pi "A" (.univ 0) (.pi "x" (.var "A") (.var "A"))

/-- Surface term for const: λx. λy. x -/
def constSurface : Surface := .lam "x" (.lam "y" (.var "x"))

/-- Surface term for flip: λf. λx. λy. f y x -/
def flipSurface : Surface :=
  .lam "f" (.lam "x" (.lam "y" (.app (.app (.var "f") (.var "y")) (.var "x"))))

/-- Surface nat zero -/
def zeroSurface : Surface := .intro "Nat" "zero" []

/-- Surface nat suc -/
def sucSurface (n : Surface) : Surface := .intro "Nat" "suc" [n]

/-- Surface nat 2 -/
def twoSurface : Surface := sucSurface (sucSurface zeroSurface)

end Lego.Cubical.Elaborate
