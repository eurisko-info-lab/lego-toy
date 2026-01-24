/-
  Lego.Cubical.Visitor: Visitor pattern for Expr traversal

  Design goals:
  1. Each Expr constructor encapsulates its own traversal logic
  2. Operations (shift, subst, freeIn) are defined generically
  3. Adding a new constructor requires only local changes

  Pattern:
  - ExprF: functor describing Expr's structure (children + reconstruction)
  - Visitor[Op]: type class for operation-specific behavior
  - traverse: generic traversal that composes them
-/

import Lego.Cubical.Core

open Lego.Core

namespace Lego.Core

/-! ## Visitor Monad

    A visitor carries:
    - State: current depth, environment
    - Operation: what to do at each node
-/

/-- Visitor state for traversal -/
structure VisitorState where
  depth : Nat := 0  -- Current binding depth
  deriving Repr

/-- Visitor monad: state + optional failure -/
abbrev VisitorM := StateT VisitorState Option

/-- Run a visitor computation -/
def runVisitor (m : VisitorM α) (depth : Nat := 0) : Option α :=
  (m.run { depth }).map Prod.fst

/-! ## Child Descriptor

    Each constructor describes its children and how they bind variables.
    This enables generic traversal without knowing all constructors.
-/

/-- How a child relates to binders -/
inductive BinderInfo where
  | none      : BinderInfo              -- Child doesn't go under binder
  | term (n : Nat) : BinderInfo         -- Goes under n term binders
  | dim (n : Nat) : BinderInfo          -- Goes under n dimension binders
  deriving Repr, BEq

/-- A child with its binding context -/
structure Child where
  expr : Expr
  binder : BinderInfo
  deriving Repr

/-- Children paired with a reconstruction function -/
structure ExprShape where
  children : List Child
  reconstruct : List Expr → Expr

/-! ## Shape Extraction

    Get the shape of an expression: its children and how to rebuild it.
    This is the "functor" view of Expr.
-/

/-- Extract shape from an expression -/
def Expr.shape : Expr → ExprShape
  -- Atomic (no children)
  | .ix n => ⟨[], fun _ => .ix n⟩
  | .lit s => ⟨[], fun _ => .lit s⟩
  | .dim0 => ⟨[], fun _ => .dim0⟩
  | .dim1 => ⟨[], fun _ => .dim1⟩
  | .dimVar n => ⟨[], fun _ => .dimVar n⟩
  | .cof_top => ⟨[], fun _ => .cof_top⟩
  | .cof_bot => ⟨[], fun _ => .cof_bot⟩
  | .nat => ⟨[], fun _ => .nat⟩
  | .zero => ⟨[], fun _ => .zero⟩
  | .circle => ⟨[], fun _ => .circle⟩
  | .base => ⟨[], fun _ => .base⟩
  | .univ n => ⟨[], fun _ => .univ n⟩

  -- Single child, no binder
  | .fst e => ⟨[⟨e, .none⟩], fun | [e'] => .fst e' | _ => .fst e⟩
  | .snd e => ⟨[⟨e, .none⟩], fun | [e'] => .snd e' | _ => .snd e⟩
  | .suc e => ⟨[⟨e, .none⟩], fun | [e'] => .suc e' | _ => .suc e⟩
  | .refl e => ⟨[⟨e, .none⟩], fun | [e'] => .refl e' | _ => .refl e⟩
  | .loop r => ⟨[⟨r, .none⟩], fun | [r'] => .loop r' | _ => .loop r⟩
  | .subIn e => ⟨[⟨e, .none⟩], fun | [e'] => .subIn e' | _ => .subIn e⟩
  | .subOut e => ⟨[⟨e, .none⟩], fun | [e'] => .subOut e' | _ => .subOut e⟩

  -- Single child, binds 1 term var
  | .lam body => ⟨[⟨body, .term 1⟩], fun | [b'] => .lam b' | _ => .lam body⟩
  -- Single child, binds 1 dim var
  | .plam body => ⟨[⟨body, .dim 1⟩], fun | [b'] => .plam b' | _ => .plam body⟩

  -- Two children, no binders
  | .app f x => ⟨[⟨f, .none⟩, ⟨x, .none⟩],
      fun | [f', x'] => .app f' x' | _ => .app f x⟩
  | .pair a b => ⟨[⟨a, .none⟩, ⟨b, .none⟩],
      fun | [a', b'] => .pair a' b' | _ => .pair a b⟩
  | .papp p r => ⟨[⟨p, .none⟩, ⟨r, .none⟩],
      fun | [p', r'] => .papp p' r' | _ => .papp p r⟩
  | .cof_eq r s => ⟨[⟨r, .none⟩, ⟨s, .none⟩],
      fun | [r', s'] => .cof_eq r' s' | _ => .cof_eq r s⟩
  | .cof_and φ ψ => ⟨[⟨φ, .none⟩, ⟨ψ, .none⟩],
      fun | [φ', ψ'] => .cof_and φ' ψ' | _ => .cof_and φ ψ⟩
  | .cof_or φ ψ => ⟨[⟨φ, .none⟩, ⟨ψ, .none⟩],
      fun | [φ', ψ'] => .cof_or φ' ψ' | _ => .cof_or φ ψ⟩

  -- Two children, second binds 1 term var (dependent types)
  | .pi dom cod => ⟨[⟨dom, .none⟩, ⟨cod, .term 1⟩],
      fun | [d', c'] => .pi d' c' | _ => .pi dom cod⟩
  | .sigma dom cod => ⟨[⟨dom, .none⟩, ⟨cod, .term 1⟩],
      fun | [d', c'] => .sigma d' c' | _ => .sigma dom cod⟩

  -- Three children
  | .path ty a b => ⟨[⟨ty, .none⟩, ⟨a, .none⟩, ⟨b, .none⟩],
      fun | [t', a', b'] => .path t' a' b' | _ => .path ty a b⟩
  | .letE ty v body => ⟨[⟨ty, .none⟩, ⟨v, .none⟩, ⟨body, .term 1⟩],
      fun | [t', v', b'] => .letE t' v' b' | _ => .letE ty v body⟩
  | .sub ty cof bdry => ⟨[⟨ty, .none⟩, ⟨cof, .none⟩, ⟨bdry, .term 1⟩],
      fun | [t', c', b'] => .sub t' c' b' | _ => .sub ty cof bdry⟩
  | .vin r a b => ⟨[⟨r, .none⟩, ⟨a, .none⟩, ⟨b, .none⟩],
      fun | [r', a', b'] => .vin r' a' b' | _ => .vin r a b⟩

  -- Four children
  | .coe r r' ty a => ⟨[⟨r, .none⟩, ⟨r', .none⟩, ⟨ty, .dim 1⟩, ⟨a, .none⟩],
      fun | [r1, r2, t', a'] => .coe r1 r2 t' a' | _ => .coe r r' ty a⟩
  | .vtype r a b equiv => ⟨[⟨r, .none⟩, ⟨a, .none⟩, ⟨b, .none⟩, ⟨equiv, .none⟩],
      fun | [r', a', b', e'] => .vtype r' a' b' e' | _ => .vtype r a b equiv⟩
  | .natElim p z s n => ⟨[⟨p, .none⟩, ⟨z, .none⟩, ⟨s, .term 2⟩, ⟨n, .none⟩],
      fun | [p', z', s', n'] => .natElim p' z' s' n' | _ => .natElim p z s n⟩
  | .circleElim p b l x => ⟨[⟨p, .none⟩, ⟨b, .none⟩, ⟨l, .dim 1⟩, ⟨x, .none⟩],
      fun | [p', b', l', x'] => .circleElim p' b' l' x' | _ => .circleElim p b l x⟩
  | .ext n fam cof bdry => ⟨[⟨fam, .dim n⟩, ⟨cof, .dim n⟩, ⟨bdry, .dim n⟩],
      fun | [f', c', b'] => .ext n f' c' b' | _ => .ext n fam cof bdry⟩

  -- Five children
  | .hcom r r' ty φ cap => ⟨[⟨r, .none⟩, ⟨r', .none⟩, ⟨ty, .none⟩, ⟨φ, .none⟩, ⟨cap, .none⟩],
      fun | [r1, r2, t', φ', c'] => .hcom r1 r2 t' φ' c' | _ => .hcom r r' ty φ cap⟩
  | .vproj r a b equiv v => ⟨[⟨r, .none⟩, ⟨a, .none⟩, ⟨b, .none⟩, ⟨equiv, .none⟩, ⟨v, .none⟩],
      fun | [r', a', b', e', v'] => .vproj r' a' b' e' v' | _ => .vproj r a b equiv v⟩

  -- Tube-based (with list of (cof, tube) pairs)
  | .hcomTube r r' ty tubes cap =>
    let tubeChildren := tubes.flatMap fun (φ, t) => [⟨φ, .none⟩, ⟨t, .dim 1⟩]
    let n := tubes.length
    ⟨[⟨r, .none⟩, ⟨r', .none⟩, ⟨ty, .none⟩] ++ tubeChildren ++ [⟨cap, .none⟩],
      fun args =>
        let r1 := args.getD 0 r
        let r2 := args.getD 1 r'
        let ty' := args.getD 2 ty
        let tubeArgs := args.drop 3 |>.take (2 * n)
        let tubes' := List.range n |>.map fun i =>
          (tubeArgs.getD (2*i) (tubes.getD i (.cof_top, cap)).1,
           tubeArgs.getD (2*i+1) (tubes.getD i (.cof_top, cap)).2)
        let cap' := args.getD (3 + 2*n) cap
        .hcomTube r1 r2 ty' tubes' cap'⟩

  | .com r r' ty tubes cap =>
    let tubeChildren := tubes.flatMap fun (φ, t) => [⟨φ, .none⟩, ⟨t, .dim 1⟩]
    let n := tubes.length
    ⟨[⟨r, .none⟩, ⟨r', .none⟩, ⟨ty, .dim 1⟩] ++ tubeChildren ++ [⟨cap, .none⟩],
      fun args =>
        let r1 := args.getD 0 r
        let r2 := args.getD 1 r'
        let ty' := args.getD 2 ty
        let tubeArgs := args.drop 3 |>.take (2 * n)
        let tubes' := List.range n |>.map fun i =>
          (tubeArgs.getD (2*i) (tubes.getD i (.cof_top, cap)).1,
           tubeArgs.getD (2*i+1) (tubes.getD i (.cof_top, cap)).2)
        let cap' := args.getD (3 + 2*n) cap
        .com r1 r2 ty' tubes' cap'⟩

  | .ghcom r r' ty tubes cap =>
    let tubeChildren := tubes.flatMap fun (φ, t) => [⟨φ, .none⟩, ⟨t, .dim 1⟩]
    let n := tubes.length
    ⟨[⟨r, .none⟩, ⟨r', .none⟩, ⟨ty, .none⟩] ++ tubeChildren ++ [⟨cap, .none⟩],
      fun args =>
        let r1 := args.getD 0 r
        let r2 := args.getD 1 r'
        let ty' := args.getD 2 ty
        let tubeArgs := args.drop 3 |>.take (2 * n)
        let tubes' := List.range n |>.map fun i =>
          (tubeArgs.getD (2*i) (tubes.getD i (.cof_top, cap)).1,
           tubeArgs.getD (2*i+1) (tubes.getD i (.cof_top, cap)).2)
        let cap' := args.getD (3 + 2*n) cap
        .ghcom r1 r2 ty' tubes' cap'⟩

  | .gcom r r' ty tubes cap =>
    let tubeChildren := tubes.flatMap fun (φ, t) => [⟨φ, .none⟩, ⟨t, .dim 1⟩]
    let n := tubes.length
    ⟨[⟨r, .none⟩, ⟨r', .none⟩, ⟨ty, .dim 1⟩] ++ tubeChildren ++ [⟨cap, .none⟩],
      fun args =>
        let r1 := args.getD 0 r
        let r2 := args.getD 1 r'
        let ty' := args.getD 2 ty
        let tubeArgs := args.drop 3 |>.take (2 * n)
        let tubes' := List.range n |>.map fun i =>
          (tubeArgs.getD (2*i) (tubes.getD i (.cof_top, cap)).1,
           tubeArgs.getD (2*i+1) (tubes.getD i (.cof_top, cap)).2)
        let cap' := args.getD (3 + 2*n) cap
        .gcom r1 r2 ty' tubes' cap'⟩

  | .fhcom r r' cap tubes =>
    let tubeChildren := tubes.flatMap fun (φ, t) => [⟨φ, .none⟩, ⟨t, .dim 1⟩]
    let n := tubes.length
    ⟨[⟨r, .none⟩, ⟨r', .none⟩, ⟨cap, .none⟩] ++ tubeChildren,
      fun args =>
        let r1 := args.getD 0 r
        let r2 := args.getD 1 r'
        let cap' := args.getD 2 cap
        let tubeArgs := args.drop 3
        let tubes' := List.range n |>.map fun i =>
          (tubeArgs.getD (2*i) (tubes.getD i (.cof_top, cap)).1,
           tubeArgs.getD (2*i+1) (tubes.getD i (.cof_top, cap)).2)
        .fhcom r1 r2 cap' tubes'⟩

  | .boxEl r r' cap sysList =>
    let sysChildren := sysList.flatMap fun (φ, s) => [⟨φ, .none⟩, ⟨s, .none⟩]
    let n := sysList.length
    ⟨[⟨r, .none⟩, ⟨r', .none⟩, ⟨cap, .none⟩] ++ sysChildren,
      fun args =>
        let r1 := args.getD 0 r
        let r2 := args.getD 1 r'
        let cap' := args.getD 2 cap
        let sysArgs := args.drop 3
        let sys' := List.range n |>.map fun i =>
          (sysArgs.getD (2*i) (sysList.getD i (.cof_top, cap)).1,
           sysArgs.getD (2*i+1) (sysList.getD i (.cof_top, cap)).2)
        .boxEl r1 r2 cap' sys'⟩

  | .capEl r r' ty tubes e =>
    let tubeChildren := tubes.flatMap fun (φ, t) => [⟨φ, .none⟩, ⟨t, .dim 1⟩]
    let n := tubes.length
    ⟨[⟨r, .none⟩, ⟨r', .none⟩, ⟨ty, .none⟩] ++ tubeChildren ++ [⟨e, .none⟩],
      fun args =>
        let r1 := args.getD 0 r
        let r2 := args.getD 1 r'
        let ty' := args.getD 2 ty
        let tubeArgs := args.drop 3 |>.take (2 * n)
        let tubes' := List.range n |>.map fun i =>
          (tubeArgs.getD (2*i) (tubes.getD i (.cof_top, e)).1,
           tubeArgs.getD (2*i+1) (tubes.getD i (.cof_top, e)).2)
        let e' := args.getD (3 + 2*n) e
        .capEl r1 r2 ty' tubes' e'⟩

  | .sys branches =>
    let branchChildren := branches.flatMap fun (φ, t) => [⟨φ, .none⟩, ⟨t, .none⟩]
    let n := branches.length
    ⟨branchChildren,
      fun args =>
        let branches' := List.range n |>.map fun i =>
          (args.getD (2*i) (branches.getD i (.cof_top, .ix 0)).1,
           args.getD (2*i+1) (branches.getD i (.cof_top, .ix 0)).2)
        .sys branches'⟩

  | .extLam n body => ⟨[⟨body, .dim n⟩], fun | [b'] => .extLam n b' | _ => .extLam n body⟩

  | .extApp e dims =>
    ⟨[⟨e, .none⟩] ++ dims.map (⟨·, .none⟩),
      fun args =>
        let e' := args.getD 0 e
        let dims' := args.drop 1
        .extApp e' dims'⟩

/-! ## Expression Accessors and Predicates

    These allow querying Expr structure without pattern matching.
    Returns Option with components if the expression matches.
-/

/-- Try to view as application (term or path) -/
def Expr.asApp? : Expr → Option (Expr × Expr × (Expr → Expr → Expr))
  | .app f x => some (f, x, .app)
  | .papp p r => some (p, r, .papp)
  | _ => none

/-- Try to view as lambda (term or path) -/
def Expr.asLam? : Expr → Option (Expr × (Expr → Expr))
  | .lam body => some (body, .lam)
  | .plam body => some (body, .plam)
  | _ => none

/-- Try to view as projection -/
def Expr.asProj? : Expr → Option (Expr × (Expr → Expr) × (Expr → Expr → Expr))
  | .fst p => some (p, .fst, fun a _ => a)
  | .snd p => some (p, .snd, fun _ b => b)
  | _ => none

/-- Try to view as pair -/
def Expr.asPair? : Expr → Option (Expr × Expr)
  | .pair a b => some (a, b)
  | _ => none

/-- Try to view as let binding -/
def Expr.asLet? : Expr → Option (Expr × Expr × Expr)
  | .letE ty val body => some (ty, val, body)
  | _ => none

/-- Try to view as subOut/subIn -/
def Expr.asSubOut? : Expr → Option Expr
  | .subOut e => some e
  | _ => none

def Expr.asSubIn? : Expr → Option Expr
  | .subIn e => some e
  | _ => none

/-! ## Beta Reduction

    Each expression form knows how to reduce itself.
    This is the key abstraction: reduction logic lives with the expression.
-/

/-- Try beta reduction at the head.
    Returns Some if a reduction was made.
    This handles: app/lam, papp/plam, fst/pair, snd/pair, let, subOut/subIn -/
def Expr.tryBetaReduce (substTerm : Nat → Expr → Expr → Expr)
                       (substDim : Expr → Expr → Expr) : Expr → Option Expr
  -- Application: (.app (.lam body) arg) → subst arg body
  | .app (.lam body) arg => some (substTerm 0 arg body)
  -- Path application: (.papp (.plam body) r) → substDim r body
  | .papp (.plam body) r => some (substDim r body)
  -- Projections
  | .fst (.pair a _) => some a
  | .snd (.pair _ b) => some b
  -- Let binding
  | .letE _ val body => some (substTerm 0 val body)
  -- Sub types
  | .subOut (.subIn t) => some t
  | _ => none

/-- Try to reduce function position to expose redex for WHNF.
    Returns Some if progress was made on the head. -/
partial def Expr.whnfStep (substTerm : Nat → Expr → Expr → Expr)
                          (substDim : Expr → Expr → Expr) (e : Expr) : Option Expr :=
  -- First try direct beta reduction
  match e.tryBetaReduce substTerm substDim with
  | some e' => some e'
  | none =>
    -- Try reducing function/head position
    match e with
    | .app f a =>
      match f.whnfStep substTerm substDim with
      | some f' => some (.app f' a)
      | none => none
    | .papp p r =>
      match p.whnfStep substTerm substDim with
      | some p' => some (.papp p' r)
      | none => none
    | .fst p =>
      match p.whnfStep substTerm substDim with
      | some p' => some (.fst p')
      | none => none
    | .snd p =>
      match p.whnfStep substTerm substDim with
      | some p' => some (.snd p')
      | none => none
    | _ => none

/-- Reduce to weak head normal form -/
def Expr.whnf' (fuel : Nat) (substTerm : Nat → Expr → Expr → Expr)
               (substDim : Expr → Expr → Expr) (e : Expr) : Expr :=
  match fuel with
  | 0 => e
  | n + 1 =>
    match e.whnfStep substTerm substDim with
    | some e' => whnf' n substTerm substDim e'
    | none => e

/-- Normalize one step: try beta at head, then recurse into children -/
partial def Expr.normalizeStep (fuel : Nat)
    (extraReduce : Expr → Option Expr)
    (substTerm : Nat → Expr → Expr → Expr)
    (substDim : Expr → Expr → Expr)
    (e : Expr) : Expr :=
  if fuel == 0 then e
  else
    -- First try extra reductions (e.g., Kan ops)
    match extraReduce e with
    | some e' => normalizeStep (fuel - 1) extraReduce substTerm substDim e'
    | none =>
      -- Try beta reduction at head
      match e.tryBetaReduce substTerm substDim with
      | some e' => normalizeStep (fuel - 1) extraReduce substTerm substDim e'
      | none =>
        -- No head reduction, recurse into children
        let shape := e.shape
        if shape.children.isEmpty then e
        else
          let children' := shape.children.map fun child =>
            normalizeStep (fuel - 1) extraReduce substTerm substDim child.expr
          let rebuilt := shape.reconstruct children'
          -- Try reductions on rebuilt term (in case children enabled new redex)
          match extraReduce rebuilt with
          | some e' => normalizeStep (fuel - 1) extraReduce substTerm substDim e'
          | none =>
            match rebuilt.tryBetaReduce substTerm substDim with
            | some e' => normalizeStep (fuel - 1) extraReduce substTerm substDim e'
            | none => rebuilt

/-! ## Generic Traversal

    Using shape, we can define traversals generically.
-/

/-- Visitor operation: what to do at each node -/
structure VisitorOp where
  /-- Transform an atomic expression (variables, constants) -/
  onAtom : Nat → Expr → Expr
  /-- Combine results from children -/
  onComposite : ExprShape → List Expr → Expr := fun shape children => shape.reconstruct children

/-- Generic traversal using shape -/
partial def Expr.traverse (op : VisitorOp) (depth : Nat) (e : Expr) : Expr :=
  let shape := e.shape
  if shape.children.isEmpty then
    op.onAtom depth e
  else
    let children' := shape.children.map fun child =>
      let childDepth := match child.binder with
        | .none => depth
        | .term n => depth + n
        | .dim n => depth + n
      traverse op childDepth child.expr
    op.onComposite shape children'

/-! ## Shift Operation (Weakening) -/

/-- Shift visitor: increment free variables above cutoff -/
def shiftOp (cutoff : Nat) (delta : Int) : VisitorOp where
  onAtom depth e :=
    match e with
    | .ix n => if n >= cutoff + depth then .ix (Int.toNat (n + delta)) else .ix n
    | .dimVar n => if n >= cutoff + depth then .dimVar (Int.toNat (n + delta)) else .dimVar n
    | _ => e

/-- Shift all free variables at or above cutoff by delta -/
def Expr.shiftAbove' (cutoff : Nat) (delta : Int) (e : Expr) : Expr :=
  e.traverse (shiftOp cutoff delta) 0

/-- Standard weakening: shift by 1 -/
def Expr.shift' (e : Expr) : Expr := e.shiftAbove' 0 1

/-! ## Substitution Operation -/

/-- Substitution visitor -/
def substOp (idx : Nat) (val : Expr) : VisitorOp where
  onAtom depth e :=
    match e with
    | .ix n =>
      if n < idx + depth then .ix n
      else if n == idx + depth then val.shiftAbove' 0 depth
      else .ix (n - 1)
    | .dimVar n =>
      if n < idx + depth then .dimVar n
      else if n == idx + depth then val.shiftAbove' 0 depth
      else .dimVar (n - 1)
    | _ => e

/-- Substitute val for variable idx -/
def Expr.subst' (idx : Nat) (val : Expr) (e : Expr) : Expr :=
  e.traverse (substOp idx val) 0

/-- Substitute at index 0 -/
def Expr.subst0' (val : Expr) (body : Expr) : Expr :=
  body.subst' 0 val

/-! ## Free Variable Check -/

/-- Check if a variable is free -/
partial def Expr.freeIn' (n : Nat) (e : Expr) : Bool :=
  let shape := e.shape
  if shape.children.isEmpty then
    match e with
    | ix m => m == n
    | dimVar m => m == n
    | _ => false
  else
    shape.children.any fun child =>
      let childN := match child.binder with
        | .none => n
        | .term k => n + k
        | .dim k => n + k
      freeIn' childN child.expr

/-! ## Method-style API

    These allow calling operations as methods:
    - e.substAt val depth
    - e.shiftAt cutoff delta
    - e.hasFree n
-/

/-- Substitute at given depth (method style) -/
def Expr.substAt (e : Expr) (val : Expr) (depth : Nat := 0) : Expr :=
  e.subst' depth val

/-- Shift at cutoff (method style) -/
def Expr.shiftAt (e : Expr) (cutoff : Nat) (delta : Int := 1) : Expr :=
  e.shiftAbove' cutoff delta

/-- Check if variable n is free (method style) -/
def Expr.hasFree (e : Expr) (n : Nat) : Bool :=
  e.freeIn' n

/-! ## Collecting Operations

    These traverse and collect information without transforming.
-/

/-- Collect all free de Bruijn indices in an expression -/
partial def Expr.freeVars' (depth : Nat) (e : Expr) : List Nat :=
  let shape := e.shape
  if shape.children.isEmpty then
    match e with
    | .ix n => if n >= depth then [n - depth] else []
    | .dimVar n => if n >= depth then [n - depth] else []
    | _ => []
  else
    shape.children.flatMap fun child =>
      let childDepth := match child.binder with
        | .none => depth
        | .term n => depth + n
        | .dim n => depth + n
      freeVars' childDepth child.expr

/-- Collect free vars at depth 0 -/
def Expr.collectFreeVars (e : Expr) : List Nat :=
  (e.freeVars' 0).eraseDups

/-! ## Occurs Check

    Check if a name (e.g., meta-variable) occurs in an expression.
-/

/-- Check if a literal name occurs in an expression -/
partial def Expr.occursName (name : String) (e : Expr) : Bool :=
  let shape := e.shape
  if shape.children.isEmpty then
    match e with
    | .lit n => n == name
    | _ => false
  else
    shape.children.any fun child => occursName name child.expr

/-! ## Variable Renaming

    Generic renaming of variables based on a mapping.
-/

/-- Renaming visitor: apply a variable mapping -/
def renameOp (ren : List (Nat × Nat)) : VisitorOp where
  onAtom depth e :=
    match e with
    | .ix n =>
      if n < depth then .ix n  -- Bound variable, keep
      else
        let adjusted := n - depth
        match ren.find? (fun (v, _) => v == adjusted) with
        | some (_, newIdx) => .ix (newIdx + depth)
        | none => .ix n  -- Not in renaming, keep
    | .dimVar n =>
      if n < depth then .dimVar n
      else
        let adjusted := n - depth
        match ren.find? (fun (v, _) => v == adjusted) with
        | some (_, newIdx) => .dimVar (newIdx + depth)
        | none => .dimVar n
    | _ => e

/-- Rename variables according to mapping -/
def Expr.renameVars' (ren : List (Nat × Nat)) (e : Expr) : Expr :=
  e.traverse (renameOp ren) 0

/-! ## Meta-variable Substitution

    Apply solved meta-variables throughout a term.
    This is used after unification to instantiate holes.
-/

/-- Meta-variable substitution visitor -/
def metaSubstOp (lookup : String → Option Expr) : VisitorOp where
  onAtom _depth e :=
    match e with
    | .lit name =>
      if name.startsWith "?" then
        match lookup name with
        | some sol => sol  -- Note: may need recursive application
        | none => e
      else e
    | _ => e

/-- Apply meta-variable solutions throughout an expression -/
partial def Expr.applyMetas' (lookup : String → Option Expr) (e : Expr) : Expr :=
  let shape := e.shape
  if shape.children.isEmpty then
    match e with
    | .lit name =>
      if name.startsWith "?" then
        match lookup name with
        | some sol => applyMetas' lookup sol  -- Recurse into solution
        | none => e
      else e
    | _ => e
  else
    let children' := shape.children.map fun child =>
      applyMetas' lookup child.expr
    shape.reconstruct children'

/-! ## Inversion for Miller Patterns

    Invert a term by renaming variables according to a spine.
    Given spine [x₃, x₁, x₀], we rename x₃→0, x₁→1, x₀→2.
-/

/-- Build variable mapping from spine -/
def buildSpineRenaming (spineVars : List Nat) : List (Nat × Nat) :=
  spineVars.zip (List.range spineVars.length)

/-- Invert a term for Miller pattern unification.
    Returns None if the term uses variables not in the spine.
-/
def Expr.invertForSpine (spineVars : List Nat) (e : Expr) : Option Expr :=
  let fvs := e.collectFreeVars
  if !fvs.all (fun v => spineVars.contains v) then
    none  -- Scope escape
  else
    let ren := buildSpineRenaming spineVars
    some (e.renameVars' ren)

/-! ## Dimension Substitution

    Substitute a dimension expression for dimVar 0, shifting others down.
    Used in Kan operations when instantiating dimension abstractions.
-/

/-- Dimension substitution visitor: replace dimVar 0 with d, shift others down -/
def dimSubstOp (d : Expr) : VisitorOp where
  onAtom depth e :=
    match e with
    | .dimVar n =>
      if n < depth then .dimVar n  -- Bound, keep
      else if n == depth then d.shiftAbove' 0 depth  -- Target: substitute
      else .dimVar (n - 1)  -- Free above target: shift down
    | _ => e

/-- Substitute dimension d for dimVar 0, shifting other dim vars down -/
def Expr.substDim0' (d : Expr) (e : Expr) : Expr :=
  e.traverse (dimSubstOp d) 0

/-! ## Generic Map (Bottom-Up)

    Apply a transformation to all subexpressions, bottom-up.
    The function receives the already-transformed expression.
-/

/-- Map a function over all subexpressions, bottom-up -/
partial def Expr.mapBottomUp (f : Expr → Expr) (e : Expr) : Expr :=
  let shape := e.shape
  if shape.children.isEmpty then
    f e
  else
    let children' := shape.children.map fun child =>
      mapBottomUp f child.expr
    f (shape.reconstruct children')

/-! ## Generic Map with Reduction

    Map + try reduction at each step. Used for normalization.
    The reduction function returns Some if it made progress.
-/

/-- Normalize with a reduction function, bottom-up -/
partial def Expr.normalizeWith (fuel : Nat) (reduce : Expr → Option Expr) (e : Expr) : Expr :=
  if fuel == 0 then e
  else
    -- First, try reduction at the top
    match reduce e with
    | some e' => normalizeWith (fuel - 1) reduce e'
    | none =>
      -- No reduction, recurse into children
      let shape := e.shape
      if shape.children.isEmpty then e
      else
        let children' := shape.children.map fun child =>
          normalizeWith (fuel - 1) reduce child.expr
        let rebuilt := shape.reconstruct children'
        -- Try reduction on rebuilt term
        match reduce rebuilt with
        | some e' => normalizeWith (fuel - 1) reduce e'
        | none => rebuilt

end Lego.Core
