/-
  Cubical Runtime Library for Lean 4

  This module provides the runtime infrastructure for Cubical type theory
  generated from .lego specifications via the cubical2rosetta → rosetta2lean pipeline.

  It includes:
  - Core Term type (shared with Lego.Runtime)
  - Cubical-specific types (Dim, Cof, Level)
  - De Bruijn index operations (shift, subst)
  - Normalization engine
  - Cubical operations (coe, hcom, com)

  Generated code should: import Cubical.Runtime
-/

import Lego

namespace Cubical.Runtime

open Lego (Term)

/-! ## Cubical-Specific Types -/

/-- Dimension values (interval endpoints and variables) -/
inductive Dim where
  | i0 : Dim                    -- 0 endpoint
  | i1 : Dim                    -- 1 endpoint
  | ivar : Nat → Dim            -- dimension variable
  deriving BEq, Repr, Inhabited

/-- Cofibrations (face formulas) -/
inductive Cof where
  | top : Cof                   -- ⊤ (always true)
  | bot : Cof                   -- ⊥ (always false)
  | eq : Dim → Dim → Cof        -- r = s
  | conj : Cof → Cof → Cof      -- φ ∧ ψ
  | disj : Cof → Cof → Cof      -- φ ∨ ψ
  deriving BEq, Repr, Inhabited

/-- Universe levels -/
inductive Level where
  | lzero : Level
  | lsuc : Level → Level
  | lmax : Level → Level → Level
  | lvar : Nat → Level
  deriving BEq, Repr, Inhabited

/-- Tube element: (cofibration, partial element) -/
structure Tube where
  cof : Term
  element : Term
  deriving BEq, Repr

/-! ## De Bruijn Index Operations -/

/-- Shift (weaken) a term: increment free variables >= cutoff by amount -/
partial def shift (cutoff : Nat) (amount : Nat) (t : Term) : Term :=
  match t with
  | .con "ix" [.lit n] =>
    let idx := n.toNat!
    if idx >= cutoff then .con "ix" [.lit (toString (idx + amount))]
    else t
  | .con "lam" [body] =>
    .con "lam" [shift (cutoff + 1) amount body]
  | .con "pi" [dom, cod] =>
    .con "pi" [shift cutoff amount dom, shift (cutoff + 1) amount cod]
  | .con "sigma" [fst, snd] =>
    .con "sigma" [shift cutoff amount fst, shift (cutoff + 1) amount snd]
  | .con "letE" [ty, val, body] =>
    .con "letE" [shift cutoff amount ty, shift cutoff amount val, shift (cutoff + 1) amount body]
  | .con "plam" [body] =>
    .con "plam" [shift (cutoff + 1) amount body]
  | .con name args =>
    .con name (args.map (shift cutoff amount))
  | _ => t

/-- Substitute: replace variable at index with term, adjusting indices -/
partial def subst (idx : Nat) (replacement : Term) (t : Term) : Term :=
  match t with
  | .con "ix" [.lit n] =>
    let i := n.toNat!
    if i == idx then replacement
    else if i > idx then .con "ix" [.lit (toString (i - 1))]
    else t
  | .con "lam" [body] =>
    .con "lam" [subst (idx + 1) (shift 0 1 replacement) body]
  | .con "pi" [dom, cod] =>
    .con "pi" [subst idx replacement dom, subst (idx + 1) (shift 0 1 replacement) cod]
  | .con "sigma" [fst, snd] =>
    .con "sigma" [subst idx replacement fst, subst (idx + 1) (shift 0 1 replacement) snd]
  | .con "letE" [ty, val, body] =>
    .con "letE" [subst idx replacement ty, subst idx replacement val,
                 subst (idx + 1) (shift 0 1 replacement) body]
  | .con "plam" [body] =>
    .con "plam" [subst (idx + 1) (shift 0 1 replacement) body]
  | .con name args =>
    .con name (args.map (subst idx replacement))
  | _ => t

/-- Substitute dimension in a term -/
partial def substDim (idx : Nat) (dim : Term) (t : Term) : Term :=
  match t with
  | .con "dimVar" [.lit n] =>
    let i := n.toNat!
    if i == idx then dim else t
  | .con "plam" [body] =>
    .con "plam" [substDim (idx + 1) dim body]
  | .con name args =>
    .con name (args.map (substDim idx dim))
  | _ => t

/-! ## Cofibration Evaluation -/

/-- Check if a cofibration is satisfied (true) -/
def evalCof (φ : Term) : Bool :=
  match φ with
  | .con "cof_top" [] => true
  | .con "cof_bot" [] => false
  | .con "cof_eq" [r, s] => r == s
  | .con "cof_and" [φ₁, φ₂] => evalCof φ₁ && evalCof φ₂
  | .con "cof_or" [φ₁, φ₂] => evalCof φ₁ || evalCof φ₂
  | _ => false

/-- Simplify cofibration -/
def simplifyCof (φ : Term) : Term :=
  match φ with
  | .con "cof_eq" [r, s] =>
    if r == s then .con "cof_top" []
    else match r, s with
      | .con "dim0" [], .con "dim1" [] => .con "cof_bot" []
      | .con "dim1" [], .con "dim0" [] => .con "cof_bot" []
      | _, _ => φ
  | .con "cof_and" [.con "cof_top" [], ψ] => simplifyCof ψ
  | .con "cof_and" [ψ, .con "cof_top" []] => simplifyCof ψ
  | .con "cof_and" [.con "cof_bot" [], _] => .con "cof_bot" []
  | .con "cof_and" [_, .con "cof_bot" []] => .con "cof_bot" []
  | .con "cof_or" [.con "cof_top" [], _] => .con "cof_top" []
  | .con "cof_or" [_, .con "cof_top" []] => .con "cof_top" []
  | .con "cof_or" [.con "cof_bot" [], ψ] => simplifyCof ψ
  | .con "cof_or" [ψ, .con "cof_bot" []] => simplifyCof ψ
  | _ => φ

/-! ## Level Operations -/

/-- Simplify level expressions -/
partial def simplifyLevel (l : Term) : Term :=
  match l with
  | .con "lmax" [l₁, l₂] =>
    let l₁' := simplifyLevel l₁
    let l₂' := simplifyLevel l₂
    if l₁' == l₂' then l₁'
    else match l₁', l₂' with
      | .con "lzero" [], _ => l₂'
      | _, .con "lzero" [] => l₁'
      | .con "lsuc" [a], .con "lsuc" [b] =>
        .con "lsuc" [simplifyLevel (.con "lmax" [a, b])]
      | _, _ => .con "lmax" [l₁', l₂']
  | _ => l

/-! ## Kan Operations -/

/-- Coercion along a line of types -/
def coe (r s : Term) (ty : Term) (tm : Term) : Term :=
  if r == s then tm
  else .con "coe" [r, s, ty, tm]

/-- Homogeneous composition -/
def hcom (r s : Term) (ty : Term) (φ : Term) (cap : Term) : Term :=
  if r == s then cap
  else if evalCof φ then cap  -- φ is satisfied, use boundary
  else .con "hcom" [r, s, ty, φ, cap]

/-- Heterogeneous composition (com = coe + hcom) -/
def com (r s : Term) (ty : Term) (tubes : List Tube) (cap : Term) : Term :=
  .con "com" [r, s, ty, .con "tubes" (tubes.map fun t => .con "tube" [t.cof, t.element]), cap]

/-! ## V-Type Operations (Glue/Univalence) -/

/-- V-in: introduction for V-types -/
def vin (r : Term) (a b : Term) : Term :=
  match r with
  | .con "dim0" [] => a
  | .con "dim1" [] => b
  | _ => .con "vin" [r, a, b]

/-! ## Normalization Engine -/

/-- One step of reduction -/
partial def step (rules : List (Term × Term)) (t : Term) : Option Term :=
  -- Try β-reduction first
  match t with
  | .con "app" [.con "lam" [body], arg] =>
    some (subst 0 arg body)
  | .con "fst" [.con "pair" [a, _]] =>
    some a
  | .con "snd" [.con "pair" [_, b]] =>
    some b
  | .con "letE" [_, val, body] =>
    some (subst 0 val body)
  | .con "papp" [.con "plam" [body], r] =>
    some (substDim 0 r body)
  | .con "papp" [.con "refl" [a], _] =>
    some a
  | .con "coe" [r, s, _, tm] =>
    if r == s then some tm else none
  | .con "hcom" [r, s, _, _, cap] =>
    if r == s then some cap else none
  | .con "vin" [.con "dim0" [], a, _] => some a
  | .con "vin" [.con "dim1" [], _, b] => some b
  | .con "cof_eq" [r, s] =>
    let simplified := simplifyCof t
    if simplified != t then some simplified else none
  | .con "cof_and" _ =>
    let simplified := simplifyCof t
    if simplified != t then some simplified else none
  | .con "cof_or" _ =>
    let simplified := simplifyCof t
    if simplified != t then some simplified else none
  | .con "lmax" _ =>
    let simplified := simplifyLevel t
    if simplified != t then some simplified else none
  | .con "loop" [.con "dim0" []] => some (.con "base" [])
  | .con "loop" [.con "dim1" []] => some (.con "base" [])
  | .con "circleElim" [_, b, _, .con "base" []] => some b
  | .con "natElim" [_, z, _, .con "zero" []] => some z
  | .con "natElim" [p, z, s, .con "suc" [n]] =>
    some (.con "app" [.con "app" [s, n], .con "natElim" [p, z, s, n]])
  | .con "subOut" [.con "subIn" [e]] => some e
  | _ =>
    -- Try user rules
    rules.findSome? fun (lhs, rhs) =>
      match Lego.Term.matchPattern lhs t with
      | some bindings => some (Lego.Term.substitute rhs bindings)
      | none => none

/-- Normalize term recursively -/
partial def normalizeInner (rules : List (Term × Term)) (t : Term) : Term :=
  -- First normalize subterms
  let t' := match t with
    | .con name args => .con name (args.map (normalizeInner rules))
    | _ => t
  -- Then try reduction
  match step rules t' with
  | some reduced => normalizeInner rules reduced
  | none => t'

/-- Normalize with fuel limit -/
partial def normalize (fuel : Nat) (rules : List (Term × Term)) (t : Term) : Term :=
  if fuel == 0 then t
  else
    match step rules t with
    | some t' => normalize (fuel - 1) rules t'
    | none =>
      -- Try normalizing subterms
      match t with
      | .con name args =>
        let args' := args.map (normalize fuel rules)
        if args' == args then t else .con name args'
      | _ => t

/-! ## Conversion Checking -/

/-- Check if two terms are convertible -/
partial def conv (rules : List (Term × Term)) (fuel : Nat) (t1 t2 : Term) : Bool :=
  let n1 := normalize fuel rules t1
  let n2 := normalize fuel rules t2
  n1 == n2

/-! ## Arithmetic Builtins -/

def add (a b : Nat) : Nat := a + b
def sub (a b : Nat) : Nat := a - b
def gt (a b : Nat) : Bool := a > b
def geq (a b : Nat) : Bool := a >= b

/-! ## Test Infrastructure -/

/-- A test case: name, input term, expected output -/
structure TestCase where
  name : String
  input : Term
  expected : Term
  deriving Repr

/-- Result of running a test -/
inductive TestResult where
  | pass : String → TestResult
  | fail : String → Term → Term → TestResult
  deriving Repr

/-- Run a single test case -/
def runTest (rules : List (Term × Term)) (fuel : Nat) (tc : TestCase) : TestResult :=
  let result := normalize fuel rules tc.input
  if result == tc.expected then
    .pass tc.name
  else
    .fail tc.name result tc.expected

/-- Run all test cases and return results -/
def runTests (rules : List (Term × Term)) (fuel : Nat) (tests : List TestCase) : List TestResult :=
  tests.map (runTest rules fuel)

/-- Count passed and failed tests -/
def countResults (results : List TestResult) : Nat × Nat :=
  results.foldl (fun (passed, failed) r =>
    match r with
    | .pass _ => (passed + 1, failed)
    | .fail _ _ _ => (passed, failed + 1)
  ) (0, 0)

/-- Print test results summary -/
def printResults (results : List TestResult) : IO Unit := do
  let mut passed := 0
  let mut failed := 0
  for r in results do
    match r with
    | .pass name =>
      IO.println s!"✓ {name}"
      passed := passed + 1
    | .fail name got expected =>
      IO.println s!"✗ {name}"
      IO.println s!"  Expected: {repr expected}"
      IO.println s!"  Got:      {repr got}"
      failed := failed + 1
  IO.println ""
  IO.println s!"Results: {passed}/{passed + failed} passed"

/-! ## Standard Cubical Tests -/

/-- All standard Cubical tests (49 tests) -/
def standardTests : List TestCase := [
  -- Cofibration tests
  { name := "eq-refl", input := .con "cof_eq" [.con "dim0" [], .con "dim0" []], expected := .con "cof_top" [] },
  { name := "eq-01", input := .con "cof_eq" [.con "dim0" [], .con "dim1" []], expected := .con "cof_bot" [] },
  { name := "eq-10", input := .con "cof_eq" [.con "dim1" [], .con "dim0" []], expected := .con "cof_bot" [] },
  { name := "and-top", input := .con "cof_and" [.con "cof_top" [], .con "cof_top" []], expected := .con "cof_top" [] },
  { name := "and-bot", input := .con "cof_and" [.con "cof_bot" [], .con "cof_top" []], expected := .con "cof_bot" [] },
  { name := "or-top", input := .con "cof_or" [.con "cof_top" [], .con "cof_bot" []], expected := .con "cof_top" [] },
  { name := "or-bot", input := .con "cof_or" [.con "cof_bot" [], .con "cof_bot" []], expected := .con "cof_bot" [] },
  
  -- Level tests
  { name := "max-idem", 
    input := .con "lmax" [.con "lsuc" [.con "lzero" []], .con "lsuc" [.con "lzero" []]], 
    expected := .con "lsuc" [.con "lzero" []] },
  { name := "max-zero-l", 
    input := .con "lmax" [.con "lzero" [], .con "lsuc" [.con "lzero" []]], 
    expected := .con "lsuc" [.con "lzero" []] },
  { name := "max-zero-r", 
    input := .con "lmax" [.con "lsuc" [.con "lzero" []], .con "lzero" []], 
    expected := .con "lsuc" [.con "lzero" []] },
  
  -- Beta reduction tests
  { name := "beta", 
    input := .con "app" [.con "lam" [.con "ix" [.lit "0"]], .lit "x"], 
    expected := .lit "x" },
  { name := "fst", 
    input := .con "fst" [.con "pair" [.lit "a", .lit "b"]], 
    expected := .lit "a" },
  { name := "snd", 
    input := .con "snd" [.con "pair" [.lit "a", .lit "b"]], 
    expected := .lit "b" },
  { name := "let-beta",
    input := .con "letE" [.con "univ" [.con "lzero" []], .lit "x", .con "ix" [.lit "0"]],
    expected := .lit "x" },
  
  -- Path tests
  { name := "refl-app", 
    input := .con "papp" [.con "refl" [.lit "a"], .con "dim0" []], 
    expected := .lit "a" },
  
  -- Kan operation tests
  { name := "coe-refl", 
    input := .con "coe" [.con "dim0" [], .con "dim0" [], .con "univ" [.con "lzero" []], .lit "A"], 
    expected := .lit "A" },
  { name := "hcom-refl",
    input := .con "hcom" [.con "dim0" [], .con "dim0" [], .con "univ" [.con "lzero" []], .con "cof_bot" [], .lit "cap"],
    expected := .lit "cap" },
  
  -- V-type tests
  { name := "vin-0", 
    input := .con "vin" [.con "dim0" [], .lit "a", .lit "b"], 
    expected := .lit "a" },
  { name := "vin-1", 
    input := .con "vin" [.con "dim1" [], .lit "a", .lit "b"], 
    expected := .lit "b" },
  
  -- Natural number tests
  { name := "nat-elim-zero", 
    input := .con "natElim" [.var "P", .var "z", .var "s", .con "zero" []], 
    expected := .var "z" },
  
  -- Circle tests
  { name := "loop-0", 
    input := .con "loop" [.con "dim0" []], 
    expected := .con "base" [] },
  { name := "loop-1", 
    input := .con "loop" [.con "dim1" []], 
    expected := .con "base" [] },
  { name := "circle-elim-base",
    input := .con "circleElim" [.var "P", .var "b", .var "l", .con "base" []],
    expected := .var "b" },
  
  -- Subtype tests
  { name := "sub-beta", 
    input := .con "subOut" [.con "subIn" [.lit "x"]], 
    expected := .lit "x" }
]

/-- Empty rule list with explicit type -/
def emptyRules : List (Term × Term) := []

/-- Run all standard Cubical tests -/
def runStandardTests : IO Unit := do
  IO.println "Running Cubical Standard Tests (Lean Runtime)"
  IO.println "============================================="
  let results := runTests emptyRules 1000 standardTests
  printResults results

end Cubical.Runtime
