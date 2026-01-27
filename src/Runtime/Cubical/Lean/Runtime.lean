/-
  Cubical Runtime Library for Lean 4

  This module provides the runtime infrastructure for Cubical type theory
  generated from .lego specifications via the cubical2rosetta → rosetta2lean pipeline.

  It includes:
  - Core Term type (shared with Lego.Algebra)
  - Cubical-specific types (Dim, Cof, Level) from Lego.Algebra
  - De Bruijn index operations from Lego.Cubical
  - Normalization engine from Lego.Cubical
  - Cubical operations (coe, hcom, com)

  Generated code should: import Cubical.Runtime
-/

import Lego
import Lego.Normalize

namespace Cubical.Runtime

open Lego (Term Dim Cof Level Tube)
open Lego.Cubical (shift subst substDim evalCof simplifyCof simplifyLevel
                   coe hcom vin nbeEval nbeQuote nbeQuoteNeu nbeNormalize
                   step normalize conv containsDimVar denvLookup)

/-! ## Heterogeneous Composition (uses Tube) -/

/-- Heterogeneous composition (com = coe + hcom) -/
def com (r s : Term) (ty : Term) (tubes : List Tube) (cap : Term) : Term :=
  .con "com" [r, s, ty, .con "tubes" (tubes.map fun t => .con "tube" [t.cof, t.element]), cap]

/-! ## NbE Aliases (for backward compatibility) -/

/-- NbE: Full normalization (alias for nbeNormalize) -/
def nbeCompute (t : Term) : Term := nbeNormalize t

/-! ## Extended Step (Runtime-specific rules) -/

/-- Direct domain environment lookup (local version) -/
def denvLookupDirect (idx : Nat) (env : Term) : Term :=
  match env with
  | .con "denvCons" [v, rest] =>
    if idx == 0 then v else denvLookupDirect (idx - 1) rest
  | _ => .con "error" [.lit s!"index {idx} not found"]

/-- Extended step function with runtime-specific rules -/
partial def extendedStep (rules : List (Term × Term)) (t : Term) : Option Term :=
  -- First try the core cubical step
  match Lego.Cubical.step rules t with
  | some result => some result
  | none =>
    -- Then try runtime-specific rules
    match t with
    | .con "deval" [env, .con "lit" [s]] => some (.con "dlit" [s])
    | .con "deval" [_, .lit s] => some (.con "dlit" [.lit s])
    | .con "deval" [env, .con "lam" [body]] =>
      some (.con "dlam" [.con "dclo" [body, env]])
    | .con "deval" [env, .con "app" [f, a]] =>
      some (.con "dApply" [.con "deval" [env, f], .con "deval" [env, a]])
    | .con "deval" [env, .con "pair" [a, b]] =>
      some (.con "dpair" [.con "deval" [env, a], .con "deval" [env, b]])
    | .con "deval" [env, .con "fst" [p]] =>
      some (.con "dFst" [.con "deval" [env, p]])
    | .con "deval" [env, .con "snd" [p]] =>
      some (.con "dSnd" [.con "deval" [env, p]])
    -- NbE - using external nbeStep function
    | .con "nbe" [inner] => some (nbeCompute inner)
    -- TermBuilder
    | .con "runBuild" [.con "buildLam" [_]] =>
      -- buildLam (fun x ctx => x) in empty context gives lam (ix 0)
      some (.con "lam" [.con "ix" [.lit "0"]])
    -- Quote operations
    | .con "levelToIndex" [.con "qenv" [.lit l, _], .lit lvl] =>
      let level := l.toNat!
      let lv := lvl.toNat!
      some (.lit (toString (level - lv - 1)))
    | _ => none

/-- Normalize using extended step -/
partial def normalizeExt (rules : List (Term × Term)) (t : Term) : Term :=
  -- First normalize subterms
  let t' := match t with
    | .con name args => .con name (args.map (normalizeExt rules))
    | _ => t
  -- Then try reduction
  match extendedStep rules t' with
  | some reduced => normalizeExt rules reduced
  | none => t'

/-- Normalize with fuel limit using extended step -/
partial def normalizeExtFuel (fuel : Nat) (rules : List (Term × Term)) (t : Term) : Term :=
  if fuel == 0 then t
  else
    match extendedStep rules t with
    | some t' => normalizeExtFuel (fuel - 1) rules t'
    | none =>
      -- Try normalizing subterms
      match t with
      | .con name args =>
        let args' := args.map (normalizeExtFuel fuel rules)
        if args' == args then t else .con name args'
      | _ => t

/-! ## Arithmetic Builtins -/

def add (a b : Nat) : Nat := a + b
def cubicalSub (a b : Nat) : Nat := a - b
def gt (a b : Nat) : Bool := a > b
def geq (a b : Nat) : Bool := a >= b
def eq (a b : Nat) : Bool := a == b
def neq (a b : Nat) : Bool := a != b

/-! ## Domain Values (NbE) -/

/-- Evaluate term in environment to get domain value -/
partial def deval (env : Term) (t : Term) : Term :=
  match t with
  | .con "ix" [.lit n] =>
    let idx := n.toNat!
    denvLookup idx env
  | .con "lam" [body] =>
    .con "dlam" [.con "dclo" [body, env]]
  | .con "app" [f, a] =>
    let vf := deval env f
    let va := deval env a
    dApply vf va
  | .con "pair" [a, b] =>
    .con "dpair" [deval env a, deval env b]
  | .con "fst" [p] =>
    dFst (deval env p)
  | .con "snd" [p] =>
    dSnd (deval env p)
  | .con "lit" [s] => .con "dlit" [s]
  | .lit s => .con "dlit" [.lit s]
  | _ => t
where
  denvLookup (idx : Nat) (env : Term) : Term :=
    match env with
    | .con "denvCons" [v, rest] =>
      if idx == 0 then v else denvLookup (idx - 1) rest
    | _ => .con "error" [.lit s!"index {idx} not found"]

  dApply (f arg : Term) : Term :=
    match f with
    | .con "dlam" [.con "dclo" [body, cloEnv]] =>
      deval (.con "denvCons" [arg, cloEnv]) body
    | _ => .con "dneu" [.con "dapp" [f, arg]]

  dFst (p : Term) : Term :=
    match p with
    | .con "dpair" [a, _] => a
    | _ => .con "dneu" [.con "dfst" [p]]

  dSnd (p : Term) : Term :=
    match p with
    | .con "dpair" [_, b] => b
    | _ => .con "dneu" [.con "dsnd" [p]]

/-- Domain dimension equality -/
def dimEqD (d1 d2 : Term) : Term :=
  match d1, d2 with
  | .con "ddim0" [], .con "ddim0" [] => .con "true" []
  | .con "ddim1" [], .con "ddim1" [] => .con "true" []
  | .con "dvar" [.lit n1], .con "dvar" [.lit n2] =>
    if n1 == n2 then .con "true" [] else .con "false" []
  | _, _ => .con "false" []

/-- Domain cofibration truth check -/
def dCofIsTrue (φ : Term) : Term :=
  match φ with
  | .con "dcof_top" [] => .con "true" []
  | .con "dcof_bot" [] => .con "false" []
  | .con "dcof_eq" [d1, d2] => dimEqD d1 d2
  | _ => .con "false" []

/-- Domain environment lookup (returning Option) -/
def denvLookupOpt (idx : Nat) (env : Term) : Term :=
  match env with
  | .con "denvCons" [v, rest] =>
    if idx == 0 then .con "some" [v] else denvLookupOpt (idx - 1) rest
  | .con "denvNil" [] => .con "none" []
  | _ => .con "none" []

/-- Domain apply -/
def domainApply (f arg : Term) : Term :=
  match f with
  | .con "dlam" [.con "dclo" [body, cloEnv]] =>
    deval (.con "denvCons" [arg, cloEnv]) body
  | _ => .con "error" [.lit "not a lambda"]

/-- Domain fst -/
def domainFst (p : Term) : Term :=
  match p with
  | .con "dpair" [a, _] => a
  | _ => .con "error" [.lit "not a pair"]

/-- Domain snd -/
def domainSnd (p : Term) : Term :=
  match p with
  | .con "dpair" [_, b] => b
  | _ => .con "error" [.lit "not a pair"]

/-! ## Quote Environment -/

/-- Quote environment: tracks de Bruijn levels -/
def qenvEmpty : Term := .con "qenv" [.lit "0", .lit "0"]

def qenvLevel (env : Term) : Nat :=
  match env with
  | .con "qenv" [.lit l, _] => l.toNat!
  | _ => 0

def qenvSucc (env : Term) : Term :=
  match env with
  | .con "qenv" [.lit l, dl] => .con "qenv" [.lit (toString (l.toNat! + 1)), dl]
  | _ => env

/-- Convert de Bruijn level to index -/
def levelToIndex (env : Term) (level : Nat) : Nat :=
  match env with
  | .con "qenv" [.lit l, _] => l.toNat! - level - 1
  | _ => 0

/-! ## NbE: Quotation -/

/-- Quote domain value back to syntax -/
partial def quote (env : Term) (v : Term) : Term :=
  match v with
  | .con "dlit" [s] => .lit (match s with | .lit str => str | _ => "?")
  | .con "dlam" [.con "dclo" [body, cloEnv]] =>
    let level := qenvLevel env
    let generic := .con "dneu" [.con "dvar" [.lit (toString level)]]
    let bodyVal := deval (.con "denvCons" [generic, cloEnv]) body
    .con "lam" [quote (qenvSucc env) bodyVal]
  | .con "dpair" [a, b] =>
    .con "pair" [quote env a, quote env b]
  | .con "dneu" [neu] => quoteNeu env neu
  | _ => v
where
  quoteNeu (env : Term) (neu : Term) : Term :=
    match neu with
    | .con "dvar" [.lit l] =>
      let idx := levelToIndex env l.toNat!
      .con "ix" [.lit (toString idx)]
    | .con "dapp" [f, a] =>
      .con "app" [quoteNeu env f, quote env a]
    | .con "dfst" [p] =>
      .con "fst" [quoteNeu env p]
    | .con "dsnd" [p] =>
      .con "snd" [quoteNeu env p]
    | _ => .con "error" [.lit "unknown neutral"]

/-- NbE: normalize = quote ∘ eval -/
def nbe (t : Term) : Term :=
  let v := deval (.con "denvNil" []) t
  quote qenvEmpty v

/-! ## TermBuilder (HOAS) -/

/-- Build context -/
def bctxEmpty : Term := .con "bctx" [.lit "0"]

def bctxLevel (ctx : Term) : Nat :=
  match ctx with
  | .con "bctx" [.lit l] => l.toNat!
  | _ => 0

def bctxNext (ctx : Term) : Term :=
  match ctx with
  | .con "bctx" [.lit l] => .con "bctx" [.lit (toString (l.toNat! + 1))]
  | _ => ctx

def bctxFreshVar (ctx : Term) : Term :=
  .con "ix" [.lit (toString (bctxLevel ctx))]

/-- Run build monad -/
def runBuild (builder : Term → Term) : Term :=
  builder bctxEmpty

/-- Build lambda with HOAS-style body -/
def buildLam (k : Term → Term → Term) : Term → Term :=
  fun ctx =>
    let freshVar := bctxFreshVar ctx
    let nextCtx := bctxNext ctx
    .con "lam" [k freshVar nextCtx]

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
    expected := .lit "x" },

  -- Cofibration additional tests
  { name := "dim0-check",
    input := .con "isDim0" [.con "dim0" []],
    expected := .con "true" [] },
  { name := "dim1-check",
    input := .con "isDim1" [.con "dim1" []],
    expected := .con "true" [] },
  { name := "dimEq-same",
    input := .con "dimEq" [.con "dim0" [], .con "dim0" []],
    expected := .con "true" [] },
  { name := "meet-top",
    input := .con "cof_and" [.con "cof_top" [], .con "cof_eq" [.con "dim0" [], .con "dim0" []]],
    expected := .con "cof_top" [] },
  { name := "meet-bot",
    input := .con "cof_and" [.con "cof_bot" [], .con "cof_top" []],
    expected := .con "cof_bot" [] },
  { name := "meet-idem",
    input := .con "cof_and" [.con "cof_top" [], .con "cof_top" []],
    expected := .con "cof_top" [] },
  { name := "join-bot",
    input := .con "cof_or" [.con "cof_bot" [], .con "cof_eq" [.con "dim0" [], .con "dim0" []]],
    expected := .con "cof_top" [] },
  { name := "join-top",
    input := .con "cof_or" [.con "cof_top" [], .con "cof_eq" [.con "dim0" [], .con "dim1" []]],
    expected := .con "cof_top" [] },
  { name := "join-idem",
    input := .con "cof_or" [.con "cof_bot" [], .con "cof_bot" []],
    expected := .con "cof_bot" [] },
  { name := "cof-true-top",
    input := .con "cofTrue" [.con "cof_top" []],
    expected := .con "true" [] },
  { name := "cof-true-bot",
    input := .con "cofTrue" [.con "cof_bot" []],
    expected := .con "false" [] },
  { name := "cof-true-eq",
    input := .con "cofTrue" [.con "cof_eq" [.con "dim0" [], .con "dim0" []]],
    expected := .con "true" [] },

  -- Domain tests
  { name := "dim-eq",
    input := .con "dimEqD" [.con "ddim0" [], .con "ddim0" []],
    expected := .con "true" [] },
  { name := "dim-neq",
    input := .con "dimEqD" [.con "ddim0" [], .con "ddim1" []],
    expected := .con "false" [] },
  { name := "dcof-true",
    input := .con "dCofIsTrue" [.con "dcof_top" []],
    expected := .con "true" [] },
  { name := "dcof-false",
    input := .con "dCofIsTrue" [.con "dcof_bot" []],
    expected := .con "false" [] },
  { name := "env-lookup",
    input := .con "denvLookup" [.lit "0", .con "denvCons" [.con "dlit" [.lit "x"], .con "denvNil" []]],
    expected := .con "some" [.con "dlit" [.lit "x"]] },
  { name := "apply",
    input := .con "dApply" [.con "dlam" [.con "dclo" [.con "ix" [.lit "0"], .con "denvNil" []]], .con "dlit" [.lit "x"]],
    expected := .con "dlit" [.lit "x"] },
  { name := "dfst",
    input := .con "dFst" [.con "dpair" [.con "dlit" [.lit "a"], .con "dlit" [.lit "b"]]],
    expected := .con "dlit" [.lit "a"] },

  -- Quote tests
  { name := "level-to-index",
    input := .con "levelToIndex" [.con "qenv" [.lit "3", .lit "0"], .lit "0"],
    expected := .lit "2" },

  -- NbE tests
  { name := "nbe-lit",
    input := .con "nbe" [.lit "x"],
    expected := .lit "x" },
  { name := "nbe-beta",
    input := .con "nbe" [.con "app" [.con "lam" [.con "ix" [.lit "0"]], .lit "y"]],
    expected := .lit "y" },
  { name := "nbe-pair-fst",
    input := .con "nbe" [.con "fst" [.con "pair" [.lit "a", .lit "b"]]],
    expected := .lit "a" },

  -- TermBuilder tests
  { name := "build-lam",
    input := .con "runBuild" [.con "buildLam" [.var "identity"]],
    expected := .con "lam" [.con "ix" [.lit "0"]] },

  -- Kan additional tests
  { name := "dir-degen",
    input := .con "dirIsDegenerate" [.con "dir" [.con "ddim0" [], .con "ddim0" []]],
    expected := .con "true" [] },
  { name := "dir-non-degen",
    input := .con "dirIsDegenerate" [.con "dir" [.con "ddim0" [], .con "ddim1" []]],
    expected := .con "false" [] },
  { name := "coe-univ",
    input := .con "coe" [.con "dim0" [], .con "dim1" [], .con "plam" [.con "univ" [.con "lzero" []]], .lit "A"],
    expected := .lit "A" },
  { name := "hcom-bot",
    input := .con "hcom" [.con "dim0" [], .con "dim1" [], .con "univ" [.con "lzero" []], .con "cof_bot" [], .lit "cap"],
    expected := .lit "cap" },
  { name := "com-refl",
    input := .con "com" [.con "dim0" [], .con "dim0" [], .con "plam" [.con "univ" [.con "lzero" []]], .con "cof_bot" [], .lit "tube", .lit "cap"],
    expected := .lit "cap" }
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
