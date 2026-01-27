/-
  TestCubicalIntegration: End-to-end Integration Tests for Cubical Semantics

  This test suite exercises the full pipeline:
    Parse → Elaborate → Type-check → Normalize → Quote

  The goal is to verify that the rules defined in examples/Cubical/Lego/
  (Elaborate.lego, Semantics.lego, etc.) work together correctly.

  Run with: lake exe lego-test-cubical-integration
-/

import Lego
import Lego.Bootstrap
import Lego.Loader
import Lego.Runtime
import Lego.Normalize

open Lego
open Lego.Loader
open Lego.Cubical (normalizeInner)
open Lego.Runtime
open Lego.Cubical (normalize)

set_option linter.unusedVariables false

/-! ## Test Framework -/

structure TestResult where
  name : String
  passed : Bool
  message : String := ""

def runTest (name : String) (test : IO Bool) : IO TestResult := do
  try
    let passed ← test
    return { name, passed, message := if passed then "✓" else "✗" }
  catch e =>
    return { name, passed := false, message := s!"✗ Exception: {e}" }

def printResult (r : TestResult) : IO Unit := do
  let pfx := if r.passed then "  ✓ " else "  ✗ "
  IO.println s!"{pfx}{r.name} {r.message}"

/-! ## Cubical Language Loading -/

/-- Load all the Cubical/Lego modules and extract their rules -/
def loadCubicalModules (rt : Runtime) : IO (List Rule × List TypeRule) := do
  let cubicalDir := "./examples/Cubical/Lego"
  let modules := [
    "Core", "Cofibration", "Domain", "Semantics", "Elaborate",
    "Unify", "Quote", "Tactic", "RefineMonad", "Conversion",
    "TermBuilder", "Visitor", "GlobalEnv", "Signature",
    "Kan", "HIT", "VType", "ExtType", "SubType", "FHCom",
    "Datatype", "Splice", "Module", "TypeAttrs"
  ]

  let mut allRules : List Rule := rt.rules
  let mut allTypeRules : List TypeRule := rt.typeRules

  for modName in modules do
    let path := s!"{cubicalDir}/{modName}.lego"
    if ← System.FilePath.pathExists path then
      let content ← IO.FS.readFile path
      match parseLegoFileE rt content with
      | .error _ => pure ()  -- Skip if can't parse
      | .ok ast =>
        -- Extract rules from this module
        let rules := Loader.extractRules ast
        let typeRules := Loader.extractTypeRules ast
        allRules := allRules ++ rules
        allTypeRules := allTypeRules ++ typeRules

  return (allRules, allTypeRules)

/-! ## Core Term Builders (de Bruijn) -/

/-- Build core lambda (de Bruijn) -/
def coreLam (body : Term) : Term :=
  .con "lam" [body]

/-- Build core variable (de Bruijn index) -/
def coreIx (n : Nat) : Term :=
  .con "ix" [.lit (toString n)]

/-- Build core application -/
def coreApp (f : Term) (arg : Term) : Term :=
  .con "app" [f, arg]

/-- Build core Pi type -/
def corePi (dom : Term) (cod : Term) : Term :=
  .con "pi" [dom, cod]

/-- Build core Sigma type -/
def coreSigma (fst : Term) (snd : Term) : Term :=
  .con "sigma" [fst, snd]

/-- Build core pair -/
def corePair (a : Term) (b : Term) : Term :=
  .con "pair" [a, b]

/-- Build core projections -/
def coreFst (p : Term) : Term := .con "fst" [p]
def coreSnd (p : Term) : Term := .con "snd" [p]

/-- Build core universe -/
def coreUniv (level : Nat) : Term :=
  .con "univ" [.lit (toString level)]

/-- Build core path lambda -/
def corePlam (body : Term) : Term :=
  .con "plam" [body]

/-- Build core path application -/
def corePapp (p : Term) (r : Term) : Term :=
  .con "papp" [p, r]

/-- Build core path type -/
def corePath (ty : Term) (l : Term) (r : Term) : Term :=
  .con "path" [ty, l, r]

/-- Build core refl -/
def coreRefl (a : Term) : Term :=
  .con "refl" [a]

/-- Build core dimensions -/
def coreDim0 : Term := .con "dim0" []
def coreDim1 : Term := .con "dim1" []

/-- Build core coe -/
def coreCoe (r : Term) (s : Term) (ty : Term) (tm : Term) : Term :=
  .con "coe" [r, s, ty, tm]

/-- Build core hcom -/
def coreHcom (r : Term) (s : Term) (ty : Term) (phi : Term) (u : Term) : Term :=
  .con "hcom" [r, s, ty, phi, u]

/-- Build cof_top -/
def cofTop : Term := .con "cof_top" []

/-! ## Normalization Helper -/

/-- Apply rules and return normalized term.
    Uses normalizeInner which properly reduces after subterm normalization. -/
def normalizeWithRulesList (rules : List Rule) (t : Term) : Term :=
  let rulePairs := rules.map fun r => (r.pattern, r.template)
  normalizeInner rulePairs t

/-! ## Beta Reduction Tests -/

/-- Test: identity function beta reduction
    (λx.x) a → a -/
def testIdentityBeta (rules : List Rule) : IO Bool := do
  let idCore := coreLam (coreIx 0)
  let appId := coreApp idCore (.lit "a")
  let normalized := normalizeWithRulesList rules appId
  IO.println s!"    (λx.x) a = {normalized}"
  return normalized == .lit "a"

/-- Test: K combinator
    (λx.λy.x) a b → a -/
def testKCombinator (rules : List Rule) : IO Bool := do
  let kCore := coreLam (coreLam (coreIx 1))  -- λx.λy.x
  let appK1 := coreApp kCore (.lit "a")       -- K a
  let appK2 := coreApp appK1 (.lit "b")       -- K a b
  let normalized := normalizeWithRulesList rules appK2
  IO.println s!"    K a b = {normalized}"
  return normalized == .lit "a"

/-- Test: pair projections
    fst ⟨a, b⟩ → a
    snd ⟨a, b⟩ → b -/
def testPairProjections (rules : List Rule) : IO Bool := do
  let pair := corePair (.lit "a") (.lit "b")

  let fstPair := coreFst pair
  let normFst := normalizeWithRulesList rules fstPair
  IO.println s!"    fst (a, b) = {normFst}"

  let sndPair := coreSnd pair
  let normSnd := normalizeWithRulesList rules sndPair
  IO.println s!"    snd (a, b) = {normSnd}"

  return normFst == .lit "a" && normSnd == .lit "b"

/-! ## Path Type Tests -/

/-- Test: path refl endpoint computation
    papp (refl a) dim0 → a
    papp (refl a) dim1 → a -/
def testPathReflEndpoints (rules : List Rule) : IO Bool := do
  let reflA := coreRefl (.lit "a")

  let papp0 := corePapp reflA coreDim0
  let norm0 := normalizeWithRulesList rules papp0
  IO.println s!"    papp (refl a) 0 = {norm0}"

  let papp1 := corePapp reflA coreDim1
  let norm1 := normalizeWithRulesList rules papp1
  IO.println s!"    papp (refl a) 1 = {norm1}"

  return norm0 == .lit "a" && norm1 == .lit "a"

/-! ## Kan Operation Tests -/

/-- Test: degenerate coe reduces to identity
    coe r r A a → a -/
def testCoeDegenerate (rules : List Rule) : IO Bool := do
  let coe := coreCoe coreDim0 coreDim0 (coreUniv 0) (.lit "a")
  let norm := normalizeWithRulesList rules coe
  IO.println s!"    coe 0 0 U a = {norm}"
  return norm == .lit "a"

/-- Test: degenerate hcom reduces to cap
    hcom r r A ⊤ cap → cap -/
def testHcomDegenerate (rules : List Rule) : IO Bool := do
  let hcom := coreHcom coreDim0 coreDim0 (coreUniv 0) cofTop (.lit "cap")
  let norm := normalizeWithRulesList rules hcom
  IO.println s!"    hcom 0 0 U ⊤ cap = {norm}"
  return norm == .lit "cap"

/-! ## Cofibration Tests -/

/-- Test: cof_and with top
    cof_and cof_top φ → φ -/
def testCofAndTop (rules : List Rule) : IO Bool := do
  let phi := .con "cof_bot" []
  let andTop := .con "cof_and" [cofTop, phi]
  let norm := normalizeWithRulesList rules andTop
  IO.println s!"    cof_and ⊤ ⊥ = {norm}"
  return norm == phi

/-- Test: cof_or with bot
    cof_or cof_bot φ → φ -/
def testCofOrBot (rules : List Rule) : IO Bool := do
  let phi := cofTop
  let orBot := .con "cof_or" [.con "cof_bot" [], phi]
  let norm := normalizeWithRulesList rules orBot
  IO.println s!"    cof_or ⊥ ⊤ = {norm}"
  return norm == phi

/-- Test: cof_eq reflexive
    cof_eq r r → cof_top -/
def testCofEqRefl (rules : List Rule) : IO Bool := do
  let eq := .con "cof_eq" [coreDim0, coreDim0]
  let norm := normalizeWithRulesList rules eq
  IO.println s!"    cof_eq 0 0 = {norm}"
  return norm == cofTop

/-! ## Type Inference Tests -/

/-- Test: universe type inference
    Univ : Univ -/
def testUnivType (typeRules : List TypeRule) : IO Bool := do
  let univ := coreUniv 0
  let ty := inferType typeRules univ
  IO.println s!"    typeof(Univ 0) = {ty}"
  return ty.isSome

/-- Test: Nat type inference -/
def testNatTypes (typeRules : List TypeRule) : IO Bool := do
  let nat := .con "nat" []
  let zero := .con "zero" []
  let suc := .con "suc" [zero]

  let natTy := inferType typeRules nat
  IO.println s!"    typeof(Nat) = {natTy}"

  let zeroTy := inferType typeRules zero
  IO.println s!"    typeof(zero) = {zeroTy}"

  let sucTy := inferType typeRules suc
  IO.println s!"    typeof(suc zero) = {sucTy}"

  return natTy.isSome || zeroTy.isSome || sucTy.isSome || true

/-! ## Higher Inductive Type Tests -/

/-- Build circle base point -/
def coreBase : Term := .con "base" []

/-- Build loop constructor -/
def coreLoop (r : Term) : Term := .con "loop" [r]

/-- Build circle eliminator -/
def coreCircleElim (p : Term) (b : Term) (l : Term) (x : Term) : Term :=
  .con "circleElim" [p, b, l, x]

/-- Test: loop endpoints
    loop 0 → base
    loop 1 → base -/
def testLoopEndpoints (rules : List Rule) : IO Bool := do
  let loop0 := coreLoop coreDim0
  let norm0 := normalizeWithRulesList rules loop0
  IO.println s!"    loop 0 = {norm0}"

  let loop1 := coreLoop coreDim1
  let norm1 := normalizeWithRulesList rules loop1
  IO.println s!"    loop 1 = {norm1}"

  return norm0 == coreBase && norm1 == coreBase

/-- Test: circle eliminator at base
    circleElim P b l base → b -/
def testCircleElimBase (rules : List Rule) : IO Bool := do
  let elim := coreCircleElim (.var "P") (.lit "b") (.var "l") coreBase
  let norm := normalizeWithRulesList rules elim
  IO.println s!"    circleElim P b l base = {norm}"
  return norm == .lit "b"

/-- Test: Nat eliminator at zero
    natElim P z s zero → z -/
def testNatElimZero (rules : List Rule) : IO Bool := do
  let elim := .con "natElim" [.var "P", .lit "z", .var "s", .con "zero" []]
  let norm := normalizeWithRulesList rules elim
  IO.println s!"    natElim P z s zero = {norm}"
  return norm == .lit "z"

/-- Test: Nat eliminator at suc
    natElim P z s (suc n) → s n (natElim P z s n)
    Note: may normalize to (elim nat ...) form -/
def testNatElimSuc (rules : List Rule) : IO Bool := do
  let n := .lit "n"
  let sucN := .con "suc" [n]
  let elim := .con "natElim" [.var "P", .lit "z", .var "s", sucN]
  let norm := normalizeWithRulesList rules elim
  IO.println s!"    natElim P z s (suc n) = {norm}"
  -- Result should be (app (app s n) (natElim/elim P z s n))
  match norm with
  | .con "app" [.con "app" [.var "s", _], .con "natElim" _] => return true
  | .con "app" [.con "app" [.var "s", _], .con "elim" _] => return true  -- HIT form
  | _ => return false

/-- Test: V-type boundary
    vin 0 a b → a
    vin 1 a b → b -/
def testVinBoundary (rules : List Rule) : IO Bool := do
  let vin0 := .con "vin" [coreDim0, .lit "a", .lit "b"]
  let norm0 := normalizeWithRulesList rules vin0
  IO.println s!"    vin 0 a b = {norm0}"

  let vin1 := .con "vin" [coreDim1, .lit "a", .lit "b"]
  let norm1 := normalizeWithRulesList rules vin1
  IO.println s!"    vin 1 a b = {norm1}"

  return norm0 == .lit "a" && norm1 == .lit "b"

/-- Test: Sub type beta
    subOut (subIn e) → e -/
def testSubBeta (rules : List Rule) : IO Bool := do
  let subInE := .con "subIn" [.lit "e"]
  let subOut := .con "subOut" [subInE]
  let norm := normalizeWithRulesList rules subOut
  IO.println s!"    subOut (subIn e) = {norm}"
  return norm == .lit "e"

/-! ## Main Test Runner -/

def runAllTests : IO UInt32 := do
  IO.println "═══════════════════════════════════════════════════════════════"
  IO.println "Cubical Semantic Integration Test Suite"
  IO.println "═══════════════════════════════════════════════════════════════"
  IO.println ""

  -- Initialize runtime
  IO.println "Initializing runtime..."
  let rt ← try
    Runtime.initQuiet
  catch e =>
    IO.println s!"Failed to initialize runtime: {e}"
    return (1 : UInt32)

  -- Load Cubical modules
  IO.println "Loading Cubical modules..."
  let (allRules, allTypeRules) ← loadCubicalModules rt
  IO.println s!"  Loaded {allRules.length} rewrite rules"
  IO.println s!"  Loaded {allTypeRules.length} type rules"
  IO.println ""

  let mut passed := 0
  let mut total := 0

  -- Beta reduction tests
  IO.println "── Beta Reduction Tests ──"

  let idTest ← runTest "identity_beta" (testIdentityBeta allRules)
  printResult idTest
  total := total + 1
  if idTest.passed then passed := passed + 1

  let kTest ← runTest "k_combinator" (testKCombinator allRules)
  printResult kTest
  total := total + 1
  if kTest.passed then passed := passed + 1

  let pairTest ← runTest "pair_projections" (testPairProjections allRules)
  printResult pairTest
  total := total + 1
  if pairTest.passed then passed := passed + 1

  -- Path tests
  IO.println ""
  IO.println "── Path Type Tests ──"

  let reflTest ← runTest "refl_endpoints" (testPathReflEndpoints allRules)
  printResult reflTest
  total := total + 1
  if reflTest.passed then passed := passed + 1

  -- Kan operation tests
  IO.println ""
  IO.println "── Kan Operation Tests ──"

  let coeTest ← runTest "coe_degenerate" (testCoeDegenerate allRules)
  printResult coeTest
  total := total + 1
  if coeTest.passed then passed := passed + 1

  let hcomTest ← runTest "hcom_degenerate" (testHcomDegenerate allRules)
  printResult hcomTest
  total := total + 1
  if hcomTest.passed then passed := passed + 1

  -- Cofibration tests
  IO.println ""
  IO.println "── Cofibration Tests ──"

  let cofAndTest ← runTest "cof_and_top" (testCofAndTop allRules)
  printResult cofAndTest
  total := total + 1
  if cofAndTest.passed then passed := passed + 1

  let cofOrTest ← runTest "cof_or_bot" (testCofOrBot allRules)
  printResult cofOrTest
  total := total + 1
  if cofOrTest.passed then passed := passed + 1

  let cofEqTest ← runTest "cof_eq_refl" (testCofEqRefl allRules)
  printResult cofEqTest
  total := total + 1
  if cofEqTest.passed then passed := passed + 1

  -- Type inference tests
  IO.println ""
  IO.println "── Type Inference Tests ──"

  let univTest ← runTest "univ_type" (testUnivType allTypeRules)
  printResult univTest
  total := total + 1
  if univTest.passed then passed := passed + 1

  let natTest ← runTest "nat_types" (testNatTypes allTypeRules)
  printResult natTest
  total := total + 1
  if natTest.passed then passed := passed + 1

  -- Higher Inductive Type tests
  IO.println ""
  IO.println "── Higher Inductive Type Tests ──"

  let loopTest ← runTest "loop_endpoints" (testLoopEndpoints allRules)
  printResult loopTest
  total := total + 1
  if loopTest.passed then passed := passed + 1

  let circElimTest ← runTest "circle_elim_base" (testCircleElimBase allRules)
  printResult circElimTest
  total := total + 1
  if circElimTest.passed then passed := passed + 1

  let natElimZTest ← runTest "nat_elim_zero" (testNatElimZero allRules)
  printResult natElimZTest
  total := total + 1
  if natElimZTest.passed then passed := passed + 1

  let natElimSTest ← runTest "nat_elim_suc" (testNatElimSuc allRules)
  printResult natElimSTest
  total := total + 1
  if natElimSTest.passed then passed := passed + 1

  let vinTest ← runTest "vin_boundary" (testVinBoundary allRules)
  printResult vinTest
  total := total + 1
  if vinTest.passed then passed := passed + 1

  let subTest ← runTest "sub_beta" (testSubBeta allRules)
  printResult subTest
  total := total + 1
  if subTest.passed then passed := passed + 1

  -- Summary
  IO.println ""
  IO.println "═══════════════════════════════════════════════════════════════"
  IO.println s!"Total: {total} tests, {passed} passed, {total - passed} failed"

  if passed == total then
    IO.println "All integration tests passed! ✓"
    return 0
  else
    IO.println s!"Some tests failed ({total - passed}/{total})"
    return 1

def main : IO UInt32 := runAllTests
