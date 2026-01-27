/-
  TestCubicalCore.lean: Tests for the core cubical TT operations

  This tests the cubical types and operations in Lego.Algebra and Lego.Normalize.
-/

import Lego
import Lego.Normalize

open Lego
open Lego.Cubical

/-! ## Test Helpers -/

def assertEqual (name : String) (actual expected : Term) : IO Bool := do
  if actual == expected then
    IO.println s!"  ✓ {name}"
    pure true
  else
    IO.println s!"  ✗ {name}"
    IO.println s!"    Expected: {expected}"
    IO.println s!"    Actual:   {actual}"
    pure false

def assertEqualBool (name : String) (actual expected : Bool) : IO Bool := do
  if actual == expected then
    IO.println s!"  ✓ {name}"
    pure true
  else
    IO.println s!"  ✗ {name}"
    IO.println s!"    Expected: {expected}"
    IO.println s!"    Actual:   {actual}"
    pure false

/-! ## Dimension Tests -/

def testDimTypes : IO Nat := do
  IO.println "\n── Dimension Types ──"
  let mut passed := 0

  -- Dim constructors work
  if ← assertEqual "dim0_construct" (.con "dim0" []) (.con "dim0" []) then passed := passed + 1
  if ← assertEqual "dim1_construct" (.con "dim1" []) (.con "dim1" []) then passed := passed + 1
  if ← assertEqual "dimVar_construct" (.con "dimVar" [.lit "0"]) (.con "dimVar" [.lit "0"]) then passed := passed + 1

  pure passed

/-! ## Cofibration Tests -/

def testCofSimplify : IO Nat := do
  IO.println "\n── Cofibration Simplification ──"
  let mut passed := 0

  -- cof_eq r r = top
  let r1 := simplifyCof (.con "cof_eq" [.con "dim0" [], .con "dim0" []])
  if ← assertEqual "eq_refl" r1 (.con "cof_top" []) then passed := passed + 1

  -- cof_eq 0 1 = bot
  let r2 := simplifyCof (.con "cof_eq" [.con "dim0" [], .con "dim1" []])
  if ← assertEqual "eq_01" r2 (.con "cof_bot" []) then passed := passed + 1

  -- cof_and top φ = φ
  let r3 := simplifyCof (.con "cof_and" [.con "cof_top" [], .con "cof_eq" [.con "dim0" [], .con "dim0" []]])
  if ← assertEqual "and_top_l" r3 (.con "cof_top" []) then passed := passed + 1

  -- cof_and bot φ = bot
  let r4 := simplifyCof (.con "cof_and" [.con "cof_bot" [], .con "cof_top" []])
  if ← assertEqual "and_bot_l" r4 (.con "cof_bot" []) then passed := passed + 1

  -- cof_or top φ = top
  let r5 := simplifyCof (.con "cof_or" [.con "cof_top" [], .con "cof_bot" []])
  if ← assertEqual "or_top_l" r5 (.con "cof_top" []) then passed := passed + 1

  -- cof_or bot φ = φ
  let r6 := simplifyCof (.con "cof_or" [.con "cof_bot" [], .con "cof_top" []])
  if ← assertEqual "or_bot_l" r6 (.con "cof_top" []) then passed := passed + 1

  pure passed

def testCofEval : IO Nat := do
  IO.println "\n── Cofibration Evaluation ──"
  let mut passed := 0

  if ← assertEqualBool "eval_top" (evalCof (.con "cof_top" [])) true then passed := passed + 1
  if ← assertEqualBool "eval_bot" (evalCof (.con "cof_bot" [])) false then passed := passed + 1
  if ← assertEqualBool "eval_eq_same" (evalCof (.con "cof_eq" [.con "dim0" [], .con "dim0" []])) true then passed := passed + 1
  if ← assertEqualBool "eval_eq_diff" (evalCof (.con "cof_eq" [.con "dim0" [], .con "dim1" []])) false then passed := passed + 1
  if ← assertEqualBool "eval_and_tt" (evalCof (.con "cof_and" [.con "cof_top" [], .con "cof_top" []])) true then passed := passed + 1
  if ← assertEqualBool "eval_and_tf" (evalCof (.con "cof_and" [.con "cof_top" [], .con "cof_bot" []])) false then passed := passed + 1
  if ← assertEqualBool "eval_or_ft" (evalCof (.con "cof_or" [.con "cof_bot" [], .con "cof_top" []])) true then passed := passed + 1
  if ← assertEqualBool "eval_or_ff" (evalCof (.con "cof_or" [.con "cof_bot" [], .con "cof_bot" []])) false then passed := passed + 1

  pure passed

/-! ## Level Tests -/

def testLevelSimplify : IO Nat := do
  IO.println "\n── Level Simplification ──"
  let mut passed := 0

  -- lmax l l = l
  let r1 := simplifyLevel (.con "lmax" [.con "lsuc" [.con "lzero" []], .con "lsuc" [.con "lzero" []]])
  if ← assertEqual "max_idem" r1 (.con "lsuc" [.con "lzero" []]) then passed := passed + 1

  -- lmax lzero l = l
  let r2 := simplifyLevel (.con "lmax" [.con "lzero" [], .con "lsuc" [.con "lzero" []]])
  if ← assertEqual "max_zero_l" r2 (.con "lsuc" [.con "lzero" []]) then passed := passed + 1

  -- lmax l lzero = l
  let r3 := simplifyLevel (.con "lmax" [.con "lsuc" [.con "lzero" []], .con "lzero" []])
  if ← assertEqual "max_zero_r" r3 (.con "lsuc" [.con "lzero" []]) then passed := passed + 1

  -- lmax (lsuc a) (lsuc b) = lsuc (lmax a b)
  let r4 := simplifyLevel (.con "lmax" [
    .con "lsuc" [.con "lsuc" [.con "lzero" []]],
    .con "lsuc" [.con "lzero" []]
  ])
  if ← assertEqual "max_suc_suc" r4 (.con "lsuc" [.con "lsuc" [.con "lzero" []]]) then passed := passed + 1

  pure passed

/-! ## Step Tests -/

def testStep : IO Nat := do
  IO.println "\n── Single-Step Reduction ──"
  let mut passed := 0
  let rules : List (Term × Term) := []

  -- Beta reduction
  let beta := step rules (.con "app" [.con "lam" [.con "ix" [.lit "0"]], .lit "x"])
  if ← assertEqual "beta" (beta.getD (.lit "?")) (.lit "x") then passed := passed + 1

  -- Fst projection
  let fst := step rules (.con "fst" [.con "pair" [.lit "a", .lit "b"]])
  if ← assertEqual "fst" (fst.getD (.lit "?")) (.lit "a") then passed := passed + 1

  -- Snd projection
  let snd := step rules (.con "snd" [.con "pair" [.lit "a", .lit "b"]])
  if ← assertEqual "snd" (snd.getD (.lit "?")) (.lit "b") then passed := passed + 1

  -- Path application to refl
  let papp := step rules (.con "papp" [.con "refl" [.lit "a"], .con "dim0" []])
  if ← assertEqual "papp_refl" (papp.getD (.lit "?")) (.lit "a") then passed := passed + 1

  -- Coe reflective
  let coeRefl := step rules (.con "coe" [.con "dim0" [], .con "dim0" [], .con "univ" [.con "lzero" []], .lit "A"])
  if ← assertEqual "coe_refl" (coeRefl.getD (.lit "?")) (.lit "A") then passed := passed + 1

  -- V-in at dim0
  let vin0 := step rules (.con "vin" [.con "dim0" [], .lit "a", .lit "b"])
  if ← assertEqual "vin_0" (vin0.getD (.lit "?")) (.lit "a") then passed := passed + 1

  -- V-in at dim1
  let vin1 := step rules (.con "vin" [.con "dim1" [], .lit "a", .lit "b"])
  if ← assertEqual "vin_1" (vin1.getD (.lit "?")) (.lit "b") then passed := passed + 1

  -- Loop at dim0
  let loop0 := step rules (.con "loop" [.con "dim0" []])
  if ← assertEqual "loop_0" (loop0.getD (.lit "?")) (.con "base" []) then passed := passed + 1

  -- Loop at dim1
  let loop1 := step rules (.con "loop" [.con "dim1" []])
  if ← assertEqual "loop_1" (loop1.getD (.lit "?")) (.con "base" []) then passed := passed + 1

  pure passed

/-! ## Normalization Tests -/

def testNormalize : IO Nat := do
  IO.println "\n── Normalization ──"
  let mut passed := 0
  let rules : List (Term × Term) := []

  -- Nested beta
  let nested := normalize 100 rules (.con "app" [
    .con "lam" [.con "app" [.con "lam" [.con "ix" [.lit "0"]], .con "ix" [.lit "0"]]],
    .lit "x"
  ])
  if ← assertEqual "nested_beta" nested (.lit "x") then passed := passed + 1

  -- Cof simplification through normalization
  let cofNorm := normalize 100 rules (.con "cof_and" [
    .con "cof_top" [],
    .con "cof_eq" [.con "dim0" [], .con "dim0" []]
  ])
  if ← assertEqual "cof_normalize" cofNorm (.con "cof_top" []) then passed := passed + 1

  -- Level normalization
  let levelNorm := normalize 100 rules (.con "lmax" [
    .con "lmax" [.con "lzero" [], .con "lsuc" [.con "lzero" []]],
    .con "lsuc" [.con "lzero" []]
  ])
  if ← assertEqual "level_normalize" levelNorm (.con "lsuc" [.con "lzero" []]) then passed := passed + 1

  pure passed

/-! ## Conversion Tests -/

def testConversion : IO Nat := do
  IO.println "\n── Conversion Checking ──"
  let mut passed := 0
  let rules : List (Term × Term) := []

  -- Identical terms
  if ← assertEqualBool "conv_refl" (conv rules 100 (.lit "x") (.lit "x")) true then passed := passed + 1

  -- After beta reduction
  let t1 := .con "app" [.con "lam" [.con "ix" [.lit "0"]], .lit "x"]
  let t2 := .lit "x"
  if ← assertEqualBool "conv_beta" (conv rules 100 t1 t2) true then passed := passed + 1

  -- Different terms
  if ← assertEqualBool "conv_diff" (conv rules 100 (.lit "x") (.lit "y")) false then passed := passed + 1

  pure passed

/-! ## Path Combinator Tests -/

def testPathCombinators : IO Nat := do
  IO.println "\n── Path Combinators ──"
  let mut passed := 0
  let rules : List (Term × Term) := []

  -- sym (refl a) = refl a
  let symRefl := step rules (.con "sym" [.con "refl" [.lit "a"]])
  if ← assertEqual "sym_refl" (symRefl.getD (.lit "?")) (.con "refl" [.lit "a"]) then passed := passed + 1

  -- trans (refl a) q = q
  let transReflL := step rules (.con "trans" [.con "refl" [.lit "a"], .con "plam" [.lit "body"]])
  if ← assertEqual "trans_refl_l" (transReflL.getD (.lit "?")) (.con "plam" [.lit "body"]) then passed := passed + 1

  -- trans p (refl b) = p
  let transReflR := step rules (.con "trans" [.con "plam" [.lit "body"], .con "refl" [.lit "b"]])
  if ← assertEqual "trans_refl_r" (transReflR.getD (.lit "?")) (.con "plam" [.lit "body"]) then passed := passed + 1

  -- happly (funExt h) x = h x
  let happlyFunExt := step rules (.con "happly" [.con "funExt" [.lit "h"], .lit "x"])
  if ← assertEqual "happly_funext" (happlyFunExt.getD (.lit "?")) (.con "app" [.lit "h", .lit "x"]) then passed := passed + 1

  -- happly (refl f) x = refl (f x)
  let happlyRefl := step rules (.con "happly" [.con "refl" [.lit "f"], .lit "x"])
  if ← assertEqual "happly_refl" (happlyRefl.getD (.lit "?")) (.con "refl" [.con "app" [.lit "f", .lit "x"]]) then passed := passed + 1

  pure passed

/-! ## Equivalence Tests -/

def testEquivalences : IO Nat := do
  IO.println "\n── Equivalences ──"
  let mut passed := 0
  let rules : List (Term × Term) := []

  -- equivFun (idEquiv A) = λx.x
  let equivFunId := step rules (.con "equivFun" [.con "idEquiv" [.lit "A"]])
  if ← assertEqual "equivFun_id" (equivFunId.getD (.lit "?")) (.con "lam" [.con "ix" [.lit "0"]]) then passed := passed + 1

  -- ua (idEquiv A) = refl A
  let uaId := step rules (.con "ua" [.con "idEquiv" [.lit "A"]])
  if ← assertEqual "ua_id" (uaId.getD (.lit "?")) (.con "refl" [.lit "A"]) then passed := passed + 1

  -- compEquiv (idEquiv A) e = e
  let compEquivIdL := step rules (.con "compEquiv" [.con "idEquiv" [.lit "A"], .lit "e"])
  if ← assertEqual "compEquiv_id_l" (compEquivIdL.getD (.lit "?")) (.lit "e") then passed := passed + 1

  -- compEquiv e (idEquiv B) = e
  let compEquivIdR := step rules (.con "compEquiv" [.lit "e", .con "idEquiv" [.lit "B"]])
  if ← assertEqual "compEquiv_id_r" (compEquivIdR.getD (.lit "?")) (.lit "e") then passed := passed + 1

  -- invEquiv (idEquiv A) = idEquiv A
  let invEquivId := step rules (.con "invEquiv" [.con "idEquiv" [.lit "A"]])
  if ← assertEqual "invEquiv_id" (invEquivId.getD (.lit "?")) (.con "idEquiv" [.lit "A"]) then passed := passed + 1

  pure passed

/-! ## Sigma Type Tests -/

def testSigmaTypes : IO Nat := do
  IO.println "\n── Sigma Types ──"
  let mut passed := 0
  let rules : List (Term × Term) := []

  -- dfst (dpair a b) = a
  let dfstPair := step rules (.con "dfst" [.con "dpair" [.lit "a", .lit "b"]])
  if ← assertEqual "dfst_pair" (dfstPair.getD (.lit "?")) (.lit "a") then passed := passed + 1

  -- dsnd (dpair a b) = b
  let dsndPair := step rules (.con "dsnd" [.con "dpair" [.lit "a", .lit "b"]])
  if ← assertEqual "dsnd_pair" (dsndPair.getD (.lit "?")) (.lit "b") then passed := passed + 1

  pure passed

/-! ## Contractibility Tests -/

def testContractibility : IO Nat := do
  IO.println "\n── Contractibility ──"
  let mut passed := 0
  let rules : List (Term × Term) := []

  -- center (mkContr c p) = c
  let centerMk := step rules (.con "center" [.con "mkContr" [.lit "c", .lit "p"]])
  if ← assertEqual "center_mk" (centerMk.getD (.lit "?")) (.lit "c") then passed := passed + 1

  -- paths (mkContr c p) = p
  let pathsMk := step rules (.con "paths" [.con "mkContr" [.lit "c", .lit "p"]])
  if ← assertEqual "paths_mk" (pathsMk.getD (.lit "?")) (.lit "p") then passed := passed + 1

  pure passed

/-! ## Propositional Truncation Tests -/

def testPropTrunc : IO Nat := do
  IO.println "\n── Propositional Truncation ──"
  let mut passed := 0
  let rules : List (Term × Term) := []

  -- propElim P isPropB f (squash x) = f x
  let propElimSquash := step rules (.con "propElim" [.lit "P", .lit "isPropB", .lit "f", .con "squash" [.lit "x"]])
  if ← assertEqual "propElim_squash" (propElimSquash.getD (.lit "?")) (.con "app" [.lit "f", .lit "x"]) then passed := passed + 1

  pure passed

/-! ## Transport Tests -/

def testTransport : IO Nat := do
  IO.println "\n── Transport ──"
  let mut passed := 0
  let rules : List (Term × Term) := []

  -- transp A ⊤ a = a
  let transpTop := step rules (.con "transp" [.lit "A", .con "cof_top" [], .lit "a"])
  if ← assertEqual "transp_top" (transpTop.getD (.lit "?")) (.lit "a") then passed := passed + 1

  -- J A a P d a (refl a) = d
  let jRefl := step rules (.con "J" [.lit "A", .lit "a", .lit "P", .lit "d", .lit "a", .con "refl" [.lit "a"]])
  if ← assertEqual "j_refl" (jRefl.getD (.lit "?")) (.lit "d") then passed := passed + 1

  pure passed

/-! ## Proof Tactics Tests -/

def testProofTactics : IO Nat := do
  IO.println "\n── Proof Tactics ──"
  let mut passed := 0
  let rules : List (Term × Term) := []

  -- have x A proof body reduces to body[proof/x]
  let haveBeta := step rules (.con "have" [.lit "x", .lit "A", .lit "proof", .con "ix" [.lit "0"]])
  if ← assertEqual "have_beta" (haveBeta.getD (.lit "?")) (.lit "proof") then passed := passed + 1

  -- let_ x A val body reduces to body[val/x]
  let letBeta := step rules (.con "let_" [.lit "x", .lit "A", .lit "val", .con "ix" [.lit "0"]])
  if ← assertEqual "let_beta" (letBeta.getD (.lit "?")) (.lit "val") then passed := passed + 1

  -- exact e = e
  let exactE := step rules (.con "exact" [.lit "e"])
  if ← assertEqual "exact_e" (exactE.getD (.lit "?")) (.lit "e") then passed := passed + 1

  pure passed

/-! ## Language Designer Tests -/

def testLangDesignerCubical : IO Nat := do
  IO.println "\n── Language Designer Cubical ──"
  let mut passed := 0
  let rules : List (Term × Term) := []

  -- transport_prop (idEquiv A) P a = P a
  let transportProp := step rules (.con "transport_prop" [.con "idEquiv" [.lit "A"], .lit "P", .lit "a"])
  if ← assertEqual "transport_prop_id" (transportProp.getD (.lit "?")) (.con "app" [.lit "P", .lit "a"]) then passed := passed + 1

  -- optimize rule (refl e) = e
  let optimize := step rules (.con "optimize" [.lit "rule", .con "refl" [.lit "e"]])
  if ← assertEqual "optimize_refl" (optimize.getD (.lit "?")) (.lit "e") then passed := passed + 1

  -- quotElim B f resp (quot a) = f a
  let quotElim := step rules (.con "quotElim" [.lit "B", .lit "f", .lit "resp", .con "quot" [.lit "a"]])
  if ← assertEqual "quotElim_quot" (quotElim.getD (.lit "?")) (.con "app" [.lit "f", .lit "a"]) then passed := passed + 1

  -- coerce_repr e a = equivFun e a
  let coerceRepr := step rules (.con "coerce_repr" [.lit "e", .lit "a"])
  if ← assertEqual "coerce_repr" (coerceRepr.getD (.lit "?")) (.con "app" [.con "equivFun" [.lit "e"], .lit "a"]) then passed := passed + 1

  -- lift_prop (idEquiv A) P x = P x
  let liftProp := step rules (.con "lift_prop" [.con "idEquiv" [.lit "A"], .lit "P", .lit "x"])
  if ← assertEqual "lift_prop_id" (liftProp.getD (.lit "?")) (.con "app" [.lit "P", .lit "x"]) then passed := passed + 1

  -- project e (embed e' t) = t
  let project := step rules (.con "project" [.lit "e", .con "embed" [.lit "e", .lit "t"]])
  if ← assertEqual "project_embed" (project.getD (.lit "?")) (.lit "t") then passed := passed + 1

  -- by_obs (obs_refl a) = refl a
  let byObsRefl := step rules (.con "by_obs" [.con "obs_refl" [.lit "a"]])
  if ← assertEqual "by_obs_refl" (byObsRefl.getD (.lit "?")) (.con "refl" [.lit "a"]) then passed := passed + 1

  -- unrefine (refine a p) = a
  let unrefine := step rules (.con "unrefine" [.con "refine" [.lit "a", .lit "p"]])
  if ← assertEqual "unrefine_refine" (unrefine.getD (.lit "?")) (.lit "a") then passed := passed + 1

  -- ind_path F (refl i) x = refl x
  let indPath := step rules (.con "ind_path" [.lit "F", .con "refl" [.lit "i"], .lit "x"])
  if ← assertEqual "ind_path_refl" (indPath.getD (.lit "?")) (.con "refl" [.lit "x"]) then passed := passed + 1

  -- lift_rule e (refl t) = refl (embed e t)
  let liftRule := step rules (.con "lift_rule" [.lit "e", .con "refl" [.lit "t"]])
  if ← assertEqual "lift_rule_refl" (liftRule.getD (.lit "?")) (.con "refl" [.con "embed" [.lit "e", .lit "t"]]) then passed := passed + 1

  pure passed

/-! ## Type Checking with Conditions Tests -/

def testTypeRuleConditions : IO Nat := do
  IO.println "\n── Type Rule Condition Checking ──"
  let mut passed := 0

  -- Create type rules with conditions
  -- Rule: (refl $a) : (Path $A $a $a) when $a : $A
  let reflRule : TypeRule := {
    name := "reflType"
    subject := .con "refl" [.var "$a"]
    type := .con "Path" [.var "$A", .var "$a", .var "$a"]
    conditions := [.con ":" [.var "$a", .var "$A"]]
  }

  -- Rule: (zero) : Nat (no conditions)
  let zeroRule : TypeRule := {
    name := "zeroType"
    subject := .con "zero" []
    type := .con "Nat" []
    conditions := []
  }

  -- Rule: (succ $n) : Nat when $n : Nat
  let succRule : TypeRule := {
    name := "succType"
    subject := .con "succ" [.var "$n"]
    type := .con "Nat" []
    conditions := [.con ":" [.var "$n", .con "Nat" []]]
  }

  let typeRules := [reflRule, zeroRule, succRule]

  -- Test basic type inference (no conditions)
  let zeroTy := inferType typeRules (.con "zero" [])
  if ← assertEqual "zero_type" (zeroTy.getD (.lit "?")) (.con "Nat" []) then passed := passed + 1

  -- Test type inference with conditions - should pass for (succ (zero))
  let succZeroTy := inferType typeRules (.con "succ" [.con "zero" []])
  if ← assertEqual "succ_zero_type" (succZeroTy.getD (.lit "?")) (.con "Nat" []) then passed := passed + 1

  -- Test applyWithCheck - basic case
  let zeroCheck := zeroRule.applyWithCheck typeRules (.con "zero" [])
  if ← assertEqual "zero_withcheck" (zeroCheck.getD (.lit "?")) (.con "Nat" []) then passed := passed + 1

  -- Test applyWithCheck - with conditions that should pass
  -- (succ (zero)) with conditions checking that (zero) : Nat
  let succZeroCheck := succRule.applyWithCheck typeRules (.con "succ" [.con "zero" []])
  if ← assertEqual "succ_zero_withcheck" (succZeroCheck.getD (.lit "?")) (.con "Nat" []) then passed := passed + 1

  pure passed

/-! ## Main -/

def main : IO UInt32 := do
  IO.println "╔═══════════════════════════════════════════════════════════════╗"
  IO.println "║             Cubical Type Theory Core Tests                    ║"
  IO.println "╚═══════════════════════════════════════════════════════════════╝"

  let mut total := 0
  let mut passed := 0

  let dimPassed ← testDimTypes
  passed := passed + dimPassed
  total := total + 3

  let cofSimplifyPassed ← testCofSimplify
  passed := passed + cofSimplifyPassed
  total := total + 6

  let cofEvalPassed ← testCofEval
  passed := passed + cofEvalPassed
  total := total + 8

  let levelPassed ← testLevelSimplify
  passed := passed + levelPassed
  total := total + 4

  let stepPassed ← testStep
  passed := passed + stepPassed
  total := total + 9

  let normPassed ← testNormalize
  passed := passed + normPassed
  total := total + 3

  let convPassed ← testConversion
  passed := passed + convPassed
  total := total + 3

  -- New proof tests
  let pathCombPassed ← testPathCombinators
  passed := passed + pathCombPassed
  total := total + 5

  let equivPassed ← testEquivalences
  passed := passed + equivPassed
  total := total + 5

  let sigmaPassed ← testSigmaTypes
  passed := passed + sigmaPassed
  total := total + 2

  let contrPassed ← testContractibility
  passed := passed + contrPassed
  total := total + 2

  let propTruncPassed ← testPropTrunc
  passed := passed + propTruncPassed
  total := total + 1

  let transpPassed ← testTransport
  passed := passed + transpPassed
  total := total + 2

  let tacticsPassed ← testProofTactics
  passed := passed + tacticsPassed
  total := total + 3

  -- Language designer constructs
  let langDesignerPassed ← testLangDesignerCubical
  passed := passed + langDesignerPassed
  total := total + 10

  -- Type rule condition checking
  let conditionPassed ← testTypeRuleConditions
  passed := passed + conditionPassed
  total := total + 4

  IO.println ""
  IO.println "═══════════════════════════════════════════════════════════════"
  IO.println s!"Total: {total} tests, {passed} passed, {total - passed} failed"

  if passed == total then
    IO.println "All tests passed! ✓"
    pure 0
  else
    IO.println s!"⚠️  {total - passed} tests failed"
    pure 1
