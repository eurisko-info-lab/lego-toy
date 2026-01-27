/-
  TestValidation.lean: Tests for cubical verification and type checking

  Tests the verification of:
  - verified rule declarations (proof has type Path lhs rhs)
  - repr equivalences (proof has type Equiv A B)
  - Type rule condition checking
-/

import Lego
import Lego.Validation

open Lego
open Lego.Validation

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

def assertNone (name : String) (v : Option α) : IO Bool := do
  if v.isNone then
    IO.println s!"  ✓ {name}"
    pure true
  else
    IO.println s!"  ✗ {name} (expected None, got Some)"
    pure false

def assertSome (name : String) (v : Option α) : IO Bool := do
  if v.isSome then
    IO.println s!"  ✓ {name}"
    pure true
  else
    IO.println s!"  ✗ {name} (expected Some, got None)"
    pure false

def assertEmpty (name : String) (lst : List α) : IO Bool := do
  if lst.isEmpty then
    IO.println s!"  ✓ {name}"
    pure true
  else
    IO.println s!"  ✗ {name} (expected empty list, got {lst.length} items)"
    pure false

def assertNonEmpty (name : String) (lst : List α) : IO Bool := do
  if !lst.isEmpty then
    IO.println s!"  ✓ {name}"
    pure true
  else
    IO.println s!"  ✗ {name} (expected non-empty list)"
    pure false

/-! ## Type Rule Tests -/

def testTypeRulesBasic : IO Nat := do
  IO.println "\n── Basic Type Rules ──"
  let mut passed := 0

  -- Create some basic type rules
  let natRule : TypeRule := {
    name := "natType"
    subject := .con "Nat" []
    type := .con "Univ" []
    conditions := []
  }

  let zeroRule : TypeRule := {
    name := "zeroType"
    subject := .con "zero" []
    type := .con "Nat" []
    conditions := []
  }

  let succRule : TypeRule := {
    name := "succType"
    subject := .con "succ" [.var "$n"]
    type := .con "Nat" []
    conditions := [.con ":" [.var "$n", .con "Nat" []]]
  }

  let typeRules := [natRule, zeroRule, succRule]

  -- Test basic inference
  let natTy := inferType typeRules (.con "Nat" [])
  if ← assertEqual "nat_is_univ" (natTy.getD (.lit "?")) (.con "Univ" []) then passed := passed + 1

  let zeroTy := inferType typeRules (.con "zero" [])
  if ← assertEqual "zero_is_nat" (zeroTy.getD (.lit "?")) (.con "Nat" []) then passed := passed + 1

  let succZeroTy := inferType typeRules (.con "succ" [.con "zero" []])
  if ← assertEqual "succ_zero_is_nat" (succZeroTy.getD (.lit "?")) (.con "Nat" []) then passed := passed + 1

  -- Test inference with nested terms
  let succSuccZeroTy := inferType typeRules (.con "succ" [.con "succ" [.con "zero" []]])
  if ← assertEqual "succ_succ_zero_is_nat" (succSuccZeroTy.getD (.lit "?")) (.con "Nat" []) then passed := passed + 1

  pure passed

/-! ## Condition Checking Tests -/

def testConditionChecking : IO Nat := do
  IO.println "\n── Condition Checking ──"
  let mut passed := 0

  -- Set up type rules
  let zeroRule : TypeRule := {
    name := "zeroType"
    subject := .con "zero" []
    type := .con "Nat" []
    conditions := []
  }

  let succRule : TypeRule := {
    name := "succType"
    subject := .con "succ" [.var "$n"]
    type := .con "Nat" []
    conditions := [.con ":" [.var "$n", .con "Nat" []]]
  }

  let typeRules := [zeroRule, succRule]

  -- Test condition passes when type matches
  let bindings1 := [("n", Term.con "zero" [])]
  let cond1 := Term.con ":" [.var "$n", .con "Nat" []]
  let check1 := checkCondition typeRules bindings1 cond1
  if ← assertEqualBool "cond_passes_zero" check1 true then passed := passed + 1

  -- Test condition passes for nested term
  let bindings2 := [("n", Term.con "succ" [.con "zero" []])]
  let check2 := checkCondition typeRules bindings2 cond1
  if ← assertEqualBool "cond_passes_succ_zero" check2 true then passed := passed + 1

  -- Test condition fails when type doesn't match
  let bindings3 := [("n", Term.lit "hello")]  -- string literal, not Nat
  let check3 := checkCondition typeRules bindings3 cond1
  -- This should be true because we're permissive when type can't be inferred
  if ← assertEqualBool "cond_permissive_unknown" check3 true then passed := passed + 1

  -- Test applyWithCheck
  let succResult := succRule.applyWithCheck typeRules (.con "succ" [.con "zero" []])
  if ← assertSome "applyWithCheck_valid" succResult then passed := passed + 1

  pure passed

/-! ## Verified Rule Validation Tests -/

def testVerifiedRuleValidation : IO Nat := do
  IO.println "\n── Verified Rule Validation ──"
  let mut passed := 0

  -- Set up type rules for paths
  let reflRule : TypeRule := {
    name := "reflType"
    subject := .con "refl" [.var "$a"]
    type := .con "Path" [.var "$A", .var "$a", .var "$a"]
    conditions := []
  }

  let typeRules := [reflRule]

  -- Test: valid verified rule with refl proof
  -- verified rule id : x ~> x via refl(x)
  let err1 := verifyVerifiedRule typeRules "id"
    (.var "x") (.var "x") (.con "refl" [.var "x"])
  if ← assertNone "valid_verified_rule_refl" err1 then passed := passed + 1

  -- Test: invalid verified rule - wrong proof type
  -- verified rule bad : x ~> y via refl(x)  -- refl(x) has type Path _ x x, not x y
  let err2 := verifyVerifiedRule typeRules "bad"
    (.var "x") (.var "y") (.con "refl" [.var "x"])
  if ← assertSome "invalid_verified_rule_wrong_type" err2 then passed := passed + 1

  -- Test: missing proof type
  let err3 := verifyVerifiedRule typeRules "missing"
    (.var "x") (.var "x") (.lit "not_a_path")
  if ← assertSome "invalid_verified_rule_no_type" err3 then passed := passed + 1

  pure passed

/-! ## Repr Equivalence Validation Tests -/

def testReprEquivValidation : IO Nat := do
  IO.println "\n── Repr Equivalence Validation ──"
  let mut passed := 0

  -- Set up type rules for equivalences
  let idEquivRule : TypeRule := {
    name := "idEquivType"
    subject := .con "idEquiv" [.var "$A"]
    type := .con "Equiv" [.var "$A", .var "$A"]
    conditions := []
  }

  let typeRules := [idEquivRule]

  -- Test: valid repr with idEquiv
  -- repr Nat ≃ Nat via idEquiv(Nat)
  let err1 := verifyReprEquiv typeRules "natId"
    (.con "Nat" []) (.con "Nat" []) (.con "idEquiv" [.con "Nat" []])
  if ← assertNone "valid_repr_idEquiv" err1 then passed := passed + 1

  -- Test: invalid repr - types don't match
  -- repr Nat ≃ Bool via idEquiv(Nat)  -- idEquiv(Nat) : Equiv Nat Nat, not Nat Bool
  let err2 := verifyReprEquiv typeRules "natBool"
    (.con "Nat" []) (.con "Bool" []) (.con "idEquiv" [.con "Nat" []])
  if ← assertSome "invalid_repr_wrong_type" err2 then passed := passed + 1

  -- Test: missing equiv type
  let err3 := verifyReprEquiv typeRules "missing"
    (.con "Nat" []) (.con "Nat" []) (.lit "not_an_equiv")
  if ← assertSome "invalid_repr_no_type" err3 then passed := passed + 1

  pure passed

/-! ## AST Extraction Tests -/

def testASTExtraction : IO Nat := do
  IO.println "\n── AST Extraction ──"
  let mut passed := 0

  -- Create mock AST with verified rules
  let ast1 := Term.con "seq" [
    .con "verifiedRule" [
      .con "ident" [.var "addComm"],
      .con "add" [.var "x", .var "y"],
      .con "add" [.var "y", .var "x"],
      .con "proof1" []
    ],
    .con "verifiedRule" [
      .con "ident" [.lit "mulComm"],
      .con "mul" [.var "x", .var "y"],
      .con "mul" [.var "y", .var "x"],
      .con "proof2" []
    ]
  ]

  -- Validate with empty type rules (all proofs should fail to type-check)
  let errors1 := validateVerifiedRules [] ast1
  -- Should get 2 errors (one for each rule that can't be type-checked)
  if ← assertEqualBool "extracts_verified_rules" (errors1.length == 2) true then passed := passed + 1

  -- Create mock AST with repr declarations
  let ast2 := Term.con "reprEquiv" [
    .con "ident" [.var "listTree"],
    .con "List" [.var "A"],
    .con "Tree" [.var "A"],
    .con "listTreeEquiv" []
  ]

  let errors2 := validateReprEquivs [] ast2
  if ← assertEqualBool "extracts_repr_equivs" (errors2.length == 1) true then passed := passed + 1

  pure passed

/-! ## Full Validation Tests -/

def testFullValidation : IO Nat := do
  IO.println "\n── Full Validation ──"
  let mut passed := 0

  -- Create a simple grammar for testing
  let grammar := Std.HashMap.emptyWithCapacity

  -- Empty rules
  let rules : List Rule := []

  -- Type rules for testing
  let reflRule : TypeRule := {
    name := "reflType"
    subject := .con "refl" [.var "$a"]
    type := .con "Path" [.var "$A", .var "$a", .var "$a"]
    conditions := []
  }

  let typeRules := [reflRule]

  -- AST with valid verified rule
  let validAST := Term.con "verifiedRule" [
    .con "ident" [.var "id"],
    .var "x",
    .var "x",
    .con "refl" [.var "x"]
  ]

  let result1 := validateFull grammar rules typeRules validAST
  if ← assertEqualBool "full_validation_passes" result1.passed true then passed := passed + 1

  -- AST with invalid verified rule
  let invalidAST := Term.con "verifiedRule" [
    .con "ident" [.var "bad"],
    .var "x",
    .var "y",  -- different from x!
    .con "refl" [.var "x"]
  ]

  let result2 := validateFull grammar rules typeRules invalidAST
  if ← assertEqualBool "full_validation_fails" result2.passed false then passed := passed + 1

  pure passed

/-! ## Main -/

def main : IO UInt32 := do
  IO.println "╔═══════════════════════════════════════════════════════════════╗"
  IO.println "║          Cubical Verification & Type Checking Tests           ║"
  IO.println "╚═══════════════════════════════════════════════════════════════╝"

  let mut total := 0
  let mut passed := 0

  let basicPassed ← testTypeRulesBasic
  passed := passed + basicPassed
  total := total + 4

  let condPassed ← testConditionChecking
  passed := passed + condPassed
  total := total + 4

  let verifiedPassed ← testVerifiedRuleValidation
  passed := passed + verifiedPassed
  total := total + 3

  let reprPassed ← testReprEquivValidation
  passed := passed + reprPassed
  total := total + 3

  let extractPassed ← testASTExtraction
  passed := passed + extractPassed
  total := total + 2

  let fullPassed ← testFullValidation
  passed := passed + fullPassed
  total := total + 2

  IO.println ""
  IO.println "═══════════════════════════════════════════════════════════════"
  IO.println s!"Total: {total} tests, {passed} passed, {total - passed} failed"

  if passed == total then
    IO.println "All tests passed! ✓"
    pure 0
  else
    IO.println s!"⚠️  {total - passed} tests failed"
    pure 1
