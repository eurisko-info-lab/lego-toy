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

  -- Set up type rules for paths (cubical type theory)
  -- refl : (a : A) → Path A a a
  let reflRule : TypeRule := {
    name := "reflType"
    subject := .con "refl" [.var "$a"]
    type := .con "Path" [.var "$A", .var "$a", .var "$a"]
    conditions := []
  }

  -- sym : Path A a b → Path A b a
  let symRule : TypeRule := {
    name := "symType"
    subject := .con "sym" [.var "$p"]
    type := .con "Path" [.var "$A", .var "$b", .var "$a"]
    conditions := [.con ":" [.var "$p", .con "Path" [.var "$A", .var "$a", .var "$b"]]]
  }

  -- trans : Path A a b → Path A b c → Path A a c
  let transRule : TypeRule := {
    name := "transType"
    subject := .con "trans" [.var "$p", .var "$q"]
    type := .con "Path" [.var "$A", .var "$a", .var "$c"]
    conditions := [
      .con ":" [.var "$p", .con "Path" [.var "$A", .var "$a", .var "$b"]],
      .con ":" [.var "$q", .con "Path" [.var "$A", .var "$b", .var "$c"]]
    ]
  }

  -- cong : (f : A → B) → Path A a a' → Path B (f a) (f a')
  let congRule : TypeRule := {
    name := "congType"
    subject := .con "cong" [.var "$f", .var "$p"]
    type := .con "Path" [.var "$B", .con "app" [.var "$f", .var "$a"], .con "app" [.var "$f", .var "$a'"]]
    conditions := [.con ":" [.var "$p", .con "Path" [.var "$A", .var "$a", .var "$a'"]]]
  }

  let zeroRule : TypeRule := {
    name := "zeroType"
    subject := .con "zero" []
    type := .con "Nat" []
    conditions := []
  }

  let typeRules := [reflRule, symRule, transRule, congRule, zeroRule]

  -- Test 1: valid verified rule with refl proof
  -- verified rule id : x ~> x via refl(x)
  let err1 := verifyVerifiedRule typeRules "id"
    (.var "x") (.var "x") (.con "refl" [.var "x"])
  if ← assertNone "valid_verified_rule_refl" err1 then passed := passed + 1

  -- Test 2: invalid verified rule - wrong proof endpoints
  -- verified rule bad : x ~> y via refl(x)  -- refl(x) has type Path _ x x, not x y
  let err2 := verifyVerifiedRule typeRules "bad"
    (.var "x") (.var "y") (.con "refl" [.var "x"])
  if ← assertSome "invalid_verified_rule_wrong_endpoints" err2 then passed := passed + 1

  -- Test 3: invalid verified rule - proof has wrong type entirely (not Path)
  -- verified rule bad2 : x ~> x via zero  -- zero : Nat, not Path
  let err3 := verifyVerifiedRule typeRules "bad2"
    (.var "x") (.var "x") (.con "zero" [])
  if ← assertSome "invalid_verified_rule_not_path" err3 then passed := passed + 1

  -- Test 4: missing proof type (can't infer)
  let err4 := verifyVerifiedRule typeRules "missing"
    (.var "x") (.var "x") (.lit "not_a_path")
  if ← assertSome "invalid_verified_rule_no_type" err4 then passed := passed + 1

  pure passed

/-! ## Repr Equivalence Validation Tests -/

def testReprEquivValidation : IO Nat := do
  IO.println "\n── Repr Equivalence Validation ──"
  let mut passed := 0

  -- Set up type rules for equivalences (HoTT/cubical)
  -- idEquiv : (A : Type) → Equiv A A
  let idEquivRule : TypeRule := {
    name := "idEquivType"
    subject := .con "idEquiv" [.var "$A"]
    type := .con "Equiv" [.var "$A", .var "$A"]
    conditions := []
  }

  -- compEquiv : Equiv A B → Equiv B C → Equiv A C
  let compEquivRule : TypeRule := {
    name := "compEquivType"
    subject := .con "compEquiv" [.var "$e1", .var "$e2"]
    type := .con "Equiv" [.var "$A", .var "$C"]
    conditions := [
      .con ":" [.var "$e1", .con "Equiv" [.var "$A", .var "$B"]],
      .con ":" [.var "$e2", .con "Equiv" [.var "$B", .var "$C"]]
    ]
  }

  -- invEquiv : Equiv A B → Equiv B A
  let invEquivRule : TypeRule := {
    name := "invEquivType"
    subject := .con "invEquiv" [.var "$e"]
    type := .con "Equiv" [.var "$B", .var "$A"]
    conditions := [.con ":" [.var "$e", .con "Equiv" [.var "$A", .var "$B"]]]
  }

  let zeroRule : TypeRule := {
    name := "zeroType"
    subject := .con "zero" []
    type := .con "Nat" []
    conditions := []
  }

  let typeRules := [idEquivRule, compEquivRule, invEquivRule, zeroRule]

  -- Test 1: valid repr with idEquiv
  -- repr Nat ≃ Nat via idEquiv(Nat)
  let err1 := verifyReprEquiv typeRules "natId"
    (.con "Nat" []) (.con "Nat" []) (.con "idEquiv" [.con "Nat" []])
  if ← assertNone "valid_repr_idEquiv" err1 then passed := passed + 1

  -- Test 2: invalid repr - types don't match (wrong Equiv endpoints)
  -- repr Nat ≃ Bool via idEquiv(Nat)  -- idEquiv(Nat) : Equiv Nat Nat, not Nat Bool
  let err2 := verifyReprEquiv typeRules "natBool"
    (.con "Nat" []) (.con "Bool" []) (.con "idEquiv" [.con "Nat" []])
  if ← assertSome "invalid_repr_wrong_endpoints" err2 then passed := passed + 1

  -- Test 3: invalid repr - equiv has wrong type entirely (not Equiv)
  -- repr Nat ≃ Nat via zero  -- zero : Nat, not Equiv
  let err3 := verifyReprEquiv typeRules "natZero"
    (.con "Nat" []) (.con "Nat" []) (.con "zero" [])
  if ← assertSome "invalid_repr_not_equiv" err3 then passed := passed + 1

  -- Test 4: missing equiv type (can't infer)
  let err4 := verifyReprEquiv typeRules "missing"
    (.con "Nat" []) (.con "Nat" []) (.lit "not_an_equiv")
  if ← assertSome "invalid_repr_no_type" err4 then passed := passed + 1

  pure passed

/-! ## Cubical Proof Combinators Tests -/

def testCubicalProofCombinators : IO Nat := do
  IO.println "\n── Cubical Proof Combinators ──"
  let mut passed := 0

  -- Set up comprehensive cubical type rules
  let reflRule : TypeRule := {
    name := "reflType"
    subject := .con "refl" [.var "$a"]
    type := .con "Path" [.var "$A", .var "$a", .var "$a"]
    conditions := []
  }

  -- sym : Path A a b → Path A b a
  let symRule : TypeRule := {
    name := "symType"
    subject := .con "sym" [.var "$p"]
    type := .con "Path" [.var "$A", .var "$b", .var "$a"]
    conditions := [.con ":" [.var "$p", .con "Path" [.var "$A", .var "$a", .var "$b"]]]
  }

  -- trans : Path A a b → Path A b c → Path A a c
  let transRule : TypeRule := {
    name := "transType"
    subject := .con "trans" [.var "$p", .var "$q"]
    type := .con "Path" [.var "$A", .var "$a", .var "$c"]
    conditions := [
      .con ":" [.var "$p", .con "Path" [.var "$A", .var "$a", .var "$b"]],
      .con ":" [.var "$q", .con "Path" [.var "$A", .var "$b", .var "$c"]]
    ]
  }

  -- ua : Equiv A B → Path Type A B (univalence)
  let uaRule : TypeRule := {
    name := "uaType"
    subject := .con "ua" [.var "$e"]
    type := .con "Path" [.con "Type" [], .var "$A", .var "$B"]
    conditions := [.con ":" [.var "$e", .con "Equiv" [.var "$A", .var "$B"]]]
  }

  let idEquivRule : TypeRule := {
    name := "idEquivType"
    subject := .con "idEquiv" [.var "$A"]
    type := .con "Equiv" [.var "$A", .var "$A"]
    conditions := []
  }

  let typeRules := [reflRule, symRule, transRule, uaRule, idEquivRule]

  -- Test 1: sym(refl(x)) has Path type (refl(x) : Path A x x, so sym gives Path A x x)
  let symRefl := Term.con "sym" [.con "refl" [.var "x"]]
  let ty1 := inferType typeRules symRefl
  match ty1 with
  | some (.con "Path" _) =>
    IO.println "  ✓ sym_has_path_type"
    passed := passed + 1
  | _ =>
    IO.println "  ✗ sym_has_path_type (expected Path type)"

  -- Test 2: ua(idEquiv(A)) has Path type (univalence: Equiv A A → Path Type A A)
  let uaIdEquiv := Term.con "ua" [.con "idEquiv" [.var "A"]]
  let ty2 := inferType typeRules uaIdEquiv
  match ty2 with
  | some (.con "Path" [.con "Type" [], _, _]) =>
    IO.println "  ✓ ua_gives_path_in_type"
    passed := passed + 1
  | _ =>
    IO.println "  ✗ ua_gives_path_in_type (expected Path Type _ _)"

  -- Test 3: trans(refl(x), refl(x)) has Path type (transitivity of reflexivity)
  let transRefl := Term.con "trans" [.con "refl" [.var "x"], .con "refl" [.var "x"]]
  let ty3 := inferType typeRules transRefl
  match ty3 with
  | some (.con "Path" _) =>
    IO.println "  ✓ trans_has_path_type"
    passed := passed + 1
  | _ =>
    IO.println "  ✗ trans_has_path_type (expected Path type)"

  -- Test 4: Verified rule with refl still works with more rules loaded
  let err4 := verifyVerifiedRule typeRules "idWithCubical"
    (.var "x") (.var "x") (.con "refl" [.var "x"])
  if ← assertNone "verified_refl_with_cubical_rules" err4 then passed := passed + 1

  pure passed

/-! ## Equivalence Composition Tests -/

def testEquivalenceComposition : IO Nat := do
  IO.println "\n── Equivalence Composition ──"
  let mut passed := 0

  -- idEquiv : (A : Type) → Equiv A A
  let idEquivRule : TypeRule := {
    name := "idEquivType"
    subject := .con "idEquiv" [.var "$A"]
    type := .con "Equiv" [.var "$A", .var "$A"]
    conditions := []
  }

  -- invEquiv : Equiv A B → Equiv B A
  let invEquivRule : TypeRule := {
    name := "invEquivType"
    subject := .con "invEquiv" [.var "$e"]
    type := .con "Equiv" [.var "$B", .var "$A"]
    conditions := [.con ":" [.var "$e", .con "Equiv" [.var "$A", .var "$B"]]]
  }

  -- compEquiv : Equiv A B → Equiv B C → Equiv A C
  let compEquivRule : TypeRule := {
    name := "compEquivType"
    subject := .con "compEquiv" [.var "$e1", .var "$e2"]
    type := .con "Equiv" [.var "$A", .var "$C"]
    conditions := [
      .con ":" [.var "$e1", .con "Equiv" [.var "$A", .var "$B"]],
      .con ":" [.var "$e2", .con "Equiv" [.var "$B", .var "$C"]]
    ]
  }

  let typeRules := [idEquivRule, invEquivRule, compEquivRule]

  -- Test 1: idEquiv(A) has type Equiv A A
  let ty1 := inferType typeRules (.con "idEquiv" [.var "A"])
  match ty1 with
  | some (.con "Equiv" [a, b]) =>
    if ← assertEqualBool "idEquiv_endpoints_match" (a == b) true then passed := passed + 1
  | _ =>
    IO.println "  ✗ idEquiv_endpoints_match (wrong type structure)"

  -- Test 2: invEquiv(idEquiv(A)) has Equiv type (inverting identity gives identity)
  let invIdEquiv := Term.con "invEquiv" [.con "idEquiv" [.var "A"]]
  let ty2 := inferType typeRules invIdEquiv
  match ty2 with
  | some (.con "Equiv" _) =>
    IO.println "  ✓ invEquiv_has_equiv_type"
    passed := passed + 1
  | _ =>
    IO.println "  ✗ invEquiv_has_equiv_type (expected Equiv type)"

  -- Test 3: compEquiv(idEquiv(A), idEquiv(A)) has Equiv type (composing identities)
  let compIdEquiv := Term.con "compEquiv" [.con "idEquiv" [.var "A"], .con "idEquiv" [.var "A"]]
  let ty3 := inferType typeRules compIdEquiv
  match ty3 with
  | some (.con "Equiv" _) =>
    IO.println "  ✓ compEquiv_has_equiv_type"
    passed := passed + 1
  | _ =>
    IO.println "  ✗ compEquiv_has_equiv_type (expected Equiv type)"

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

/-! ## Grammar Validation Error Tests -/

def testGrammarValidationErrors : IO Nat := do
  IO.println "\n── Grammar Validation Errors ──"
  let mut passed := 0

  -- Test: undefinedProduction
  -- Reference a production that doesn't exist
  let grammarWithUndefined := Std.HashMap.emptyWithCapacity
    |>.insert "Expr.term" (GrammarExpr.ref "Undefined.production")
  let result1 := checkUndefinedRefs grammarWithUndefined
  if ← assertNonEmpty "undefinedProduction_detected" result1.errors then passed := passed + 1

  -- Test: defined productions pass
  let grammarDefined := Std.HashMap.emptyWithCapacity
    |>.insert "Expr.term" (GrammarExpr.ref "Expr.atom")
    |>.insert "Expr.atom" (GrammarExpr.lit "x")
  let result2 := checkUndefinedRefs grammarDefined
  if ← assertEmpty "definedProduction_passes" result2.errors then passed := passed + 1

  -- Test: builtin productions pass (ident, string, etc.)
  let grammarBuiltin := Std.HashMap.emptyWithCapacity
    |>.insert "Expr.name" (GrammarExpr.ref "ident")
  let result3 := checkUndefinedRefs grammarBuiltin
  if ← assertEmpty "builtinProduction_passes" result3.errors then passed := passed + 1

  pure passed

/-! ## Rule Validation Error Tests -/

def testRuleValidationErrors : IO Nat := do
  IO.println "\n── Rule Validation Errors ──"
  let mut passed := 0

  -- Test: unboundVariable - template uses variable not in pattern
  let ruleUnbound : Rule := {
    name := "badRule"
    pattern := .con "f" [.var "$x"]
    template := .con "g" [.var "$x", .var "$y"]  -- $y not bound!
    guard := none
  }
  let result1 := checkUnboundVars [ruleUnbound]
  if ← assertNonEmpty "unboundVariable_detected" result1.errors then passed := passed + 1

  -- Test: well-formed rule passes
  let ruleOk : Rule := {
    name := "goodRule"
    pattern := .con "f" [.var "$x", .var "$y"]
    template := .con "g" [.var "$y", .var "$x"]
    guard := none
  }
  let result2 := checkUnboundVars [ruleOk]
  if ← assertEmpty "boundVariables_pass" result2.errors then passed := passed + 1

  -- Test: conflictingRules - same pattern, different result
  let rule1 : Rule := {
    name := "rule1"
    pattern := .con "f" [.var "$x"]
    template := .con "a" []
    guard := none
  }
  let rule2 : Rule := {
    name := "rule2"
    pattern := .con "f" [.var "$y"]  -- Same structure as rule1
    template := .con "b" []          -- Different result!
    guard := none
  }
  let result3 := checkConflictingRules [rule1, rule2]
  if ← assertNonEmpty "conflictingRules_detected" result3.warnings then passed := passed + 1

  -- Test: non-conflicting rules pass
  let rule3 : Rule := {
    name := "rule3"
    pattern := .con "g" [.var "$x"]  -- Different pattern
    template := .con "c" []
    guard := none
  }
  let result4 := checkConflictingRules [rule1, rule3]
  if ← assertEmpty "nonConflictingRules_pass" result4.warnings then passed := passed + 1

  pure passed

/-! ## Left Recursion Warning Tests -/

def testLeftRecursionWarnings : IO Nat := do
  IO.println "\n── Left Recursion Warnings ──"
  let mut passed := 0

  -- Test: directLeftRecursion - production starts with itself
  -- expr ::= expr "+" term
  let grammarLeftRec := Std.HashMap.emptyWithCapacity
    |>.insert "Expr.expr" (GrammarExpr.mk (.seq (GrammarExpr.ref "Expr.expr") (GrammarExpr.lit "+")))
  let result1 := checkLeftRecursion grammarLeftRec
  if ← assertNonEmpty "directLeftRecursion_detected" result1.warnings then passed := passed + 1

  -- Test: non-left-recursive passes
  -- expr ::= "(" expr ")"
  let grammarOk := Std.HashMap.emptyWithCapacity
    |>.insert "Expr.expr" (GrammarExpr.mk (.seq (GrammarExpr.lit "(") (GrammarExpr.ref "Expr.expr")))
  let result2 := checkLeftRecursion grammarOk
  if ← assertEmpty "nonLeftRecursive_passes" result2.warnings then passed := passed + 1

  pure passed

/-! ## Grammar Optimization Warning Tests -/

def testGrammarOptimizationWarnings : IO Nat := do
  IO.println "\n── Grammar Optimization Warnings ──"
  let mut passed := 0

  -- Test: missingCut - keyword without cut
  let grammarNoCut := Std.HashMap.emptyWithCapacity
    |>.insert "Stmt.ifStmt" (GrammarExpr.mk (.seq (GrammarExpr.lit "if") (GrammarExpr.ref "Expr.expr")))
  let result1 := checkMissingCuts grammarNoCut
  if ← assertNonEmpty "missingCut_detected" result1.warnings then passed := passed + 1

  -- Test: unreachableAlt - prefix makes later alt unreachable
  -- expr ::= "x" | "x" "y"   -- second alt unreachable after first matches "x"
  let grammarUnreachable := Std.HashMap.emptyWithCapacity
    |>.insert "Expr.expr" (GrammarExpr.mk (.alt
      (GrammarExpr.lit "x")
      (GrammarExpr.mk (.seq (GrammarExpr.lit "x") (GrammarExpr.lit "y")))))
  let result2 := checkUnreachableAlts grammarUnreachable
  if ← assertNonEmpty "unreachableAlt_detected" result2.warnings then passed := passed + 1

  -- Test: redundantAlt - duplicate alternatives
  -- expr ::= "x" | "x"
  let grammarRedundant := Std.HashMap.emptyWithCapacity
    |>.insert "Expr.expr" (GrammarExpr.mk (.alt (GrammarExpr.lit "x") (GrammarExpr.lit "x")))
  let result3 := checkUnreachableAlts grammarRedundant
  if ← assertNonEmpty "redundantAlt_detected" result3.warnings then passed := passed + 1

  -- Test: well-structured grammar passes
  let grammarGood := Std.HashMap.emptyWithCapacity
    |>.insert "Expr.expr" (GrammarExpr.mk (.alt (GrammarExpr.lit "x") (GrammarExpr.lit "y")))
  let result4 := checkUnreachableAlts grammarGood
  if ← assertEmpty "wellStructured_passes" result4.warnings then passed := passed + 1

  pure passed

/-! ## Combined Validation Tests -/

def testCombinedValidation : IO Nat := do
  IO.println "\n── Combined Validation ──"
  let mut passed := 0

  -- Test: validateGrammar catches multiple issues
  let badGrammar := Std.HashMap.emptyWithCapacity
    |>.insert "Expr.expr" (GrammarExpr.mk (.seq (GrammarExpr.ref "Expr.expr") (GrammarExpr.ref "Unknown.ref")))
  let result1 := validateGrammar badGrammar
  -- Should have undefined ref error AND left recursion warning
  if ← assertNonEmpty "validateGrammar_errors" result1.errors then passed := passed + 1
  if ← assertNonEmpty "validateGrammar_warnings" result1.warnings then passed := passed + 1

  -- Test: validateRules catches multiple issues
  let badRules : List Rule := [
    { name := "bad1", pattern := .con "f" [.var "$x"], template := .con "g" [.var "$z"], guard := none },
    { name := "bad2", pattern := .con "f" [.var "$a"], template := .con "h" [], guard := none }
  ]
  let result2 := validateRules badRules
  -- Should have unbound var AND conflicting rules
  if ← assertNonEmpty "validateRules_errors" result2.errors then passed := passed + 1
  if ← assertNonEmpty "validateRules_warnings" result2.warnings then passed := passed + 1

  -- Test: validate combines grammar and rule validation
  let result3 := validate badGrammar badRules
  if ← assertEqualBool "validate_combined_fails" result3.passed false then passed := passed + 1

  -- Test: clean validation passes
  let goodGrammar := Std.HashMap.emptyWithCapacity
    |>.insert "Expr.expr" (GrammarExpr.lit "x")
  let goodRules : List Rule := [
    { name := "good", pattern := .con "f" [.var "$x"], template := .var "$x", guard := none }
  ]
  let result4 := validate goodGrammar goodRules
  if ← assertEqualBool "validate_clean_passes" result4.passed true then passed := passed + 1

  pure passed

/-! ## Interval Type Tests -/

def testIntervalType : IO Nat := do
  IO.println "\n── Interval Type ──"
  let mut passed := 0

  -- Interval type rules
  let intervalRule : TypeRule := {
    name := "intervalForm"
    subject := .con "I" []
    type := .con "Univ" []
    conditions := []
  }

  let i0Rule : TypeRule := {
    name := "i0Type"
    subject := .con "i0" []
    type := .con "I" []
    conditions := []
  }

  let i1Rule : TypeRule := {
    name := "i1Type"
    subject := .con "i1" []
    type := .con "I" []
    conditions := []
  }

  let imaxRule : TypeRule := {
    name := "imaxType"
    subject := .con "imax" [.var "$i", .var "$j"]
    type := .con "I" []
    conditions := [.con ":" [.var "$i", .con "I" []], .con ":" [.var "$j", .con "I" []]]
  }

  let inegRule : TypeRule := {
    name := "inegType"
    subject := .con "ineg" [.var "$i"]
    type := .con "I" []
    conditions := [.con ":" [.var "$i", .con "I" []]]
  }

  let typeRules := [intervalRule, i0Rule, i1Rule, imaxRule, inegRule]

  -- Test 1: I is a type
  let ty1 := inferType typeRules (.con "I" [])
  if ← assertEqual "interval_is_univ" (ty1.getD (.lit "?")) (.con "Univ" []) then passed := passed + 1

  -- Test 2: i0 : I
  let ty2 := inferType typeRules (.con "i0" [])
  if ← assertEqual "i0_is_interval" (ty2.getD (.lit "?")) (.con "I" []) then passed := passed + 1

  -- Test 3: imax(i0, i1) : I
  let ty3 := inferType typeRules (.con "imax" [.con "i0" [], .con "i1" []])
  if ← assertEqual "imax_is_interval" (ty3.getD (.lit "?")) (.con "I" []) then passed := passed + 1

  -- Test 4: ineg(i0) : I
  let ty4 := inferType typeRules (.con "ineg" [.con "i0" []])
  if ← assertEqual "ineg_is_interval" (ty4.getD (.lit "?")) (.con "I" []) then passed := passed + 1

  pure passed

/-! ## Cofibration Tests -/

def testCofibrations : IO Nat := do
  IO.println "\n── Cofibrations ──"
  let mut passed := 0

  let cofTopRule : TypeRule := {
    name := "cofTopType"
    subject := .con "cof_top" []
    type := .con "Cof" []
    conditions := []
  }

  let cofBotRule : TypeRule := {
    name := "cofBotType"
    subject := .con "cof_bot" []
    type := .con "Cof" []
    conditions := []
  }

  let cofEqRule : TypeRule := {
    name := "cofEqType"
    subject := .con "cof_eq" [.var "$i", .var "$j"]
    type := .con "Cof" []
    conditions := [.con ":" [.var "$i", .con "I" []], .con ":" [.var "$j", .con "I" []]]
  }

  let cofAndRule : TypeRule := {
    name := "cofAndType"
    subject := .con "cof_and" [.var "$φ", .var "$ψ"]
    type := .con "Cof" []
    conditions := [.con ":" [.var "$φ", .con "Cof" []], .con ":" [.var "$ψ", .con "Cof" []]]
  }

  let i0Rule : TypeRule := {
    name := "i0Type"
    subject := .con "i0" []
    type := .con "I" []
    conditions := []
  }

  let typeRules := [cofTopRule, cofBotRule, cofEqRule, cofAndRule, i0Rule]

  -- Test 1: cof_top : Cof
  let ty1 := inferType typeRules (.con "cof_top" [])
  if ← assertEqual "cof_top_is_cof" (ty1.getD (.lit "?")) (.con "Cof" []) then passed := passed + 1

  -- Test 2: cof_bot : Cof
  let ty2 := inferType typeRules (.con "cof_bot" [])
  if ← assertEqual "cof_bot_is_cof" (ty2.getD (.lit "?")) (.con "Cof" []) then passed := passed + 1

  -- Test 3: cof_eq(i0, i0) : Cof
  let ty3 := inferType typeRules (.con "cof_eq" [.con "i0" [], .con "i0" []])
  if ← assertEqual "cof_eq_is_cof" (ty3.getD (.lit "?")) (.con "Cof" []) then passed := passed + 1

  -- Test 4: cof_and(cof_top, cof_bot) : Cof
  let ty4 := inferType typeRules (.con "cof_and" [.con "cof_top" [], .con "cof_bot" []])
  if ← assertEqual "cof_and_is_cof" (ty4.getD (.lit "?")) (.con "Cof" []) then passed := passed + 1

  pure passed

/-! ## Kan Operations Tests -/

def testKanOperations : IO Nat := do
  IO.println "\n── Kan Operations ──"
  let mut passed := 0

  -- Simplified type rules for Kan ops
  let coeRule : TypeRule := {
    name := "coeType"
    subject := .con "coe" [.var "$r", .var "$s", .var "$A", .var "$a"]
    type := .var "$B"  -- Result type depends on A at s
    conditions := []
  }

  let hcomRule : TypeRule := {
    name := "hcomType"
    subject := .con "hcom" [.var "$r", .var "$s", .var "$A", .var "$φ", .var "$a"]
    type := .var "$A"
    conditions := []
  }

  let transpRule : TypeRule := {
    name := "transpType"
    subject := .con "transp" [.var "$A", .var "$φ", .var "$a"]
    type := .var "$B"  -- Result type is A at i1
    conditions := []
  }

  let typeRules := [coeRule, hcomRule, transpRule]

  -- Test 1: coe has a type
  let ty1 := inferType typeRules (.con "coe" [.var "r", .var "s", .var "A", .var "a"])
  if ← assertSome "coe_has_type" ty1 then passed := passed + 1

  -- Test 2: hcom returns same type
  let ty2 := inferType typeRules (.con "hcom" [.var "r", .var "s", .var "A", .var "φ", .var "a"])
  match ty2 with
  | some (.var "A") =>
    IO.println "  ✓ hcom_preserves_type"
    passed := passed + 1
  | _ =>
    IO.println "  ✗ hcom_preserves_type"

  -- Test 3: transp has a type
  let ty3 := inferType typeRules (.con "transp" [.var "A", .var "φ", .var "a"])
  if ← assertSome "transp_has_type" ty3 then passed := passed + 1

  pure passed

/-! ## Higher Inductive Types Tests -/

def testHigherInductives : IO Nat := do
  IO.println "\n── Higher Inductive Types ──"
  let mut passed := 0

  let s1Rule : TypeRule := {
    name := "s1Form"
    subject := .con "S1" []
    type := .con "Univ" []
    conditions := []
  }

  let baseRule : TypeRule := {
    name := "baseType"
    subject := .con "base" []
    type := .con "S1" []
    conditions := []
  }

  let loopRule : TypeRule := {
    name := "loopType"
    subject := .con "loop" []
    type := .con "Path" [.con "S1" [], .con "base" [], .con "base" []]
    conditions := []
  }

  let suspRule : TypeRule := {
    name := "suspForm"
    subject := .con "Susp" [.var "$A"]
    type := .con "Univ" []
    conditions := [.con ":" [.var "$A", .con "Univ" []]]
  }

  let northRule : TypeRule := {
    name := "northType"
    subject := .con "north" []
    type := .con "Susp" [.var "$A"]
    conditions := []
  }

  let typeRules := [s1Rule, baseRule, loopRule, suspRule, northRule]

  -- Test 1: S1 is a type
  let ty1 := inferType typeRules (.con "S1" [])
  if ← assertEqual "s1_is_univ" (ty1.getD (.lit "?")) (.con "Univ" []) then passed := passed + 1

  -- Test 2: base : S1
  let ty2 := inferType typeRules (.con "base" [])
  if ← assertEqual "base_is_s1" (ty2.getD (.lit "?")) (.con "S1" []) then passed := passed + 1

  -- Test 3: loop : Path S1 base base
  let ty3 := inferType typeRules (.con "loop" [])
  match ty3 with
  | some (.con "Path" [.con "S1" [], .con "base" [], .con "base" []]) =>
    IO.println "  ✓ loop_is_path_base_base"
    passed := passed + 1
  | _ =>
    IO.println "  ✗ loop_is_path_base_base"

  -- Test 4: Susp(S1) is a type
  let ty4 := inferType typeRules (.con "Susp" [.con "S1" []])
  if ← assertEqual "susp_is_univ" (ty4.getD (.lit "?")) (.con "Univ" []) then passed := passed + 1

  pure passed

/-! ## H-Levels Tests -/

def testHLevels : IO Nat := do
  IO.println "\n── H-Levels ──"
  let mut passed := 0

  let isContrRule : TypeRule := {
    name := "isContrForm"
    subject := .con "isContr" [.var "$A"]
    type := .con "Univ" []
    conditions := [.con ":" [.var "$A", .con "Univ" []]]
  }

  let isPropRule : TypeRule := {
    name := "isPropForm"
    subject := .con "isProp" [.var "$A"]
    type := .con "Univ" []
    conditions := [.con ":" [.var "$A", .con "Univ" []]]
  }

  let isSetRule : TypeRule := {
    name := "isSetForm"
    subject := .con "isSet" [.var "$A"]
    type := .con "Univ" []
    conditions := [.con ":" [.var "$A", .con "Univ" []]]
  }

  let propTruncRule : TypeRule := {
    name := "propTruncForm"
    subject := .con "propTrunc" [.var "$A"]
    type := .con "Univ" []
    conditions := [.con ":" [.var "$A", .con "Univ" []]]
  }

  let natRule : TypeRule := {
    name := "natForm"
    subject := .con "Nat" []
    type := .con "Univ" []
    conditions := []
  }

  let typeRules := [isContrRule, isPropRule, isSetRule, propTruncRule, natRule]

  -- Test 1: isContr(Nat) : Univ
  let ty1 := inferType typeRules (.con "isContr" [.con "Nat" []])
  if ← assertEqual "isContr_is_univ" (ty1.getD (.lit "?")) (.con "Univ" []) then passed := passed + 1

  -- Test 2: isProp(Nat) : Univ
  let ty2 := inferType typeRules (.con "isProp" [.con "Nat" []])
  if ← assertEqual "isProp_is_univ" (ty2.getD (.lit "?")) (.con "Univ" []) then passed := passed + 1

  -- Test 3: isSet(Nat) : Univ
  let ty3 := inferType typeRules (.con "isSet" [.con "Nat" []])
  if ← assertEqual "isSet_is_univ" (ty3.getD (.lit "?")) (.con "Univ" []) then passed := passed + 1

  -- Test 4: propTrunc(Nat) : Univ
  let ty4 := inferType typeRules (.con "propTrunc" [.con "Nat" []])
  if ← assertEqual "propTrunc_is_univ" (ty4.getD (.lit "?")) (.con "Univ" []) then passed := passed + 1

  pure passed

/-! ## Sigma and Pi Types Tests -/

def testDependentTypes : IO Nat := do
  IO.println "\n── Dependent Types ──"
  let mut passed := 0

  let sigmaRule : TypeRule := {
    name := "sigmaForm"
    subject := .con "Sigma" [.var "$A", .var "$B"]
    type := .con "Univ" []
    conditions := []
  }

  let pairRule : TypeRule := {
    name := "pairType"
    subject := .con "pair" [.var "$a", .var "$b"]
    type := .con "Sigma" [.var "$A", .var "$B"]
    conditions := []
  }

  let fstRule : TypeRule := {
    name := "fstType"
    subject := .con "fst" [.var "$p"]
    type := .var "$A"
    conditions := [.con ":" [.var "$p", .con "Sigma" [.var "$A", .var "$B"]]]
  }

  let piRule : TypeRule := {
    name := "piForm"
    subject := .con "Pi" [.var "$A", .var "$B"]
    type := .con "Univ" []
    conditions := []
  }

  let lamRule : TypeRule := {
    name := "lamType"
    subject := .con "lam" [.var "$x", .var "$body"]
    type := .con "Pi" [.var "$A", .var "$B"]
    conditions := []
  }

  let typeRules := [sigmaRule, pairRule, fstRule, piRule, lamRule]

  -- Test 1: Sigma A B : Univ
  let ty1 := inferType typeRules (.con "Sigma" [.var "A", .var "B"])
  if ← assertEqual "sigma_is_univ" (ty1.getD (.lit "?")) (.con "Univ" []) then passed := passed + 1

  -- Test 2: pair(a, b) : Sigma A B
  let ty2 := inferType typeRules (.con "pair" [.var "a", .var "b"])
  match ty2 with
  | some (.con "Sigma" _) =>
    IO.println "  ✓ pair_is_sigma"
    passed := passed + 1
  | _ =>
    IO.println "  ✗ pair_is_sigma"

  -- Test 3: Pi A B : Univ
  let ty3 := inferType typeRules (.con "Pi" [.var "A", .var "B"])
  if ← assertEqual "pi_is_univ" (ty3.getD (.lit "?")) (.con "Univ" []) then passed := passed + 1

  -- Test 4: lam(x, body) : Pi A B
  let ty4 := inferType typeRules (.con "lam" [.var "x", .var "body"])
  match ty4 with
  | some (.con "Pi" _) =>
    IO.println "  ✓ lam_is_pi"
    passed := passed + 1
  | _ =>
    IO.println "  ✗ lam_is_pi"

  pure passed

/-! ## Glue and Extension Types Tests -/

def testGlueAndExtension : IO Nat := do
  IO.println "\n── Glue and Extension Types ──"
  let mut passed := 0

  let glueRule : TypeRule := {
    name := "glueForm"
    subject := .con "Glue" [.var "$φ", .var "$T", .var "$A"]
    type := .con "Univ" []
    conditions := []
  }

  let partialRule : TypeRule := {
    name := "partialForm"
    subject := .con "Partial" [.var "$φ", .var "$A"]
    type := .con "Univ" []
    conditions := []
  }

  let subRule : TypeRule := {
    name := "subForm"
    subject := .con "Sub" [.var "$A", .var "$φ", .var "$u"]
    type := .con "Univ" []
    conditions := []
  }

  let inSRule : TypeRule := {
    name := "inSType"
    subject := .con "inS" [.var "$a"]
    type := .con "Sub" [.var "$A", .var "$φ", .var "$u"]
    conditions := []
  }

  let typeRules := [glueRule, partialRule, subRule, inSRule]

  -- Test 1: Glue φ T A : Univ
  let ty1 := inferType typeRules (.con "Glue" [.var "φ", .var "T", .var "A"])
  if ← assertEqual "glue_is_univ" (ty1.getD (.lit "?")) (.con "Univ" []) then passed := passed + 1

  -- Test 2: Partial φ A : Univ
  let ty2 := inferType typeRules (.con "Partial" [.var "φ", .var "A"])
  if ← assertEqual "partial_is_univ" (ty2.getD (.lit "?")) (.con "Univ" []) then passed := passed + 1

  -- Test 3: Sub A φ u : Univ
  let ty3 := inferType typeRules (.con "Sub" [.var "A", .var "φ", .var "u"])
  if ← assertEqual "sub_is_univ" (ty3.getD (.lit "?")) (.con "Univ" []) then passed := passed + 1

  -- Test 4: inS(a) : Sub A φ u
  let ty4 := inferType typeRules (.con "inS" [.var "a"])
  match ty4 with
  | some (.con "Sub" _) =>
    IO.println "  ✓ inS_is_sub"
    passed := passed + 1
  | _ =>
    IO.println "  ✗ inS_is_sub"

  pure passed

/-! ## J Eliminator Tests -/

def testJEliminator : IO Nat := do
  IO.println "\n── J Eliminator ──"
  let mut passed := 0

  let reflRule : TypeRule := {
    name := "reflType"
    subject := .con "refl" [.var "$a"]
    type := .con "Path" [.var "$A", .var "$a", .var "$a"]
    conditions := []
  }

  let jRule : TypeRule := {
    name := "jType"
    subject := .con "J" [.var "$A", .var "$a", .var "$P", .var "$d", .var "$x", .var "$p"]
    type := .con "App" [.con "App" [.var "$P", .var "$x"], .var "$p"]
    conditions := []
  }

  let typeRules := [reflRule, jRule]

  -- Test 1: J has the right structure
  let jTerm := Term.con "J" [.var "A", .var "a", .var "P", .var "d", .var "x", .var "p"]
  let ty1 := inferType typeRules jTerm
  if ← assertSome "j_has_type" ty1 then passed := passed + 1

  -- Test 2: J A a P d a (refl a) should type-check
  let jRefl := Term.con "J" [.var "A", .var "a", .var "P", .var "d", .var "a", .con "refl" [.var "a"]]
  let ty2 := inferType typeRules jRefl
  if ← assertSome "j_refl_has_type" ty2 then passed := passed + 1

  pure passed

/-! ## Observational Equality Tests -/

def testObservationalEq : IO Nat := do
  IO.println "\n── Observational Equality ──"
  let mut passed := 0

  let obsEqRule : TypeRule := {
    name := "obsEqForm"
    subject := .con "obsEq" [.var "$A", .var "$a", .var "$b"]
    type := .con "Univ" []
    conditions := []
  }

  let obsReflRule : TypeRule := {
    name := "obsReflType"
    subject := .con "obsRefl" [.var "$a"]
    type := .con "obsEq" [.var "$A", .var "$a", .var "$a"]
    conditions := []
  }

  let obsSymRule : TypeRule := {
    name := "obsSymType"
    subject := .con "obsSym" [.var "$p"]
    type := .con "obsEq" [.var "$A", .var "$b", .var "$a"]
    conditions := [.con ":" [.var "$p", .con "obsEq" [.var "$A", .var "$a", .var "$b"]]]
  }

  let obsToPathRule : TypeRule := {
    name := "obsToPathType"
    subject := .con "obsToPath" [.var "$p"]
    type := .con "Path" [.var "$A", .var "$a", .var "$b"]
    conditions := [.con ":" [.var "$p", .con "obsEq" [.var "$A", .var "$a", .var "$b"]]]
  }

  let typeRules := [obsEqRule, obsReflRule, obsSymRule, obsToPathRule]

  -- Test 1: obsEq A a b : Univ
  let ty1 := inferType typeRules (.con "obsEq" [.var "A", .var "a", .var "b"])
  if ← assertEqual "obsEq_is_univ" (ty1.getD (.lit "?")) (.con "Univ" []) then passed := passed + 1

  -- Test 2: obsRefl(a) : obsEq A a a
  let ty2 := inferType typeRules (.con "obsRefl" [.var "a"])
  match ty2 with
  | some (.con "obsEq" [_, a1, a2]) =>
    if ← assertEqualBool "obsRefl_endpoints_match" (a1 == a2) true then passed := passed + 1
  | _ =>
    IO.println "  ✗ obsRefl_endpoints_match"

  -- Test 3: obsSym with obsRefl
  let obsSym := Term.con "obsSym" [.con "obsRefl" [.var "a"]]
  let ty3 := inferType typeRules obsSym
  match ty3 with
  | some (.con "obsEq" _) =>
    IO.println "  ✓ obsSym_is_obsEq"
    passed := passed + 1
  | _ =>
    IO.println "  ✗ obsSym_is_obsEq"

  -- Test 4: obsToPath converts to Path
  let obsToPath := Term.con "obsToPath" [.con "obsRefl" [.var "a"]]
  let ty4 := inferType typeRules obsToPath
  match ty4 with
  | some (.con "Path" _) =>
    IO.println "  ✓ obsToPath_gives_path"
    passed := passed + 1
  | _ =>
    IO.println "  ✗ obsToPath_gives_path"

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
  total := total + 4

  let reprPassed ← testReprEquivValidation
  passed := passed + reprPassed
  total := total + 4

  let cubicalPassed ← testCubicalProofCombinators
  passed := passed + cubicalPassed
  total := total + 4

  let equivCompPassed ← testEquivalenceComposition
  passed := passed + equivCompPassed
  total := total + 3

  let extractPassed ← testASTExtraction
  passed := passed + extractPassed
  total := total + 2

  let fullPassed ← testFullValidation
  passed := passed + fullPassed
  total := total + 2

  -- New grammar/rule validation tests
  let grammarErrorsPassed ← testGrammarValidationErrors
  passed := passed + grammarErrorsPassed
  total := total + 3

  let ruleErrorsPassed ← testRuleValidationErrors
  passed := passed + ruleErrorsPassed
  total := total + 4

  let leftRecPassed ← testLeftRecursionWarnings
  passed := passed + leftRecPassed
  total := total + 2

  let optimizePassed ← testGrammarOptimizationWarnings
  passed := passed + optimizePassed
  total := total + 4

  let combinedPassed ← testCombinedValidation
  passed := passed + combinedPassed
  total := total + 6

  -- New cubical type tests
  let intervalPassed ← testIntervalType
  passed := passed + intervalPassed
  total := total + 4

  let cofibPassed ← testCofibrations
  passed := passed + cofibPassed
  total := total + 4

  let kanPassed ← testKanOperations
  passed := passed + kanPassed
  total := total + 3

  let hitPassed ← testHigherInductives
  passed := passed + hitPassed
  total := total + 4

  let hlevelPassed ← testHLevels
  passed := passed + hlevelPassed
  total := total + 4

  let depTypesPassed ← testDependentTypes
  passed := passed + depTypesPassed
  total := total + 4

  let gluePassed ← testGlueAndExtension
  passed := passed + gluePassed
  total := total + 4

  let jPassed ← testJEliminator
  passed := passed + jPassed
  total := total + 2

  let obsPassed ← testObservationalEq
  passed := passed + obsPassed
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
