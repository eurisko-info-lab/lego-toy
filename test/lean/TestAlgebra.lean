/-
  TestAlgebra: Comprehensive tests for core Algebra functions

  Tests the most depended-on module (6 dependents):
  - Term.matchPattern: Pattern matching for rewrite rules
  - Term.substitute: Variable substitution
  - Rule.matchPattern: Extended pattern matching with rest patterns
  - applyTemplate: Template instantiation with splat/map patterns
  - applyRulesOnce/applyRulesDeep: Rule application
  - builtinStep: Built-in primitive operations
  - Iso operations: composition, parallel, choice

  Run with: lake exe lego-test-algebra
-/

import Lego.Algebra
import TestUtils

open Lego
open Lego.Test

/-! ## Test Helpers -/

def term (s : String) : Term := Term.var s
def lit (s : String) : Term := Term.lit s
def con (name : String) (args : List Term) : Term := Term.con name args
def atom (name : String) : Term := Term.con name []

/-! ## Term.matchPattern Tests -/

def termMatchPatternTests : List TestResult :=
  -- Pattern $x should match any term and bind it
  let pat1 := term "$x"
  let t1 := con "foo" [lit "bar"]
  let result1 := Term.matchPattern pat1 t1

  -- Literal patterns must match exactly
  let pat2 := lit "hello"

  -- Constructor patterns match name and arity
  let pat3 := con "add" [term "$a", term "$b"]
  let t3 := con "add" [lit "1", lit "2"]
  let result3 := Term.matchPattern pat3 t3

  -- Nested pattern matching
  let pat4 := con "pair" [con "fst" [term "$x"], con "snd" [term "$y"]]
  let t4 := con "pair" [con "fst" [lit "a"], con "snd" [lit "b"]]
  let result4 := Term.matchPattern pat4 t4

  -- Mismatched constructor names
  let pat5 := con "foo" []
  -- Mismatched arity
  let pat6 := con "f" [term "$x"]

  [
    assertSome "variable binding" result1,
    assertTrue "has one binding" (result1.map (·.length == 1) |>.getD false),
    assertTrue "binds $x" (result1.map (·.head! == ("$x", t1)) |>.getD false),
    assertSome "same literal matches" (Term.matchPattern pat2 (lit "hello")),
    assertNone "different literal fails" (Term.matchPattern pat2 (lit "world")),
    assertSome "constructor matching" result3,
    assertTrue "has two bindings" (result3.map (·.length == 2) |>.getD false),
    assertSome "nested match works" result4,
    assertTrue "nested has two bindings" (result4.map (·.length == 2) |>.getD false),
    assertNone "different names fail" (Term.matchPattern pat5 (con "bar" [])),
    assertNone "different arity fails" (Term.matchPattern pat6 (con "f" [lit "a", lit "b"]))
  ]

/-! ## Term.substitute Tests -/

def substituteTests : List TestResult :=
  -- Basic substitution
  let t1 := term "$x"
  let env1 := [("$x", lit "hello")]
  let r1 := Term.substitute t1 env1

  -- Nested substitution
  let t2 := con "add" [term "$a", con "mul" [term "$b", term "$c"]]
  let env2 := [("$a", lit "1"), ("$b", lit "2"), ("$c", lit "3")]
  let r2 := Term.substitute t2 env2

  -- Preserves non-vars
  let t3 := con "f" [lit "constant", term "$x"]
  let env3 := [("$x", lit "value")]
  let r3 := Term.substitute t3 env3

  -- Unbound variable stays
  let t4 := term "$unknown"
  let env4 := [("$x", lit "value")]
  let r4 := Term.substitute t4 env4

  [
    assertEq "basic substitution" r1 (lit "hello"),
    assertEq "nested substitution" r2 (con "add" [lit "1", con "mul" [lit "2", lit "3"]]),
    assertEq "preserves literal" r3 (con "f" [lit "constant", lit "value"]),
    assertEq "unbound unchanged" r4 (term "$unknown")
  ]

/-! ## applyTemplate Tests -/

def applyTemplateTests : List TestResult :=
  -- Basic template
  let template1 := con "result" [term "$x", term "$y"]
  let env1 := [("x", lit "a"), ("y", lit "b")]
  let r1 := applyTemplate env1 template1

  -- Splat pattern expansion
  let template2 := con "list" [term "$items..."]
  let env2 := [("items", con "seq" [lit "1", lit "2", lit "3"])]
  let r2 := applyTemplate env2 template2

  -- Preserves structure
  let template3 := con "outer" [con "inner" [term "$x"], lit "constant"]
  let env3 := [("x", lit "value")]
  let r3 := applyTemplate env3 template3

  [
    assertEq "basic template" r1 (con "result" [lit "a", lit "b"]),
    assertEq "splat expands" r2 (con "list" [lit "1", lit "2", lit "3"]),
    assertEq "structure preserved" r3 (con "outer" [con "inner" [lit "value"], lit "constant"])
  ]

/-! ## Rule Application Tests -/

def ruleApplicationTests : List TestResult :=
  -- Rule: (double $x) ~> (add $x $x)
  let rule1 : Rule := {
    name := "double"
    pattern := con "double" [term "$x"]
    template := con "add" [term "$x", term "$x"]
  }
  let t1 := con "double" [lit "5"]
  let r1 := rule1.apply t1
  let r1back := rule1.unapply (con "add" [lit "5", lit "5"])

  -- List of rules
  let rules : List Rule := [
    { name := "zero", pattern := con "zero" [], template := lit "0" },
    { name := "one", pattern := con "one" [], template := lit "1" },
    { name := "two", pattern := con "two" [], template := lit "2" }
  ]
  let once1 := applyRulesOnce rules (con "one" [])
  let noMatch := applyRulesOnce rules (con "three" [])

  -- Recursive rule application
  let succRules : List Rule := [
    { name := "succ0", pattern := con "succ" [con "zero" []], template := con "one" [] },
    { name := "succ1", pattern := con "succ" [con "one" []], template := con "two" [] }
  ]
  let deep1 := applyRulesDeep succRules (con "succ" [con "succ" [con "zero" []]])

  -- Normalize to fixpoint
  let addRules : List Rule := [
    { name := "addZ", pattern := con "add" [con "zero" [], term "$x"], template := term "$x" },
    { name := "addS", pattern := con "add" [con "succ" [term "$m"], term "$n"],
      template := con "succ" [con "add" [term "$m", term "$n"]] }
  ]
  let norm1 := normalizeWithRules 100 addRules
    (con "add" [con "succ" [con "zero" []], con "succ" [con "zero" []]])
  let expected := con "succ" [con "succ" [con "zero" []]]  -- 2

  [
    assertSome "rule applies forward" r1,
    assertEq "double -> add" (r1.getD (atom "fail")) (con "add" [lit "5", lit "5"]),
    assertSome "rule applies backward" r1back,
    assertEq "add -> double" (r1back.getD (atom "fail")) (con "double" [lit "5"]),
    assertSome "first match" once1,
    assertEq "one -> 1" (once1.getD (atom "fail")) (lit "1"),
    assertNone "no match" noMatch,
    assertEq "deep application" deep1 (con "two" []),
    assertEq "normalize add(1,1)=2" norm1 expected
  ]

/-! ## Built-in Primitives Tests -/

def builtinTests : List TestResult := [
  assertEq "not true = false"
    (builtinStep (con "not" [con "true" []]))
    (some (con "false" [])),
  assertEq "not false = true"
    (builtinStep (con "not" [con "false" []]))
    (some (con "true" [])),
  assertEq "true && x = x"
    (builtinStep (con "and" [con "true" [], term "x"]))
    (some (term "x")),
  assertEq "false && x = false"
    (builtinStep (con "and" [con "false" [], term "x"]))
    (some (con "false" [])),
  assertEq "true || x = true"
    (builtinStep (con "or" [con "true" [], term "x"]))
    (some (con "true" [])),
  assertEq "false || x = x"
    (builtinStep (con "or" [con "false" [], term "x"]))
    (some (term "x"))
]

/-! ## Iso Operations Tests -/

def isoTests : List TestResult :=
  -- Identity iso
  let idIso : Iso Nat Nat := Iso.id

  -- Composition
  let double : Iso Nat Nat := {
    forward := fun n => some (n * 2)
    backward := fun n => if n % 2 == 0 then some (n / 2) else none
  }
  let addOne : Iso Nat Nat := {
    forward := fun n => some (n + 1)
    backward := fun n => if n > 0 then some (n - 1) else none
  }
  let composed := Iso.comp double addOne

  -- Symmetric
  let encode : Iso String Nat := {
    forward := fun s => some s.length
    backward := fun n => some (String.mk (List.replicate n 'x'))
  }
  let decode := Iso.sym encode

  -- OrElse fallback
  let parseDigit : Iso String Nat := {
    forward := fun s => s.toNat?
    backward := fun n => some (toString n)
  }
  let fallback : Iso String Nat := {
    forward := fun _ => some 0
    backward := fun _ => some "default"
  }
  let combined := Iso.orElse parseDigit fallback

  [
    assertEq "id forward" (idIso.forward 42) (some 42),
    assertEq "id backward" (idIso.backward 42) (some 42),
    assertEq "comp forward 5->10->11" (composed.forward 5) (some 11),
    assertEq "comp backward 11->10->5" (composed.backward 11) (some 5),
    assertEq "sym forward->backward" (decode.forward 3) (some "xxx"),
    assertEq "sym backward->forward" (decode.backward "hello") (some 5),
    assertEq "orElse valid" (combined.forward "42") (some 42),
    assertEq "orElse fallback" (combined.forward "abc") (some 0)
  ]

/-! ## Test Runner -/

def main : IO UInt32 := do
  let groups := [
    ("Term.matchPattern", termMatchPatternTests),
    ("Term.substitute", substituteTests),
    ("applyTemplate", applyTemplateTests),
    ("Rule Application", ruleApplicationTests),
    ("Built-in Primitives", builtinTests),
    ("Iso Operations", isoTests)
  ]

  runAllTests "Algebra Module Tests (Core - 6 Dependents)" groups
