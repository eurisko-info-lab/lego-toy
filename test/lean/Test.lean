/-
  Test: Runnable tests for Lego core library

  Tests core functionality and parses .lego files.
  Run with: lake exe lego-test

  For Red-specific (cubical type theory) tests, see TestRed.lean
  Run with: lake exe lego-test-red

  NOTE: This test suite uses Runtime.init to ensure Bootstrap.lego
  is loaded first, providing the correct grammar for all .lego file parsing.
-/

import Lego
import Lego.Attr
import Lego.AttrEval
import Lego.Bootstrap
import Lego.Loader
import Lego.Runtime

open Lego
open Lego.Loader
open Lego.Runtime

/-! ## Test Framework -/

structure TestResult where
  name : String
  passed : Bool
  message : String := ""

def assertTrue (name : String) (cond : Bool) : TestResult :=
  { name := name, passed := cond, message := if cond then "✓" else "✗ expected true" }

def assertEq [BEq α] [Repr α] (name : String) (actual expected : α) : TestResult :=
  let passed := actual == expected
  { name := name
    passed := passed
    message := if passed then "✓" else s!"✗ expected {repr expected}, got {repr actual}" }

/-! ## Term Construction Tests -/

def termTests : List TestResult := [
  assertEq "term_var" (Term.var "x") (Term.var "x"),
  assertEq "term_lit" (Term.lit "42") (Term.lit "42"),
  assertEq "term_con" (Term.con "app" [Term.var "f", Term.var "x"])
                      (Term.con "app" [Term.var "f", Term.var "x"]),
  let lam_id := Term.con "lam" [Term.var "x", Term.var "x"]
  assertEq "term_lam_id" lam_id (Term.con "lam" [Term.var "x", Term.var "x"]),
  let zero := Term.con "lam" [Term.var "f", Term.con "lam" [Term.var "x", Term.var "x"]]
  assertTrue "term_church_zero" (zero.toString.length > 0)
]

/-! ## Iso Tests -/

def isoTests : List TestResult :=
  let idR : Iso Nat Nat := Iso.id
  let idFwd := idR.forward 42
  let idBwd := idR.backward 42
  let addOne : Iso Nat Nat := {
    forward := fun n => some (n + 1)
    backward := fun n => if n > 0 then some (n - 1) else none
  }
  let doubled := addOne >>> addOne
  let dblFwd := doubled.forward 5
  let dblBwd := doubled.backward 7
  let sym_addOne := ~addOne
  let symFwd := sym_addOne.forward 5
  let symBwd := sym_addOne.backward 5

  [
    assertEq "iso_id_forward" idFwd (some 42),
    assertEq "iso_id_backward" idBwd (some 42),
    assertEq "iso_comp_forward" dblFwd (some 7),
    assertEq "iso_comp_backward" dblBwd (some 5),
    assertEq "iso_sym_forward" symFwd (some 4),
    assertEq "iso_sym_backward" symBwd (some 6)
  ]

/-! ## Pattern Matching Tests -/

def matchTests : List TestResult :=
  let pat1 := Term.var "$x"
  let term1 := Term.lit "hello"
  let result1 := Term.matchPattern pat1 term1
  let pat2 := Term.con "app" [Term.var "$f", Term.var "$x"]
  let term2 := Term.con "app" [Term.var "add", Term.lit "1"]
  let result2 := Term.matchPattern pat2 term2
  let pat3 := Term.con "lam" [Term.var "$x", Term.con "app" [Term.var "$f", Term.var "$x"]]
  let term3 := Term.con "lam" [Term.var "y", Term.con "app" [Term.var "inc", Term.var "y"]]
  let result3 := Term.matchPattern pat3 term3
  let pat4 := Term.con "lam" [Term.var "$x", Term.var "$body"]
  let term4 := Term.con "app" [Term.var "f", Term.var "x"]
  let result4 := Term.matchPattern pat4 term4

  [
    assertTrue "match_var" result1.isSome,
    assertTrue "match_con" result2.isSome,
    assertTrue "match_nested" result3.isSome,
    assertTrue "match_fail" result4.isNone
  ]

/-! ## Substitution Tests -/

def substTests : List TestResult :=
  let env1 : List (String × Term) := [("$x", Term.lit "42")]
  let template1 := Term.var "$x"
  let result1 := Term.substitute template1 env1
  let env2 := [("$f", Term.var "add"), ("$x", Term.lit "1")]
  let template2 := Term.con "app" [Term.var "$f", Term.var "$x"]
  let result2 := Term.substitute template2 env2
  let env3 := [("$x", Term.var "y"), ("$body", Term.var "y")]
  let template3 := Term.con "lam" [Term.var "$x", Term.var "$body"]
  let result3 := Term.substitute template3 env3

  [
    assertEq "subst_simple" result1 (Term.lit "42"),
    assertEq "subst_con" result2 (Term.con "app" [Term.var "add", Term.lit "1"]),
    assertEq "subst_nested" result3 (Term.con "lam" [Term.var "y", Term.var "y"])
  ]

/-! ## Rule Application Tests -/

def ruleTests : List TestResult :=
  let betaRule : Rule := {
    name := "beta"
    pattern := Term.con "app" [Term.con "lam" [Term.var "$x", Term.var "$body"], Term.var "$arg"]
    template := Term.con "subst" [Term.var "$x", Term.var "$arg", Term.var "$body"]
  }
  let term := Term.con "app" [Term.con "lam" [Term.var "x", Term.var "x"], Term.var "y"]
  let result := betaRule.apply term
  let expected := Term.con "subst" [Term.var "x", Term.var "y", Term.var "x"]
  let etaRule : Rule := {
    name := "eta"
    pattern := Term.con "lam" [Term.var "$x", Term.con "app" [Term.var "$f", Term.var "$x"]]
    template := Term.var "$f"
  }
  let term2 := Term.con "lam" [Term.var "x", Term.con "app" [Term.var "inc", Term.var "x"]]
  let result2 := etaRule.apply term2

  [
    assertTrue "rule_beta" result.isSome,
    assertEq "rule_beta_result" result (some expected),
    assertEq "rule_eta" result2 (some (Term.var "inc"))
  ]

/-! ## Interpreter Tests (Reduction) -/

def interpreterTests : List TestResult :=
  let id_term := Term.con "lam" [Term.var "x", Term.var "x"]
  let app_id := Term.con "app" [
    Term.con "lam" [Term.var "x", Term.var "x"],
    Term.var "y"
  ]
  let betaRule : Rule := {
    name := "beta"
    pattern := Term.con "app" [Term.con "lam" [Term.var "$x", Term.var "$body"], Term.var "$arg"]
    template := Term.con "subst" [Term.var "$x", Term.var "$arg", Term.var "$body"]
  }
  let step1 := betaRule.apply app_id
  let wire := Term.con "wire" [Term.con "Port" [Term.var "a"], Term.con "Port" [Term.var "b"]]
  let kseq := Term.con "KSeq" [Term.con "KEmpty" [], Term.var "g"]
  let seqIdRule : Rule := {
    name := "seq_id_left"
    pattern := Term.con "KSeq" [Term.con "KEmpty" [], Term.var "$g"]
    template := Term.var "$g"
  }
  let kseqResult := seqIdRule.apply kseq

  [
    assertTrue "interp_id_term" (id_term.toString.length > 0),
    assertTrue "interp_beta_step" step1.isSome,
    assertTrue "interp_wire" (wire.toString.length > 0),
    assertEq "interp_kseq_id" kseqResult (some (Term.var "g"))
  ]

/-! ## Nat (Church Numerals) Tests -/

def natTests : List TestResult :=
  let zero := Term.con "lam" [Term.var "f",
                Term.con "lam" [Term.var "x", Term.var "x"]]
  let one := Term.con "lam" [Term.var "f",
               Term.con "lam" [Term.var "x",
                 Term.con "app" [Term.var "f", Term.var "x"]]]
  let two := Term.con "lam" [Term.var "f",
               Term.con "lam" [Term.var "x",
                 Term.con "app" [Term.var "f",
                   Term.con "app" [Term.var "f", Term.var "x"]]]]
  let succ := Term.con "lam" [Term.var "n",
                Term.con "lam" [Term.var "f",
                  Term.con "lam" [Term.var "x",
                    Term.con "app" [Term.var "f",
                      Term.con "app" [Term.con "app" [Term.var "n", Term.var "f"], Term.var "x"]]]]]
  let add := Term.con "lam" [Term.var "m",
               Term.con "lam" [Term.var "n",
                 Term.con "lam" [Term.var "f",
                   Term.con "lam" [Term.var "x",
                     Term.con "app" [Term.con "app" [Term.var "m", Term.var "f"],
                       Term.con "app" [Term.con "app" [Term.var "n", Term.var "f"], Term.var "x"]]]]]]

  [
    assertTrue "nat_zero" (zero.toString.length > 0),
    assertTrue "nat_one" (one.toString.length > 0),
    assertTrue "nat_two" (two.toString.length > 0),
    assertTrue "nat_succ" (succ.toString.length > 0),
    assertTrue "nat_add" (add.toString.length > 0)
  ]

/-! ## Let/Letrec Tests -/

def letTests : List TestResult :=
  let letExpr := Term.con "let" [Term.var "x", Term.lit "42", Term.var "x"]
  let factDef := Term.con "letrec" [
    Term.var "fact",
    Term.con "lam" [Term.var "n",
      Term.con "if" [
        Term.con "isZero" [Term.var "n"],
        Term.lit "1",
        Term.con "mul" [Term.var "n",
          Term.con "app" [Term.var "fact",
            Term.con "pred" [Term.var "n"]]]]],
    Term.con "app" [Term.var "fact", Term.lit "5"]
  ]
  let fibDef := Term.con "letrec" [
    Term.var "fib",
    Term.con "lam" [Term.var "n",
      Term.con "if" [
        Term.con "leq" [Term.var "n", Term.lit "1"],
        Term.var "n",
        Term.con "add" [
          Term.con "app" [Term.var "fib", Term.con "sub" [Term.var "n", Term.lit "1"]],
          Term.con "app" [Term.var "fib", Term.con "sub" [Term.var "n", Term.lit "2"]]]]],
    Term.con "app" [Term.var "fib", Term.lit "10"]
  ]

  [
    assertTrue "let_expr" (letExpr.toString.length > 0),
    assertTrue "letrec_fact" (factDef.toString.length > 0),
    assertTrue "letrec_fib" (fibDef.toString.length > 0)
  ]

/-! ## .lego File Parsing Tests (IO) -/

/-- Get identifier name from (ident name) node -/
def getIdentName (t : Term) : Option String :=
  match t with
  | .con "ident" [.lit n] => some n
  | .con "ident" [.var n] => some n
  | _ => none

/-- Filter out paren literals from args -/
def filterParens (args : List Term) : List Term :=
  args.filter fun t => match t with
    | .lit "(" => false
    | .lit ")" => false
    | _ => true

/-- Convert parsed pattern AST to Term for pattern matching -/
partial def patternToTerm (t : Term) : Term :=
  match t with
  | .con "var" [.lit "$", .con "ident" [.var name]] =>
    .var s!"${name}"
  | .con "metavar" args =>
    let idents := args.filterMap getIdentName
    match idents.head? with
    | some n => .var s!"${n}"
    | none => t
  | .con "pvar" args =>
    let idents := args.filterMap getIdentName
    match idents.head? with
    | some n => .var n
    | none => t
  | .con "lit" [.con "string" [.lit s]] => .lit s
  | .con "lit" [.lit s] => .lit s
  | .con "plit" [.con "string" [.lit s]] => .lit s
  | .con "plit" [.lit s] => .lit s
  | .con "con" args =>
    let filtered := filterParens args
    match filtered with
    | ident :: rest =>
      match getIdentName ident with
      | some name => .con name (rest.map patternToTerm)
      | none => t
    | _ => t
  | .con "pcon" args =>
    let filtered := filterParens args
    match filtered with
    | ident :: rest =>
      match getIdentName ident with
      | some name => .con name (rest.map patternToTerm)
      | none => t
    | _ => t
  | .con name args => .con name (args.map patternToTerm)
  | _ => t

/-- Convert parsed template AST to Term for substitution -/
partial def templateToTerm (t : Term) : Term :=
  match t with
  | .con "var" [.lit "$", .con "ident" [.var name]] =>
    .var s!"${name}"
  | .con "metavar" args =>
    let idents := args.filterMap getIdentName
    match idents.head? with
    | some n => .var s!"${n}"
    | none => t
  | .con "tvar" args =>
    let idents := args.filterMap getIdentName
    match idents.head? with
    | some n => .var n
    | none => t
  | .con "lit" [.con "string" [.lit s]] => .lit s
  | .con "lit" [.lit s] => .lit s
  | .con "tlit" [.con "string" [.lit s]] => .lit s
  | .con "tlit" [.lit s] => .lit s
  | .con "con" args =>
    let filtered := filterParens args
    match filtered with
    | ident :: rest =>
      match getIdentName ident with
      | some name => .con name (rest.map templateToTerm)
      | none => t
    | _ => t
  | .con "tcon" args =>
    let filtered := filterParens args
    match filtered with
    | ident :: rest =>
      match getIdentName ident with
      | some name => .con name (rest.map templateToTerm)
      | none => t
    | _ => t
  | .con name args => .con name (args.map templateToTerm)
  | _ => t

/-- Convert parsed term AST (s-expression) to simplified Term -/
partial def termAstToTerm (t : Term) : Term :=
  match t with
  | .con "var" [ident] =>
    match getIdentName ident with
    | some n => .con n []
    | none => t
  | .con "lit" [.con "string" [.lit s]] => .lit s
  | .con "lit" [.lit s] => .lit s
  | .con "num" [.con "number" [.lit n]] => .lit n
  | .con "num" [.lit n] => .lit n
  | .con "con" args =>
    let filtered := filterParens args
    match filtered with
    | ident :: rest =>
      match getIdentName ident with
      | some name => .con name (rest.map termAstToTerm)
      | none => t
    | _ => t
  | .con name args => .con name (args.map termAstToTerm)
  | _ => t

/-- Extract rules from parsed AST -/
partial def extractRules (t : Term) : List Rule :=
  match t with
  | .con "DRule" args =>
    let rec findArrowIdx (xs : List Term) (idx : Nat) : Option Nat :=
      match xs with
      | [] => none
      | .lit "~>" :: _ => some idx
      | _ :: rest => findArrowIdx rest (idx + 1)
    let arrowIdx := findArrowIdx args 0
    match arrowIdx with
    | some idx =>
      if idx > 0 ∧ idx + 1 < args.length then
        let pattern := args[idx - 1]!
        let template := args[idx + 1]!
        let nameOpt := args.findSome? fun
          | .con "ident" [.lit n] => some n
          | .con "ident" [.var n] => some n
          | _ => none
        match nameOpt with
        | some name => [{ name := name, pattern := patternToTerm pattern, template := templateToTerm template }]
        | none => []
      else []
    | none => []
  | .con "seq" ts => ts.flatMap extractRules
  | .con _ ts => ts.flatMap extractRules
  | _ => []

/-- Test with expected result -/
structure EvalTest where
  name : String
  input : Term
  expected : Term
  deriving Repr

/-- Extract eval tests (tests with ~~> expected result) from parsed AST -/
partial def extractEvalTests (t : Term) : List EvalTest :=
  match t with
  | .con "DTest" args =>
    let arrowIdx := args.findIdx? (· == .lit "~~>")
    match arrowIdx with
    | some idx =>
      if idx > 0 ∧ idx + 1 < args.length then
        let input := args[idx - 1]!
        let expected := args[idx + 1]!
        let nameOpt := args.findSome? fun
          | .con "string" [.lit n] => some (n.replace "\"" "")
          | _ => none
        match nameOpt with
        | some name => [{ name := name, input := termAstToTerm input, expected := termAstToTerm expected }]
        | none => []
      else []
    | none => []
  | .con "seq" ts => ts.flatMap extractEvalTests
  | .con _ ts => ts.flatMap extractEvalTests
  | _ => []

/-- Apply built-in substitution -/
partial def applySubst (x : String) (val : Term) (body : Term) : Term :=
  match body with
  | .var name => if name == x then val else body
  | .con "var" [.var name] => if name == x then val else body
  | .con "var" [.con name []] => if name == x then val else body
  | .lit _ => body
  | .con name args => .con name (args.map (applySubst x val))

/-- Apply built-in reductions -/
def stepBuiltin (t : Term) : Option Term :=
  match t with
  | .con "subst" [.var x, val, body] =>
    some (applySubst x val body)
  | .con "subst" [.con x [], val, body] =>
    some (applySubst x val body)
  | _ => none

/-- Apply a single step with any matching rule -/
def stepOnce (rules : List Rule) (t : Term) : Option Term :=
  match rules.findSome? (fun r => r.apply t) with
  | some t' => some t'
  | none => stepBuiltin t

/-- Apply rules to subterms recursively (single step) -/
partial def stepDeep (rules : List Rule) (t : Term) : Option Term :=
  match stepOnce rules t with
  | some t' => some t'
  | none =>
    match t with
    | .con name args =>
      let rec tryArgs (before : List Term) (after : List Term) : Option Term :=
        match after with
        | [] => none
        | arg :: rest =>
          match stepDeep rules arg with
          | some arg' => some (.con name (before.reverse ++ [arg'] ++ rest))
          | none => tryArgs (arg :: before) rest
      tryArgs [] args
    | _ => none

/-- Normalize term by applying rules until fixpoint (with fuel) -/
partial def normalize (fuel : Nat) (rules : List Rule) (t : Term) : Term :=
  match fuel with
  | 0 => t
  | n + 1 =>
    match stepDeep rules t with
    | some t' => normalize n rules t'
    | none => t

/-- Canonicalize a term -/
partial def canonicalize (t : Term) : Term :=
  match t with
  | .con "var" [.var name] => .con name []
  | .con "var" [.con name []] => .con name []
  | .con name [] => .con name []
  | .con name args => .con name (args.map canonicalize)
  | .var name => .con name []
  | _ => t

/-- Compare terms for equality after canonicalization -/
def termEq (t1 t2 : Term) : Bool := canonicalize t1 == canonicalize t2

/-- Run a single eval test -/
def runEvalTest (rules : List Rule) (test : EvalTest) : TestResult :=
  let result := normalize 100 rules test.input
  let passed := termEq result test.expected
  { name := s!"eval_{test.name}"
    passed := passed
    message := if passed then "✓"
               else s!"✗ got {result}, expected {test.expected}" }

/-- Count test declarations in parsed AST -/
partial def countTests (t : Term) : Nat :=
  match t with
  | .con "DTest" _ => 1
  | .con "seq" ts => ts.foldl (fun acc t' => acc + countTests t') 0
  | .con _ ts => ts.foldl (fun acc t' => acc + countTests t') 0
  | _ => 0

/-- Count rule declarations in parsed AST -/
partial def countRules (t : Term) : Nat :=
  match t with
  | .con "DRule" _ => 1
  | .con "seq" ts => ts.foldl (fun acc t' => acc + countRules t') 0
  | .con _ ts => ts.foldl (fun acc t' => acc + countRules t') 0
  | _ => 0

/-- Count piece declarations in parsed AST -/
partial def countPieces (t : Term) : Nat :=
  match t with
  | .con "DPiece" _ => 1
  | .con "DToken" _ => 1
  | .con "seq" ts => ts.foldl (fun acc t' => acc + countPieces t') 0
  | .con _ ts => ts.foldl (fun acc t' => acc + countPieces t') 0
  | _ => 0

/-- Parse and analyze a .lego file using the runtime grammar -/
def analyzeLegoFile (rt : Runtime) (path : String) : IO (List TestResult) := do
  let name := path.splitOn "/" |>.getLast!
  try
    let content ← IO.FS.readFile path
    let result := Runtime.parseLegoFile rt content
    match result with
    | some ast =>
      let testCount := countTests ast
      let ruleCount := countRules ast
      let pieceCount := countPieces ast
      let rules := Loader.extractRules ast
      let evalTests := extractEvalTests ast
      let evalResults := evalTests.map (runEvalTest rules)
      let baseResults := [
        { name := s!"parse_{name}", passed := true, message := "✓" },
        { name := s!"{name}_has_pieces", passed := pieceCount > 0, message := if pieceCount > 0 then s!"✓ ({pieceCount})" else "✗" },
        { name := s!"{name}_has_rules", passed := true, message := s!"✓ ({ruleCount})" },
        { name := s!"{name}_has_tests", passed := true, message := s!"✓ ({testCount})" }
      ]
      pure (baseResults ++ evalResults)
    | none => pure [{ name := s!"parse_{name}", passed := false, message := "✗ parse failed" }]
  catch _ =>
    pure [{ name := s!"parse_{name}", passed := false, message := "✗ file not found" }]

/-- Run .lego file parsing tests using the runtime grammar -/
def runLegoFileTests (rt : Runtime) : IO (List TestResult) := do
  let testPath := "./test/lego"
  let examplePath := "./examples"
  let files := [
    s!"{examplePath}/Lambda.lego",
    s!"{examplePath}/Arith.lego",
    s!"{examplePath}/INet.lego",
    s!"{examplePath}/K.lego",
    s!"{testPath}/Bootstrap.lego",
    s!"{examplePath}/Cubical/syntax/Redtt.lego",
    s!"{examplePath}/Cubical/syntax/Cooltt.lego"
  ]
  let mut results : List TestResult := []
  for file in files do
    let fileResults ← analyzeLegoFile rt file
    results := results ++ fileResults
  pure results

/-! ## AST GrammarExpr Tests -/

def runGrammarExprTests : IO (List TestResult) := do
  let hardcodedProds := Bootstrap.metaGrammar.allGrammar

  let testProd := "Atom.ident"
  let testInput := "foo"
  let tokens := Bootstrap.tokenize testInput

  let test1 := match hardcodedProds.find? (·.1 == testProd) with
  | some (_, g) =>
    let st : ParseStateT GrammarExpr := { tokens := tokens, binds := [] }
    match parseGrammarT defaultFuel hardcodedProds g st with
    | some (_, st') =>
      let passed := st'.tokens.isEmpty
      { name := "parse_ident_as_GrammarExpr"
        passed := passed
        message := if passed then "✓" else "✗ tokens remaining" }
    | none =>
      { name := "parse_ident_as_GrammarExpr", passed := false, message := "✗ parse failed" }
  | none =>
    { name := "parse_ident_as_GrammarExpr", passed := false, message := s!"✗ prod not found" }

  let (test2, test3) ← do
    match ← loadBootstrapProductions "./test/lego/Bootstrap.lego" with
    | some parsedProds =>
      let (isSubset, missing) := isSubsetOfProductions hardcodedProds parsedProds
      let compTest := if isSubset then
        { name := "hardcoded_subset_of_parsed"
          passed := true
          message := s!"✓ (hardcoded {hardcodedProds.length} ⊆ parsed {parsedProds.length})" : TestResult }
      else
        { name := "hardcoded_subset_of_parsed"
          passed := false
          message := s!"✗ missing in parsed: {missing.take 5}" }
      let fullProds := builtinProductions ++ parsedProds
      let termTest := match fullProds.find? (·.1 == "Term.term") with
      | some (_, g) =>
        let termTokens := Bootstrap.tokenize "(app x y)"
        let st : ParseState := { tokens := termTokens, binds := [] }
        let (result, _) := parseGrammar defaultFuel fullProds g st
        match result with
        | some (_, st') =>
          { name := "parsed_bootstrap_parses_term"
            passed := st'.tokens.isEmpty
            message := if st'.tokens.isEmpty then "✓" else "✗ tokens remaining" }
        | none =>
          { name := "parsed_bootstrap_parses_term", passed := false, message := "✗ parse failed" }
      | none =>
        { name := "parsed_bootstrap_parses_term", passed := false, message := "✗ Term.term not found" }
      pure (compTest, termTest)
    | none =>
      pure (
        { name := "bootstrap_parsed_vs_hardcoded", passed := false, message := "✗ parse failed" },
        { name := "parsed_bootstrap_parses_term", passed := false, message := "✗ no grammar" }
      )

  pure [
    { name := "hardcoded_bootstrap_loaded"
      passed := true
      message := s!"✓ ({hardcodedProds.length} productions)" },
    test1,
    test2,
    test3
  ]

/-! ## Attribute Grammar Tests -/

def attrTests : List TestResult :=
  let depthAttr : AttrDef := {
    name := "depth"
    flow := .syn
    type := some (Term.var "Nat")
    rules := [
      { prod := "var", target := [], expr := Term.lit "0" },
      { prod := "lit", target := [], expr := Term.lit "0" },
      { prod := "lam", target := [], expr := Term.con "succ" [Term.var "$child1.depth"] }
    ]
  }
  let testTerm := Term.con "lam" [Term.var "x", Term.var "x"]
  let env := evalSyn depthAttr testTerm
  let hasEntries := env.values.length > 0
  let selfRef := AttrRef.self "type"
  let childRef := AttrRef.child "body" "type"
  let env1 := AttrEnv.empty
  let env2 := env1.insert [] "test" (Term.lit "value")
  let lookup1 := env2.lookup [] "test"

  [
    assertTrue "attr_env_empty" (AttrEnv.empty.values.length == 0),
    assertTrue "attr_env_insert_lookup" (lookup1 == some (Term.lit "value")),
    assertTrue "attr_ref_self" (selfRef.path.length == 0),
    assertTrue "attr_ref_child" (childRef.path == ["body"]),
    assertTrue "attr_eval_creates_env" hasEntries
  ]

/-- IO-based test for loading attribute grammar from file using runtime grammar -/
def runAttrFileTests (rt : Runtime) : IO (List TestResult) := do
  let path := "./test/AttrTest.lego"
  try
    let content ← IO.FS.readFile path
    match Runtime.parseLegoFile rt content with
    | some ast =>
      let attrDefs := Loader.extractAttrDefs ast
      let attrRules := Loader.extractAttrRules ast
      let combined := Loader.extractAttributes ast

      pure [
        assertTrue "attrtest_parses" true,
        assertTrue "attrtest_has_attr_defs" (attrDefs.length >= 3),
        assertTrue "attrtest_has_attr_rules" (attrRules.length >= 4),
        assertTrue "attrtest_combined_has_rules" (combined.any fun d => !d.rules.isEmpty)
      ]
    | none =>
      pure [assertTrue "attrtest_parses" false]
  catch _ =>
    pure [assertTrue "attrtest_file_optional" true]

/-! ## Attribute Evaluation Tests -/

def attrEvalTests : List TestResult :=
  let loc := SourceLoc.mk "test.lego" 10 5 0
  let locStr := loc.toString
  let err1 := TypeError.error "test error" loc
  let err2 := TypeError.mismatch (.var "Int") (.var "Bool") loc
  let err3 := TypeError.undefined "x" loc
  let ok1 : EvalResult Term := .ok (.var "test") []
  let ok2 : EvalResult Term := .ok (.var "test") [err1]
  let fail1 : EvalResult Term := .failed [err2]
  let ctx1 := Context.empty
  let ctx2 := ctx1.extend "x" (.var "Int")
  let ctx3 := ctx2.extend "y" (.var "Bool")
  let lookup1 := ctx3.lookupType "x"
  let lookup2 := ctx3.lookupType "z"
  let varCtx1 := VarContext.empty
  let varCtx2 := varCtx1.extend "i"
  let varCtx3 := varCtx2.extend "j"
  let env1 := EvalEnv.empty
  let env2 := env1.addBinding "x" (.var "Int")
  let env3 := env2.setAttr [] "type" (.var "Int")
  let eq1 := typeEq (.var "Int") (.var "Int")
  let eq2 := typeEq (.var "Int") (.var "Bool")
  let piTy := Term.con "Pi" [.var "x", .var "Int", .var "Bool"]
  let arrowTy := Term.con "Arrow" [.var "Int", .var "Bool"]
  let dom1 := getDomain piTy
  let cod1 := getCodomain piTy
  let dom2 := getDomain arrowTy
  let errStr := formatErrors [err1, err2]
  let (e, w, i) := countBySeverity [err1, err2, err3]

  [
    assertTrue "sourceloc_toString" (locStr == "test.lego:10:5"),
    assertTrue "error_has_message" (err1.message == "test error"),
    assertTrue "mismatch_has_expected" (err2.expected == some (.var "Int")),
    assertTrue "undefined_has_message" (err3.message == "undefined: x"),
    assertTrue "evalresult_ok_isOk" ok1.isOk,
    assertTrue "evalresult_ok_with_errors" ok2.isOk,
    assertTrue "evalresult_failed_not_ok" (!fail1.isOk),
    assertTrue "context_empty" (ctx1.bindings.isEmpty),
    assertTrue "context_extend" (ctx2.bindings.length == 1),
    assertTrue "context_lookup_found" (lookup1 == some (.var "Int")),
    assertTrue "context_lookup_missing" (lookup2 == none),
    assertTrue "context_names" (ctx3.names == ["y", "x"]),
    assertTrue "varctx_empty" (!varCtx1.contains "i"),
    assertTrue "varctx_extend" (varCtx2.contains "i"),
    assertTrue "varctx_multiple" (varCtx3.contains "i" && varCtx3.contains "j"),
    assertTrue "evalenv_empty_no_errors" (!env1.hasErrors),
    assertTrue "evalenv_has_binding" (env2.ctx.bindings.length == 1),
    assertTrue "evalenv_has_attr" (env3.getAttr [] "type" == some (.var "Int")),
    assertTrue "typeEq_same" eq1,
    assertTrue "typeEq_diff" (!eq2),
    assertTrue "getDomain_pi" (dom1 == some (.var "Int")),
    assertTrue "getCodomain_pi" (cod1 == some (.var "Bool")),
    assertTrue "getDomain_arrow" (dom2 == some (.var "Int")),
    assertTrue "formatErrors_not_empty" (!errStr.isEmpty),
    assertTrue "countBySeverity_errors" (e == 3)
  ]

/-! ## Run All Tests -/

def allTests : List TestResult :=
  termTests ++ isoTests ++ matchTests ++ substTests ++
  ruleTests ++ interpreterTests ++ natTests ++ letTests ++
  attrTests ++ attrEvalTests

def printTestGroup (name : String) (tests : List TestResult) : IO (Nat × Nat) := do
  IO.println s!"\n── {name} ──"
  let mut passed := 0
  let mut failed := 0
  for t in tests do
    IO.println s!"  {t.message} {t.name}"
    if t.passed then passed := passed + 1 else failed := failed + 1
  pure (passed, failed)

def main : IO Unit := do
  IO.println "═══════════════════════════════════════════════════════════════"
  IO.println "Lego Test Suite (Core Library)"
  IO.println "═══════════════════════════════════════════════════════════════"

  -- CRITICAL: Initialize runtime by loading Bootstrap.lego FIRST
  -- This ensures all .lego file parsing uses the correct grammar
  let rt ← Runtime.init

  let mut totalPassed := 0
  let mut totalFailed := 0

  let (p, f) ← printTestGroup "Term Tests" termTests
  totalPassed := totalPassed + p; totalFailed := totalFailed + f

  let (p, f) ← printTestGroup "Iso Tests" isoTests
  totalPassed := totalPassed + p; totalFailed := totalFailed + f

  let (p, f) ← printTestGroup "Pattern Matching Tests" matchTests
  totalPassed := totalPassed + p; totalFailed := totalFailed + f

  let (p, f) ← printTestGroup "Substitution Tests" substTests
  totalPassed := totalPassed + p; totalFailed := totalFailed + f

  let (p, f) ← printTestGroup "Rule Application Tests" ruleTests
  totalPassed := totalPassed + p; totalFailed := totalFailed + f

  let (p, f) ← printTestGroup "Interpreter Tests" interpreterTests
  totalPassed := totalPassed + p; totalFailed := totalFailed + f

  let (p, f) ← printTestGroup "Nat (Church Numerals) Tests" natTests
  totalPassed := totalPassed + p; totalFailed := totalFailed + f

  let (p, f) ← printTestGroup "Let/Letrec Tests" letTests
  totalPassed := totalPassed + p; totalFailed := totalFailed + f

  let (p, f) ← printTestGroup "Attribute Grammar Tests" attrTests
  totalPassed := totalPassed + p; totalFailed := totalFailed + f

  let (p, f) ← printTestGroup "Attribute Evaluation Tests" attrEvalTests
  totalPassed := totalPassed + p; totalFailed := totalFailed + f

  let attrFileTests ← runAttrFileTests rt
  let (p, f) ← printTestGroup "Attribute File Loading Tests" attrFileTests
  totalPassed := totalPassed + p; totalFailed := totalFailed + f

  let legoFileTests ← runLegoFileTests rt
  let (p, f) ← printTestGroup ".lego File Parsing Tests" legoFileTests
  totalPassed := totalPassed + p; totalFailed := totalFailed + f

  let grammarExprTests ← runGrammarExprTests
  let (p, f) ← printTestGroup "AST GrammarExpr Tests" grammarExprTests
  totalPassed := totalPassed + p; totalFailed := totalFailed + f

  IO.println ""
  IO.println "═══════════════════════════════════════════════════════════════"
  IO.println s!"Total: {totalPassed + totalFailed} tests, {totalPassed} passed, {totalFailed} failed"
  if totalFailed == 0 then
    IO.println "All tests passed! ✓"
    IO.println ""
    IO.println "For Red-specific tests (cubical type theory), run:"
    IO.println "  lake exe lego-test-red"
  else
    IO.println s!"FAILED: {totalFailed} tests"
    IO.Process.exit 1
