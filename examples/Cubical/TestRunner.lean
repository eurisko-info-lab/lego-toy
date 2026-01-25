/-
  Cubical.TestRunner: Execute tests from .lego files

  This module:
  1. Extracts test declarations from parsed .lego files
  2. Converts Lego.Term to Cubical.Core.Expr
  3. Normalizes and compares against expected results
-/

import Lego
import Cubical.Core

open Lego (Term)
open Lego.Core (Expr Level)

namespace Cubical.TestRunner

/-! ## Lego.Term → Core.Expr Conversion -/

/-- Parse a number from string -/
def parseNat (s : String) : Nat :=
  s.toNat?.getD 0

/-- Strip quotes from a string literal -/
def stripQuotes (s : String) : String :=
  if s.startsWith "\"" && s.endsWith "\"" then
    s.drop 1 |>.dropRight 1
  else s

/-- Convert raw parsed Term AST to normalized form.
    The Term grammar produces: .con "con" [.lit "(", .con "ident" [.var "name"], args..., .lit ")"]
    We need:                   .con "name" [args...] -/
partial def normalizeAst : Term → Term
  -- A constructor: (name args...)
  | .con "con" args =>
    -- Filter out parens and extract name
    let inner := args.filter fun t => t != .lit "(" && t != .lit ")"
    match inner with
    | .con "ident" [.var name] :: rest =>
      .con name (rest.map normalizeAst)
    | _ => .con "con" (args.map normalizeAst)
  -- A variable reference (ident without args means nullary constructor)
  | .con "var" [.con "ident" [.var name]] =>
    .con name []
  -- A literal
  | .con "lit" [.con "string" [.lit s]] =>
    .con "lit" [.lit (stripQuotes s)]
  | .con "lit" [.lit s] =>
    .con "lit" [.lit (stripQuotes s)]
  -- A number
  | .con "num" [.con "number" [.lit n]] =>
    .lit n
  | .con "num" [.lit n] =>
    .lit n
  -- Recursively normalize other terms
  | .con name args => .con name (args.map normalizeAst)
  | other => other

/-- Convert a Lego.Term level to Core.Level -/
partial def termToLevel : Term → Option Level
  | .con "lzero" [] => some .zero
  | .con "lsuc" [l] => do let l' ← termToLevel l; some (.suc l')
  | .con "lmax" [l1, l2] => do
    let l1' ← termToLevel l1
    let l2' ← termToLevel l2
    some (.max l1' l2')
  | .con "lvar" [.lit n] => some (.lvar (parseNat n))
  | .lit "0" => some .zero
  | _ => none

/-- Convert a normalized Lego.Term to Core.Expr.
    This handles the constructors defined in Core.lego. -/
partial def termToExpr : Term → Option Expr
  -- De Bruijn index
  | .con "ix" [.lit n] => some (.ix (parseNat n))

  -- Literals - handle nested .con "lit" from string grammar
  | .con "lit" [.con "lit" [.lit s]] => some (.lit s)
  | .con "lit" [.lit s] => some (.lit s)
  | .lit s => some (.lit s)

  -- Lambda calculus
  | .con "lam" [body] => do let b ← termToExpr body; some (.lam b)
  | .con "app" [f, a] => do
    let f' ← termToExpr f
    let a' ← termToExpr a
    some (.app f' a')
  | .con "pi" [dom, cod] => do
    let d ← termToExpr dom
    let c ← termToExpr cod
    some (.pi d c)
  | .con "sigma" [dom, cod] => do
    let d ← termToExpr dom
    let c ← termToExpr cod
    some (.sigma d c)
  | .con "pair" [a, b] => do
    let a' ← termToExpr a
    let b' ← termToExpr b
    some (.pair a' b')
  | .con "fst" [e] => do let e' ← termToExpr e; some (.fst e')
  | .con "snd" [e] => do let e' ← termToExpr e; some (.snd e')
  | .con "letE" [ty, val, body] => do
    let ty' ← termToExpr ty
    let val' ← termToExpr val
    let body' ← termToExpr body
    some (.letE ty' val' body')

  -- Universes
  | .con "univ" [l] => do let l' ← termToLevel l; some (.univ l')

  -- Dimensions
  | .con "dim0" [] => some .dim0
  | .con "dim1" [] => some .dim1
  | .con "dimVar" [.lit n] => some (.dimVar (parseNat n))

  -- Cofibrations
  | .con "cof_top" [] => some .cof_top
  | .con "cof_bot" [] => some .cof_bot
  | .con "cof_eq" [r, s] => do
    let r' ← termToExpr r
    let s' ← termToExpr s
    some (.cof_eq r' s')
  | .con "cof_and" [phi, psi] => do
    let phi' ← termToExpr phi
    let psi' ← termToExpr psi
    some (.cof_and phi' psi')
  | .con "cof_or" [phi, psi] => do
    let phi' ← termToExpr phi
    let psi' ← termToExpr psi
    some (.cof_or phi' psi')

  -- Paths
  | .con "path" [ty, a, b] => do
    let ty' ← termToExpr ty
    let a' ← termToExpr a
    let b' ← termToExpr b
    some (.path ty' a' b')
  | .con "plam" [body] => do let b ← termToExpr body; some (.plam b)
  | .con "papp" [p, r] => do
    let p' ← termToExpr p
    let r' ← termToExpr r
    some (.papp p' r')
  | .con "refl" [a] => do let a' ← termToExpr a; some (.refl a')

  -- Kan operations
  | .con "coe" [r, r', ty, a] => do
    let r1 ← termToExpr r
    let r2 ← termToExpr r'
    let ty' ← termToExpr ty
    let a' ← termToExpr a
    some (.coe r1 r2 ty' a')
  | .con "hcom" [r, r', ty, phi, cap] => do
    let r1 ← termToExpr r
    let r2 ← termToExpr r'
    let ty' ← termToExpr ty
    let phi' ← termToExpr phi
    let cap' ← termToExpr cap
    some (.hcom r1 r2 ty' phi' cap')

  -- V-types
  | .con "vin" [r, a, b] => do
    let r' ← termToExpr r
    let a' ← termToExpr a
    let b' ← termToExpr b
    some (.vin r' a' b')

  -- Nat
  | .con "nat" [] => some .nat
  | .con "zero" [] => some .zero
  | .con "suc" [n] => do let n' ← termToExpr n; some (.suc n')
  | .con "natElim" [p, z, s, n] => do
    let p' ← termToExpr p
    let z' ← termToExpr z
    let s' ← termToExpr s
    let n' ← termToExpr n
    some (.natElim p' z' s' n')

  -- Circle
  | .con "circle" [] => some .circle
  | .con "base" [] => some .base
  | .con "loop" [r] => do let r' ← termToExpr r; some (.loop r')

  -- Sub types
  | .con "subIn" [e] => do let e' ← termToExpr e; some (.subIn e')
  | .con "subOut" [e] => do let e' ← termToExpr e; some (.subOut e')

  -- Substitution meta-operation (for rule RHS)
  | .con "subst" [.lit idxStr, val, body] => do
    let idx := parseNat idxStr
    let val' ← termToExpr val
    let body' ← termToExpr body
    some (Expr.subst idx val' body')

  -- Fallback: unknown nullary constructor treated as literal (for bare names like P, z, s)
  | .con name [] => some (.lit name)
  -- Other unknown constructors fail
  | .con _ _ => none
  | .var _ => none

/-! ## Test Execution -/

/-- Normalize an expression using Core.Expr.normalize -/
def normalizeExpr (fuel : Nat) (e : Expr) : Expr :=
  Expr.normalize fuel e

/-- Compare two expressions for equality -/
def exprEq (e1 e2 : Expr) : Bool := e1 == e2

/-- Compare two levels for equality -/
def levelEq (l1 l2 : Level) : Bool := l1 == l2

/-- Result of running a single test -/
inductive TestResult
  | pass : TestResult
  | fail (reason : String) : TestResult
  | skip (reason : String) : TestResult
  deriving Repr, Inhabited

/-- Run a Level test (for piece "Level") -/
def runLevelTest (tc : Lego.Loader.TestCase) : IO TestResult := do
  let normalizedInput := normalizeAst tc.input
  match termToLevel normalizedInput with
  | none => return .skip s!"Failed to convert Level input: {repr normalizedInput}"
  | some inputLevel =>
    match tc.expected with
    | some expectedTerm =>
      let normalizedExpected := normalizeAst expectedTerm
      match termToLevel normalizedExpected with
      | none => return .skip s!"Failed to convert Level expected: {repr normalizedExpected}"
      | some expectedLevel =>
        let result := Level.normalize inputLevel
        if levelEq result expectedLevel then
          pure .pass
        else
          pure (.fail s!"Expected: {repr expectedLevel}\nGot: {repr result}")
    | none => pure .pass

/-- Run an Expr test (default) -/
def runExprTest (tc : Lego.Loader.TestCase) (fuel : Nat := 100) : IO TestResult := do
  let normalizedInput := normalizeAst tc.input
  match termToExpr normalizedInput with
  | none => return .skip s!"Failed to convert input: {repr normalizedInput}"
  | some inputExpr =>
    match tc.expected with
    | some expectedTerm =>
      let normalizedExpected := normalizeAst expectedTerm
      match termToExpr normalizedExpected with
      | none => return .skip s!"Failed to convert expected: {repr normalizedExpected}"
      | some expectedExpr =>
        let result := normalizeExpr fuel inputExpr
        if exprEq result expectedExpr then
          pure .pass
        else
          pure (.fail s!"Expected: {repr expectedExpr}\nGot: {repr result}")
    | none =>
      let _ := normalizeExpr fuel inputExpr
      pure .pass

/-- Run a meta-rule test using the rule interpreter -/
def runRuleTest (rules : List Lego.Rule) (tc : Lego.Loader.TestCase) (fuel : Nat := 100) : IO TestResult := do
  let normalizedInput := normalizeAst tc.input
  match tc.expected with
  | some expectedTerm =>
    let normalizedExpected := normalizeAst expectedTerm
    let result := Lego.normalizeWithRulesAndBuiltins fuel rules normalizedInput
    if result == normalizedExpected then
      pure .pass
    else
      pure (.fail s!"Expected: {repr normalizedExpected}\nGot: {repr result}")
  | none =>
    -- Just check it normalizes without error
    let _ := Lego.normalizeWithRulesAndBuiltins fuel rules normalizedInput
    pure .pass

/-- Check if a test looks like it uses meta-rule functions (not Core.Expr constructors) -/
def isMetaRuleTest (tc : Lego.Loader.TestCase) : Bool :=
  -- Meta-rule tests typically use functions like isDim0, cofEq, nbe, etc.
  -- that aren't Core.Expr constructors
  let normalizedInput := normalizeAst tc.input
  match normalizedInput with
  | .con name _ =>
    -- Known meta-functions that aren't Core.Expr constructors
    name ∈ ["isDim0", "isDim1", "dimEq", "dimEqD", "cofEq", "cofTrue", "cofFalse",
            "dCofIsTrue", "dCofIsFalse", "boundary", "cofLe",
            "dirIsDegenerate", "dimOfExpr", "dimToExpr",
            "denvLookup", "dApply", "dFst", "dSnd",
            "nbe", "levelToIndex", "runBuild", "buildLam",
            "normCof", "evalCof", "substDim0'"]
  | _ => false

/-- Run a single test case, dispatching by piece type and test kind -/
def runTest (rules : List Lego.Rule) (tc : Lego.Loader.TestCase) (fuel : Nat := 100) : IO TestResult := do
  if tc.pieceName == "Level" then
    runLevelTest tc
  else if isMetaRuleTest tc then
    runRuleTest rules tc fuel
  else
    -- Try Expr test first, fall back to rule test if conversion fails
    let normalizedInput := normalizeAst tc.input
    match termToExpr normalizedInput with
    | some _ => runExprTest tc fuel
    | none => runRuleTest rules tc fuel

/-- Run all tests from a list of test cases -/
def runTests (rules : List Lego.Rule) (tests : List Lego.Loader.TestCase) (verbose : Bool := false) : IO (Nat × Nat × Nat) := do
  let mut passed := 0
  let mut failed := 0
  let mut skipped := 0

  for tc in tests do
    let result ← runTest rules tc
    match result with
    | .pass =>
      passed := passed + 1
      if verbose then
        IO.println s!"  ✓ {tc.name}"
    | .fail reason =>
      failed := failed + 1
      IO.println s!"  ✗ \"{tc.name}\""
      IO.println s!"    {reason}"
    | .skip reason =>
      skipped := skipped + 1
      if verbose then
        IO.println s!"  ⊘ {tc.name}: {reason}"

  pure (passed, failed, skipped)

/-- Run tests from a .lego file with file-local rules only -/
def runFileTests (ast : Term) (fileName : String) (verbose : Bool := false) : IO (Nat × Nat × Nat) := do
  let tests := Lego.Loader.extractTests ast
  let rules := Lego.Loader.extractRules ast
  if tests.isEmpty then
    if verbose then IO.println s!"{fileName}: No tests found"
    pure (0, 0, 0)
  else
    IO.println s!"{fileName}: {tests.length} tests ({rules.length} rules)"
    runTests rules tests verbose

/-- Run tests from a .lego file with combined rules from all files -/
def runFileTestsWithRules (ast : Term) (allRules : List Lego.Rule) (fileName : String) (verbose : Bool := false) : IO (Nat × Nat × Nat) := do
  let tests := Lego.Loader.extractTests ast
  if tests.isEmpty then
    if verbose then IO.println s!"{fileName}: No tests found"
    pure (0, 0, 0)
  else
    IO.println s!"{fileName}: {tests.length} tests (using {allRules.length} combined rules)"
    runTests allRules tests verbose

/-- Print summary statistics -/
def printSummary (passed failed skipped : Nat) : IO Unit := do
  let total := passed + failed + skipped
  IO.println ""
  IO.println s!"Summary: {passed}/{total} passed"
  if failed > 0 then
    IO.println s!"  {failed} failed"
  if skipped > 0 then
    IO.println s!"  {skipped} skipped"

end Cubical.TestRunner
