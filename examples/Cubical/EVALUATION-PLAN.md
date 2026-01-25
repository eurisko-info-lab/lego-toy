# Cubical Evaluation Plan

## Goal: Execute .lego Tests and Evaluate Cubical Code

### Immediate Priority: Enable .lego Test Execution

The Cubical/Lego/*.lego files already contain test declarations:
```lego
test "beta": (app (lam (ix 0)) (lit "x")) ~~> (lit "x") ;
test "coe-refl": (coe dim0 dim0 (univ lzero) (lit "A")) ~~> (lit "A") ;
```

These tests are parsed but never executed.

## Implementation Plan

### Step 1: Test Extraction (30 min)

Add to `Lego/Loader.lean`:

```lean
/-- Extract test declarations from a parsed .lego file -/
def extractTests (ast : Term) : List (String × Term × Term) :=
  extractTestsRec ast
where
  extractTestsRec : Term → List (String × Term × Term)
  | .con "DTest" [_, .con "string" [.lit name], _, input, _, expected, _] =>
    [(name, input, expected)]
  | .con "DTestsBlock" items =>
    items.flatMap extractTestsRec
  | .con "testCase" [.con "string" [.lit name], _, expected] =>
    -- For inline tests without input
    [(name, .lit "", expected)]
  | .con _ args => args.flatMap extractTestsRec
  | _ => []
```

### Step 2: Test Execution (1 hour)

Create `Cubical/TestRunner.lean`:

```lean
import Cubical.Core
import Lego.Interp

/-- Convert Lego.Term to Cubical.Core.Expr -/
def termToExpr : Lego.Term → Option Core.Expr
  | .con "ix" [.lit n] => some (.ix n.toNat!)
  | .con "lam" [body] => do let b ← termToExpr body; some (.lam b)
  | .con "app" [f, a] => do 
    let f' ← termToExpr f
    let a' ← termToExpr a
    some (.app f' a')
  | .con "dim0" [] => some .dim0
  | .con "dim1" [] => some .dim1
  | .con "coe" [r, s, A, a] => do
    let r' ← termToExpr r; let s' ← termToExpr s
    let A' ← termToExpr A; let a' ← termToExpr a
    some (.coe r' s' A' a')
  | .lit s => some (.lit s)
  | _ => none

/-- Run a single test -/
def runTest (name : String) (input expected : Lego.Term) : IO Bool := do
  match termToExpr input, termToExpr expected with
  | some inp, some exp =>
    let result := Core.Expr.normalize 100 inp
    let pass := result == exp
    if !pass then
      IO.println s!"  ✗ {name}: expected {exp}, got {result}"
    pure pass
  | _, _ =>
    IO.println s!"  ✗ {name}: failed to convert terms"
    pure false

/-- Run all tests from a .lego file -/
def runFileTests (path : String) : IO (Nat × Nat) := do
  let ast ← Lego.Loader.loadLego path
  let tests := extractTests ast
  let mut passed := 0
  let mut total := 0
  for (name, input, expected) in tests do
    total := total + 1
    if ← runTest name input expected then
      passed := passed + 1
  pure (passed, total)
```

### Step 3: Integration with lego-test-red (30 min)

Add to `test/lean/TestRed.lean`:

```lean
/-- Run .lego embedded tests -/
def runLegoEmbeddedTests : IO (Nat × Nat) := do
  let files := [
    "examples/Cubical/Lego/Core.lego",
    "examples/Cubical/Lego/Cofibration.lego",
    "examples/Cubical/Lego/Kan.lego",
    -- ... etc
  ]
  let mut totalPassed := 0
  let mut totalTests := 0
  for file in files do
    let (p, t) ← Cubical.TestRunner.runFileTests file
    IO.println s!"{file}: {p}/{t}"
    totalPassed := totalPassed + p
    totalTests := totalTests + t
  pure (totalPassed, totalTests)
```

### Step 4: Rules-Based Evaluation (2 hours)

The real power comes from using the .lego rules for evaluation:

```lean
/-- Apply rules from a .lego file to a term -/
def applyRules (rules : List (String × Term × Term)) (t : Core.Expr) : Core.Expr :=
  rules.foldl (fun acc (_, pattern, template) =>
    match matchPattern pattern acc with
    | some binds => instantiate template binds
    | none => acc) t
```

This allows evaluation defined by .lego rules rather than hard-coded Lean.

## Architecture

```
┌─────────────────────────────────────────────────────────┐
│                   .lego file                            │
│  piece Core                                             │
│    term ::= "app" term term → app | ...                │
│    rule beta: (app (lam $b) $a) ~> (subst 0 $a $b) ;   │
│    test "t1": (app (lam (ix 0)) (lit "x")) ~~> ...     │
└─────────────────────────────────────────────────────────┘
          │
          ▼ (Lego.Loader.loadLego)
┌─────────────────────────────────────────────────────────┐
│  Lego.Term (parsed AST)                                 │
│    .con "DPiece" [...]                                 │
└─────────────────────────────────────────────────────────┘
          │
    ┌─────┴─────┐
    ▼           ▼
extractRules  extractTests
    │           │
    ▼           ▼
┌─────────┐  ┌─────────────────────────────────────────┐
│ Rules   │  │ Tests: (name, input, expected)         │
│ β, fst..│  │ ("beta", (app (lam ...) ...), ...)    │
└─────────┘  └─────────────────────────────────────────┘
    │           │
    │           ▼ (termToExpr)
    │        ┌─────────────────────────────────────────┐
    │        │ Core.Expr test cases                   │
    │        └─────────────────────────────────────────┘
    │           │
    └─────┬─────┘
          ▼
┌─────────────────────────────────────────────────────────┐
│  TestRunner.runTest                                     │
│    - Apply rules to normalize                           │
│    - Compare with expected                              │
│    - Report pass/fail                                   │
└─────────────────────────────────────────────────────────┘
```

## End-to-End .red Evaluation (Future)

Once the above works, extend to .red files:

1. **Parse .red**: Already works via Redtt.lego grammar
2. **Lower to Core**: Transform surface AST → de Bruijn Core.Expr
3. **Evaluate**: Use rules from RedttElab.lego + Core.lego
4. **Run tests**: Execute `test` declarations in .red files

## Files to Create/Modify

| File | Action |
|------|--------|
| `src/Lego/Loader.lean` | Add `extractTests` |
| `examples/Cubical/TestRunner.lean` | New: test runner |
| `examples/Cubical/Interp.lean` | New: Term → Expr conversion |
| `test/lean/TestRed.lean` | Add embedded test runner |
| `lakefile.lean` | Add Cubical modules to test target |

## Validation

After implementation:

```bash
# Run existing tests (should still pass)
lake exe lego-test-red

# Run embedded .lego tests  
lake exe lego-test-red --lego-tests

# Expected output:
# examples/Cubical/Lego/Core.lego: 6/6 ✓
# examples/Cubical/Lego/Cofibration.lego: 3/3 ✓
# examples/Cubical/Lego/Kan.lego: 2/2 ✓
# ...
```

## Success Criteria

1. All tests embedded in Cubical/Lego/*.lego files pass
2. Test execution uses rules defined in .lego (not just hard-coded)
3. Can add new rules in .lego and see them take effect
4. Foundation for .red evaluation pipeline
