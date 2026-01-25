# Cubical Examples Codebase Analysis

## Overview

The `examples/Cubical/` directory contains a comprehensive implementation of Cubical Type Theory (CTT) in Lean 4, along with grammar specifications for parsing .red (redtt) and .cooltt files.

## Directory Structure

```
examples/Cubical/
├── *.lean           # Hand-coded Lean implementation (24 files)
├── Lego/            # .lego grammar/rule specs (24 files)  
├── test/            # Parser tests for .red/.cooltt files
├── tools/           # Code generation pipeline
└── doc/             # Documentation and experimental .lego files
```

## Current Assets

### 1. Hand-Coded Lean Implementation (examples/Cubical/*.lean)

| Module | Purpose | LOC |
|--------|---------|-----|
| Core.lean | De Bruijn indexed terms + substitution | ~1900 |
| Semantics.lean | NbE evaluation with Kan ops | ~360 |
| Domain.lean | Semantic domain for NbE | ~416 |
| Cofibration.lean | Face lattice operations | ~200 |
| Kan.lean | Coe/HCom computations | ~300 |
| GlobalEnv.lean | Global definitions/datatypes | ~619 |
| Elaborate.lean | Bidirectional type checking | ~500 |
| Unify.lean | Unification | ~350 |
| Quote.lean | Quotation (semantics→syntax) | ~250 |
| Module.lean | Module system | ~350 |
| ... | (14 more modules) | |

**Total: ~7000+ LOC hand-coded Lean**

### 2. Lego Specifications (examples/Cubical/Lego/*.lego)

Each .lego file mirrors a .lean file with:
- Grammar productions for AST
- Rewrite rules for evaluation
- Test cases

Example from Core.lego:
```
piece Expr
  term ::= "ix" <number> → ix
         | "lam" term → lam
         | "app" term term → app
         | ...
  
  rule beta: (app (lam $body) $arg) ~> (subst 0 $arg $body) ;
  test "beta": (app (lam (ix 0)) (lit "x")) ~~> (lit "x") ;
```

### 3. Test Grammars (examples/Cubical/test/*.lego)

| File | Purpose | Status |
|------|---------|--------|
| Redtt.lego | Parser grammar for .red files | ✓ Parses ~800 tests |
| Cooltt.lego | Parser grammar for .cooltt files | ✓ Working |
| RedttAST.lego | AST definitions | ✓ |
| RedttElab.lego | Elaboration rules | ✓ |
| RedttTyped.lego | Type system | ✓ |

### 4. Code Generation Tools (examples/Cubical/tools/)

```
tools/Cubical/
├── Cubical.lean       # Main multi-target generation
├── SExpr.lean         # S-expression parser
├── ToRedTT.lean       # Generate .red code
├── ToCoolTT.lean      # Generate .cooltt code
├── ToLean.lean        # Generate .lean code
└── GeneratedPipeline.lean  # .lego → .lean conversion
```

## What Can Be Generated

### A. From .lego → .lean (already working)

The `generated/CubicalGen/` directory shows .lego → .lean generation works:
- Rewrite rules become Lean pattern-matching functions
- Grammar productions become inductive types
- Tests become assertions

### B. Potential Generation Targets

| Source | Target | Difficulty | Value |
|--------|--------|------------|-------|
| Lego/*.lego | Core.lean etc | Medium | Unify specs & impl |
| .lego rules | .red proofs | Hard | Verified rules |
| .lego rules | .cooltt proofs | Hard | Verified rules |
| Core.lean | .red tests | Medium | Test generation |

## Evaluation Architecture

### Current: Hand-Coded Evaluation

```
test/lean/TestRed.lean uses:
  Cubical/Core.lean    - Expr.step, Expr.normalize
  Cubical/Semantics.lean - eval, whnf
  Cubical/Kan.lean     - doRigidCoe, doRigidHCom
```

Test execution:
```bash
lake exe lego-test-red           # 823 tests
scripts/run-cooltt-tests.sh      # CoolTT parsing tests
```

### Interpretation Pipeline

```
.red file
    │
    ▼ (Redtt.lego grammar)
Lego.Term (parsed AST)
    │
    ▼ (rules from RedttElab.lego)  
Core.Expr (de Bruijn terms)
    │
    ▼ (Semantics.eval / Core.normalize)
Core.Expr (normalized)
```

### Key Evaluation Functions

1. **Core.Expr.step** - Single-step reduction:
   - β-reduction: `(app (lam body) arg) ~> subst 0 arg body`
   - Path app: `(papp (plam body) dim) ~> substDim 0 dim body`
   - Projections: `(fst (pair a b)) ~> a`
   - Kan degenerate: `(coe r r A a) ~> a`

2. **Core.Expr.normalize** - Multi-step with fuel

3. **Semantics.eval** - NbE with context:
   - Variable lookup
   - Rigid Kan operations (coe/hcom through type formers)

## Gaps and Opportunities

### 1. Missing: Unified .lego → .lean Pipeline

The Rosetta pipeline exists for `src/Lego/*.rosetta` → `src/Lego/*.lean`.
We need the same for `Cubical/Lego/*.lego` → `Cubical/*.lean`.

**Proposed approach:**
```
Cubical/Lego/Core.lego
    │
    ▼ (tools/ToLean.lean enhanced)
Cubical/Core.generated.lean
    │
    ▼ (diff with)
Cubical/Core.lean (hand-coded)
```

### 2. Missing: Test Execution from .lego Tests

The .lego files contain `test` declarations:
```
test "beta": (app (lam (ix 0)) (lit "x")) ~~> (lit "x") ;
```

But no runtime executes them. Need:
- Extract tests from parsed .lego
- Run through interpreter
- Compare results

### 3. Missing: End-to-End .red Evaluation

Currently we can:
✓ Parse .red files (Redtt.lego grammar)
✓ Evaluate Core.Expr (Semantics.eval)

Missing:
✗ Transform parsed .red AST → Core.Expr
✗ Execute .red definitions
✗ Run .red tests

## Recommended Actions

### Phase 1: Enable .lego Test Execution

1. Add test extraction to Lego.Loader
2. Add test runner to lego-test-red
3. Verify Cubical/Lego/*.lego tests pass

### Phase 2: Generate Lean from Lego Specs

1. Enhance GeneratedPipeline.lean to handle full module
2. Generate Cubical/Core.generated.lean
3. Compare with hand-coded, minimize diff

### Phase 3: .red Evaluation Pipeline

1. Implement AST → Core.Expr transform (Surface → IR)
2. Add definition evaluation
3. Support `def` and `data` execution

### Phase 4: Bidirectional Verification

1. Extract type rules from Cubical/Lego/*.lego
2. Generate type checking code
3. Verify against existing Elaborate.lean

## File Mappings

| Hand-Coded | Lego Spec | Status |
|------------|-----------|--------|
| Core.lean | Lego/Core.lego | Both exist, need sync |
| Cofibration.lean | Lego/Cofibration.lego | Both exist |
| Kan.lean | Lego/Kan.lego | Both exist |
| Semantics.lean | Lego/Semantics.lego | Both exist |
| Domain.lean | Lego/Domain.lego | Both exist |
| ... | ... | |

## Test Commands

```bash
# Parse all .lego files (including Cubical)
lake exe lego-test-parse examples/Cubical/Lego/*.lego

# Run Core IR tests
lake exe lego-test-red

# Run redtt library parsing (needs redtt checkout)
lake exe lego-test-red --parse-redtt ~/redtt/library

# Run cooltt parsing  
lake exe lego-test-red --cooltt
```

## Conclusion

The Cubical codebase has:
- ✅ Solid hand-coded implementation
- ✅ Grammar specs for parsing Red/Cool
- ✅ Lego specifications paralleling the implementation
- ⚠️ No unified generation pipeline
- ⚠️ No .lego test execution
- ⚠️ No end-to-end .red evaluation

The key opportunity is to unify the .lego specs with the .lean implementation through code generation, enabling:
1. Single source of truth
2. Verified evaluation rules
3. Test generation
4. Multi-target output (Lean execution + Red/Cool proofs)
