# Cubical Directory Structure

This directory implements Cubical Type Theory in three layers.

## Architectural Layers

```
┌─────────────────────────────────────────────────────────────┐
│  LAYER 1: Semantic Reference (what things MEAN)             │
│  doc/CubicalTT.lego - binding structure, typing rules       │
│  doc/Core4.lego - minimal 4-primitive derivation            │
└─────────────────────────────────────────────────────────────┘
                              ↓
┌─────────────────────────────────────────────────────────────┐
│  LAYER 2: De Bruijn IR (how things are REPRESENTED)         │
│  Lego/Core.lego - de Bruijn indexed terms + reduction       │
│  Lego/Cofibration.lego - cofibration algebra                │
│  Lego/Kan.lego - Kan operation implementations              │
│  *.lean - hand-coded Lean implementation                    │
└─────────────────────────────────────────────────────────────┘
                              ↓
┌─────────────────────────────────────────────────────────────┐
│  LAYER 3: Surface Syntax (what users WRITE)                 │
│  syntax/Redtt.lego - parse .red files                       │
│  syntax/Cooltt.lego - parse .cooltt files                   │
└─────────────────────────────────────────────────────────────┘
```

## Directory Contents

### Lego/ - Canonical Code Generation Specs
These .lego files are the authoritative specifications for generating the hand-coded .lean files.

| File | Purpose | Tests |
|------|---------|-------|
| Core.lego | De Bruijn terms, β-reduction | 15 ✓ |
| Cofibration.lego | Cofibration algebra | 15 (6 core) |
| Kan.lego | coe, hcom, com operations | 7 |
| Domain.lego | Semantic domain for NbE | 7 |
| Quote.lego | Quotation (semantics→syntax) | 4 |
| ... (24 files total) | | |

### syntax/ - Surface Language Parsers
Parse external file formats (.red, .cooltt) into AST.

| File | Purpose |
|------|---------|
| Redtt.lego | Parse redtt .red files |
| Cooltt.lego | Parse cooltt .cooltt files |
| CubicalFeatures.lego | Feature coverage tests |
| RedttAST.lego | AST definitions |
| RedttElab.lego | Elaboration rules |
| RedttTyped.lego | Type system |

### doc/ - Documentation & Tutorials
Reference material and experimental designs.

| File | Purpose |
|------|---------|
| CubicalTT.lego | Shared semantic foundation |
| Core4.lego | Minimalist "4 primitives" approach |
| TypeTheoryCore.lego | Math foundations |
| TypeTheoryFromMath.lego | Math→syntax mapping |
| RosettaMath.lego | Mathematical notation reference |
| Red.lego | redtt-specific extensions |
| Cool.lego | cooltt-specific extensions |

### tools/ - Code Generation
| File | Purpose |
|------|---------|
| Cubical.lean | Multi-target generation driver |
| cubical2rosetta.lego | CubicalTT → Rosetta transform |

### *.lean - Hand-Coded Implementation
24 Lean 4 files (~12K LOC) implementing cubical type theory.
Goal: Generate these from Lego/*.lego specs.

## Test Execution

```bash
# Run embedded .lego tests (49 tests, 41 passing)
lake exe lego-test-embedded

# Run full Cubical test suite  
lake exe lego-test-red

# Parse redtt library
lake exe lego-test-red --parse-redtt ~/redtt/library
```

## Test Status

The embedded test runner executes tests defined in `.lego` files:

| File | Tests | Status | Notes |
|------|-------|--------|-------|
| Core.lego | 15 | ✓ All passing | Basic term operations |
| Cofibration.lego | 15 | ✓ All passing | Cofibration primitives |
| Kan.lego | 7 | 5/7 | 2 need cross-file rules (dimEqD from Domain) |
| Domain.lego | 7 | 5/7 | 2 need complex guards (env-lookup) |
| Quote.lego | 4 | 1/4 | 3 need NbE evaluation chain |
| TermBuilder.lego | 1 | 0/1 | Needs HOAS handling |

### Known Limitations
- Cross-file rule dependencies not yet resolved (rules from imports)
- Complex NbE chains need more evaluation fuel
- HOAS patterns (`fun x => e`) not fully handled

## Code Generation Goals

1. **Lego/*.lego → *.lean**: Generate hand-coded Lean from specs
2. **syntax/*.lego → parsers**: Generate surface language parsers
3. **Unified evaluation**: Use .lego rules for both testing and execution

## Key Invariants

1. `Lego/Core.lego` is the canonical de Bruijn IR spec
2. Hand-coded `*.lean` should converge with generated code
3. Tests in .lego files run against Core.Expr.normalize
4. Surface parsers (syntax/) are separate from IR (Lego/)
