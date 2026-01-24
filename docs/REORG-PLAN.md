# Project Reorganization Plan

## Current State Analysis

### Directory Structure Issues

| Current | Problem | Proposed |
|---------|---------|----------|
| `doc/` + `docs/` | Duplicate directories | Merge to `docs/` |
| `src/Rosetta/REDESIGN.md` | Doc in source | Move to `docs/` (duplicate exists) |
| `examples/Cubical/*.md` | Docs mixed with code | Move to `docs/cubical/` |
| `test/RED-TODO.md` | Doc in test dir | Move to `docs/` |
| Root `*.lean` files | Cluttered root | Move to appropriate dirs |
| `Rosetta/` at root | Unclear purpose vs `src/Rosetta/` | Rename to `pipelines/` |
| `Cubical/` at root | Single file, unclear | Move to `tools/` |
| `tmp/` | Build artifacts | Add to `.gitignore` |

### Root Level Cleanup

Files at root that should move:

| File | Destination | Reason |
|------|-------------|--------|
| `LegoGen.lean` | `tools/LegoGen.lean` | Code generator tool |
| `RosettaMain.lean` | `src/Rosetta/Main.lean` | Entry point for Rosetta |
| `Main.lean` | Keep | Main entry point |
| `run-cooltt-tests.sh` | `scripts/` | Script |
| `libGenerated.rlib` | `.gitignore` | Build artifact |

### Proposed Structure

```
lego-toy/
├── README.md
├── lakefile.lean
├── lean-toolchain
├── lake-manifest.json
├── Main.lean                    # Main entry point
│
├── src/                         # Core library
│   ├── Lego.lean               # Re-exports
│   └── Lego/
│       ├── Algebra.lean        # Core types
│       ├── Attr.lean           # Attributes  
│       ├── AttrEval.lean       # Evaluation
│       ├── Bootstrap.lean      # Bootstrap (uses generated/)
│       ├── Interp.lean         # Interpreter
│       ├── Loader.lean         # File loading
│       ├── Runtime.lean        # Runtime support
│       └── Validation.lean     # Validation
│
├── src/Rosetta/                 # Rosetta IR
│   ├── Rosetta.lean            # Core Rosetta types
│   ├── CodeGen.lean            # Frag AST
│   ├── UnifiedCodeGen.lean     # Unified emitters
│   └── *.lego                  # Rosetta specs
│
├── src/Runtime/                 # Target language runtimes
│   ├── Lean/
│   ├── Scala/
│   ├── Haskell/
│   └── Rust/
│
├── generated/                   # Bootstrap (CHECKED IN)
│   ├── BootstrapGrammar.lean
│   ├── BootstrapTokenizer.lean
│   ├── BootstrapRules.lean
│   └── MinimalBootstrapTokenizer.lean
│
├── pipelines/                   # Code generation pipelines (was Rosetta/)
│   ├── Pipeline.lean           # Main pipeline
│   ├── RosettaPipeline.lean
│   ├── MultiTargetPipeline.lean
│   ├── GrammarDrivenPipeline.lean
│   └── GenericPrettyPrinter.lean
│
├── tools/                       # CLI tools
│   ├── ToLean.lean             # Generate Lean
│   ├── ToAntlr.lean            # Generate ANTLR
│   ├── ToTreeSitter.lean       # Generate Tree-sitter
│   ├── LegoGen.lean            # RedTT/CoolTT generator
│   ├── GeneratedPipeline.lean
│   └── Cubical/                # Cubical-specific tools
│
├── test/                        # Tests
│   ├── lean/                   # Lean test files
│   │   ├── Test.lean
│   │   ├── TestRed.lean
│   │   └── ...
│   └── lego/                   # Lego test specs
│       ├── Bootstrap.lego
│       ├── Redtt.lego
│       └── ...
│
├── examples/                    # Example languages/domains
│   ├── Arith.lego
│   ├── Lambda.lego
│   ├── K.lego
│   ├── INet.lego
│   ├── AI/
│   ├── Cubical/
│   └── Quantum/
│
├── docs/                        # Documentation
│   ├── README.md               # Overview
│   ├── ARCHITECTURE.md         # System architecture
│   ├── BOOTSTRAP.md            # Bootstrap process
│   ├── GENTIME-RUNTIME.md      # GenTime/Runtime design
│   ├── LEGO-ANALYSIS.md        # Language analysis
│   ├── REDTT.md                # RedTT documentation
│   └── cubical/                # Cubical docs (from examples/)
│
└── scripts/                     # Build/CI scripts
    ├── bootstrap.sh
    └── run-cooltt-tests.sh
```

---

## TODO/Incomplete Code Inventory

### Critical (Blocks Functionality)

| File | Line | Issue |
|------|------|-------|
| `Cubical/GeneratedPipeline.lean` | 235 | `sorry -- TODO: implement` |
| `tools/GeneratedPipeline.lean` | 228 | `sorry` fallback for unhandled rules |

### High Priority (Simplified/Stub)

| File | Line | Issue |
|------|------|-------|
| `Rosetta/GenericPrettyPrinter.lean` | 115 | `-- TODO: Parse grammar rules` |
| `Rosetta/GrammarDrivenPipeline.lean` | 1494 | `-- TODO: For multi-file output` |
| `tools/Cubical/ToRedTT.lean` | 147 | Stub proof body |
| `examples/Cubical/Module.lean` | 265 | `stub - actual file loading would be in IO` |
| `examples/Quantum/C12.lego` | 62, 96 | Placeholder composition/evaluation |
| `examples/Quantum/Quantum.lego` | 132 | Soundness/completeness placeholders |

### Medium Priority (Simplified Implementations)

| File | Line | Issue |
|------|------|-------|
| `examples/Cubical/Cofibration.lean` | 193 | `Simplified: just check structural inclusion` |
| `examples/Cubical/VType.lean` | 158, 204 | Simplified coercion/representation |
| `examples/Cubical/Domain.lean` | 317 | `Placeholder` literal |
| `test/LeanParseAllTest.lean` | 20-21, 68 | `simplified` do/by parsing |
| `test/CubicalFeatures.lego` | 153, 160 | `simplified` types/terms |

### Deprecated Code to Remove

| File | Line | Issue |
|------|------|-------|
| `src/Lego/Interp.lean` | 72 | `DEPRECATED - use findSubstrFromBytes` |
| `src/Lego/Bootstrap.lean` | 102, 108 | `DEPRECATED` parse functions |
| `src/Rosetta/Rosetta.lean` | 92 | `legacy` extractCtorName |
| `Rosetta/GrammarDrivenPipeline.lean` | 850 | Duplicated term-to-pattern functions marked DEPRECATED |
| `Rosetta/MultiTargetPipeline.lean` | 52, 67, 676 | `legacy mode` combined output |

---

## 5-Way Interchangeability Architecture

**Goal**: The same `.rosetta` spec compiles to 5 equivalent implementations:
1. **Hand-coded Lean** (`src/Lego/*.lean`) - reference implementation
2. **Generated Lean** (`lake exe multi-target *.rosetta -t lean`)
3. **Generated Scala** (`lake exe multi-target *.rosetta -t scala`)
4. **Generated Haskell** (`lake exe multi-target *.rosetta -t haskell`)
5. **Generated Rust** (`lake exe multi-target *.rosetta -t rust`)

### Architecture Layers

```
┌─────────────────────────────────────────────────────────────────┐
│                    .rosetta Specifications                       │
│  (ADTs + Rewrite Rules = Declarative Semantics)                 │
└─────────────────────────────────────────────────────────────────┘
                              │
                              ▼
┌─────────────────────────────────────────────────────────────────┐
│                  GenTime Code Generators                         │
│  GrammarDrivenPipeline.lean → termToPatternFrag, emitRewriteRule│
└─────────────────────────────────────────────────────────────────┘
                              │
              ┌───────────────┼───────────────┬──────────────┐
              ▼               ▼               ▼              ▼
        ┌─────────┐     ┌─────────┐     ┌─────────┐    ┌─────────┐
        │  Lean   │     │  Scala  │     │ Haskell │    │  Rust   │
        │ Runtime │     │ Runtime │     │ Runtime │    │ Runtime │
        └─────────┘     └─────────┘     └─────────┘    └─────────┘
              │               │               │              │
              ▼               ▼               ▼              ▼
        ┌─────────────────────────────────────────────────────────┐
        │        Generated ADTs + Generated Rewrite Functions      │
        │        (import Runtime; generated code uses Runtime)     │
        └─────────────────────────────────────────────────────────┘
```

### Current Coverage Analysis

| Module | Hand-coded Lean | .rosetta Spec | Coverage | Gap |
|--------|----------------|---------------|----------|-----|
| `Algebra` | 427 lines | 259 lines | 61% | Core types OK, BiReducer partial |
| `Attr` | 298 lines | 284 lines | 95% | Good |
| `AttrEval` | 615 lines | 408 lines | 66% | Missing: error handling, complex eval |
| `Interp` | 881 lines | 206 lines | **23%** | Missing: lexer, packrat, IO |
| `Loader` | 1203 lines | 242 lines | **20%** | Missing: file IO, caching |
| `Runtime` | 312 lines | 312 lines | 100% | ✅ Complete |
| `Validation` | 363 lines | 395 lines | 109% | ✅ Complete (rosetta has more) |
| `Bootstrap` | 122 lines | N/A | N/A | Uses generated/ |

### Runtime Libraries Status ✅ AUDITED

All 4 Runtime libraries provide equivalent functionality:

| Feature | Lean | Scala | Haskell | Rust |
|---------|------|-------|---------|------|
| `Term` | ✅ | ✅ | ✅ | ✅ |
| `GrammarExpr` | ✅ | ✅ | ✅ | ✅ |
| `Production` | ✅ | ✅ | ✅ | ✅ |
| `Rule` | ✅ | ✅ | ✅ | ✅ |
| `Token` | ✅ | ✅ | ✅ | ✅ |
| `ParseState` | ✅ | ✅ | ✅ | ✅ |
| `parseGrammar` | ✅ | ✅ | ✅ | ✅ `parse_grammar` |
| `matchPattern` | ✅ | ✅ | ✅ | ✅ `match_pattern` |
| `substitute` | ✅ | ✅ | ✅ | ✅ |
| `applyRule` | ✅ | ✅ | ✅ | ✅ `apply_rule` |
| `normalize` | ✅ | ✅ | ✅ | ✅ |
| `readFile` | ✅ | ✅ | ✅ | ✅ `read_file` |
| `writeFile` | ✅ | ✅ | ✅ | ✅ `write_file` |
| `fileExists` | ✅ | ✅ | ✅ `doesFileExist` | ✅ `file_exists` |
| `combineSeq` | ✅ | ✅ | ✅ | ✅ `combine_seq` |
| `wrapNode` | ✅ | ✅ | ✅ | ✅ `wrap_node` |
| `findProduction` | ✅ | ✅ | ✅ | ✅ `find_production` |
| `findAllProductions` | ✅ | ✅ | ✅ | ✅ `find_all_productions` |

**Note**: Rust uses snake_case per language conventions. The code generator handles naming automatically.

| Language | File | Lines |
|----------|------|-------|
| Lean | `src/Runtime/Lean/Runtime.lean` | 306 |
| Scala | `src/Runtime/Scala/Runtime.scala` | 320 |
| Haskell | `src/Runtime/Haskell/Runtime.hs` | 349 |
| Rust | `src/Runtime/Rust/runtime.rs` | 571 |

### What's Missing for True Interchangeability

#### 1. **Interp.rosetta** needs expansion (23% coverage)
Current `.rosetta` has: ADTs (Token, ParseState, ParseResult) + rewrite rules
Missing from `.rosetta`:
- `lexGrammar` - character-level parsing
- `parseGrammar` - token-level parsing with packrat
- `tokenizeWithGrammar` - IO-aware tokenization
- `computeLineCol` - source location tracking
- `printGrammar` - unparsing

**Resolution**: These algorithms are now in the **Runtime libraries** (all 4 languages).
Generated code imports Runtime and calls these functions. No need to expand Rosetta specs.

#### 2. **Loader.rosetta** needs expansion (20% coverage)
Missing:
- File I/O (`readFile`, `writeFile`)
- Module caching
- Import resolution
- Pretty printing

**Resolution**: IO operations are in **Runtime libraries** (`readFile`, `writeFile`, `fileExists`).
Module caching and import resolution can remain target-specific or be added to Runtime.

#### 3. **Bootstrap interchangeability**
Currently `src/Lego/Bootstrap.lean` imports from `generated/`.
For full interchangeability:
- Bootstrap.rosetta → generates Bootstrap.lean/scala/hs/rs
- Runtime imports remain target-specific
- Generated code must work with any Runtime

### Action Plan for 5-Way Interchangeability

#### Phase A: Complete Runtime Libraries ✅ DONE
1. [x] Lean Runtime - Complete (306 lines, 18 functions)
2. [x] Scala Runtime - Complete (320 lines, 18 functions)
3. [x] Haskell Runtime - Complete (349 lines, 18 functions)
4. [x] Rust Runtime - Complete (571 lines, 18 functions)

#### Phase B: Expand Rosetta Specs
1. [ ] Add algorithmic constructs to Rosetta grammar
   - `def` for pure functions
   - `partial def` for recursive algorithms
   - Pattern guards / conditional rewrites
2. [ ] Expand Interp.rosetta with parsing algorithms
3. [ ] Expand Loader.rosetta with module management
4. [ ] Add IO abstraction layer to rosetta

#### Phase C: Verification Infrastructure
1. [ ] Create `scripts/verify-interop.sh`:
   - Generate all 4 targets from each .rosetta
   - Run equivalent test suite on each
   - Compare outputs for behavioral equivalence
2. [ ] CI job for cross-target testing
3. [ ] Property-based testing across implementations

#### Phase D: Documentation
1. [ ] Document Runtime API contract (what generated code expects)
2. [ ] Document how to add new target languages
3. [ ] Document testing methodology for equivalence

---

## Bootstrap Process Documentation

### Current Bootstrap Chain

```
                   ┌─────────────────────────────────┐
                   │   generated/Bootstrap*.lean    │
                   │   (checked in, V_{n-1})         │
                   └─────────────┬───────────────────┘
                                 │
                                 ▼
                   ┌─────────────────────────────────┐
                   │   lake build tolean             │
                   │   (builds with V_{n-1})         │
                   └─────────────┬───────────────────┘
                                 │
                                 ▼
                   ┌─────────────────────────────────┐
                   │   tolean test/Bootstrap.lego    │
                   │   → V_n (new generated files)   │
                   └─────────────┬───────────────────┘
                                 │
                                 ▼
                   ┌─────────────────────────────────┐
                   │   diff V_{n-1} vs V_n           │
                   │   (fixpoint check)              │
                   └─────────────────────────────────┘
```

### Files in Bootstrap Chain

| File | Role |
|------|------|
| `test/Bootstrap.lego` | Source grammar definition |
| `generated/BootstrapGrammar.lean` | Generated parser |
| `generated/BootstrapTokenizer.lean` | Generated tokenizer |
| `generated/BootstrapRules.lean` | Generated reduction rules |
| `src/Lego/Bootstrap.lean` | Hand-written wrapper that imports generated |
| `tools/ToLean.lean` | Generator that produces Bootstrap*.lean |

### Hand-Coded vs Generated Interchangeability

**Goal**: Any generated version should be swappable with hand-coded.

**Current State**:
- `src/Lego/Bootstrap.lean` imports from `generated/`
- Hand-coded `.lean` files in `src/Lego/` have `.rosetta` equivalents
- `multi-target` pipeline can generate Lean from `.rosetta`

**Gap Analysis**:

| Component | Hand-coded | Generated | Interchangeable? |
|-----------|------------|-----------|------------------|
| Grammar | `generated/BootstrapGrammar.lean` | From `Bootstrap.lego` | ✅ Yes |
| Tokenizer | `generated/BootstrapTokenizer.lean` | From `Bootstrap.lego` | ✅ Yes |
| Rules | `generated/BootstrapRules.lean` | From `Bootstrap.lego` | ✅ Yes |
| Algebra | `src/Lego/Algebra.lean` | `Algebra.rosetta` | ⚠️ Partial |
| Interp | `src/Lego/Interp.lean` | `Interp.rosetta` | ⚠️ Partial |
| Runtime | `src/Lego/Runtime.lean` | `Runtime.rosetta` | ⚠️ Partial |
| AttrEval | `src/Lego/AttrEval.lean` | `AttrEval.rosetta` | ⚠️ Partial |
| Loader | `src/Lego/Loader.lean` | `Loader.rosetta` | ⚠️ Partial |
| Validation | `src/Lego/Validation.lean` | `Validation.rosetta` | ⚠️ Partial |

**Actions Needed**:

1. **Verify Rosetta coverage**: Run `lake exe multi-target src/Lego/*.rosetta` and diff against hand-coded
2. **Create bootstrap test**: Script that:
   - Generates Lean from all `.rosetta` files
   - Builds with generated instead of hand-coded
   - Runs test suite
3. **Document switch mechanism**: How to swap hand-coded ↔ generated in lakefile

---

## Duplicate/Redundant Files

| Files | Resolution |
|-------|------------|
| `docs/REDESIGN.md` = `src/Rosetta/REDESIGN.md` | Delete `src/Rosetta/REDESIGN.md` |
| `doc/` vs `docs/` | Merge `doc/redtt-ir.lego` → `examples/` or `docs/`, delete `doc/` |
| Multiple pipeline files in `Rosetta/` | Consolidate, remove deprecated code |

---

## Recommended Execution Order

### Phase 1: Quick Wins (No Code Changes) ✅ DONE
1. [x] Delete duplicate `src/Rosetta/REDESIGN.md`
2. [x] Move `doc/redtt-ir.lego` → `examples/`
3. [x] Delete empty `doc/` directory
4. [x] Move `run-cooltt-tests.sh` → `scripts/`
5. [x] Add `tmp/`, `*.rlib` to `.gitignore`
6. [x] Move `examples/Cubical/*.md` → `docs/cubical/`
7. [x] Move `test/RED-TODO.md` → `docs/`

### Phase 2: Structure Reorganization
1. [ ] Rename root `Rosetta/` → `pipelines/`
2. [ ] Move `LegoGen.lean` → `tools/`
3. [ ] Move `Cubical/GeneratedPipeline.lean` → `tools/`
4. [ ] Update `lakefile.lean` with new paths
5. [ ] Split `test/` into `test/lean/` and `test/lego/`

### Phase 3: Code Cleanup
1. [ ] Remove deprecated functions from `Interp.lean`, `Bootstrap.lean`
2. [ ] Remove deprecated emitters from `GrammarDrivenPipeline.lean`
3. [ ] Implement TODOs in `GenericPrettyPrinter.lean`
4. [ ] Replace `sorry` with proper implementations

### Phase 4: Bootstrap Verification
1. [ ] Create `scripts/verify-generated.sh` to diff hand-coded vs generated
2. [ ] Create `scripts/build-with-generated.sh` to test generated-only build
3. [ ] Document the swap process in `docs/BOOTSTRAP.md`
4. [ ] Add CI job for bootstrap verification

---

## Metrics After Reorg

| Metric | Before | After (Target) |
|--------|--------|----------------|
| Root files | 11 | 5 |
| Doc directories | 2 | 1 |
| Deprecated functions | 6 | 0 |
| TODO comments | 15 | 5 |
| `sorry` in code | 4 | 0 |
| Duplicate docs | 2 | 0 |
