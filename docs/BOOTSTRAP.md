# Bootstrap Process

This document describes the bootstrap chain for Lego's self-hosting code generation.

## Overview

Lego uses a **bootstrap chain** where the code generator generates itself:

```
gen(V_n) = tolean_{V_{n-1}}(Bootstrap.lego)
```

There's no circular dependency because generation of version N uses the
previously-built `tolean` (version N-1).

## Bootstrap Files

| File | Purpose |
|------|---------|
| `test/lego/Bootstrap.lego` | Source grammar definition |
| `generated/BootstrapGrammar.lean` | Generated parser |
| `generated/BootstrapTokenizer.lean` | Generated tokenizer |
| `generated/BootstrapRules.lean` | Generated reduction rules |
| `generated/MinimalBootstrapTokenizer.lean` | Minimal tokenizer variant |

## Build Stages

```
┌─────────────────────────────────┐
│   generated/Bootstrap*.lean    │  ← V_{n-1} (checked into git)
│   (checked in)                  │
└─────────────┬───────────────────┘
              │
              ▼
┌─────────────────────────────────┐
│   lake build tolean             │  ← Build generator using V_{n-1}
└─────────────┬───────────────────┘
              │
              ▼
┌─────────────────────────────────┐
│   tolean Bootstrap.lego         │  ← Generate V_n
│   → generated/*.lean.new        │
└─────────────┬───────────────────┘
              │
              ▼
┌─────────────────────────────────┐
│   diff V_{n-1} vs V_n           │  ← Fixpoint check
│   (should be identical)         │
└─────────────────────────────────┘
```

## Scripts

### Regenerate Bootstrap Files

```bash
./scripts/bootstrap.sh
```

This will:
1. Build `tolean` using current `generated/*.lean`
2. Regenerate from `Bootstrap.lego`
3. Update `generated/*.lean` if different

### Verify Bootstrap (CI)

```bash
./scripts/bootstrap.sh --check
```

This verifies that `generated/*.lean` files are canonical (match what
would be regenerated). Use this in CI to ensure bootstrap files are
up-to-date.

### Verify Generated Coverage

```bash
./scripts/verify-generated.sh
```

Compares hand-coded `.lean` files against generated versions from
`.rosetta` specs. Shows coverage percentage and identifies gaps.

### Test Generated Build

```bash
./scripts/build-with-generated.sh
```

Attempts to build the project using generated code instead of
hand-coded implementations. This validates 5-way interchangeability.

## 5-Way Interchangeability

The goal is that code can be swapped between:

1. **Hand-coded Lean** (`src/Lego/*.lean`)
2. **Generated Lean** (`lake exe multi-target *.rosetta -t lean`)
3. **Generated Scala** (`lake exe multi-target *.rosetta -t scala`)
4. **Generated Haskell** (`lake exe multi-target *.rosetta -t haskell`)
5. **Generated Rust** (`lake exe multi-target *.rosetta -t rust`)

### Current Coverage

| Module | Hand-coded | .rosetta | Status |
|--------|------------|----------|--------|
| Algebra | 427 lines | 259 lines | Partial |
| Attr | 298 lines | 284 lines | Good |
| AttrEval | 615 lines | 408 lines | Partial |
| Interp | 881 lines | 206 lines | Low |
| Loader | 1203 lines | 242 lines | Low |
| Runtime | 312 lines | 312 lines | ✅ Complete |
| Validation | 363 lines | 395 lines | ✅ Complete |

### Gap Analysis

Low coverage in `Interp.rosetta` and `Loader.rosetta` is because:
- Parsing algorithms are now in **Runtime libraries** (all 4 languages)
- File I/O is target-specific (in Runtime)
- Complex packrat parsing isn't expressible in pure rewrite rules

This is by design: `.rosetta` specs define **ADTs and rewrite rules**,
while **algorithms** live in the Runtime libraries.

## Swapping Hand-Coded ↔ Generated

To use generated code instead of hand-coded:

1. Generate Lean from `.rosetta`:
   ```bash
   lake exe multi-target src/Lego/*.rosetta -o generated/Lego -t lean
   ```

2. Modify `lakefile.lean` to use generated sources:
   ```lean
   lean_lib «Lego» where
     srcDir := "generated"  -- was "src"
     roots := #[`Lego.Algebra, `Lego.Runtime, ...]
   ```

3. Rebuild:
   ```bash
   rm -rf .lake/build && lake build
   ```

Note: This will only work once `.rosetta` coverage reaches ~100%.

## CI Integration

Add to your CI workflow:

```yaml
- name: Verify Bootstrap
  run: ./scripts/bootstrap.sh --check

- name: Verify Generated Coverage
  run: ./scripts/verify-generated.sh --summary
```

This ensures:
1. Bootstrap files are canonical (fixpoint achieved)
2. Generated coverage is tracked over time
