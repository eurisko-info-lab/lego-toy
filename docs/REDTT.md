# Red: Cubical Type Theory Implementation

## Overview

Red is a cubical type theory implementation in Lean 4, providing:
- **De Bruijn indexed Core IR** with full substitution engine
- **Cubical type checker** with path types, coercion, and composition
- **Universe polymorphism** with Level expressions
- **η-laws** for functions, pairs, and paths
- **Tube agreement checking** for higher-dimensional composition

## Architecture

```
                    ┌─────────────────┐
                    │   Lego.Term     │  ← AST (s-expressions)
                    └────────┬────────┘
                             │ elaborate
                             ▼
┌──────────────────────────────────────────────────┐
│              Lego.Red.Core                       │
│  ┌──────────────────────────────────────────┐   │
│  │           Level (Universe levels)        │   │
│  │  zero | suc | max | lvar                 │   │
│  └──────────────────────────────────────────┘   │
│  ┌──────────────────────────────────────────┐   │
│  │           Expr (De Bruijn terms)          │   │
│  │  ix | lam | app | pi | sigma | pair      │   │
│  │  univ | path | plam | papp | refl        │   │
│  │  coe | hcom | hcomTube | dim0/1 | dimVar │   │
│  │  cof_* | nat | zero | suc | circle | ... │   │
│  └──────────────────────────────────────────┘   │
│  ┌──────────────────────────────────────────┐   │
│  │        Substitution & Reduction           │   │
│  │  shift | subst | step | eval | normalize │   │
│  └──────────────────────────────────────────┘   │
│  ┌──────────────────────────────────────────┐   │
│  │           Type Checker (infer/check)      │   │
│  │  conv | infer | check | checkTubeAgree   │   │
│  └──────────────────────────────────────────┘   │
└──────────────────────────────────────────────────┘
                             │
                             ▼
┌──────────────────────────────────────────────────┐
│           Lego.Red.TypeAttrs                     │
│  AST↔IR rules + Attribute grammar type rules    │
└──────────────────────────────────────────────────┘
```

## Universe Polymorphism

Universe levels are first-class expressions:

```lean
inductive Level where
  | zero  : Level                    -- Level 0
  | suc   : Level → Level            -- ℓ + 1
  | max   : Level → Level → Level    -- max ℓ₁ ℓ₂
  | lvar  : Nat → Level              -- Level variable (de Bruijn)
```

### Level Operations

| Operation | Description |
|-----------|-------------|
| `Level.ofNat n` | Convert `Nat` to `Level` |
| `Level.toNat? l` | Convert to `Nat` if concrete |
| `Level.normalize l` | Simplify level expression |
| `Level.levelEq l₁ l₂` | Check equality (normalizing) |
| `Level.leq l₁ l₂` | Check `l₁ ≤ l₂` (for cumulativity) |

### Universe Typing Rules

```
Γ ⊢ Type^ℓ : Type^(suc ℓ)

Γ ⊢ A : Type^i    Γ, x:A ⊢ B : Type^j
────────────────────────────────────────
      Γ ⊢ (Π x:A. B) : Type^(max i j)

Γ ⊢ A : Type^i    Γ, x:A ⊢ B : Type^j
────────────────────────────────────────
      Γ ⊢ (Σ x:A. B) : Type^(max i j)
```

## Core IR (De Bruijn Indexed)

### Term Structure

```lean
inductive Expr where
  -- Basic λ-calculus
  | ix    : Nat → Expr                      -- Variable (de Bruijn index)
  | lit   : String → Expr                   -- Literal
  | lam   : Expr → Expr                     -- λ. body
  | app   : Expr → Expr → Expr              -- f x
  | pi    : Expr → Expr → Expr              -- Π A. B
  | sigma : Expr → Expr → Expr              -- Σ A. B
  | pair  : Expr → Expr → Expr              -- (a, b)
  | fst   : Expr → Expr                     -- π₁
  | snd   : Expr → Expr                     -- π₂
  | letE  : Expr → Expr → Expr → Expr       -- let : A = v in body
  | univ  : Level → Expr                    -- Type^ℓ
  
  -- Interval and dimensions
  | dim0  : Expr                            -- 0 : 𝕀
  | dim1  : Expr                            -- 1 : 𝕀
  | dimVar : Nat → Expr                     -- dimension variable
  
  -- Cofibrations
  | cof_top : Expr                          -- ⊤
  | cof_bot : Expr                          -- ⊥
  | cof_eq  : Expr → Expr → Expr            -- r = s
  | cof_and : Expr → Expr → Expr            -- φ ∧ ψ
  | cof_or  : Expr → Expr → Expr            -- φ ∨ ψ
  
  -- Path types
  | path  : Expr → Expr → Expr → Expr       -- path A a b
  | plam  : Expr → Expr                     -- λi. body
  | papp  : Expr → Expr → Expr              -- p @ r
  | refl  : Expr → Expr                     -- refl a
  
  -- Cubical operations
  | coe   : Expr → Expr → Expr → Expr → Expr     -- coe r r' (λi.A) a
  | hcom  : Expr → Expr → Expr → Expr → Expr → Expr  -- hcom r r' A φ cap
  | hcomTube : Expr → Expr → Expr → List (Expr × Expr) → Expr → Expr
              -- hcom with explicit tubes: hcom r r' A [(φ,tube)...] cap
```

### Substitution Engine

The substitution engine maintains the presheaf model:

```lean
-- Shift free variables at or above cutoff
partial def shiftAbove (cutoff : Nat) (delta : Int) : Expr → Expr

-- Substitute value for index
partial def subst (idx : Nat) (val : Expr) : Expr → Expr

-- Single-step reduction
partial def step : Expr → Option Expr

-- Full evaluation (fuel-limited)
partial def eval : Expr → Expr
```

**Key β-reductions:**
- `(λ. body) arg → body[0 := arg]`
- `fst (pair a b) → a`
- `snd (pair a b) → b`
- `(λi. body) @ r → body[0 := r]`
- `coe r r A a → a` when `r = r'`
- `hcom r r A φ cap → cap` when `r = r'`

## Type Checking

### Conversion

The `conv` function implements definitional equality with full η-laws:

```lean
partial def conv (a b : Expr) : Bool
```

**Supported η-laws:**
| η-law | Description |
|-------|-------------|
| Functions | `f ≡ λx. f x` |
| Pairs | `p ≡ (fst p, snd p)` |
| Paths | `p ≡ λi. p @ i` |
| Refl | `refl a ≡ λi. a` |

### Type Inference

```lean
partial def infer (ctx : Ctx) : Expr → TCResult Expr
partial def check (ctx : Ctx) (e : Expr) (ty : Expr) : TCResult Unit
```

**Key rules:**
- Variable lookup: `Γ(n) = A  ⟹  Γ ⊢ #n : A`
- Application: `Γ ⊢ f : Π A B  ⟹  Γ ⊢ f a : B[a/0]`
- Path elimination: `Γ ⊢ p : path A a b  ⟹  Γ ⊢ p @ r : A`

### Path Checking

When checking `Γ ⊢ λi. body : path A a b`:
1. Check `Γ, i:𝕀 ⊢ body : A`
2. Verify boundaries: `body[0/i] ≡ a` and `body[1/i] ≡ b`

### Tube Agreement

For `hcomTube r r' A [(φ₁,tube₁), ...] cap`:
- When `φᵢ` holds: require `tubeᵢ(r) ≡ cap`
- Skip check when `φᵢ = ⊥`

```lean
partial def checkTubeAgreement 
  (r : Expr) (ty : Expr) (tubes : List (Expr × Expr)) (cap : Expr) 
  : TCResult Expr
```

## AST ↔ IR Transformation

The `TypeAttrs` module provides bidirectional rules:

```lean
-- AST → IR
(.con "type" [], .con "univ" [.lit "0"])
(.con "Arrow" [.var "A", .var "B"], .con "Pi" [.lit "_", .var "A", .var "B"])

-- IR → AST
(.con "univ" [.lit "0"], .con "type" [])
(.con "Pi" [.lit "_", .var "A", .var "B"], .con "Arrow" [.var "A", .var "B"])
```

## Testing

```bash
# Run all Red tests (190 tests)
lake exe lego-test-red --all

# Run specific test categories
lake exe lego-test-red           # Core tests only
```

**Test Categories:**
| Category | Count | Description |
|----------|-------|-------------|
| Type checking | ~50 | Basic type inference |
| Conversion | 14 | η-laws, structural |
| Universe levels | 8 | Level operations |
| Tube agreement | 4 | hcomTube checking |
| Redtt library | 725/725 | Parsing redtt files |
| Redtt type check | 10 | Full type checking |

## Mathematical Structure

### Presheaf Model

Terms form a presheaf over the category of contexts:
- **Objects**: Contexts `Γ`
- **Morphisms**: Substitutions `σ : Δ → Γ`
- **Action**: `t[σ]` for `t : Term(Γ)`, `σ : Δ → Γ`

### Cubical Structure

The interval `𝕀` with:
- Endpoints: `0, 1 : 𝕀`
- Dimension variables: `i, j, k, ... : 𝕀`

Cofibrations as propositions about dimensions:
- `⊤, ⊥` (true, false)
- `i = 0`, `i = 1`, `i = j`
- `φ ∧ ψ`, `φ ∨ ψ`

### Key Cubical Operations

| Operation | Type | Description |
|-----------|------|-------------|
| `path A a b` | Type | Identity type |
| `coe r r' (λi.A) a` | `A[r'/i]` | Coercion along type line |
| `hcom r r' A φ cap` | A | Composition with tubes |

## Usage Example

```lean
import Lego.Red.Core

open Lego.Core

-- Create a simple term: λx. x
def id_term := Expr.lam (.ix 0)

-- Type check: id has type Π Nat. Nat
def id_type := Expr.pi .nat .nat
#eval check [] id_term id_type  -- ok: ()

-- Path: refl 0 : path Nat 0 0
def refl_zero := Expr.refl .zero
#eval infer [] refl_zero  -- ok: path Nat zero zero
```

## Files

| File | Lines | Purpose |
|------|-------|---------|
| `src/Lego/Red/Core.lean` | ~1460 | Core IR, substitution, type checker |
| `src/Lego/Red/TypeAttrs.lean` | ~430 | AST↔IR rules, type rules |
| `TestRed.lean` | ~1360 | Test suite (190 tests) |
