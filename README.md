# Lego: A Minimal Language for Building Languages

**Lego** is a declarative language workbench in Lean 4 where syntax is an expression, not a procedure.
The same grammar drives parsing, printing, and validation bidirectionally.

## Quick Start

```bash
lake build
lake exe pipeline           # Generate .lean from .lego
lake build CubicalGenerated # Compile generated cubical TT
```

## Leverage Metrics

| Input | Output | Ratio |
|-------|--------|-------|
| 99 derives | 1,718 functions | **17x** |
| 99 derives | 11,236 Lean lines | **113x** |
| Bootstrap.lego (521 lines) | Full meta-grammar | - |

## Philosophy

**Everything is a BiReducer.**

A `BiReducer A B` is a partial isomorphism between types `A` and `B`:
- `forward : A → Option B`
- `backward : B → Option A`

When both succeed: `forward ∘ backward = id` and `backward ∘ forward = id`.

## The Key Insight

Grammar is not special. It's just a `BiReducer TokenStream Term`.

| Component | BiReducer Type | Forward | Backward |
|-----------|---------------|---------|----------|
| **Grammar** | `TokenStream ⇌ Term` | parse | print |
| **Rules** | `Term ⇌ Term` | reduce | expand |
| **Types** | `Term → Option Type` | infer | - |

A **Piece** = Grammar + Rules = Syntax + Free Interpreter

A **Language** = ⊔ Pieces = Merged Grammar + Merged Interpreter

**The grammar (Meta) is pre-compiled, but structurally identical to any user-defined language.**

## Core Algebra

```
BiReducer composition:

  id     : A ⇌ A                         -- identity
  >>>    : (A ⇌ B) → (B ⇌ C) → (A ⇌ C)   -- sequential
  ***    : (A ⇌ B) → (C ⇌ D) → (A×C ⇌ B×D)  -- parallel (product)
  |||    : (A ⇌ C) → (B ⇌ C) → (A+B ⇌ C) -- choice (coproduct)
  orElse : (A ⇌ B) → (A ⇌ B) → (A ⇌ B)   -- alternative
  ~      : (A ⇌ B) → (B ⇌ A)             -- symmetric (flip)
```

These form a **dagger compact category** enriched over partial isomorphisms.

## Grammar Algebra

`GrammarExpr` is the free Kleene algebra (*-semiring):

| Constructor | Notation | Algebra |
|------------|----------|---------|
| `empty` | ε | identity for alt |
| `lit s` | "s" | literal match |
| `ref n` | n | production reference |
| `seq` | ⬝ | monoid (associative, ε identity) |
| `alt` | ⊕ | commutative, associative |
| `star` | * | Kleene closure |
| `bind` | x ← g | capture binding |
| `node` | ⟨name⟩ g | AST wrapper |

Laws:
- `(a ⬝ b) ⬝ c = a ⬝ (b ⬝ c)` (seq associative)
- `ε ⬝ a = a = a ⬝ ε` (seq identity)
- `a ⊕ b = b ⊕ a` (alt commutative)
- `(a ⊕ b) ⊕ c = a ⊕ (b ⊕ c)` (alt associative)
- `a* = (a ⬝ a*) ⊕ ε` (star unfold)
- `a ⬝ (b ⊕ c) = (a ⬝ b) ⊕ (a ⬝ c)` (distribution)

## File Structure

```
toy/
├── lakefile.lean            -- Lake build config
├── lean-toolchain           -- Lean version
├── Main.lean                -- Entry point
├── Test.lean                -- Core test suite (111 tests)
├── TestRed.lean             -- Red/cubical tests (190 tests)
├── ATTR-TODO.md             -- Attribute grammar implementation status
├── README.md                -- This file
├── docs/
│   └── REDTT.md             -- Red module documentation
└── src/
    ├── Lego.lean            -- Re-exports all modules
    └── Lego/
        ├── Algebra.lean     -- BiReducer, Term, GrammarExpr, Rule, Piece, Language
        ├── AttrGrammar.lean -- Attribute Grammar types and evaluation
        ├── AttrEval.lean    -- Runtime evaluation with error reporting
        ├── Interp.lean      -- Grammar interpretation (parse/print)
        ├── Bootstrap.lean   -- Meta (pre-compiled, like Grammar.sexpr)
        ├── Laws.lean        -- Algebraic laws and axioms
        ├── Red/
        │   ├── Core.lean    -- Cubical type theory core IR
        │   └── TypeAttrs.lean -- Type checking rules
        └── Example/
            └── Lambda.lean  -- Lambda calculus + Interaction nets examples
```

## Red: Cubical Type Theory

The `Lego.Red` module implements cubical type theory with:
- **De Bruijn indexed Core IR** with substitution engine
- **Universe polymorphism** with Level expressions (zero, suc, max, lvar)
- **Path types** with η-laws: `p ≡ λi. p @ i`, `refl a ≡ λi. a`
- **Coercion and composition** (coe, hcom, hcomTube)
- **Tube agreement checking** for composition

See [docs/REDTT.md](docs/REDTT.md) for full documentation.

```bash
# Run Red tests (190 tests)
lake exe lego-test-red --all
```

## Attribute Grammars

Attribute Grammars extend the bidirectional reducer model with **synthesized** and **inherited** attributes:

| Attribute Type | Morphism | Direction | Example |
|----------------|----------|-----------|---------|
| **Synthesized** | Catamorphism | Bottom-up | Type inference: `type` |
| **Inherited** | Paramorphism | Top-down | Context: `ctx`, `expected` |

### Key Types

```lean
-- Attribute flow direction
inductive AttrFlow | syn | inh | synInh

-- Attribute definition
structure AttrDef where
  name : String
  flow : AttrFlow
  rules : List AttrRule

-- Evaluation environment
structure EvalEnv where
  attrs : AttrEnv           -- Computed attributes
  ctx : Context             -- Typing context
  dimCtx : DimContext       -- Dimension context (cubical)
  errors : List TypeError   -- Accumulated errors
  loc : SourceLoc           -- Current source location
```

### Scope Handling for Binders

The evaluator properly extends context when entering binder bodies:

```lean
-- λ w : Type . w
-- child 0: "w" (binding position - skip lookup)
-- child 1: Type (reference - lookup in ctx)
-- child 2: w (reference - lookup in EXTENDED ctx with w:Type)

def binderProductions : List (String × Nat × Nat × Nat) :=
  [ ("lam", 0, 1, 2)    -- λ x : A . body
  , ("Pi", 0, 1, 2)     -- Π x : A . B
  , ("Sigma", 0, 1, 2)  -- Σ x : A . B
  , ("let", 0, 1, 3)    -- let x : A = v in body
  ]
```

### Tests

All 127 tests pass including:
- 733/733 redtt library parsing (100%)
- Attribute evaluation on lam, pi, app, refl, path, coe, hcom
- Scope handling: `lam_id`, `lam_nested`, `pi_dep`

## Meta: Just Another Language

The Meta is defined in [Bootstrap.lean](src/Lego/Bootstrap.lean) as a regular `Language`:

```lean
def metaGrammar : Language := {
  name := "Meta"
  pieces := [atomPiece, termPiece, patternPiece, templatePiece, grammarExprPiece, filePiece]
}
```

It has the same structure as any user-defined language. The only difference is it's pre-compiled in Lean (bootstrapped) rather than parsed from a `.lego` file.

## The Roundtrip Theorem

```lean
theorem roundtrip (lang : Language) (startProd : String) :
    let interp := lang.toInterp startProd
    ∀ t : Term, ∀ tokens : TokenStream,
      interp.parse tokens = some t →
      interp.print t >>= interp.parse = some t
```

This is provable from the lawfulness of BiReducers.

## Building

```bash
lake build
lake exe pipeline           # Generate .lean from .lego files
lake build CubicalGenerated # Compile generated code
```

## Example Languages

The [Example/Lambda.lean](src/Lego/Example/Lambda.lean) file shows that user-defined languages have the exact same structure as the Meta:

```lean
-- Lambda Calculus: same structure as Meta
def lambdaCalc : Language := {
  name := "LambdaCalculus"
  pieces := [atomPiece, exprPiece, betaPiece]
}

-- Interaction Nets: also same structure
def inetLang : Language := {
  name := "InteractionNets"
  pieces := [inetPiece]
}
```

Each language gets a free interpreter from its rules:
- Lambda: β-reduction via `Rule.toBiReducer`
- Interaction Nets: annihilation/commutation via `Rule.toBiReducer`
