# Cubical Type Theory in Lego

This document describes the cubical type theory features implemented in Lego,
enabling formal proofs of program transformations and verified rules.

## Overview

Lego's cubical TT implementation provides:

1. **Path Types** - Propositional equality with computational content
2. **Equivalences** - Quasi-invertible maps between types  
3. **Univalence** - Equivalent types are equal (ua)
4. **Higher Inductive Types** - Circle, Suspensions, Pushouts
5. **Glue/V Types** - For proving univalence
6. **Verified Rules** - Rewrite rules with cubical proofs
7. **Face Lattice** - De Morgan algebra for partial elements

## File Organization

```
src/Lego/
├── CubicalBase.lego    # Core primitives (Interval, Cofibrations, Paths)
├── Lego.lego           # Semantics (HITs, Glue, V types, Systems)
└── VerifiedLego.lego   # Verified versions of all rules

examples/
├── CubicalProofs.lego  # Comprehensive examples (funext, ua, etc.)
└── Cubical/            # Advanced cubical examples
```

## Core Primitives (CubicalBase.lego)

### The Interval

The abstract interval I with endpoints 0 and 1:

```
I : Univ
dim0 : I          -- endpoint 0
dim1 : I          -- endpoint 1
dimVar n : I      -- dimension variable
dimNeg r : I      -- negation: 1-r
dimMax r s : I    -- max(r,s)
dimMin r s : I    -- min(r,s)
```

**Computation rules:**
- `dimNeg dim0 ~~> dim1`
- `dimNeg dim1 ~~> dim0`
- `dimNeg (dimNeg r) ~~> r`
- `dimMax dim0 r ~~> r`
- `dimMax dim1 r ~~> dim1`

### Cofibrations (Face Formulas)

Cofibrations describe faces of the interval cube:

```
Cof : Univ
cof_top : Cof           -- ⊤ (always true)
cof_bot : Cof           -- ⊥ (never true)
cof_eq r s : Cof        -- r = s
cof_and φ ψ : Cof       -- φ ∧ ψ
cof_or φ ψ : Cof        -- φ ∨ ψ
```

**Simplification rules:**
- `cof_eq r r ~~> cof_top`
- `cof_eq dim0 dim1 ~~> cof_bot`
- `cof_and cof_top φ ~~> φ`
- `cof_and cof_bot φ ~~> cof_bot`
- `cof_or cof_top φ ~~> cof_top`
- `cof_or cof_bot φ ~~> φ`

### Face Lattice (De Morgan Algebra)

Extended operations forming a de Morgan algebra:

```
cof_neg φ : Cof              -- negation ¬φ
boundary i : Cof             -- (i=0) ∨ (i=1)
forallI i φ : Cof            -- ∀i. φ
existsI i φ : Cof            -- ∃i. φ
cof_implies φ ψ : Cof        -- φ → ψ
cof_iff φ ψ : Cof            -- φ ↔ ψ
```

**De Morgan laws:**
- `cof_neg (cof_and φ ψ) ~~> cof_or (cof_neg φ) (cof_neg ψ)`
- `cof_neg (cof_or φ ψ) ~~> cof_and (cof_neg φ) (cof_neg ψ)`
- `cof_neg cof_top ~~> cof_bot`
- `cof_neg cof_bot ~~> cof_top`

**Lattice laws:**
- `cof_and φ φ ~~> φ` (idempotence)
- `cof_or φ φ ~~> φ`
- `cof_and φ (cof_neg φ) ~~> cof_bot` (complement)
- `cof_or φ (cof_neg φ) ~~> cof_top`

### Path Types

Identity types with computational content:

```
Path A a b : Univ        -- Type of paths from a to b in A
plam i . body : Path     -- Path lambda (i is dimension variable)
papp p r : A             -- Path application at dimension r
refl a : Path A a a      -- Reflexivity: constant path
```

**Computation rules:**
- `papp (plam i . body) r ~~> body[i := r]`
- `papp (refl a) r ~~> a`

### Path Combinators

```
sym p : Path A b a                    -- Symmetry
trans p q : Path A a c                -- Transitivity  
cong f p : Path B (f a) (f b)         -- Congruence
funExt h : Path (A → B) f g           -- Function extensionality
```

**Computation rules:**
- `sym (refl a) ~~> refl a`
- `trans (refl a) q ~~> q`
- `trans p (refl b) ~~> p`
- `cong f (refl a) ~~> refl (f a)`

### Kan Operations

Coercion and homogeneous composition:

```
coe r s A a : A[i:=s]        -- Coerce a along type line A
hcom r s A φ cap : A         -- Homogeneous composition
```

**Degenerate cases:**
- `coe r r A a ~~> a`
- `hcom r r A φ cap ~~> cap`

### Equivalences

```
Equiv A B : Univ             -- Type of equivalences
idEquiv A : Equiv A A        -- Identity equivalence
compEquiv e1 e2 : Equiv A C  -- Composition
invEquiv e : Equiv B A       -- Inverse
equivFun e : A → B           -- Underlying function
ua e : Path Univ A B         -- Univalence: equiv → path
```

**Computation rules:**
- `equivFun (idEquiv A) ~~> λx.x`
- `ua (idEquiv A) ~~> refl A`
- `invEquiv (idEquiv A) ~~> idEquiv A`
- `compEquiv (idEquiv A) e ~~> e`

## Higher Inductive Types (Lego.lego)

### Circle (S¹)

```
S1 : Univ                    -- Circle type
base : S1                    -- Base point
loop : Path S1 base base     -- The loop
```

**Elimination:**
- `loop dim0 ~~> base`
- `loop dim1 ~~> base`

### Suspension

```
Susp A : Univ                -- Suspension of A
north : Susp A
south : Susp A  
merid a : Path (Susp A) north south
```

### Pushout

```
Pushout A B C f g : Univ
inl a : Pushout
inr b : Pushout
push c : Path (Pushout) (inl (f c)) (inr (g c))
```

## Glue Types (Univalence)

Glue types allow building equivalences from partial data:

```
Glue A [(φ, (T, e))] : Univ
glue a t : Glue A [...]
unglue g : A
```

**Key rule:**
- `unglue (glue a t) ~~> a`

## V Types (Simpler Univalence)

V types provide a simpler mechanism for univalence:

```
V r A B e : Univ             -- V type at dimension r
vin r a b : V r A B e        -- V introduction
vproj v : B                  -- V projection
```

**Boundary behavior:**
- `V dim0 A B e ~~> A`
- `V dim1 A B e ~~> B`
- `vin dim0 a b ~~> a`
- `vin dim1 a b ~~> b`

## Partial Elements and Systems

### Partial Types

```
Partial φ A : Univ           -- Partial element of A on face φ
Sub A φ u : Univ             -- Subtype (extension type)
subIn e : Sub A φ u          -- Introduction
subOut s : A                 -- Elimination
```

### Systems

Collections of partial elements on multiple faces:

```
sys [φ₁ ↦ u₁] [φ₂ ↦ u₂] ...  -- System of partial elements
sysEmpty : System
sysProj sys φ : A            -- Project from system
sysExtend sys φ u : System   -- Extend system
```

**Computation rules:**
- `subOut (subIn e) ~~> e`
- `sysExtend a cof_top u ~~> u`
- `sysExtend a cof_bot u ~~> a`

### System Composition

```
hcomSys r s A sys cap : A    -- Composition with system
comSys r s A sys cap : A     -- Composition (heterogeneous)
fillSys r s A sys cap i : A  -- Filler
```

## Verified Rules

Verified rules include a proof term showing the transformation is valid:

```
verified rule name: pattern ~> template via proof ;
```

### Design Pattern

| Rule Type | Use Case | Proof Needed? |
|-----------|----------|---------------|
| `rule` | Definitional computation | No |
| `verified rule` | Semantic-preserving optimization | Yes |

**Example:**
```
-- Definitional (no proof needed):
rule add_zero: (add zero n) ~> n ;

-- Theorem (proof required):
verified rule add_zero_right: (add n zero) ~> n
  via (refl n) ;
```

The key insight: `add zero n = n` is immediate by definition, but
`add n zero = n` requires induction to prove!

### Proof Combinators

| Combinator | Type | Use |
|------------|------|-----|
| `refl a` | `Path A a a` | Identity |
| `sym p` | `Path A b a` | Reverse direction |
| `trans p q` | `Path A a c` | Chain proofs |
| `cong f p` | `Path B (f a) (f b)` | Apply function |
| `ua e` | `Path Univ A B` | Univalence |

## Type Rules Summary

### Formation Rules

| Type | Formation |
|------|-----------|
| `Path A a b` | `A : Univ, a : A, b : A` |
| `Equiv A B` | `A : Univ, B : Univ` |
| `Glue A sys` | `A : Univ, sys : System` |
| `V r A B e` | `r : I, A : Univ, B : Univ, e : Equiv A B` |

### Introduction Rules

| Constructor | Type |
|-------------|------|
| `refl a` | `Path A a a` when `a : A` |
| `plam i . body` | `Path A a b` when endpoints match |
| `idEquiv A` | `Equiv A A` |
| `ua e` | `Path Univ A B` when `e : Equiv A B` |

### Elimination Rules

| Eliminator | Type |
|------------|------|
| `papp p r` | `A` when `p : Path A a b, r : I` |
| `sym p` | `Path A b a` when `p : Path A a b` |
| `equivFun e` | `A → B` when `e : Equiv A B` |
| `coe r s A a` | `A[s]` when `a : A[r]` |

## Examples

See [examples/CubicalProofs.lego](../examples/CubicalProofs.lego) for:

- Path type usage with Nat, List, Bool
- Verified rules with refl, sym, trans, cong
- Equivalence examples (Nat ≃ BinaryNat)
- Univalence and transport
- Function extensionality (funext)
- Quotient types

## Implementation Notes

### Bootstrap Chain

```
Hardcoded Grammar
    → parses Bootstrap.lego
    → Bootstrap grammar REPLACES hardcoded

Bootstrap Grammar  
    → parses CubicalBase.lego
    → parses Lego.lego
    
Lego Grammar
    → parses all other .lego files
```

### Test Coverage

- 221+ main tests including cubical features
- Face lattice: 11 tests for de Morgan algebra
- Partial elements: 5 tests for systems
- HITs: Tests for loop, merid endpoints
- Kan ops: Tests for coe/hcom degeneracy

Run tests with:
```bash
lake exe lego-test       # Main tests
lake exe lego-test-red   # Cubical-specific tests
```
