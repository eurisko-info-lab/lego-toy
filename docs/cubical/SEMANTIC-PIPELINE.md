# Cubical Semantic Pipeline

This document describes the end-to-end semantic pipeline for Cubical Type Theory in Lego, with concrete examples.

## Pipeline Overview

```
Surface Syntax (Cooltt/Redtt)
        ↓ Parse (Grammar)
       AST
        ↓ AST→IR (TypeAttrs)
    Core IR (de Bruijn)
        ↓ Elaborate (Elaborate.lego)
  Elaborated Term + Type
        ↓ Normalize (Semantics.lego)
    Normal Form
        ↓ Quote (Quote.lego)
    Quoted Term
```

## 1. Surface Syntax Parsing

**Input**: Cooltt surface syntax
```
def id : (A : type) → A → A := λ A x. x
```

**Grammar** (from `Cooltt.lego`):
```
expr ::= "λ" binders "." expr → lam
       | expr expr → app
       | "type" → type
       | ...
```

**Output**: AST
```
(def (ident "id") 
     (Arrow (cell "A" type) (Arrow A A))
     (lam (binders (simpleBinder "A") (simpleBinder "x")) (var "x")))
```

## 2. AST to Core IR

**Rules** (from `TypeAttrs.lego`):
```
rule astLamTyped: (ast (lam (binders (typedBinder $x $A)) $body)) ~>
  (lam $x $A (ast $body)) ;

rule astLamSimple: (ast (lam (binders (simpleBinder $x)) $body)) ~>
  (lam $x (hole) (ast $body)) ;

rule astArrow: (ast (Arrow $A $B)) ~> (pi "_" (ast $A) (ast $B)) ;
```

**Example transformation**:
```
AST:  (lam (binders (simpleBinder "x")) (var "x"))
  ↓ astLamSimple
IR:   (lam "x" (hole) (var "x"))
  ↓ name resolution (de Bruijn)
Core: (lam (ix 0))
```

## 3. Core IR (de Bruijn indexed)

**Syntax** (from `Core.lego`):
```
term ::= "ix" <number> → ix        -- de Bruijn index
       | "lam" term → lam          -- λ-abstraction (body only)
       | "app" term term → app     -- application
       | "pi" term term → pi       -- Π type
       | "univ" level → univ       -- universe
       | ...
```

**Key Operations**:

### Shift (weakening)
```
shift k n e = e with free vars ≥ k incremented by n

rule shiftIx: (shift $k $n (ix $m)) ~> 
  (ix (if (geq $m $k) (add $m $n) $m)) ;

rule shiftLam: (shift $k $n (lam $body)) ~> 
  (lam (shift (add $k 1) $n $body)) ;
```

### Substitution
```
subst k v e = e[v/ix k]

rule substIxHit: (subst $k $v (ix $k)) ~> $v ;
rule substIxMiss: (subst $k $v (ix $m)) ~> 
  (ix (if (gt $m $k) (sub $m 1) $m)) when (neq $k $m) ;

rule substLam: (subst $k $v (lam $body)) ~> 
  (lam (subst (add $k 1) (shift 0 1 $v) $body)) ;
```

## 4. Beta Reduction

**Rule** (from `Core.lego`):
```
rule beta: (app (lam $body) $arg) ~> (subst 0 $arg $body) ;
```

**Example**: Identity function
```
(app (lam (ix 0)) "a")
  ↓ beta
(subst 0 "a" (ix 0))
  ↓ substIxHit (k=0 matches ix 0)
"a"
```

**Example**: K combinator `(λx.λy.x) a b`
```
(app (app (lam (lam (ix 1))) "a") "b")
  ↓ beta on inner app
(app (subst 0 "a" (lam (ix 1))) "b")
  ↓ substLam
(app (lam (subst 1 (shift 0 1 "a") (ix 1))) "b")
  ↓ shiftLit (literals don't shift)
(app (lam (subst 1 "a" (ix 1))) "b")
  ↓ substIxHit (k=1 matches ix 1)
(app (lam "a") "b")
  ↓ beta
(subst 0 "b" "a")
  ↓ substLit (literals don't substitute)
"a"
```

## 5. Path Types

**Syntax**:
```
term ::= "path" term term term → path    -- Path A a b
       | "plam" term → plam              -- λi.e (dimension abstraction)
       | "papp" term term → papp         -- p @ r (path application)
       | "refl" term → refl              -- reflexivity
```

**Rules**:
```
rule reflApp: (papp (refl $a) $r) ~> $a ;

rule plamApp0: (papp (plam $body) dim0) ~> (substDim 0 dim0 $body) ;
rule plamApp1: (papp (plam $body) dim1) ~> (substDim 0 dim1 $body) ;
```

**Example**: Path endpoints
```
(papp (refl "a") dim0)
  ↓ reflApp
"a"

(papp (refl "a") dim1)
  ↓ reflApp
"a"
```

## 6. Cofibrations

**Syntax**:
```
term ::= "cof_top" → cof_top       -- ⊤
       | "cof_bot" → cof_bot       -- ⊥
       | "cof_eq" term term → cof_eq    -- r = s
       | "cof_and" term term → cof_and  -- φ ∧ ψ
       | "cof_or" term term → cof_or    -- φ ∨ ψ
```

**Rules**:
```
rule eqRefl: (cof_eq $r $r) ~> cof_top ;
rule eq01: (cof_eq dim0 dim1) ~> cof_bot ;
rule andTop: (cof_and cof_top $φ) ~> $φ ;
rule andBot: (cof_and cof_bot $φ) ~> cof_bot ;
rule orTop: (cof_or cof_top $φ) ~> cof_top ;
rule orBot: (cof_or cof_bot $φ) ~> $φ ;
```

**Examples**:
```
(cof_eq dim0 dim0)
  ↓ eqRefl
cof_top

(cof_and cof_top (cof_eq dim0 dim1))
  ↓ andTop
(cof_eq dim0 dim1)
  ↓ eq01
cof_bot
```

## 7. Kan Operations

### Coercion (coe)
Transport along a line of types.

**Syntax**: `coe r r' A a` — coerce `a : A@r` to `A@r'`

**Rules**:
```
rule coeRefl: (coe $r $r $A $a) ~> $a ;  -- degenerate
```

**Example**:
```
(coe dim0 dim0 (univ 0) "a")
  ↓ coeRefl
"a"
```

### Homogeneous Composition (hcom)
Fill a box with compatible faces.

**Syntax**: `hcom r r' A φ cap` — compose with constraint φ

**Rules**:
```
rule hcomRefl: (hcom $r $r $A $φ $cap) ~> $cap ;  -- degenerate
```

**Example**:
```
(hcom dim0 dim0 (univ 0) cof_top "cap")
  ↓ hcomRefl
"cap"
```

## 8. Higher Inductive Types

### Circle (S¹)

**Syntax**:
```
term ::= "base" → base
       | "loop" term → loop
       | "circleElim" term term term term → circleElim
```

**Rules**:
```
rule loop0: (loop dim0) ~> base ;
rule loop1: (loop dim1) ~> base ;
rule circleElimBase: (circleElim $P $b $l base) ~> $b ;
```

**Example**:
```
(loop dim0)
  ↓ loop0
base

(circleElim P "baseCase" "loopCase" base)
  ↓ circleElimBase
"baseCase"
```

### Natural Numbers

**Rules**:
```
rule natElimZero: (natElim $P $z $s zero) ~> $z ;
rule natElimSuc: (natElim $P $z $s (suc $n)) ~> 
  (app (app $s $n) (natElim $P $z $s $n)) ;
```

## 9. V-Types (Glue types for Univalence)

**Syntax**:
```
term ::= "vtype" term term term term → vtype
       | "vin" term term term → vin
       | "vproj" term term term term term → vproj
```

**Rules**:
```
rule vin0: (vin dim0 $a $b) ~> $a ;
rule vin1: (vin dim1 $a $b) ~> $b ;
```

**Example**: V-type boundary
```
(vin dim0 "left" "right")
  ↓ vin0
"left"

(vin dim1 "left" "right")
  ↓ vin1
"right"
```

## 10. Type Inference

**Type Rules** (from `Core.lego`):
```
type univType: (univ $n) : (univ (lsuc $n)) ;
type natType: nat : (univ lzero) ;
type zeroType: zero : nat ;
type sucType: (suc $n) : nat when $n : nat ;
type piType: (pi $A $B) : (univ (lmax $l1 $l2)) 
  when $A : (univ $l1), $B : (univ $l2) ;
```

**Examples**:
```
typeof(univ 0) = univ (lsuc 0) = univ 1
typeof(nat) = univ 0
typeof(zero) = nat
typeof(suc zero) = nat
```

## 11. Elaboration (Bidirectional)

**Infer rules** (synthesize type):
```
rule inferLit: (infer $ctx (lit $s)) ~> 
  (ok term: (lit $s) type: (univ lzero) ctx: $ctx) ;

rule inferUniv: (infer $ctx (univ $n)) ~>
  (ok term: (univ (levelOfNat $n)) type: (univ (levelOfNat (suc $n))) ctx: $ctx) ;
```

**Check rules** (check against type):
```
rule checkLam: (check $ctx (lam $body) (pi $dom $cod)) ~>
  (checkLamBody $ctx $dom $cod $body) ;
```

## 12. Normalization Flow

**Complete example**: Normalizing `(λx.x) (λy.y) z`

```
Input: (app (app (lam (ix 0)) (lam (ix 0))) "z")

Step 1: Normalize inner app
  (app (lam (ix 0)) (lam (ix 0)))
    ↓ beta
  (subst 0 (lam (ix 0)) (ix 0))
    ↓ substIxHit
  (lam (ix 0))

Step 2: Result so far
  (app (lam (ix 0)) "z")
    ↓ beta
  (subst 0 "z" (ix 0))
    ↓ substIxHit
  "z"

Final: "z"
```

## Module Organization

| Module | Purpose | Key Rules |
|--------|---------|-----------|
| `Core.lego` | Core IR, subst, shift | beta, fstPair, sndPair |
| `Cofibration.lego` | Cofibration logic | eqRefl, andTop, orBot |
| `Kan.lego` | Kan operations | coeRefl, hcomRefl |
| `HIT.lego` | Higher inductives | loop0/1, natElim |
| `VType.lego` | V-types | vin0/1 |
| `TypeAttrs.lego` | AST→IR, synType | astLam, synTypeUniv |
| `Elaborate.lego` | Elaboration | infer, check |
| `Semantics.lego` | Evaluation | eval, whnf |
| `Quote.lego` | Readback | quote |
| `Unify.lego` | Unification | unify, solve |

## Rule Counts (from integration tests)

- **1,615 rewrite rules** total
- **142 type rules** total
- 122 Cooltt grammar productions
- 36 AST→IR transformation rules
- 14 synType rules
- 16 infer + 18 check + 61 eval rules
- 44 quote/readback rules
- 36 unification rules

## Running Tests

```bash
# Main integration tests (29 tests)
lake exe lego-test-cubical-integration

# Full test suite (227 tests)
lake exe lego-test

# Cooltt library parsing (100% parse rate)
lake exe lego-test-cool --all
```
