# Expr Constructor Origins: redtt vs cooltt

This document tracks which `Expr` constructors come from **redtt**, which from **cooltt**, and which are **shared** between both implementations.

## Lego Language Files

The shared and language-specific constructs are defined as `.lego` files with **pieces** (each having grammar, rules, tests):

| File | Pieces | Description |
|------|--------|-------------|
| [CubicalTT.lego](CubicalTT.lego) | 13 | Dimension, Cofibration, Core, Lambda, Pi, Sigma, Path, System, Coe, Hcom, Com, VType, Sub |
| [Red.lego](Red.lego) | 7 | ExtType, GCom, Data, Twin, Restrict, FHcom, BoxCap |
| [Cool.lego](Cool.lego) | 7 | Nat, Circle, Signature, El, CofExt, Gel, LockedCof |

Each **piece** encapsulates:
- Grammar productions (`piece X ::= ...`)
- Reduction rules (`rule name: ... ~> ...`)
- Typing rules (`type name: ... : ...`)
- Tests (`test "name": ... ~~> ...`)

## Summary

| Category | Pieces | Description |
|----------|--------|-------------|
| **Shared (CubicalTT)** | 13 | Core cubical type theory |
| **redtt-only (Red)** | 7 | Twins, Data types, Extension types |
| **cooltt-only (Cool)** | 7 | HITs, Signatures, El types |

---

## Shared Constructors (Both redtt and cooltt)

These form the core of cubical type theory:

| Constructor | redtt | cooltt | Description |
|-------------|-------|--------|-------------|
| `ix` | `Ix` | `Var` | De Bruijn index |
| `lam` | `Lam` | `Lam` | Lambda abstraction |
| `app` | `FunApp` (frame) | `Ap` | Function application |
| `pi` | `Pi` | `Pi` | Dependent function type |
| `sigma` / `pair` / `fst` / `snd` | `Sg`, `Cons`, `Fst`, `Snd` | `Sg`, `Pair`, `Fst`, `Snd` | Sigma types |
| `letE` | `Let` | `Let` | Let binding |
| `univ` | `Univ` | `Univ` | Universe |
| `dim0` / `dim1` | `Dim0`, `Dim1` | `Dim0`, `Dim1` | Interval endpoints |
| `dimVar` | dimension in `Ix` | `Var` (at `TpDim`) | Dimension variable |
| `coe` | `Coe` (head) | `Coe` | Coercion |
| `hcom` | `HCom` (head) | `HCom` | Homogeneous composition |
| `com` | `Com` (head) | `Com` | Heterogeneous composition |
| `fhcom` | `FHCom` | `FHCom` (in domain) | Fibrant hcom (type-level) |
| `boxEl` | `Box` | `Box` | Box introduction |
| `capEl` | `Cap` (frame) | `Cap` | Cap elimination |
| `vtype` | `V` | `CodeV` | V-type (univalence) |
| `vin` | `VIn` | `VIn` | V-type introduction |
| `vproj` | `VProj` (frame) | `VProj` | V-type projection |
| `sub` | (via `Restrict`) | `Sub` | Subtype/restriction |
| `subIn` | (implicit) | `SubIn` | Subtype introduction |
| `subOut` | `RestrictForce` (frame) | `SubOut` | Subtype elimination |

---

## redtt-Only Constructors

Features specific to redtt's design:

| Constructor | redtt Form | Description |
|-------------|------------|-------------|
| `lit` | `Var` (named) | String literals (redtt uses named globals) |
| `ghcom` | `GHCom` | Generalized hcom (for non-strict Kan) |
| `gcom` | `GCom` | Generalized com |
| `ext` | `Ext` | Extension types (n-ary path abstraction) |
| `extLam` | `ExtLam` | Extension lambda |
| `extApp` | `ExtApp` (frame) | Extension application |
| — | `Restrict` / `RestrictThunk` | Restriction types (cofibration guards) |
| — | `Data` / `Intro` | User-defined data types |
| — | `Elim` (frame) | Data type elimination |
| — | `FortyTwo` | Internal placeholder |
| — | `twin` | Twin variables (for two-level TT) |
| — | `Meta` | Metavariables |

### redtt's Unique Architecture

1. **Spine-based application**: redtt uses `(head, spine)` pairs where `head` can be `Coe`, `HCom`, `Com`, `GHCom`, `GCom` and `spine` is a list of frames (`FunApp`, `ExtApp`, `Fst`, `Snd`, `VProj`, `Cap`, `Elim`, `RestrictForce`).

2. **Extension types** (`Ext`): Multi-dimensional path types with explicit boundary systems. cooltt handles this differently through the type system.

3. **Generalized composition**: `GHCom` and `GCom` handle types without strict Kan structure by expanding the composition.

4. **Data types**: redtt has first-class `Data` and `Intro` constructors for user-defined inductive types.

---

## cooltt-Only Constructors

Features specific to cooltt's design:

| Constructor | cooltt Form | Description |
|-------------|-------------|-------------|
| `nat` / `zero` / `suc` | `Nat`, `Zero`, `Suc` | Natural numbers |
| `natElim` | `NatElim` | Nat eliminator |
| `circle` / `base` / `loop` | `Circle`, `Base`, `Loop` | Circle HIT |
| `circleElim` | `CircleElim` | Circle eliminator |
| — | `Signature` / `Struct` / `Proj` | First-class records |
| — | `CodeNat`, `CodeCircle`, `CodeUniv` | Universe codes |
| — | `CodePi`, `CodeSg`, `CodeSignature` | Type codes |
| — | `CodeExt` | Extension type code |
| — | `ElIn` / `ElOut` | El type intro/elim |
| — | `Prf` | Proof term (for cofibrations) |
| — | `CofSplit` | Cofibration case split |
| — | `ForallCof` | Universal cofibration |
| — | `Global` | Global references |
| — | `Ann` | Type annotations |
| — | `ESub` | Explicit substitutions |

### cooltt's Unique Architecture

1. **Stable vs Unstable codes**: cooltt distinguishes type codes that are stable under dimension substitution (`stable_code`: `Pi`, `Sg`, `Signature`, `Ext`, `Nat`, `Circle`, `Univ`) from unstable ones (`unstable_code`: `HCom`, `V`).

2. **El types**: Explicit `ElIn`/`ElOut` for moving between codes and their denotations.

3. **First-class records**: `Signature`, `Struct`, `Proj` for dependent record types (not present in redtt).

4. **Built-in HITs**: `Nat` and `Circle` are primitive rather than user-defined.

5. **Binding forms**: `BindSym` and `LetSym` for dimension probing during coercion.

---

## Lego-Specific Additions

Our implementation adds:

| Constructor | Description |
|-------------|-------------|
| `path` | Sugar for non-dependent path type (derived from `ext`) |
| `plam` | Path lambda (sugar for `extLam 1`) |
| `papp` | Path application (sugar for `extApp _ [r]`) |
| `refl` | Reflexivity (sugar) |
| `sys` | Explicit system representation |
| `hcomTube` | hcom with explicit tube list |
| `cof_top` / `cof_bot` / `cof_eq` / `cof_and` / `cof_or` | Explicit cofibration constructors |

---

## Cofibration Handling Comparison

| Feature | redtt | cooltt | Lego |
|---------|-------|--------|------|
| Cof type | Implicit in `face` | `Cof` with `Le`, `Join`, `Meet` | Explicit `cof_*` constructors |
| Faces | `('r, 'a) face` = `r × r × a` | `(cof * tm_clo)` | `(Expr × Expr)` pairs |
| Systems | `('r, 'a) system` = list of faces | `(cof * tm_clo) list` | `List (Expr × Expr)` |
| Restrict | `Restrict`, `RestrictThunk` | via `Sub` type | via `sub` |

---

## Type/Term Separation

| Aspect | redtt | cooltt | Lego |
|--------|-------|--------|------|
| Separation | Single `tm` type | `tp` vs `t` (syntax) | Single `Expr` type |
| Universe | `Univ {kind; lvl}` | `Univ` (type), `CodeUniv` (code) | `univ` with `Level` |
| El type | Implicit | Explicit `El`, `ElIn`, `ElOut` | Implicit |

---

## Design Decisions for Lego

Our `Expr` type combines features from both:

1. **From redtt**: Extension types, ghcom/gcom, restriction-style subtypes
2. **From cooltt**: Nat, Circle as primitive HITs, explicit cofibrations
3. **Unified**: Single `Expr` type (like redtt) without type/term stratification
4. **Simplified**: Direct constructors rather than spine-based (no frames)
5. **Sugar**: `path`/`plam`/`papp`/`refl` for common patterns

### What We Don't Have (Yet)

- `Data`/`Intro`/`Elim` (user-defined data types)
- `Signature`/`Struct`/`Proj` (first-class records)  
- `Meta` (metavariables for elaboration)
- `twin` (two-level type theory features)
- `Global` (we use `lit` for named references)
