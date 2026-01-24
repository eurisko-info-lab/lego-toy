# Visitor Pattern Refactoring Guide

## Goal

**Make `Expr` a black box** outside of `Core.lean` and `Visitor.lean`. No module should pattern match on Expr constructors directly.

## Philosophy

The more math, the less code and bugs. `Expr` is an **initial algebra** (free structure). The visitor pattern extracts its **functor** (`shape`) so operations can be defined generically.

## The Pattern

### Before (Bad)
```lean
partial def myOperation : Expr → Expr
  | .ix n => ...
  | .lam body => .lam (myOperation body)
  | .app f x => .app (myOperation f) (myOperation x)
  | .pi dom cod => .pi (myOperation dom) (myOperation cod)
  -- ... 60+ more cases
```

### After (Good)
```lean
def myOperation (e : Expr) : Expr :=
  e.traverse myOp 0
-- OR
def myOperation (e : Expr) : Expr :=
  e.normalizeStep fuel extraReduce Expr.subst substDim0
```

## Key Abstractions in Visitor.lean

### 1. `Expr.shape : Expr → ExprShape`
Extracts children and reconstruction function. This is the **only place** that knows all constructors.

```lean
structure ExprShape where
  children : List Child      -- subexpressions with binding info
  reconstruct : List Expr → Expr  -- rebuild from transformed children
```

### 2. `Expr.traverse (op : VisitorOp) (depth : Nat) (e : Expr) : Expr`
Generic traversal. Define `onAtom` for leaves (variables), get recursion for free.

### 3. `Expr.tryBetaReduce`
Knows how to reduce: app/lam, papp/plam, fst/pair, snd/pair, let, subOut/subIn.

### 4. `Expr.normalizeStep fuel extraReduce substTerm substDim`
Generic normalizer. Pass domain-specific reductions, get full normalization.

## Refactoring Checklist

For each module, find and transform:

### Pattern 1: Pure Traversal (shift, subst, rename, collect)
**Signature**: `Expr → Expr` or `Expr → SomeResult`

| Before | After |
|--------|-------|
| `partial def freeVars (depth : Nat) : Expr → List Nat` | `e.freeVars' depth` |
| `partial def shiftAbove (c d : Nat) : Expr → Expr` | `e.shiftAbove' c d` |
| `partial def subst (idx : Nat) (val : Expr) : Expr → Expr` | `e.subst' idx val` |
| `partial def substDim0 (d : Expr) : Expr → Expr` | `e.substDim0' d` |
| `partial def occurs (name : GName) : Expr → Bool` | `e.occursName name.name` |
| `partial def applyMetas (st) : Expr → Expr` | `e.applyMetas' lookup` |

**How to convert**: Define a `VisitorOp` with `onAtom` handling the base cases.

### Pattern 2: Normalization (eval, whnf, normalize)
**Signature**: `Expr → Expr` with recursive calls after pattern match

| Before | After |
|--------|-------|
| Manual match on `.app`, `.papp`, `.fst`, etc. with post-reduction | `e.normalizeStep fuel extraReduce substTerm substDim` |

**How to convert**: 
1. Extract domain-specific reductions into `extraReduce : Expr → Option Expr`
2. Call `e.normalizeStep fuel extraReduce Expr.subst substDim0`

### Pattern 3: Structural Query (isApp?, asLam?, etc.)
**Signature**: Match to extract components

| Before | After |
|--------|-------|
| `match e with \| .app f x => ... \| _ => ...` | `match e.asApp? with \| some (f, x, mk) => ... \| none => ...` |
| `match e with \| .lam body => ... \| .plam body => ...` | `match e.asLam? with \| some (body, mk) => ...` |

### Pattern 4: Domain-Specific Match (Kan ops, type formers)
**These are OK to keep** - they match on domain-specific constructors:
- `reduceKan` matches `.coe`, `.hcom`, `.hcomTube`, `.com`
- `reduceCoe` matches `.univ`, `.pi`, `.sigma`, `.path`
- Type checking matches type formers

**Rule**: If you're matching to **dispatch domain logic**, keep it. If you're matching to **recurse into children**, use `shape`.

## Available Visitor Operations

```lean
-- Traversal
e.traverse op depth           -- generic map with VisitorOp
e.mapBottomUp f               -- apply f to all subexprs

-- Variable operations
e.shiftAbove' cutoff delta    -- shift free vars
e.shift'                      -- shift by 1
e.subst' idx val              -- substitute
e.subst0' val                 -- substitute at 0
e.substDim0' d                -- dimension substitution
e.renameVars' ren             -- rename by mapping

-- Queries
e.freeVars' depth             -- collect free vars
e.collectFreeVars             -- free vars at depth 0
e.freeIn' n                   -- is var n free?
e.hasFree n                   -- alias for freeIn'
e.occursName name             -- does literal occur?

-- Accessors (return Option)
e.asApp?                      -- (f, x, rebuild)
e.asLam?                      -- (body, rebuild)
e.asProj?                     -- (p, rebuild, select)
e.asPair?                     -- (a, b)
e.asLet?                      -- (ty, val, body)
e.asSubOut?                   -- inner expr
e.asSubIn?                    -- inner expr

-- Normalization
e.tryBetaReduce subst substDim  -- one beta step
e.normalizeStep fuel extra subst substDim  -- full normalize
e.normalizeWith fuel reduce     -- simple normalize with reducer
e.invertForSpine vars           -- Miller pattern inversion
e.applyMetas' lookup            -- apply meta solutions
```

## Module Status

| Module | Status | Expr Matches | Notes |
|--------|--------|--------------|-------|
| `Core.lean` | Keep | 28 | Defines Expr, allowed to match |
| `Visitor.lean` | Keep | 30 | Defines shape/traverse, allowed |
| `Kan.lean` | ✅ Done | 0 | Uses normalizeStep with reduceKan |
| `Conversion.lean` | ✅ Done | 4 | whnf uses visitor; 4 remaining in equate_neutral (structural) |
| `Semantics.lean` | ✅ Done | 0 | eval uses tryBetaReduce + shape |
| `FHCom.lean` | ✅ Done | 0 | normalizeFHCom uses normalizeStep |
| `VType.lean` | ✅ Done | 4 | normalizeVExpr uses normalizeStep; 4 in tests |
| `Splice.lean` | ✅ Done | 0 | substSpliced uses traverse |
| `GlobalEnv.lean` | ✅ Done | 12 | normalizeWithGlobals uses whnfStep; 12 in type-directed infer/check |
| `Unify.lean` | Partial | 9 | freeVars/occurs/applyMetas done; some remain |
| `Elaborate.lean` | TODO | 10 | Type-directed, may need matches |
| `SubType.lean` | TODO | 9 | Domain-specific |
| `Domain.lean` | TODO | 8 | Domain operations |
| `Datatype.lean` | Check | 2 | May be domain-specific |
| `Quote.lean` | OK | 0 | No Expr matches |
| `TypeAttrs.lean` | OK | 0 | No Expr matches |
| `Cofibration.lean` | OK | 0 | No Expr matches |
| `ExtType.lean` | OK | 0 | No Expr matches |
| `Glue.lean` | OK | 0 | No Expr matches |
| `HIT.lean` | OK | 0 | No Expr matches |

**Completed**: Kan, Conversion, Semantics, FHCom, VType, Splice, GlobalEnv
**Remaining**: Elaborate (10), SubType (9), Domain (8), Unify (9), Datatype (2)

## How to Add New Operations

1. Check if it's a pure traversal → Define `VisitorOp`, use `traverse`
2. Check if it's normalization → Use `normalizeStep` with custom `extraReduce`
3. Check if it needs structural query → Add accessor to Visitor.lean
4. If truly domain-specific match → Keep the match, but only for domain constructors

## Adding New Expr Constructors

When adding a new constructor to `Expr`:

1. Add case to `Expr.shape` in Visitor.lean (specify children and binder info)
2. Add case to `Expr.tryBetaReduce` if it has reduction rules
3. Add accessor (`asNewThing?`) if modules need to query it
4. **No other modules need changes** - they use shape/traverse

This is the key benefit: **extensibility is localized**.
