# Lexer Unification

**Goal**: Make the Token piece in Bootstrap.lego actually drive the lexer, replacing the hardcoded `Bootstrap.tokenize`.

## Status: Phase 1 Complete ✅

**Decision**: Option 1 - Extend Grammar Algebra (most principled)

### Implemented Grammar Algebra Extensions

The `GrammarF` type now includes PEG-style operators for proper lexer semantics:

| Construct | Syntax | Description |
|-----------|--------|-------------|
| **cut** | `!g` | Commit point - no backtracking past this on success |
| **ordered** | `g1 / g2` | PEG ordered choice - first match wins (left-biased) |
| **longest** | `#longest[g1, g2, ...]` | Maximal munch - try all, pick longest match |

### Files Modified

- [src/Lego/Algebra.lean](src/Lego/Algebra.lean) - Added `cut`, `ordered`, `longest` to `GrammarF`
- [src/Lego/Interp.lean](src/Lego/Interp.lean) - Implemented lexer/parser semantics for new constructs
- [src/Lego/Loader.lean](src/Lego/Loader.lean) - AST → GrammarExpr conversion for new constructs
- [src/Lego/Validation.lean](src/Lego/Validation.lean) - Reference extraction for new constructs
- [generated/BootstrapGrammar.lean](generated/BootstrapGrammar.lean) - Grammar piece for parsing new syntax
- [test/Bootstrap.lego](test/Bootstrap.lego) - Grammar syntax and Token piece updated

### Example Usage in Bootstrap.lego

```lego
-- Multi-character operators using #longest for proper maximal munch
-- This ensures "::=" is matched as one token, not ":" ":" "="
multiop ::= #longest[
  ':' ':' '=',    -- ::=
  '=' 'I' '=',    -- =I=
  '~' '~' '>',    -- ~~>
  ':' '=',        -- :=
  '~' '>',        -- ~>
  '-' '>',        -- ->
  '<' '-',        -- <-
  '=' '>',        -- =>
  '@' '@'         -- @@
] ;

-- Ordered choice for disambiguation
expr ::= ident "/" alt | alt ;  -- PEG: try ident first, then alt
```

## Remaining Work (Phase 2)

| Feature | Status | Notes |
|---------|--------|-------|
| Character literals `'x'` | ✓ Handled | Already in Token piece |
| Multi-char operators | ✓ Ordered | Using op2/op3 with manual priority |
| Special syntax `<ident>` | ✓ Handled | In Token piece |
| Comments `--` | ✓ Handled | In Token piece |
| Greek letters | ✓ Handled | Explicit list (could use Unicode categories) |
| **Regenerate tokenizer** | ✓ Done | `lake exe tolean --tokenizer` |
| **Regenerate grammar** | ✓ Done | `lake exe tolean --grammar` |
| **hashident token** | ✓ Added | `#longest` tokenizes as single token |
| **Use in user grammars** | ⏳ TODO | Runtime parsing needs investigation |

### Bootstrap Updates

Added `hashident` production to Token piece:
```lego
hashident ::= '#' alpha (alpha | digit)* ;
```

Updated `mainTokenProds` priority order in ToLean.lean to include `hashident` before `ident`.

## Mathematical Foundation

The extended grammar algebra remains algebraically principled:

| Construct | Algebra |
|-----------|---------|
| `alt` (\|) | Coproduct (unordered, symmetric) |
| `ordered` (/) | Left-biased coproduct (asymmetric) |
| `longest` | Maximal element under length ordering |
| `cut` | Commitment/continuation semantics |

The key insight: **tokenization is a special case of parsing** where:
- Input is `CharStream` instead of `TokenStream`
- Output is a single token (not an AST)
- `longest` provides proper maximal munch semantics
- `ordered` provides PEG disambiguation
