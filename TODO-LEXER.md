# TODO: Lexer Unification

**Goal**: Make the Token piece in Bootstrap.lego actually drive the lexer, replacing the hardcoded `Bootstrap.tokenize`.

## Current State

| Feature | Bootstrap.lego Token | Hardcoded `tokenize` |
|---------|---------------------|---------------------|
| Character literals `'x'` | ✗ Not handled | ✓ Special case |
| Multi-char operators `::=` `~>` `~~>` `:=` | ✗ Not handled | ✓ Hardcoded lookahead |
| Special syntax `<ident>` | ✗ Not handled | ✓ Special case |
| Comments `--` | ✗ Not handled | ✓ Stripped before tokenization |
| Greek letters | ✓ Explicit 48-char list | Uses `isUnicodeLetter` predicate |
| Unicode symbols | `→←↔⊕` only | Uses `isUnicodeSymChar` (larger set) |
| String escapes | `"` `\` `n` `t` `r` | Same |

## Options

### Option 1: Extend Grammar Algebra
Add lookahead/maximal munch constructs:
- `!g` - cut (already exists, for error recovery)
- Longest match semantics for token grammars

### Option 2: Add Multi-char Token Rules
```
token Token
  op ::= ':' ':' '=' → coloncoloneq
       | '~' '~' '>' → tildetildegt
       | '~' '>' → tildegt
       | ':' '=' → coloneq ;
```
Would need ordered choice (PEG-style) to prefer longer matches.

### Option 3: Accept the Gap
Token piece = specification, hardcoded = implementation.
Document the intended semantics in Bootstrap.lego, generate the hardcoded version.

## Missing from Bootstrap.lego Token

1. **Character literal** `char ::= '\'' charBody '\'' ;`
2. **Multi-char operators** with longest-match semantics
3. **Special syntax** `special ::= '<' ident '>' ;`
4. **Comments** `comment ::= '-' '-' linechar* ;`
5. **Whitespace** `ws ::= ' ' | '\t' | '\n' ;`

## Decision Needed

Which approach to pursue? The algebraic approach (Option 1) is most principled but requires grammar algebra extensions.
