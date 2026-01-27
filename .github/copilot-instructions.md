# Copilot Instructions for Lego-Toy

## HARD RULES (NO EXCEPTIONS)

1. **Grammar Loading Order is FIXED**: The hardcoded bootstrap grammar is used ONLY to load Bootstrap.lego. Once loaded, Bootstrap.lego's grammar REPLACES the hardcoded version. Then Lego.lego is loaded, providing the full grammar to parse any other .lego file. This order is immutable across ALL execution paths including tests.

2. **Use ./tmp NOT /tmp**: Always use the local `./tmp` directory for temporary files, never system `/tmp`.

3. **Each Language Owns Its Tokenizer**: Each language defines its own tokenizer through inheritance. Bootstrap.lego defines the minimum lexer to parse Lego.lego. Never modify Bootstrap.lego or the hardcoded tokenizer to please another .lego file. If a language needs different tokenization, it should define its own token rules in its own .lego file.

4. **Keywords Are FOLLOW-Conflict Literals**: Keywords are determined by FOLLOW conflict analysis: a literal needs to be a keyword when it follows a reference that can transitively end with a star (greedy). This prevents the star from consuming the keyword delimiter. Example: `"in"` in `letinvalue "in" expr` where `letinvalue` ends with `appitem*`. Not ALL grammar literals become keywords.

## Project Overview

Lego is a self-hosting meta-language for defining domain-specific languages (DSLs) using grammar-driven rewriting. It compiles to multiple target languages (Lean, Scala, Haskell, Rust).

## Architecture

### Bootstrap Chain (FIXED ORDER - NO EXCEPTIONS)
```
Hardcoded Grammar (generated/*.lean)
    → parses test/lego/Bootstrap.lego ONLY
    → Bootstrap.lego grammar REPLACES hardcoded
    
Bootstrap.lego grammar
    → parses src/Lego/Lego.lego  
    → Lego.lego grammar becomes the active grammar
    
Lego.lego grammar
    → parses ALL other *.lego files
```

**Critical**: Bootstrap.lego defines SYNTAX. Lego.lego defines SEMANTICS.

### File Types

| Extension | Purpose | Parser |
|-----------|---------|--------|
| `.lego` | Grammar + rules definitions | Runtime (Lego.lego grammar) |
| `.rosetta` | IR for multi-target codegen | Pipeline (similar grammar) |
| `.lean` | Lean 4 source | Lake |

### Key Directories

| Directory | Purpose |
|-----------|---------|
| `src/Lego/` | Core library (hand-coded Lean + .rosetta specs) |
| `src/Rosetta/` | Rosetta IR and code generators |
| `generated/` | Bootstrap files (CHECKED IN, regenerated via bootstrap.sh) |
| `tools/` | Code generation pipelines and utilities |
| `test/lego/` | Test .lego files including Bootstrap.lego |
| `examples/` | Example DSLs (Arith, Lambda, Cubical, Quantum, AI) |

## Grammar Layers

### Bootstrap.lego (test/lego/Bootstrap.lego)
Defines the meta-syntax for .lego files:
- `lang Name := ...` - language declaration
- `token TokenName ... ;` - lexer rules  
- `piece PieceName ... ;` - grammar pieces with productions
- `rule name : pattern ~> template ;` - rewrite rules
- `type name : pattern : type when ... ;` - typing judgments
- `test "name" : input ~~> expected ;` - test cases

### Lego.lego (src/Lego/Lego.lego)
Extends Bootstrap with semantic constructs:
- `CorePrimitives` - Univ, Var, App, Subst
- `Binders` - Lam with beta reduction
- `Products` - Pair, Fst, Snd
- `ADTDef` - algebraic data types
- `RewriteRules` - pattern → template transforms
- `Judgments` - typing with premises
- `Modules` - module/import system

## Common Tasks

### Adding new grammar features
1. If it's core syntax (affects how .lego files are written): modify `test/lego/Bootstrap.lego`
2. If it's semantic (new term forms, rules): modify `src/Lego/Lego.lego`
3. Run `./scripts/bootstrap.sh` after Bootstrap.lego changes
4. Run tests: `lake exe lego-test`

### Bootstrap regeneration
```bash
./scripts/bootstrap.sh        # Regenerate generated/*.lean
./scripts/bootstrap.sh --check  # Verify canonical (CI)
```

The bootstrap must reach **fixpoint**: `tolean(Bootstrap.lego) = generated/*.lean`

### Running tests
```bash
lake exe lego-test      # Main tests (116 tests)
lake exe lego-test-red  # Cubical/RedTT tests (823 tests)
```

### Code generation pipelines
```bash
lake exe pipeline src/Rosetta/rosetta2lean.lego  # Run transformation pipeline
lake exe multi-target src/Lego/*.rosetta -t lean  # Generate Lean from Rosetta
lake exe tolean --grammar file.lego              # Generate Lean parser
```

## Code Patterns

### Term representation
```lean
inductive Term where
  | var : String → Term           -- $x variable
  | lit : String → Term           -- "literal"
  | con : String → List Term → Term  -- (Constructor args...)
```

### Rule syntax in .lego files
```
rule name : (pattern $x $y) ~> (template $x $y) ;
rule guarded : (pat $x) ~> (tmpl $x) when $x : SomeType ;
```

### Grammar productions
```
piece MyPiece
  expr ::= "keyword" term → node
         | expr "+" expr → add ;
```

## Important Invariants

1. **Bootstrap must be self-hosting**: generated files parse Bootstrap.lego which regenerates identical files
2. **Runtime libraries are equivalent**: Lean/Scala/Haskell/Rust runtimes provide same API
3. **Hand-coded ↔ Generated**: src/Lego/*.lean should match generated from *.rosetta

## Debugging Tips

- Parse failure? Check if grammar piece defines the construct
- "Unknown namespace"? Check imports and generated/ files
- Bootstrap fails? Run `git checkout -- generated/` to restore, then debug
- Token issues? Check `mainTokenProds` order in ToLean.lean (longer tokens before shorter)

## File Naming Conventions

- `Foo.lean` - Lean implementation
- `Foo.rosetta` - Rosetta IR spec (generates to multiple targets)
- `Foo.lego` - Lego grammar/rules definition
- `foo2bar.lego` - Transformation from foo format to bar format
