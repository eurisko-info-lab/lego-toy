# GenTime + Runtime Architecture

## Overview

This architecture separates language-specific concerns into two layers:

1. **GenTime.<lang>** - Compile-time syntax templates loaded by the code generator
2. **Runtime.<lang>** - Runtime library linked by generated code

This allows the **code generator to be language-agnostic** - it only works with Rosetta AST and GenTime rules.

## Directory Structure

```
src/
├── Rosetta/
│   ├── GenTime.lego          # Lean 4 syntax templates
│   ├── GenTime.scala.lego    # Scala syntax templates  
│   ├── GenTime.hs.lego       # Haskell syntax templates
│   └── GenTime.rs.lego       # Rust syntax templates
│
├── Runtime/
│   ├── Lean/
│   │   └── Runtime.lean      # ~250 lines - parsing engine, IO, HashMap
│   ├── Scala/
│   │   └── Runtime.scala     # ~300 lines - same API
│   ├── Haskell/
│   │   └── Runtime.hs        # ~280 lines - same API
│   └── Rust/
│       └── runtime.rs        # ~400 lines - same API
```

## GenTime Templates

Each GenTime file defines rewrite rules that map Rosetta constructs to target syntax:

```
-- Rosetta construct      Target syntax
(inductive $name $ctors)  ~~>  "inductive $name where..."     -- Lean
(inductive $name $ctors)  ~~>  "sealed trait $name ..."       -- Scala
(inductive $name $ctors)  ~~>  "data $name = ..."             -- Haskell
(inductive $name $ctors)  ~~>  "pub enum $name { ... }"       -- Rust
```

### Key Construct Categories

| Category | Rosetta | Lean | Scala | Haskell | Rust |
|----------|---------|------|-------|---------|------|
| ADT | `inductive` | `inductive ... where` | `sealed trait` + `case class` | `data ... =` | `enum` |
| Function | `def` | `def ... :=` | `def ... = {}` | `name :: ... =` | `fn ... -> {}` |
| Match | `match` | `match ... with` | `... match {}` | `case ... of` | `match ... {}` |
| Option | `some/none` | `some/none` | `Some/None` | `Just/Nothing` | `Some/None` |
| Import | `import` | `import` | `import ._` | `import` | `use ...::*` |

## Runtime Library

Each Runtime library provides the same core API:

### Types
- `Term` - Universal AST node (Var, Lit, Con)
- `GrammarExpr` - Grammar algebra (lit, ref, seq, alt, star, plus, opt, node)
- `Production` - Named grammar rule
- `Rule` - Rewrite rule (lhs → rhs)
- `Token` - Lexer tokens

### Parsing Engine
- `parseGrammar(fuel, prods, g, state) → ParseResult` - Packrat parser
- `findProduction(prods, name)` - Lookup production
- `combineSeq(t1, t2)` - Sequence combination
- `wrapNode(name, t)` - Constructor wrapping

### IO Operations
- `readFile(path) → String/IO String`
- `writeFile(path, content)`
- `fileExists(path) → Bool`

### Term Utilities
- `matchPattern(pattern, term) → Option<Bindings>`
- `substitute(bindings, term) → Term`
- `applyRule(rule, term) → Option<Term>`
- `normalize(rules, term, fuel) → Term`

## Code Generation Flow

```
┌─────────────────────────────────────────────────────────────────┐
│                     Code Generator (Language-Agnostic)          │
├─────────────────────────────────────────────────────────────────┤
│  1. Parse .rosetta file → Rosetta AST                          │
│  2. Load GenTime.<lang> rules for target language              │
│  3. Transform: Rosetta AST → Target AST (using GenTime rules)  │
│  4. Pretty-print Target AST (generic indentation/newlines)     │
│  5. Prepend: import Runtime.<lang>                             │
└─────────────────────────────────────────────────────────────────┘
         │
         ▼
┌─────────────────────────────────────────────────────────────────┐
│                        Generated Code                           │
├─────────────────────────────────────────────────────────────────┤
│  import Lego.Runtime  -- or use lego_runtime::*; etc.          │
│                                                                 │
│  -- Types (generated from .rosetta type declarations)          │
│  inductive Term where ...                                      │
│                                                                 │
│  -- Functions (generated from .rosetta function definitions)   │
│  def transform (t : Term) : Term := ...                        │
│                                                                 │
│  -- Rules (generated from .rosetta ~~> rules)                  │
│  def rule1 := Rule.new "rule1" (lhs) (rhs)                    │
└─────────────────────────────────────────────────────────────────┘
         │
         ▼ links at compile/runtime
┌─────────────────────────────────────────────────────────────────┐
│                      Runtime Library                            │
├─────────────────────────────────────────────────────────────────┤
│  parseGrammar, lexGrammar, normalize, matchPattern, ...        │
│  IO operations, HashMap memoization                            │
└─────────────────────────────────────────────────────────────────┘
```

## Benefits

1. **No language-specific code in generator** - All syntax knowledge is in GenTime files
2. **Easy to add new languages** - Just create GenTime.<newlang>.lego + Runtime.<newlang>
3. **Separation of concerns**:
   - GenTime: Syntax/surface form
   - Runtime: Execution semantics
   - Generator: Pure transformation
4. **Self-hosting path clearer** - Bootstrap just needs GenTime rules for itself
5. **Testing simplified** - Each layer can be tested independently

## Coverage Analysis

### Before (with GenTime + Runtime)
- Generated code: Types + Rules + simple functions = ~38%
- Hand-crafted: parseGrammar, lexGrammar, IO, HashMap = ~62%

### After (with GenTime + Runtime)
- Generated code: Types + Rules + functions = ~38%
- Runtime library: parseGrammar, lexGrammar, IO, HashMap = ~62%
- **Total coverage: 100%** (generated + runtime)

The "gap" moves from "needs to be generated" to "provided by runtime" - which is the correct architecture since parsing/IO are genuinely target-specific.

## Implementation Status

### Phase 1: Foundation ✅
1. ✅ Create Runtime libraries for 4 languages (~1,500 lines total)
2. ✅ Create CodeGen.rosetta - abstract syntax for output
3. ✅ Create codegen2*.rosetta - rewrite rules using Cons/Nil syntax
4. ✅ Fix pipeline to parse .rosetta files correctly

### Phase 2: Lean Implementation ✅
5. ✅ CodeGen.lean - Frag AST with Inhabited, BEq, Repr
6. ✅ UnifiedCodeGen.lean - termToPatternFrag, termToExprFrag
7. ✅ Language-specific emitters: emitLeanRewriteRule, emitScalaADT, etc.
8. ✅ TargetLang enum for dispatch

### Phase 3: Pipeline Integration ✅
9. ✅ Modify GrammarDrivenPipeline to use UnifiedCodeGen
10. ✅ Wire up Frag → String rendering in pipeline via CodeGen.render
11. ✅ Add TargetLang.toUnified conversion
12. [ ] Remove duplicated termToLeanExpr/termToScalaExpr/etc. (can deprecate)

### Phase 4: Testing ✅
13. ✅ Test: generated code from CodeGen.rosetta works
14. [ ] Verify: Rosetta → Lean → compile → run (optional)
15. [ ] Remove deprecated code (optional cleanup)

