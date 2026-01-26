# Lego Test Plan

This document outlines the comprehensive testing strategy for the Lego meta-language system.

## Test Categories

### 1. Grammar Interpreter Unit Tests (`TestGrammarInterp.lean`)

Test the core grammar interpreter (Interp.lean) at both levels:

#### 1.1 Character-Level Grammar (Lexer)
- **Parsing tests**: literal matching, alternatives, sequences, kleene star, optional
- **Print tests**: roundtrip token → string
- **Error handling**: location tracking, error messages

#### 1.2 Token-Level Grammar (Parser)
- **Parsing tests**: references, sequences, alternatives, star, optional, node construction
- **Print tests**: AST → token stream
- **Roundtrip tests**:
  - `parse(print(ast)) == ast` (parse-of-print)
  - `print(parse(input)) == normalized(input)` (print-of-parse)
- **Error handling**: detailed parse errors with location, expected vs actual

#### 1.3 Error Cases
- Unexpected token
- Missing expected token
- Ambiguous grammar
- Infinite loop detection
- Malformed AST for printing

### 2. Language/Piece Composition Tests (`TestComposition.lean`)

Test the language inheritance and piece composition system:

#### 2.1 Basic Inheritance
- Single parent inheritance
- Multi-parent inheritance (diamond)
- Production override
- Production extension

#### 2.2 Piece System
- Piece definition parsing
- Piece inclusion in language
- Piece production extraction
- Token vs grammar pieces

#### 2.3 Error Cases
- Circular inheritance detection
- Missing parent language
- Duplicate production names
- Ambiguous productions
- Invalid piece reference

### 3. Integration Tests (`TestIntegration.lean`)

Test the full pipeline from source to output:

#### 3.1 Bootstrap Chain
- Hardcoded grammar parses Bootstrap.lego
- Bootstrap.lego grammar parses Lego.lego
- Lego.lego grammar parses all other .lego files

#### 3.2 File Parsing Coverage
```
.lego files:
  - test/lego/Bootstrap.lego
  - src/Lego/Lego.lego
  - examples/Arith.lego
  - examples/Lambda.lego
  - examples/K.lego
  - examples/INet.lego
  - examples/AI/*.lego
  - examples/Quantum/*.lego
  - examples/Cubical/**/*.lego

.rosetta files:
  - src/Rosetta/Rosetta.lego
  - src/Lego/*.rosetta

Target language files:
  - src/Rosetta/Lean.lego
  - src/Rosetta/Scala.lego
  - src/Rosetta/Haskell.lego
  - src/Rosetta/Rust.lego
```

#### 3.3 Roundtrip Tests
For each grammar:
- Parse file → AST
- Print AST → string
- Parse string → AST'
- Verify AST == AST' (modulo whitespace normalization)

### 4. Code Generator Tests (`TestCodeGen.lean`)

Compare generated code against reference implementations:

#### 4.1 Lean Generation
- Compare `lake exe tolean --grammar Bootstrap.lego` output with `generated/*.lean`
- Verify structural equivalence
- Test that generated code compiles

#### 4.2 Multi-Target Generation
- Generate same source to Lean, Scala, Haskell, Rust
- Verify each target produces valid syntax
- Check that key structures (ADTs, functions) are present

### 5. Performance Tests (`TestPerformance.lean`)

Benchmark critical operations:
- Parse time for Bootstrap.lego
- Parse time for large files (Cubical examples)
- Normalization time with many rules

## Test Infrastructure

### Test Framework
```lean
-- Enhanced test result with timing
structure TestResult where
  name : String
  passed : Bool
  message : String := ""
  duration : Nat := 0  -- milliseconds
  location : Option String := none

-- Test categories for organization
inductive TestCategory
  | Unit : TestCategory
  | Integration : TestCategory
  | Performance : TestCategory
```

### Test Runner
```bash
# Run all tests
lake exe lego-test-all

# Run specific categories
lake exe lego-test-grammar     # Grammar interpreter tests
lake exe lego-test-compose     # Composition tests
lake exe lego-test-pipeline    # Integration/pipeline tests
lake exe lego-test-codegen     # Code generator tests
```

## Coverage Goals

| Category | Current | Target |
|----------|---------|--------|
| Grammar parsing | Partial | Full |
| Grammar printing | Minimal | Full |
| Roundtrip | None | Full |
| Composition | Basic | Full error coverage |
| File parsing | ~50 files | All .lego/.rosetta |
| Code generation | None | Lean reference comparison |

## Implementation Priority

1. **Grammar roundtrip tests** - Critical for correctness
2. **Error handling tests** - Essential for usability
3. **File parsing coverage** - Prevents regressions
4. **Code generator comparison** - Ensures generated code matches reference
5. **Performance benchmarks** - Optimization feedback
