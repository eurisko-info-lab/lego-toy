# Test Consolidation Plan

## Status: Phases 1-4 Complete ✓

### Phase 1: Create Shared Test Utilities ✅
- Created `test/lean/TestUtils.lean` with common test framework
- Added to lakefile as `TestUtils` library

### Phase 2: Migrate Test Files ✅
- Migrated TestGrammarInterp, TestComposition, TestIntegration, TestCodeGenComparison
- Removed ~95 lines of duplicate framework code

### Phase 3: Unified Test Runner ✅
- Created `lake exe lego-test-all` command
- Options: `--quick`, `--verbose`, `--help`
- Runs all 5 test suites with unified summary

### Phase 4: Improved Coverage ✅
- Added Unicode handling tests (3 tests)
- Added edge case tests (4 tests)
- Added rule composition tests (3 tests)
- Total tests: 159 → 169 (quick mode)

## Current Test Inventory

### Registered Test Executables (lakefile.lean)

| Executable | File | Tests | Status | Purpose |
|------------|------|-------|--------|---------|
| `lego-test` | Test.lean | 116 | ✅ Pass | Core library tests (Term, Iso, Rules, Attr, file parsing) |
| `lego-test-grammar` | TestGrammarInterp.lean | 15 | ✅ Pass | Grammar interpreter (char/token level, roundtrip, errors) |
| `lego-test-compose` | TestComposition.lean | 11 | ✅ Pass | Language/piece composition, inheritance, merging |
| `lego-test-pipeline` | TestIntegration.lean | 162 | ⚠️ 122 pass | Full pipeline (bootstrap, all files, targets) |
| `lego-test-codegen-compare` | TestCodeGenComparison.lean | 17 | ✅ Pass | Code generator comparison (Lean, cross-target, semantic) |
| `lego-test-cool` | TestCool.lean | ~50 | ✅ Pass | CoolTT library parsing |
| `lego-test-runtime` | TestRuntime.lean | ~5 | ✅ Pass | Runtime bootstrap system |
| `lego-test-minimal` | TestMinimalBootstrap.lean | ~10 | ✅ Pass | Minimal ASCII tokenizer |
| `lego-test-parse` | TestParseAll.lean | varies | ✅ Pass | Comprehensive file parsing |
| `test-grammar-driven` | TestGrammarDriven.lean | ~10 | ? | Grammar-driven pipeline |
| `test-codegen` | TestCodeGen.lean | ~10 | ? | Code generation tests |

### Unregistered Test Files (have `def main` but no lakefile entry)

| File | Lines | Purpose | Status |
|------|-------|---------|--------|
| LeanGrammarTest.lean | 140 | Lean grammar tests | Likely redundant |
| LeanParseTest.lean | 90 | Lean parsing tests | Redundant (left-recursion notes) |
| LeanParseAllTest.lean | 60 | Parse all Lean files | Likely redundant |
| QuickLeanTest.lean | 50 | Quick Lean tests | Redundant |
| SimpleParseTest.lean | 160 | Simple grammar tests | Educational/development |
| TokenDebug.lean | 80 | Token debugging | Development tool only |
| TestRosettaParse.lean | 100 | Rosetta parsing | Likely redundant |

## Analysis

### Overlap Analysis

1. **File Parsing Tests**: Heavy overlap between:
   - `Test.lean` (runLegoFileTests)
   - `TestParseAll.lean` (comprehensive file testing)
   - `TestIntegration.lean` (pipeline tests)
   - Multiple smaller files

2. **Grammar Tests**: Overlap between:
   - `TestGrammarInterp.lean` (new, comprehensive)
   - `LeanGrammarTest.lean` (old, redundant)
   - `SimpleParseTest.lean` (old, educational)

3. **Code Generation**: Overlap between:
   - `TestCodeGenComparison.lean` (new, comprehensive)
   - `TestCodeGen.lean` (older version)
   - `test-grammar-driven` (pipeline-focused)

### Test Framework Duplication

Every test file defines its own:
```lean
structure TestResult where
  name : String
  passed : Bool
  message : String := ""

def assertTrue (name : String) (cond : Bool) : TestResult := ...
def assertEq [BEq α] [Repr α] (name : String) (actual expected : α) : TestResult := ...
```

**Recommendation**: Extract to shared `test/lean/TestUtils.lean`

## Consolidation Recommendations

### Phase 1: Create Shared Test Utilities

Create `test/lean/TestUtils.lean`:
```lean
namespace Lego.Test

structure TestResult where
  name : String
  passed : Bool
  message : String := ""

def assertTrue (name : String) (cond : Bool) : TestResult := ...
def assertEq [BEq α] [Repr α] (name : String) (actual expected : α) : TestResult := ...
def assertSome (name : String) (opt : Option α) : TestResult := ...
def assertNone (name : String) (opt : Option α) : TestResult := ...
def assertContains (name : String) (s sub : String) : TestResult := ...

def printTestGroup (name : String) (tests : List TestResult) : IO (Nat × Nat) := ...
def runTests (name : String) (groups : List (String × List TestResult)) : IO Unit := ...

-- Common helpers
def String.containsSubstr (s sub : String) : Bool := (s.splitOn sub).length > 1
```

### Phase 2: Consolidate Core Tests

**Keep as primary suites:**
1. `lego-test` - Core library (116 tests)
2. `lego-test-grammar` - Grammar interpreter (15 tests)  
3. `lego-test-compose` - Composition (11 tests)
4. `lego-test-pipeline` - Integration (162 tests)
5. `lego-test-codegen-compare` - Code generation (17 tests)

**Deprecate/Remove:**
- `LeanGrammarTest.lean` → covered by TestGrammarInterp
- `LeanParseTest.lean` → covered by TestIntegration
- `LeanParseAllTest.lean` → covered by TestParseAll
- `QuickLeanTest.lean` → covered by Test.lean
- `TokenDebug.lean` → development tool, not a test

**Keep for specialized use:**
- `TestCool.lean` - CoolTT-specific tests
- `TestMinimalBootstrap.lean` - Minimal tokenizer tests
- `TestRuntime.lean` - Bootstrap verification

### Phase 3: Reorganize Test Structure

```
test/
├── lean/
│   ├── TestUtils.lean           # Shared test framework (NEW)
│   ├── Test.lean                # Core library tests (keep, refactor to use TestUtils)
│   ├── TestGrammarInterp.lean   # Grammar interpreter (keep)
│   ├── TestComposition.lean     # Composition tests (keep)
│   ├── TestIntegration.lean     # Pipeline integration (keep)
│   ├── TestCodeGenComparison.lean # Code gen comparison (keep)
│   ├── TestCool.lean            # CoolTT-specific (keep)
│   ├── TestRuntime.lean         # Bootstrap verification (keep)
│   ├── TestMinimalBootstrap.lean # Minimal tokenizer (keep)
│   └── deprecated/              # Move deprecated tests here
│       ├── LeanGrammarTest.lean
│       ├── LeanParseTest.lean
│       └── ...
└── lego/
    └── (existing test .lego files)
```

### Phase 4: Improve Test Quality

#### 1. Add Missing Coverage

**Grammar Interpreter (TestGrammarInterp.lean):**
- [ ] More unicode handling tests
- [ ] Precedence/associativity tests
- [ ] Larger grammar roundtrips

**Composition (TestComposition.lean):**
- [ ] Diamond inheritance tests
- [ ] Rule precedence in composed languages
- [ ] Grammar conflict resolution tests

**Integration (TestIntegration.lean):**
- [ ] Fix 40 failing Cubical tests or mark as expected
- [ ] Add transformation chain tests (lego → rosetta → targets)
- [ ] Test error propagation through pipeline

**Code Generation (TestCodeGenComparison.lean):**
- [ ] AST equivalence tests (not just substring)
- [ ] Roundtrip: generate → compile → run
- [ ] Cross-target semantic equivalence

#### 2. Improve Error Messages

Current:
```
  ✗ expected {expected}, got {actual}
```

Improved:
```
  ✗ test_name FAILED
    Expected: {expected}
    Actual:   {actual}
    Location: file.lean:123
    Context:  (relevant context from test setup)
```

#### 3. Add Test Categories/Tags

```lean
inductive TestCategory
  | unit      -- Unit tests
  | parsing   -- Parsing tests
  | codegen   -- Code generation
  | semantic  -- Semantic/rule tests
  | slow      -- Slow tests (skip in quick mode)
```

#### 4. Add Performance Benchmarks

```lean
def benchmarkParsing : IO Unit := do
  let start ← IO.monoMsNow
  -- parse all files
  let elapsed := (← IO.monoMsNow) - start
  IO.println s!"Parsing benchmark: {elapsed}ms"
```

## Proposed Unified Test Command

```bash
# Run all fast tests (default)
lake exe lego-test-all

# Run specific category
lake exe lego-test-all --category=parsing
lake exe lego-test-all --category=codegen

# Run including slow tests
lake exe lego-test-all --include-slow

# Run with verbose output
lake exe lego-test-all --verbose

# Run specific test file
lake exe lego-test-all --file=TestGrammarInterp
```

## Migration Path

### Completed
1. ✅ **Phase 1**: Created TestUtils.lean, added to lakefile
2. ✅ **Phase 2**: Migrated new test files to use TestUtils
3. ✅ **Phase 3**: Created unified test runner (`lego-test-all`)
4. ✅ **Phase 4**: Added Unicode, edge case, and rule composition tests

### Remaining
5. **Week 5**: Migrate legacy Test.lean to use TestUtils
6. **Week 6**: Deprecate/remove redundant test files
7. **Week 7**: Add more comprehensive coverage (pending)

## Success Metrics

- Single entry point for all tests
- No duplicate test framework code
- All tests pass (or are marked as expected failures)
- Clear categorization of test types
- < 30 second total test time for unit tests
- Comprehensive coverage report

## Known Issues to Address

1. **Cubical files failing**: 40 tests in TestIntegration fail on Cubical examples
   - Action: Either fix Cubical grammar or mark as expected failures

2. **Roundtrip limitations**: Some print functions return empty
   - Action: Document as known limitation, test what works

3. **Runtime initialization spam**: Every test prints "[Lego] Loading..."
   - Action: Add quiet mode or singleton runtime

4. **Test isolation**: Tests may affect each other through shared state
   - Action: Reset state between test groups

## Files to Delete After Consolidation

After verification that all functionality is covered:
- `test/lean/LeanGrammarTest.lean`
- `test/lean/LeanParseTest.lean`
- `test/lean/LeanParseAllTest.lean`
- `test/lean/QuickLeanTest.lean`
- `test/lean/TokenDebug.lean`
- `test/lean/TestRosettaParse.lean`

Total reduction: ~600 lines of duplicate code
