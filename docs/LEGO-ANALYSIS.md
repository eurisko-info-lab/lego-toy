# Comprehensive Exploration Report: Lego Lean Codebase

I've completed a thorough analysis of the Lean code in `/home/patrick/IdeaProjects/lego/toy/`. Here's a detailed breakdown:

## 1. Overall Structure and Purpose

**Lego** is a **minimal language workbench** for defining and composing domain-specific languages (DSLs). The key insight is that **languages are algebras that compose via categorical pushouts**. The same grammar expression drives **bidirectional** parsing AND printing.

**Core Philosophy:**
- Everything is an **Iso** (partial isomorphism A ⇌ B)
- Grammar is data that can be interpreted at runtime
- The system is self-hosting: a grammar can parse grammars

**Code Organization (2,100+ lines total):**
- `Algebra.lean` (377 lines) - Core algebraic structures
- `Interp.lean` (470 lines) - Grammar interpretation engine (total with fuel)
- `Loader.lean` (605 lines) - Load/parse .lego files
- `Validation.lean` (359 lines) - Semantic validation
- `Laws.lean` (179 lines) - Algebraic laws: proven theorems + axioms
- `Bootstrap.lean` (56 lines) - Meta-grammar definition

---

## 2. Data Types and Core Structures

### The 5 Core Pieces (from Algebra.lean):

#### 1. `Iso A B` - Partial Isomorphism (atomic unit)
```lean
structure Iso (A B : Type) where
  forward  : A → Option B   -- parse/reduce
  backward : B → Option A   -- print/expand
```
- Composition: `f >>> g`
- Parallel: `f *** g` (products)
- Choice: `f ||| g` (coproducts)
- Symmetric: `~f` (flip directions)
- Alternative: `f <|> g` (fallback)

#### 2. `Term` - Universal AST
```lean
inductive Term where
  | var : String → Term              -- variables/identifiers
  | con : String → List Term → Term  -- constructors
  | lit : String → Term              -- string literals
```
- Inductive matching/substitution via `matchPattern` and `substitute`

#### 3. `GrammarExpr` - Grammar Algebra (Kleene *-semiring)
```lean
inductive GrammarF (α : Type) where
  | empty : GrammarF α               -- ε
  | lit   : String → GrammarF α      -- literal
  | ref   : String → GrammarF α      -- production reference
  | seq   : α → α → GrammarF α       -- sequence
  | alt   : α → α → GrammarF α       -- alternative
  | star  : α → GrammarF α           -- Kleene star
  | bind  : String → α → GrammarF α  -- capture binding
  | node  : String → α → GrammarF α  -- AST node wrapper

inductive GrammarExpr where
  | mk : GrammarF GrammarExpr → GrammarExpr
```
- Fixed-point recursion structure
- Infix operators: `⬝` (seq), `⊕` (alt)

#### 4. `Token` - Atomic text unit
```lean
inductive Token where
  | ident  : String → Token
  | lit    : String → Token
  | sym    : String → Token
  | number : String → Token
```

#### 5. `Rule` - Bidirectional rewrite rule
```lean
structure Rule where
  name     : String
  pattern  : Term
  template : Term
```
- Converts to `Iso Term Term` via pattern matching + substitution

### Language Composition:

```lean
structure Piece where
  name    : String
  level   : PieceLevel := .syntax  -- token or syntax
  grammar : List (String × GrammarExpr)
  rules   : List Rule

structure Language where
  name   : String
  pieces : List Piece
```

---

## 3. How Parsing, Tokenization, and Interpretation Work

### A. Character-Level Lexing (`lexGrammar` in Interp.lean)

```lean
partial def lexGrammar (prods : Productions) (g : GrammarExpr) (st : LexState) : LexResult
```

- **Input**: CharStream (List Char), Grammar expression
- **Process**: Recursively interprets grammar on character stream
- **Special handling**:
  - Single-char literals: `'x'` matches character x
  - Multi-char patterns: standard sequence matching
  - Star operator: greedy repetition
  - Unicode support: handles comments (any unicode) and strings (any unicode)

### B. Grammar-Driven Tokenization (`tokenizeWithGrammar` in Interp.lean)

```lean
partial def tokenizeWithGrammar (prods : Productions) (mainProds : List String) 
    (input : String) : TokenStream
```

- **Special lexing rules:**
  - Strings: `"..."` (any unicode content)
  - Comments: `--` to end-of-line (any unicode)
  - Production name determines token type:
    - ends with "ident" → `Token.ident`
    - ends with "number" → `Token.number`
    - ends with "string" → `Token.lit`
    - "ws" or "comment" → skip
    - otherwise → `Token.sym`

### C. Token-Level Parsing (`parseGrammar` in Interp.lean)

```lean
def parseGrammar (fuel : Nat) (prods : Productions) (g : GrammarExpr) (st : ParseState) : ParseResult
```

- **Total function**: Uses fuel parameter for termination (no partial)
- **Input**: TokenStream, Grammar, ParseState (tokens + bindings), fuel limit
- **Handles built-in token types**: `TOKEN.ident`, `TOKEN.string`, `TOKEN.char`, `TOKEN.number`, `TOKEN.sym`
- **Sequence**: combines adjacent terms via `combineSeq` helper (seqs flatten)
- **Star**: collects 0+ repetitions into `(seq ...)` term via inner `go` function
- **Bind**: captures to bindings list
- **Node**: wraps result with constructor name

### D. Bidirectional Printing (`printGrammar` in Interp.lean)

```lean
def printGrammar (fuel : Nat) (prods : Productions) (g : GrammarExpr) (t : Term) 
    (acc : List Token) : Option (List Token)
```

- **Total function**: Uses fuel parameter like parseGrammar
- **Inverse of parsing**: reconstructs token stream from term
- Uses `splitSeq` to decompose sequenced terms
- Returns accumulated token list

### E. Parameterized Parsing (AST Typeclass) (`parseGrammarT` in Interp.lean)

```lean
class AST (α : Type) where
  var : String → α
  lit : String → α
  con : String → List α → α
  unit : α := con "unit" []
  seq : α → α → α := fun a b => con "seq" [a, b]

partial def parseGrammarT [AST α] (prods : Productions) (g : GrammarExpr) 
    (st : ParseStateT α) : ParseResultT α
```

- **Power of abstraction**: Same grammar can parse into:
  - `Term` (generic S-expressions)
  - `GrammarExpr` (meta-circular: parse grammar into grammar)
  - Any custom AST type with AST instance

**Meta-Circular Capability:**
- Bootstrap grammar has `instance : AST GrammarExpr`
- This enables parsing `.lego` files (which define grammars) into `GrammarExpr` values
- Those values can then be executed as grammar interpreters

---

## 4. Loader Architecture (Loader.lean)

The Loader converts parsed `.lego` file AST back into executable `Productions`:

**Key Functions:**

- **`astToGrammarExpr`** - Converts parsed pattern AST to GrammarExpr
  - Handles: literals, references, sequences, alternatives, star, annotations, groups
  - Strips quotes, processes escape sequences, qualifies names with piece prefixes

- **`extractPieceProductions`** - Extracts grammar rules from DPiece/DToken nodes
  - Parses structure: `piece Name ::= expr ;`
  - Optional annotation: `expr → ConName`

- **`extractAllProductions`** - Recursively extracts all productions from parsed file
  - Flattens nested structures
  - Includes built-in productions: name, ident, string, number

- **`patternAstToTerm`** - Converts parsed pattern to Pattern-matching Term
  - Handles multiple AST formats from grammar evolution
  - Converts metavariables: `(var "$" (ident x))` → `.var "$x"`
  - Unwraps seq/parens wrapper nodes

- **`extractRules`** - Extracts rewrite rules from DRule AST nodes
  - Pattern: `rule name: pattern ~> template`

- **`LoadedGrammar`** structure encapsulates:
  ```lean
  structure LoadedGrammar where
    productions : Productions
    symbols : List String
    startProd : String
    validation : ValidationResult := ValidationResult.empty
  ```

---

## 5. Validation Architecture (Validation.lean)

Detects semantic errors that pass parsing:

**Error Categories:**

### Grammar Errors:
- `undefinedProduction` - References undefined production
- `duplicateProduction` - Same production defined twice
- `directLeftRecursion` - Production starts with self-reference
- `indirectLeftRecursion` - Circular references

### Rule Errors:
- `unboundVariable` - Template uses variable not in pattern
- `conflictingRules` - Same pattern, different results

### Optimization Warnings:
- `missingCut` - Suggests cut points after keywords
- `unreachableAlt` - Alternative unreachable due to prefix
- `redundantAlt` - Duplicate alternatives
- `ruleCycle` - Potential non-terminating rule sequence

**Validation Helpers:**

- `extractRefs` - Collects all production references from grammar
- `checkUndefinedRefs` - Validates all references exist
- `isDirectLeftRec` - Tests if production is left-recursive
- `flattenAlts` - Flattens alternative operators
- `patternKey` - Creates structural key for pattern grouping
- `structurallyEqual` - Tests grammar expression equality
- `isPrefix` - Checks if one grammar is prefix of another

---

## 6. Laws and Algebraic Properties (Laws.lean)

### Proven Theorems:

```lean
-- Iso Laws (fully proven)
instance : LawfulIso (Iso.id : Iso A A)
theorem comp_lawful [LawfulIso f] [LawfulIso g] : 
    (f >>> g) is lawful if f and g are

-- Grammar Parsing Laws (proven via structural decomposition)
theorem star_unfold_zero : parseGrammar 0 prods g.star st = none
    -- Zero fuel trivially fails

theorem empty_succeeds : fuel > 0 → parseGrammar fuel prods .empty st = some (.con "unit" [], st)
    -- Empty grammar returns unit

theorem alt_first_success' : parseGrammar fuel prods (.mk (.alt g1 g2)) st = some (t, st') →
    (parseGrammar (fuel-1) prods g1 st = some (t, st') ∨
     (parseGrammar (fuel-1) prods g1 st = none ∧
      parseGrammar (fuel-1) prods g2 st = some (t, st')))
    -- Case analysis on first alternative (both branches proven)
```

**Proof Pattern:** Match on fuel, handle 0 trivially, then for `n+1` simp and case analyze.

### Axioms (remaining):

```lean
-- Kleene Algebra Laws
axiom seq_assoc : Sequence is associative (semantically)
    -- Requires showing combineSeq is associative

-- Alternative Laws (corrected from original)
axiom alt_comm_disjoint : For disjoint alternatives, a|b = b|a
    -- Note: Original alt_comm_semantic was FALSE (Option.<|> is left-biased)
axiom alt_left_fail : parseGrammar _ a st = none → (a|b) = b
axiom alt_left_success : parseGrammar _ a st = some r → (a|b) = some r

-- Bidirectional Roundtrip
axiom roundtrip : parse ∘ print = id (on domain where both succeed)

-- Confluence
axiom confluence : Normalizing with rules is confluent (Church-Rosser)
```

### Edge Cases (marked sorry, need lemmas about nested `go` or do-notation):

```lean
theorem seq_parse'      -- do-notation bind elimination
theorem star_zero_matches -- go's internal fuel semantics
theorem star_one_match   -- go's accumulation semantics
```

---

## 7. Opportunities for Quotients, Equivalences, and Path-Based Reasoning

I identified several places where these advanced techniques would be beneficial:

### A. Grammar Equivalence / Normal Forms (Primary Candidate)

**Current State:** Grammar expressions use `BEq` for decidable equality, but this is **syntactic**.

**Opportunity:** Define semantic equivalence using **quotients or setoids**:
```lean
-- Semantic equality for GrammarExpr
def grammarSemanticEq (g1 g2 : GrammarExpr) : Prop :=
  ∀ (prods : Productions) (st : ParseState),
    parseGrammar prods g1 st = parseGrammar prods g2 st
```

**Use Quotients:**
```lean
instance grammarSetoid : Setoid GrammarExpr where
  r := grammarSemanticEq
  iseqv := ⟨refl_gram_eq, symm_gram_eq, trans_gram_eq⟩

-- Grammar normal form via quotient
def GrammarExprNorm := Quotient grammarSetoid

-- Properties like commutativity become true in quotient:
theorem alt_comm_norm (g1 g2 : GrammarExprNorm) :
    g1.alt g2 = g2.alt g1 := ...
```

**Benefits:**
- Prove algebraic laws up to semantic equivalence
- Implement simplification/canonicalization as quotient lifting
- Track "normal forms" for grammar expressions
- Reason about grammar optimization transformations

### B. Term Substitution via Equivalence Classes

**Current State:** Substitution via list of bindings

**Opportunity:** Use **equivalence relations** on Term to handle:
- Alpha-equivalence (variable renaming): `λx.x ≡α λy.y`
- Beta-equivalence (reduction steps)
- Eta-equivalence (extensionality)

```lean
-- Alpha equivalence
def alphaEq : Term → Term → Prop := ...

instance alphaSub : Setoid Term where
  r := alphaEq
  iseqv := ...

-- Substitution respects alpha-equivalence
lemma subst_respects_alpha (t : Term) (env : List (String × Term)) :
  (substitute t env) ≈α (substitute t env) := ...
```

**Benefits:**
- Formalize correct alpha-renaming
- Prove substitution lemmas (e.g., composition, commutativity)
- Automated variable capture avoidance

### C. Rule Application Equivalence

**Current State:** Rules are bidirectional but no formal equivalence structure

**Opportunity:** Define **equivalence relation** for rule application:

```lean
-- Term reduction via rules
def reducesTo (r : Rule) (t1 t2 : Term) : Prop :=
  r.apply t1 = some t2

-- Reflexive-transitive closure
def normalizesTo (rules : List Rule) (t1 t2 : Term) : Prop :=
  t2 ∈ {t | t1 reduces to t in zero or more steps}

instance normalizeSetoid : Setoid Term where
  r := fun t1 t2 => ∀ rules, normalizesTo rules t1 t2
  iseqv := ...

-- Quotient: terms up to normalization
def TermModulo (rules : List Rule) := Quotient (normalizeSetoid rules)
```

**Benefits:**
- Prove confluence formally (Church-Rosser)
- Quotient gives canonical representatives
- Type-safe normal forms

### D. Path-Based Reasoning for Bidirectional Transformations

**Current State:** Iso is just two functions with no formal relationship

**Opportunity:** Use **paths** to express roundtrip property:

```lean
-- Iso as a path/retraction pair
structure LawfulIsoPath (A B : Type) where
  forward : A → B
  backward : B → A
  forward_backward : ∀ b, forward (backward b) = b
  backward_forward : ∀ a, backward (forward a) = a

-- Path equality: these form a path between types
def typePathFromIso (iso : Iso A B) : A ≃ B :=
  ⟨iso.forward, iso.backward, 
   sorry, -- forward_backward
   sorry  -- backward_forward
  ⟩
```

**Advanced:** Use **higher inductive types** for grammar equivalence:

```lean
inductive GrammarPath : GrammarExpr → GrammarExpr → Type where
  -- Reflexivity
  | refl : ∀ g, GrammarPath g g
  
  -- Commutativity of alt
  | alt_comm : ∀ g1 g2, GrammarPath (g1.alt g2) (g2.alt g1)
  
  -- Associativity of seq
  | seq_assoc : ∀ g1 g2 g3, GrammarPath ((g1.seq g2).seq g3) (g1.seq (g2.seq g3))
  
  -- Star unfolds
  | star_unfold : ∀ g, GrammarPath g.star ((g.seq g.star).alt .empty)
  
  -- Transitivity
  | trans : ∀ g1 g2 g3, GrammarPath g1 g2 → GrammarPath g2 g3 → GrammarPath g1 g3
  
  -- Compatibility with operations
  | seq_cong : ∀ {g1 g1' g2 g2'}, GrammarPath g1 g1' → GrammarPath g2 g2' → 
               GrammarPath (g1.seq g2) (g1'.seq g2')
```

**Benefits:**
- Formal proofs of algebraic laws
- Construct paths as proofs of equivalence
- Implement decision procedures via path elimination

### E. Bootstrap Self-Typing via Equivalence

**Current State:** Bootstrap grammar parses itself, but no formal proof

**Opportunity:** Prove bootstrap grammar is well-formed:

```lean
def bootstrapGrammarLooksLikeBootstrap : Prop :=
  parseBootstrap bootstrapGrammarSource = some bootstrapGrammar

-- Equivalence: parsing self-source gives self
theorem bootstrap_self_type :
    bootstrapGrammarLooksLikeBootstrap := by
  unfold bootstrapGrammarLooksLikeBootstrap
  -- Proof by reflexivity or computational verification
  rfl
```

---

## 8. Generated Files

The `generated/` directory contains pre-compiled code:

- **BootstrapGrammar.lean** - Pre-computed grammar productions from Bootstrap.lego
- **BootstrapTokenizer.lean** - Generated tokenizer for Bootstrap grammar
- **BootstrapRules.lean** - Pre-computed rewrite rules + helper functions:
  - `combineSeq` - Flattens nested seq terms
  - `splitSeq` - Decomposes seq into two parts
  - `wrapNode` - Wraps term with node name
  - `unwrapNode` - Unwraps node wrapper

---

## 9. Key Architectural Insights

1. **Everything is bidirectional**: Same grammar for parse AND print
2. **Self-hosting**: Bootstrap grammar can parse grammars (including itself)
3. **AST abstraction**: Generic grammar engine works with any type having `AST` instance
4. **Composition**: Languages built by combining pieces (pushouts)
5. **Syntax is data**: Grammar expressions are first-class values, can be constructed at runtime
6. **Two-level interpretation**: Separate lexer (char→token) and parser (token→term)
7. **Parameterized parsing**: `parseGrammarT` enables parsing into custom AST types
8. **Validation separate from interpretation**: Type-checking happens before execution

---

## 10. Summary: Where Quotients/Equivalences/Paths Would Add Value

| Area | Current | Opportunity | Benefit |
|------|---------|-------------|---------|
| Grammar equivalence | Syntactic BEq | Semantic setoid + quotient | Prove Kleene algebra laws formally |
| Term substitution | List-based bindings | Equivalence classes for alpha/beta/eta | Type-safe, formally correct rewriting |
| Rule normalization | Fixpoint iteration | Quotient by reducibility | Canonical representatives, confluence |
| Iso properties | Proven for id/comp | Path types / equivalences | Extend to all constructions |
| Bootstrap self-proof | Informal | Higher inductive GrammarPath | Formal verification of meta-circularity |
| Grammar parsing laws | Mix of proven/axioms | Complete proofs via go lemmas | Full formal verification |

**Key Discovery:** `Option.<|>` is left-biased, not commutative—the original `alt_comm_semantic` axiom was FALSE. Replaced with correct `alt_comm_disjoint` for genuinely disjoint alternatives.

The codebase is a beautiful example of **language as algebra**, and these techniques would formalize the algebraic properties. The fuel-based total functions now enable proving theorems that were previously only axioms.
