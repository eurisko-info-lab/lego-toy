## Transformation from Original Lego to Rosetta

The transformation is a rewriting process at the AST/IR level (using your tooling for pattern-matching and template generation). It maps the original Lego specs to Rosetta constructs, abstracting away details like concrete syntax parsing (e.g., "<ident>" becomes abstract Var) and focusing on semantics. This is done via rules that preserve meaning but lift to higher abstractions.

### Step 1: Parse Original Lego to AST
- Use your Lego parser to get the AST: lang, piece, term ::=, rule, type (judge in Rosetta), test.

### Step 2: Apply Rewriting Rules to Transform
- **Syntax (term ::=)**: Map to ADTDef.
  - Original: term ::= "U" → U | <ident> → var | ...
  - Transform: adt Term { UnivC : Term ; VarC : Ident → Term ; ... }
    - Where Ident is an abstract type (impl: String in Haskell, &str in Rust).
    - Special: "<ident>" → VarC (abstract binder).
    - Operators like "∨" → infix constructors, e.g., Join : Term → Term → Term.

- **Rules (rule name: pattern ~> repl)**: Map directly to rewriteRule.
  - Original: rule join0L: (join 0 $r) ~> $r ;
  - Transform: rewrite join0L: (Join (Const 0) $r) ~> $r ;
    - Const for literals like 0/1 (add to ADT if needed).
    - $var remains wildcard.

- **Types (type name: term : type when conds)**: Map to judgeDecl.
  - Original: type PiForm: (Π ($x : $A) $B) : U when $A : U, [$x : $A] $B : U ;
  - Transform: judge piForm: (Pi $x : $A $B) : Univ when $A : Univ, ctx [$x : $A] $B : Univ ;
    - Use ctxCond for contexts.

- **Tests (test name: term ~~> term)**: Map directly to testDecl.
  - No change needed.

- **Pieces (piece Name)**: Map to moduleDecl.
  - Original: piece Dimension ... ;
  - Transform: module Dimension { adt Dim { ... }; rewrite ...; judge ...; test ...; }
  - Imports: For "import CubicalTT" → importDecl CubicalTT.

- **Additional Abstractions**:
  - Dimensions/Cofibrations: Map to ADTs with abstract ops (e.g., Join, Meet as constructors).
  - Systems/Branches: Abstract as lists or maps; use Pair for cons (impl chooses Vec/List).
  - Substitution: Use Subst primitive everywhere original uses subst (e.g., in beta).
  - Binders: Use Lam/DLam for all abstractions.

### Step 3: Handle Dependencies and Composition
- Traverse pieces bottom-up: Start with Core, add Lambda/Pi, etc.
- For Red/Cool extensions: Import base (import CubicalTT), then add new modules.

### Step 4: Output Rosetta Lego
- Print the transformed AST in Lego syntax using your printer.

This transformation ensures the Rosetta spec is high-level: no concrete parsing code, no explicit recursion in rules (impl generates it), abstract vars/subst. From Rosetta, generate target code:
- Haskell: ADTs → data/GADTs, rewrites → pattern matches in a normalize function, judges → typecheck function.
- Rust: ADTs → enums, rewrites → match in a reduce method.
- Avoids target-specific constraints (e.g., no IO in Lean, no lifetimes in Haskell).
