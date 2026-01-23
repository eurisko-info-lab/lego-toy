/-
  Lego.Algebra: Core algebraic structures for bidirectional transformations

  The fundamental insight: everything is an Iso (partial isomorphism).
  - Grammar: Token ↔ Term (representation ↔ structure)
  - Rules:   Term ↔ Term  (structure ↔ structure)
  - Types:   Term → Prop  (structure → validity)

  A Language is a composition of Isos.
-/

namespace Lego

/-! ## The Core: Partial Isomorphism -/

/-- A partial isomorphism between types A and B.
    This is the atomic unit of computation in Lego.

    Mathematically: a partial isomorphism (A ⇌ B)
    - forward:  A → Option B  (parse/reduce)
    - backward: B → Option A  (print/expand)

    Laws (when both succeed):
    - forward ∘ backward = id
    - backward ∘ forward = id
-/
structure Iso (A B : Type) where
  forward  : A → Option B
  backward : B → Option A

namespace Iso

/-- Identity: A ⇌ A -/
def id : Iso A A where
  forward  := some
  backward := some

/-- Composition: (A ⇌ B) → (B ⇌ C) → (A ⇌ C) -/
def comp (f : Iso A B) (g : Iso B C) : Iso A C where
  forward  := fun a => f.forward a >>= g.forward
  backward := fun c => g.backward c >>= f.backward

infixr:90 " >>> " => comp

/-- Parallel composition (product): (A ⇌ B) → (C ⇌ D) → (A × C ⇌ B × D) -/
def par (f : Iso A B) (g : Iso C D) : Iso (A × C) (B × D) where
  forward  := fun (a, c) => do
    let b ← f.forward a
    let d ← g.forward c
    pure (b, d)
  backward := fun (b, d) => do
    let a ← f.backward b
    let c ← g.backward d
    pure (a, c)

infixr:80 " *** " => par

/-- Choice (coproduct): (A ⇌ C) → (B ⇌ C) → (A ⊕ B ⇌ C) -/
def choice (f : Iso A C) (g : Iso B C) : Iso (Sum A B) C where
  forward := fun
    | .inl a => f.forward a
    | .inr b => g.forward b
  backward := fun c =>
    match f.backward c with
    | some a => some (.inl a)
    | none => g.backward c |>.map .inr

infixr:70 " ||| " => choice

/-- Alternative: try first, fallback to second (same types) -/
def orElse (f g : Iso A B) : Iso A B where
  forward := fun a => f.forward a <|> g.forward a
  backward := fun b => f.backward b <|> g.backward b

/-- Symmetric: flip forward and backward -/
def sym (f : Iso A B) : Iso B A where
  forward  := f.backward
  backward := f.forward

prefix:max "~" => sym

end Iso

/-! ## The AST Algebra: Typeclass for building typed ASTs -/

/-- AST typeclass: abstraction over AST construction.
    Allows grammar parsing to build into any target type.

    The default instance builds `Term` (generic S-expressions).
    Custom instances can build typed GADTs with compile-time validation.

    Algebraic structure: Free algebra over {var, lit, con}
    - var: String → α     (variables/identifiers)
    - lit: String → α     (literals)
    - con: String → List α → α  (constructors/nodes)
-/
class AST (α : Type) where
  /-- Build a variable/identifier node -/
  var : String → α
  /-- Build a literal node -/
  lit : String → α
  /-- Build a constructor/application node -/
  con : String → List α → α
  /-- Build an empty/unit node (default: con "unit" []) -/
  unit : α := con "unit" []
  /-- Build a sequence from two nodes (default: combine into seq) -/
  seq : α → α → α := fun a b => con "seq" [a, b]

namespace AST

/-- Convenience: constructor with no arguments -/
def atom [AST α] (s : String) : α := AST.con s []

/-- Convenience: wrap a node with a constructor name -/
def wrap [AST α] (name : String) (inner : α) : α := AST.con name [inner]

end AST

/-! ## Terms: The Universal Structure -/

/-- Term: the universal AST representation.
    Everything reduces to/from Terms. -/
inductive Term where
  | var : String → Term
  | con : String → List Term → Term
  | lit : String → Term
  deriving Repr, BEq, Inhabited

/-- Default AST instance: build Term (generic S-expressions) -/
instance : AST Term where
  var := Term.var
  lit := Term.lit
  con := Term.con

namespace Term

/-- Constructor with no arguments -/
def atom (s : String) : Term := con s []

/-- Convenient constructor -/
def app (f : String) (args : List Term) : Term := con f args

/-- Match a pattern against a term, returning bindings -/
partial def matchPattern (pat : Term) (t : Term) : Option (List (String × Term)) :=
  match pat, t with
  | .var name, _ =>
    if name.startsWith "$" then some [(name, t)]
    else if t == pat then some []
    else none
  | .lit a, .lit b => if a == b then some [] else none
  | .con c1 args1, .con c2 args2 =>
    if c1 == c2 && args1.length == args2.length then
      matchList args1 args2
    else none
  | _, _ => none
where
  matchList : List Term → List Term → Option (List (String × Term))
    | [], [] => some []
    | p :: ps, t :: ts => do
      let m1 ← matchPattern p t
      let m2 ← matchList ps ts
      pure (m1 ++ m2)
    | _, _ => none

/-- Apply substitution with bindings to produce a term -/
partial def substitute (t : Term) (env : List (String × Term)) : Term :=
  match t with
  | .var name =>
    if name.startsWith "$" then
      env.find? (·.1 == name) |>.map (·.2) |>.getD t
    else t
  | .lit s => .lit s
  | .con c args => .con c (args.map (substitute · env))

/-- Convert term to string representation -/
partial def toString : Term → String
  | .var name => name
  | .lit s => s!"\"{s}\""
  | .con c [] => s!"({c})"
  | .con c args => s!"({c} {" ".intercalate (args.map toString)})"

instance : ToString Term := ⟨toString⟩

end Term

/-! ## Tokens: The Universal Representation -/

/-- Token: atomic unit of text representation -/
inductive Token where
  | ident  : String → Token
  | lit    : String → Token
  | sym    : String → Token
  | number : String → Token
  deriving Repr, BEq, Inhabited

namespace Token

/-- Convert token back to source text -/
def toString : Token → String
  | .ident s  => s
  | .lit s    => s
  | .sym s    => s
  | .number s => s

end Token

/-- A stream of tokens with position tracking -/
abbrev TokenStream := List Token

/-! ## The Grammar Algebra -/

/-- GrammarF: functor for grammar expressions.
    This is the *-semiring (Kleene algebra) structure extended with
    PEG-style operators for lexer support:
    - cut: commit point (no backtracking past this)
    - ordered: PEG ordered choice (first match wins, left-biased)
    - longest: maximal munch (try all alternatives, pick longest match) -/
inductive GrammarF (α : Type) where
  | empty   : GrammarF α                    -- ε (identity for alt)
  | lit     : String → GrammarF α           -- literal string
  | ref     : String → GrammarF α           -- reference to production
  | seq     : α → α → GrammarF α            -- sequence (monoidal)
  | alt     : α → α → GrammarF α            -- alternative (coproduct, unordered)
  | star    : α → GrammarF α                -- Kleene star
  | bind    : String → α → GrammarF α       -- capture binding
  | node    : String → α → GrammarF α       -- AST node wrapper
  -- PEG extensions for lexer semantics
  | cut     : α → GrammarF α                -- commit point: !g (no backtrack on success)
  | ordered : α → α → GrammarF α            -- ordered choice: g1 / g2 (PEG-style, first wins)
  | longest : List α → GrammarF α           -- maximal munch: try all, pick longest
  deriving Repr, BEq

/-- Fixed point of GrammarF -/
inductive GrammarExpr where
  | mk : GrammarF GrammarExpr → GrammarExpr
  deriving Repr, BEq

namespace GrammarExpr

def empty : GrammarExpr := mk .empty
def lit (s : String) : GrammarExpr := mk (.lit s)
def ref (s : String) : GrammarExpr := mk (.ref s)
def seq (a b : GrammarExpr) : GrammarExpr := mk (.seq a b)
def alt (a b : GrammarExpr) : GrammarExpr := mk (.alt a b)
def star (g : GrammarExpr) : GrammarExpr := mk (.star g)
def plus (g : GrammarExpr) : GrammarExpr := g.seq g.star  -- one or more = g g*
def bind (x : String) (g : GrammarExpr) : GrammarExpr := mk (.bind x g)
def node (n : String) (g : GrammarExpr) : GrammarExpr := mk (.node n g)
-- PEG extensions
def cut (g : GrammarExpr) : GrammarExpr := mk (.cut g)           -- commit: !g
def ordered (a b : GrammarExpr) : GrammarExpr := mk (.ordered a b)  -- ordered choice: a / b
def longest (gs : List GrammarExpr) : GrammarExpr := mk (.longest gs)  -- maximal munch

-- Infix notation
infixr:65 " ⬝ " => seq   -- sequence
infixr:60 " ⊕ " => alt   -- alternative (unordered)
infixr:55 " // " => ordered  -- ordered choice (PEG)

end GrammarExpr

/-- AST instance for GrammarExpr: parsing can build grammar expressions directly.

    This demonstrates the power of the AST abstraction:
    - The same grammar can parse into Term (data) or GrammarExpr (syntax).
    - Meta-circular: a grammar can parse itself into another grammar.

    Mapping:
    - var s     → ref s        (variable = production reference)
    - lit s     → lit s        (literal = literal match)
    - con "seq" [a,b] → seq a b
    - con "alt" [a,b] → alt a b
    - con "star" [g]  → star g
    - con "bind" [GrammarExpr.ref x, g] → bind x g
    - con "cut" [g]   → cut g    (PEG commit)
    - con "ordered" [a,b] → ordered a b  (PEG ordered choice)
    - con "longest" gs → longest gs  (maximal munch)
    - con name args   → node name (seqAll args)  (general case)
-/
instance : AST GrammarExpr where
  var := GrammarExpr.ref
  lit := GrammarExpr.lit
  con name args := match name, args with
    | "seq", [a, b] => GrammarExpr.seq a b
    | "alt", [a, b] => GrammarExpr.alt a b
    | "star", [g] => GrammarExpr.star g
    | "bind", [GrammarExpr.mk (.ref x), g] => GrammarExpr.bind x g
    | "node", [GrammarExpr.mk (.lit n), g] => GrammarExpr.node n g
    | "node", [GrammarExpr.mk (.ref n), g] => GrammarExpr.node n g
    -- PEG extensions
    | "cut", [g] => GrammarExpr.cut g
    | "ordered", [a, b] => GrammarExpr.ordered a b
    | "longest", gs => GrammarExpr.longest gs
    | _, [] => GrammarExpr.lit name  -- nullary constructor as literal
    | _, [g] => GrammarExpr.node name g  -- wrap single arg
    | _, gs => GrammarExpr.node name (gs.foldl GrammarExpr.seq GrammarExpr.empty)
  unit := GrammarExpr.empty
  seq := GrammarExpr.seq

/-! ## Rule Algebra -/

/-- A rewrite rule: pattern ↔ template -/
structure Rule where
  name     : String
  pattern  : Term
  template : Term
  deriving Repr, BEq

/-- Match a pattern against a term, returning bindings -/
partial def matchPattern (pat : Term) (t : Term) : Option (List (String × Term)) :=
  match pat, t with
  | .var name, _ =>
    if name.startsWith "$" then some [(name.drop 1, t)]
    else if t == pat then some []
    else none
  | .lit a, .lit b => if a == b then some [] else none
  | .con c1 args1, .con c2 args2 =>
    if c1 == c2 && args1.length == args2.length then
      matchList args1 args2
    else none
  | _, _ => none
where
  matchList : List Term → List Term → Option (List (String × Term))
    | [], [] => some []
    | p :: ps, t :: ts => do
      let m1 ← matchPattern p t
      let m2 ← matchList ps ts
      pure (m1 ++ m2)
    | _, _ => none

/-- Apply a template with bindings to produce a term -/
partial def applyTemplate (env : List (String × Term)) : Term → Term
  | .var name =>
    if name.startsWith "$" then
      env.find? (·.1 == name.drop 1) |>.map (·.2) |>.getD (.var name)
    else .var name
  | .lit s => .lit s
  | .con c args => .con c (args.map (applyTemplate env))

/-- Convert a Rule to an Iso on Terms -/
def Rule.toIso (r : Rule) : Iso Term Term where
  forward := fun t =>
    match matchPattern r.pattern t with
    | some env => some (applyTemplate env r.template)
    | none => none
  backward := fun t =>
    match matchPattern r.template t with
    | some env => some (applyTemplate env r.pattern)
    | none => none

/-- Apply a rule to a term (forward direction) -/
def Rule.apply (r : Rule) (t : Term) : Option Term :=
  r.toIso.forward t

/-- Apply a rule in reverse (backward direction) -/
def Rule.unapply (r : Rule) (t : Term) : Option Term :=
  r.toIso.backward t

/-! ## Type Rule Algebra -/

/-- A typing rule: term : type when conditions -/
structure TypeRule where
  name       : String
  subject    : Term       -- the term being typed (pattern)
  type       : Term       -- its type
  conditions : List Term  -- premises (when clauses)
  deriving Repr, BEq

/-- Check if a type rule applies to a term (pattern match subject) -/
def TypeRule.matches (tr : TypeRule) (t : Term) : Option (List (String × Term)) :=
  matchPattern tr.subject t

/-! ## Language: Composition of Pieces -/

/-- Piece level: what kind of stream does this piece operate on? -/
inductive PieceLevel where
  | token  : PieceLevel  -- CharStream → Token (lexer)
  | syntax : PieceLevel  -- TokenStream → Term (parser)
  deriving Repr, BEq

/-- A Piece: grammar fragment + rules + type rules.
    Each piece is a self-contained language fragment with its own interpreter. -/
structure Piece where
  name       : String
  level      : PieceLevel := .syntax  -- default to syntax-level
  grammar    : List (String × GrammarExpr)
  rules      : List Rule
  typeRules  : List TypeRule := []
  deriving Repr

/-- A Language: composition of pieces via pushout.
    Language = ⊔ Pieces = Combined Grammar + Combined Interpreter -/
structure Language where
  name    : String
  pieces  : List Piece
  deriving Repr

namespace Language

/-- Get all grammar productions from syntax-level pieces -/
def allGrammar (lang : Language) : List (String × GrammarExpr) :=
  lang.pieces.filter (·.level == .syntax) |>.flatMap (·.grammar)

/-- Get all token productions from token-level pieces -/
def tokenGrammar (lang : Language) : List (String × GrammarExpr) :=
  lang.pieces.filter (·.level == .token) |>.flatMap (·.grammar)

/-- Get all rules -/
def allRules (lang : Language) : List Rule :=
  lang.pieces.flatMap (·.rules)

/-- Get all type rules -/
def allTypeRules (lang : Language) : List TypeRule :=
  lang.pieces.flatMap (·.typeRules)

/-- Combine rules into a single Iso that tries each rule -/
def combineRules (rules : List Rule) : Iso Term Term :=
  match rules with
  | [] => Iso.id
  | r :: rs => rs.foldl (fun acc r' => Iso.orElse acc r'.toIso) r.toIso

/-- Get combined interpreter from all rules -/
def interpreter (lang : Language) : Iso Term Term :=
  combineRules lang.allRules

end Language

end Lego
