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

/-! ## Cubical Types -/

/-- Dimension values (interval endpoints and variables) -/
inductive Dim where
  | i0 : Dim                    -- 0 endpoint
  | i1 : Dim                    -- 1 endpoint
  | ivar : Nat → Dim            -- dimension variable (de Bruijn)
  deriving BEq, Repr, Inhabited

/-- Cofibrations (face formulas) -/
inductive Cof where
  | top : Cof                   -- ⊤ (always true)
  | bot : Cof                   -- ⊥ (always false)
  | eq : Dim → Dim → Cof        -- r = s
  | conj : Cof → Cof → Cof      -- φ ∧ ψ
  | disj : Cof → Cof → Cof      -- φ ∨ ψ
  deriving BEq, Repr, Inhabited

/-- Universe levels -/
inductive Level where
  | lzero : Level               -- Level 0
  | lsuc : Level → Level        -- ℓ + 1
  | lmax : Level → Level → Level -- max ℓ₁ ℓ₂
  | lvar : Nat → Level          -- Level variable (de Bruijn)
  deriving BEq, Repr, Inhabited

namespace Level

/-- Convert Nat to Level -/
def ofNat : Nat → Level
  | 0 => lzero
  | n + 1 => lsuc (ofNat n)

/-- Try to convert Level to Nat (fails if contains variables) -/
def toNat? : Level → Option Nat
  | lzero => some 0
  | lsuc l => l.toNat?.map (· + 1)
  | lmax l1 l2 => do
    let n1 ← l1.toNat?
    let n2 ← l2.toNat?
    pure (max n1 n2)
  | lvar _ => none

/-- Normalize level expression -/
partial def normalize : Level → Level
  | lmax l1 l2 =>
    let l1' := normalize l1
    let l2' := normalize l2
    if l1' == l2' then l1'
    else match l1', l2' with
      | lzero, _ => l2'
      | _, lzero => l1'
      | lsuc a, lsuc b => lsuc (normalize (lmax a b))
      | _, _ => lmax l1' l2'
  | l => l

/-- Check level equality (normalizing) -/
def levelEq (l1 l2 : Level) : Bool :=
  normalize l1 == normalize l2

end Level

/-! ## Terms: The Universal Structure -/

/-- Term: the universal AST representation.
    Everything reduces to/from Terms. -/
inductive Term where
  | var : String → Term
  | con : String → List Term → Term
  | lit : String → Term
  deriving Repr, BEq, Inhabited

/-- Tube element: (cofibration term, partial element) for Kan operations -/
structure Tube where
  cof : Term
  element : Term
  deriving BEq, Repr

/-! ## Cubical Proof Types -/

/-- H-level numbers for truncation hierarchy -/
inductive HLevelNum where
  | hprop : HLevelNum           -- -1 (contractible) / 0 (proposition)
  | hset : HLevelNum            -- 1 (set)
  | hgroupoid : HLevelNum       -- 2 (groupoid)
  | hlevel : Nat → HLevelNum    -- n (general h-level)
  deriving BEq, Repr, Inhabited

namespace HLevelNum

/-- Convert to natural number (using convention: prop = 1, set = 2, ...) -/
def toNat : HLevelNum → Nat
  | hprop => 1
  | hset => 2
  | hgroupoid => 3
  | hlevel n => n

/-- Check if one level is ≤ another -/
def le (l1 l2 : HLevelNum) : Bool :=
  l1.toNat <= l2.toNat

end HLevelNum

/-- Equivalence data: forward map with inverse and proofs -/
structure EquivData where
  /-- Forward function -/
  fwd : Term
  /-- Backward function (inverse) -/
  bwd : Term
  /-- Section: bwd ∘ fwd ~ id -/
  sec : Term
  /-- Retraction: fwd ∘ bwd ~ id -/
  ret : Term
  deriving BEq, Repr

/-- Contractibility witness: center + paths to center -/
structure ContrData where
  /-- The center of contraction -/
  center : Term
  /-- Proof that all points are path-connected to center -/
  paths : Term
  deriving BEq, Repr

/-- Fiber data: element + path to target -/
structure FiberData where
  /-- Element in the domain -/
  point : Term
  /-- Path from f(point) to target -/
  path : Term
  deriving BEq, Repr

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
  | nl     : Token              -- Newline
  | indent : Token              -- Increase indentation
  | dedent : Token              -- Decrease indentation
  | sp     : Token              -- Space
  deriving Repr, BEq, Inhabited

namespace Token

/-- Convert token back to source text (layout tokens handled by renderer) -/
def toString : Token → String
  | .ident s  => s
  | .lit s    => s
  | .sym s    => s
  | .number s => s
  | .nl       => "\n"
  | .indent   => ""  -- Layout, handled by renderer
  | .dedent   => ""  -- Layout, handled by renderer
  | .sp       => " "

/-- Render tokens to string with proper indentation handling -/
def renderTokens (tokens : List Token) : String :=
  let rec go (indent : Nat) (acc : String) (needSpace : Bool) (toks : List Token) : String :=
    match toks with
    | [] => acc
    | t :: rest =>
      match t with
      | .indent => go (indent + 2) acc false rest
      | .dedent =>
        let newIndent := if indent >= 2 then indent - 2 else 0
        go newIndent acc false rest
      | .nl =>
        let spaces := String.join (List.replicate indent " ")
        let newAcc := acc ++ "\n" ++ spaces
        go indent newAcc false rest
      | .sp => go indent (acc ++ " ") false rest
      | other =>
        let s := Token.toString other
        let sep := if needSpace && !acc.isEmpty then " " else ""
        let newAcc := acc ++ sep ++ s
        go indent newAcc true rest
  go 0 "" false tokens

end Token

/-- A stream of tokens with position tracking -/
abbrev TokenStream := List Token

/-! ## The Grammar Algebra -/

/-- GrammarF: functor for grammar expressions.
    This is the *-semiring (Kleene algebra) structure extended with
    PEG-style operators for lexer support:
    - cut: commit point (no backtracking past this)
    - ordered: PEG ordered choice (first match wins, left-biased)
    - longest: maximal munch (try all alternatives, pick longest match)
    - layout: layout annotations for pretty-printing (@nl, @indent, @dedent, @sp, @nsp) -/
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
  -- Layout annotations (for pretty-printing, ignored during parsing)
  | layout  : String → GrammarF α           -- layout annotation: nl, indent, dedent, sp, nsp
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
-- Layout annotations
def layout (kind : String) : GrammarExpr := mk (.layout kind)    -- @nl, @indent, @dedent, @sp, @nsp

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

/-! ## Generic Rule Algebra -/

/-- Typeclass for anything that can be applied to a term to produce a result.
    Both rewrite rules and type rules implement this interface. -/
class Applicable (R : Type) where
  /-- Apply the rule to a term, returning the result if it matches -/
  apply : R → Term → Option Term
  /-- Get the name of the rule (for tracing) -/
  name : R → String

/-! ## Rewrite Rule -/

/-- A rewrite rule: pattern ↔ template with optional guard -/
structure Rule where
  name     : String
  pattern  : Term
  template : Term
  guard    : Option Term := none  -- when clause (evaluated to true/false)
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
    if c1 == c2 then
      matchListWithRest args1 args2
    else none
  | _, _ => none
where
  /-- Merge bindings, checking consistency: if a variable is already bound,
      the new binding must be equal -/
  mergeBindings (env1 env2 : List (String × Term)) : Option (List (String × Term)) :=
    env2.foldlM (init := env1) fun acc (name, term) =>
      match acc.find? (·.1 == name) with
      | some (_, existing) => if existing == term then some acc else none
      | none => some ((name, term) :: acc)
  /-- Check if a pattern is a rest pattern ($name... or restVar node) -/
  isRestPattern : Term → Option String
    | .var name => if name.startsWith "$" && name.endsWith "..."
                   then some (name.drop 1 |>.dropRight 3)
                   else none
    -- Handle parsed restVar node: (restVar (ident name)) or (restVar name)
    | .con "restVar" [.con "ident" [.var name]] => some name
    | .con "restVar" [.con "ident" [.lit name]] => some name
    | .con "restVar" [.var name] => some name
    | .con "restVar" [.lit name] => some name
    | _ => none
  /-- Match pattern list, supporting rest patterns ($name...) to capture remaining items.
      The rest pattern captures all items between its position and the patterns that follow.
      Example: pattern [$a, $rest..., $z] matches terms [1,2,3,4,5] with a=1, rest=[2,3,4], z=5 -/
  matchListWithRest : List Term → List Term → Option (List (String × Term))
    | [], [] => some []
    | [p], ts =>
      -- If last pattern is a rest pattern, capture all remaining terms
      match isRestPattern p with
      | some restName =>
        -- Avoid double-wrapping: if there's exactly one term and it's already a seq, use it directly
        match ts with
        | [single@(.con "seq" _)] => some [(restName, single)]
        | _ => some [(restName, .con "seq" ts)]
      | none =>
        match ts with
        | [t] => matchPattern p t
        | _ => none  -- Single non-rest pattern but multiple terms
    | p :: ps, ts => do
      -- Check if current pattern is a rest pattern
      match isRestPattern p with
      | some restName =>
        -- Rest pattern with trailing patterns: match trailing first, capture middle
        -- ps = trailing patterns, ts = all remaining terms
        -- We need to find how many terms to capture vs leave for trailing
        let trailingCount := ps.length
        if ts.length < trailingCount then
          none  -- Not enough terms for trailing patterns
        else
          let captureCount := ts.length - trailingCount
          let (captured, trailing) := ts.splitAt captureCount
          -- Match trailing patterns with trailing terms
          let trailingBindings ← matchListWithRest ps trailing
          -- Combine rest capture with trailing bindings
          -- Avoid double-wrapping: if there's exactly one capture and it's already a seq, use it directly
          let captureBinding := match captured with
            | [single@(.con "seq" _)] => (restName, single)
            | _ => (restName, .con "seq" captured)
          mergeBindings [captureBinding] trailingBindings
      | none =>
        match ts with
        | [] => none  -- More patterns than terms
        | t :: rest =>
          let m1 ← matchPattern p t
          let m2 ← matchListWithRest ps rest
          mergeBindings m1 m2
    | [], _ :: _ => none  -- More terms than patterns (no rest to capture)

/-- Check if a template element is a splat pattern ($name... or restVar node) -/
def isSplatPattern (t : Term) : Option String :=
  match t with
  | .var name => if name.startsWith "$" && name.endsWith "..."
                 then some (name.drop 1 |>.dropRight 3)
                 else none
  -- Handle parsed restVar node: (restVar (ident name)) or (restVar name)
  | .con "restVar" [.con "ident" [.var name]] => some name
  | .con "restVar" [.con "ident" [.lit name]] => some name
  | .con "restVar" [.var name] => some name
  | .con "restVar" [.lit name] => some name
  | _ => none

/-- Check if a template element is a @map pattern: (@map wrapper $items...) or (mapExpr wrapper $items...) -/
def isMapPattern (t : Term) : Option (Term × String) :=
  -- Helper to find restVar in a list of terms
  let findRestVar : List Term → Option String := fun ts =>
    ts.findSome? fun t =>
      match t with
      | .con "restVar" [.con "ident" [.var name]] => some name
      | .con "restVar" [.con "ident" [.lit name]] => some name
      | .con "restVar" [.var name] => some name
      | .con "restVar" [.lit name] => some name
      | .con "templateArg" [.con "restVar" args] =>
        match args with
        | [.con "ident" [.var name]] => some name
        | [.con "ident" [.lit name]] => some name
        | [.var name] => some name
        | [.lit name] => some name
        | _ => none
      | _ => none
  -- Helper to extract wrapper name from various node types
  let getWrapperName : Term → Option String := fun t =>
    match t with
    | .var name => some name
    | .lit name => some name
    | .con "ident" [.var name] => some name
    | .con "ident" [.lit name] => some name
    | .con name [] => some name  -- nullary constructor like (map) or (transformConstr)
    | _ => none
  match t with
  | .con "@map" [wrapper, .var items] =>
    if items.startsWith "$" && items.endsWith "..."
    then some (wrapper, items.drop 1 |>.dropRight 3)
    else none
  -- Handle parsed mapExpr from Bootstrap grammar: "@" ident templateArg+ → mapExpr
  -- Actual structure: (mapExpr "@" (wrapper) (fn) (restVar ...) (unit))
  -- where wrapper is the function to apply, fn is another arg, etc.
  -- The "@" is first child, wrapper is second
  | .con "mapExpr" (.lit "@" :: rest) =>
    -- First non-@ element should be the wrapper function name (like "transformConstr")
    -- Then we need to find the restVar
    match rest with
    | [] => none
    | wrapperTerm :: args =>
      -- The wrapper is typically (map) which we skip, actual wrapper is next
      -- Structure: "@" (map) (transformConstr) (restVar) (unit)
      -- So args = [(map), (transformConstr), (restVar), (unit)]
      -- We want transformConstr as wrapper, and find restVar
      let nonEmptyArgs := args.filter (fun x => match x with | .con "unit" [] => false | _ => true)
      match nonEmptyArgs with
      | [] => none
      | [singleArg] =>
        -- Only restVar, use wrapperTerm as wrapper
        match findRestVar [singleArg], getWrapperName wrapperTerm with
        | some items, some wname => some (.var wname, items)
        | _, _ => none
      | _ =>
        -- Find first non-map, non-restVar as wrapper, and find restVar
        let possibleWrappers := nonEmptyArgs.filter (fun x =>
          match x with
          | .con "restVar" _ => false
          | .con "map" [] => false  -- skip the "map" keyword
          | _ => true)
        let wrapper := possibleWrappers.head?
        match wrapper, findRestVar nonEmptyArgs with
        | some w, some items =>
          match getWrapperName w with
          | some wname => some (.var wname, items)
          | none => none
        | _, _ => none
  -- Handle mapExpr with (ident wrapper) as first child
  | .con "mapExpr" (.con "ident" [.var wrapper] :: rest) =>
    match findRestVar rest with
    | some items => some (.var wrapper, items)
    | none => none
  | .con "mapExpr" (wrapper :: rest) =>
    match findRestVar rest with
    | some items => some (wrapper, items)
    | none => none
  | _ => none

/-- Apply a template with bindings to produce a term.
    Supports:
    - Splat patterns ($name...) which expand a seq of terms as children
    - Map patterns (@map wrapper $items...) which wrap each item -/
partial def applyTemplate (env : List (String × Term)) : Term → Term
  | .var name =>
    if name.startsWith "$" then
      -- Check for splat pattern first
      if name.endsWith "..." then
        let varName := name.drop 1 |>.dropRight 3
        env.find? (·.1 == varName) |>.map (·.2) |>.getD (.var name)
      else
        env.find? (·.1 == name.drop 1) |>.map (·.2) |>.getD (.var name)
    else .var name
  | .lit s => .lit s
  | .con c args =>
    -- Process args, expanding splat patterns and @map
    let expandedArgs := args.flatMap fun arg =>
      -- Check for @map pattern first
      match isMapPattern arg with
      | some (wrapper, varName) =>
        match env.find? (·.1 == varName) with
        | some (_, .con "seq" children) =>
          children.map fun child =>
            -- Apply wrapper to each child: (wrapper child)
            let wrappedChild := Term.con wrapper.toString [applyTemplate env child]
            wrappedChild
        | some (_, other) =>
          [Term.con wrapper.toString [applyTemplate env other]]
        | none => [arg]
      | none =>
        -- Check for splat pattern
        match isSplatPattern arg with
        | some varName =>
          match env.find? (·.1 == varName) with
          | some (_, .con "seq" children) => children.map (applyTemplate env)
          | some (_, other) => [applyTemplate env other]
          | none => [arg]
        | none => [applyTemplate env arg]
    .con c expandedArgs

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

/-- Rule implements Applicable for the generic rule system -/
instance : Applicable Rule where
  apply := Rule.apply
  name := Rule.name

/-! ## Built-in Primitives (needed for guard evaluation) -/

/-- Built-in rules for primitive operations (eq, neq, add, sub, etc.) -/
def builtinStep (t : Term) : Option Term :=
  match t with
  -- Boolean operations
  | .con "true" [] => none
  | .con "false" [] => none
  | .con "not" [.con "true" []] => some (.con "false" [])
  | .con "not" [.con "false" []] => some (.con "true" [])
  | .con "and" [.con "true" [], b] => some b
  | .con "and" [.con "false" [], _] => some (.con "false" [])
  | .con "and" [a, .con "true" []] => some a
  | .con "and" [_, .con "false" []] => some (.con "false" [])
  | .con "or" [.con "true" [], _] => some (.con "true" [])
  | .con "or" [.con "false" [], b] => some b
  | .con "or" [_, .con "true" []] => some (.con "true" [])
  | .con "or" [a, .con "false" []] => some a

  -- Numeric equality
  | .con "eq" [.lit a, .lit b] =>
    if a == b then some (.con "true" []) else some (.con "false" [])
  | .con "neq" [.lit a, .lit b] =>
    if a != b then some (.con "true" []) else some (.con "false" [])

  -- Constructor equality (for things like ddim0, ddim1)
  | .con "eq" [.con a [], .con b []] =>
    if a == b then some (.con "true" []) else some (.con "false" [])
  | .con "neq" [.con a [], .con b []] =>
    if a != b then some (.con "true" []) else some (.con "false" [])

  -- Numeric comparisons
  | .con "gt" [.lit a, .lit b] =>
    match a.toNat?, b.toNat? with
    | some na, some nb => if na > nb then some (.con "true" []) else some (.con "false" [])
    | _, _ => none
  | .con "lt" [.lit a, .lit b] =>
    match a.toNat?, b.toNat? with
    | some na, some nb => if na < nb then some (.con "true" []) else some (.con "false" [])
    | _, _ => none
  | .con "geq" [.lit a, .lit b] =>
    match a.toNat?, b.toNat? with
    | some na, some nb => if na >= nb then some (.con "true" []) else some (.con "false" [])
    | _, _ => none
  | .con "leq" [.lit a, .lit b] =>
    match a.toNat?, b.toNat? with
    | some na, some nb => if na <= nb then some (.con "true" []) else some (.con "false" [])
    | _, _ => none

  -- Arithmetic
  | .con "add" [.lit a, .lit b] =>
    match a.toNat?, b.toNat? with
    | some na, some nb => some (.lit (toString (na + nb)))
    | _, _ => none
  | .con "sub" [.lit a, .lit b] =>
    match a.toNat?, b.toNat? with
    | some na, some nb => some (.lit (toString (na - nb)))
    | _, _ => none
  | .con "mul" [.lit a, .lit b] =>
    match a.toNat?, b.toNat? with
    | some na, some nb => some (.lit (toString (na * nb)))
    | _, _ => none

  -- Conditionals
  | .con "if" [.con "true" [], thenBranch, _] => some thenBranch
  | .con "if" [.con "false" [], _, elseBranch] => some elseBranch

  -- Option handling
  | .con "fromOption" [.con "some" [x], _] => some x
  | .con "fromOption" [.con "none" [], dflt] => some dflt

  -- HOAS: Beta reduction for fun expressions
  -- (con [fun args..., arg1, arg2, ...]) → body[params := args]
  | .con "con" (.con "fun" funArgs :: appArgs) =>
    if appArgs.isEmpty then none
    else hoasBeta funArgs appArgs

  -- HOAS: Application flattening
  -- ((f args...) newArg) → (f args... newArg)
  -- This handles cases like ((buildLam k) ctx) → (buildLam k ctx)
  | .con "con" [.con name args, newArg] =>
    some (.con name (args ++ [newArg]))

  -- HOAS: Multi-arg beta reduction
  -- (fun x y => body) applied to args
  | .con "fun" funArgs =>
    -- Check if this is a saturated application (all params have args)
    hoasReduce funArgs

  | _ => none
where
  /-- Extract parameter names and body from fun args.
      fun [x, y, con ["=>"], body] → (["x", "y"], body) -/
  extractFunParams (args : List Term) : Option (List String × Term) :=
    let rec go (acc : List String) (rest : List Term) : Option (List String × Term) :=
      match rest with
      | [] => none
      | [body] => some (acc.reverse, body)
      | .con "con" [.lit "=>"] :: body :: _ => some (acc.reverse, body)
      | .lit "=>" :: body :: _ => some (acc.reverse, body)
      | .con name [] :: rest' => go (name :: acc) rest'
      | _ => none
    go [] args

  /-- Substitute a variable in a term -/
  substVar (varName : String) (replacement : Term) (t : Term) : Term :=
    match t with
    | .con name [] => if name == varName then replacement else t
    | .con name args => .con name (args.map (substVar varName replacement))
    | .var name => if name == varName then replacement else t
    | .lit _ => t

  /-- Apply HOAS beta reduction: (fun x y ... => body) arg1 arg2 ... -/
  hoasBeta (funArgs : List Term) (appArgs : List Term) : Option Term :=
    match extractFunParams funArgs with
    | none => none
    | some (params, body) =>
      if appArgs.length < params.length then
        -- Partial application: return a new fun with remaining params
        let appliedParams := params.take appArgs.length
        let remainingParams := params.drop appArgs.length
        let body' := appliedParams.zip appArgs |>.foldl
          (fun acc (param, arg) => substVar param arg acc) body
        if remainingParams.isEmpty then
          some body'
        else
          -- Rebuild fun with remaining params
          let paramTerms := remainingParams.map (fun p => Term.con p [])
          some (.con "fun" (paramTerms ++ [.lit "=>", body']))
      else if appArgs.length == params.length then
        -- Exact application
        let result := params.zip appArgs |>.foldl
          (fun acc (param, arg) => substVar param arg acc) body
        some result
      else
        -- Over-application: apply body to remaining args
        let result := params.zip (appArgs.take params.length) |>.foldl
          (fun acc (param, arg) => substVar param arg acc) body
        let remaining := appArgs.drop params.length
        some (.con "con" ([result] ++ remaining))

  /-- Check if a fun can reduce (has no unbound params as immediate children) -/
  hoasReduce (_ : List Term) : Option Term :=
    -- This handles bare fun expressions - nothing to reduce without application
    none

/-- Apply built-in primitives recursively -/
partial def applyBuiltinsDeep (t : Term) : Term :=
  let t' := match t with
    | .con name args => .con name (args.map applyBuiltinsDeep)
    | other => other
  match builtinStep t' with
  | some result => applyBuiltinsDeep result
  | none => t'

/-! ## Rule Interpreter

    The meta-rule interpreter applies rewrite rules to normalize terms.
    It uses a bottom-up strategy: normalize children first, then apply rules at the root.
-/

/-- Evaluate a guard condition given a substitution -/
def evaluateGuard (env : List (String × Term)) (guard : Term) : Bool :=
  -- Apply substitution to the guard, then evaluate with builtins
  let guardInst := applyTemplate env guard
  let guardEval := applyBuiltinsDeep guardInst
  -- Check if it evaluated to true
  match guardEval with
  | .con "true" [] => true
  | .lit "true" => true
  | _ => false

/-- Apply a rule with optional guard to a term -/
def Rule.applyWithGuard (r : Rule) (t : Term) : Option Term :=
  match matchPattern r.pattern t with
  | some env =>
    -- Check guard if present
    match r.guard with
    | none => some (applyTemplate env r.template)
    | some guard =>
      if evaluateGuard env guard
      then some (applyTemplate env r.template)
      else none
  | none => none

/-- Apply a list of rules to a term, returning first match (with guard support) -/
def applyRulesOnce (rules : List Rule) (t : Term) : Option Term :=
  rules.findSome? (·.applyWithGuard t)

/-- Apply rules recursively to all subterms (bottom-up) -/
partial def applyRulesDeep (rules : List Rule) (t : Term) : Term :=
  -- First normalize children
  let t' := match t with
    | .con name args => .con name (args.map (applyRulesDeep rules))
    | other => other
  -- Then try to apply rules at root
  match applyRulesOnce rules t' with
  | some result => applyRulesDeep rules result  -- Keep reducing
  | none => t'

/-- Normalize a term using rules with fuel limit -/
partial def normalizeWithRules (fuel : Nat) (rules : List Rule) (t : Term) : Term :=
  if fuel == 0 then t
  else
    let t' := applyRulesDeep rules t
    if t' == t then t  -- Fixpoint reached
    else normalizeWithRules (fuel - 1) rules t'

/-- Full normalization: builtins + user rules -/
def normalizeWithRulesAndBuiltins (fuel : Nat) (rules : List Rule) (t : Term) : Term :=
  match fuel with
  | 0 => t
  | fuel' + 1 =>
    -- Apply user rules
    let t1 := applyRulesDeep rules t
    -- Apply builtins
    let t2 := applyBuiltinsDeep t1
    if t2 == t then t
    else normalizeWithRulesAndBuiltins fuel' rules t2

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

/-- Apply a type rule to infer the type of a term (basic, no condition checking).
    Returns the type with pattern variables substituted. -/
def TypeRule.apply (tr : TypeRule) (t : Term) : Option Term :=
  match tr.matches t with
  | some bindings => some (applyTemplate bindings tr.type)
  | none => none

/-- TypeRule implements Applicable for the generic rule system -/
instance : Applicable TypeRule where
  apply := TypeRule.apply
  name := TypeRule.name

/-- Structural equality for terms -/
partial def termStructuralEq (t1 t2 : Term) : Bool :=
  match t1, t2 with
  | .var n1, .var n2 => n1 == n2
  | .lit s1, .lit s2 => s1 == s2
  | .con c1 args1, .con c2 args2 =>
    c1 == c2 && args1.length == args2.length &&
    (args1.zip args2 |>.all fun (a, b) => termStructuralEq a b)
  | _, _ => false

/-- Check if a term is a natural number literal (natLit "123") or just a plain lit -/
def isNatLit (t : Term) : Bool :=
  match t with
  | .con "natLit" [.lit _] => true
  | .lit s => s.all Char.isDigit  -- bare digit literals
  | _ => false

/-- Check if a term is an integer literal (includes negLit) -/
def isIntLit (t : Term) : Bool :=
  match t with
  | .con "negLit" [.lit _] => true
  | _ => isNatLit t

/-- Check if a term is a rational literal -/
def isRatLit (t : Term) : Bool :=
  match t with
  | .con "ratLit" [.lit _, .lit _] => true
  | _ => false

/-- Check if a term is a real/decimal literal -/
def isRealLit (t : Term) : Bool :=
  match t with
  | .con "decLit" [.lit _] => true
  | _ => false

/-- Check if a term is an identifier (not a metavar) -/
def isIdent (t : Term) : Bool :=
  match t with
  | .con "ident" [.var _] => true
  | .con "ident" [.lit _] => true
  | _ => false

/-- Check if a term is a dimension term -/
def isDim (t : Term) : Bool :=
  match t with
  | .con "dim0" [] => true
  | .con "dim1" [] => true
  | .con "dimMax" _ => true
  | .con "dimMin" _ => true
  | .con "dimNeg" _ => true
  | .var _ => true  -- dimension variables
  | _ => false

/-- Check if a term is a metavar ($x) -/
def isMetaVar (t : Term) : Bool :=
  match t with
  | .var s => s.startsWith "$" || s.get 0 == '$'
  | _ => false

/-- Check if a term is a string literal -/
def isString (t : Term) : Bool :=
  match t with
  | .lit _ => true
  | _ => false

/-- Check if a term is a number -/
def isNumber (t : Term) : Bool :=
  isNatLit t || isIntLit t || isRatLit t || isRealLit t

/-- Check if a term is a literal (string or number) -/
def isLiteral (t : Term) : Bool :=
  match t with
  | .lit _ => true
  | _ => false

/-- Check a single condition: $x : $T means the term bound to $x should have type $T.
    Also handles side conditions like (isNatLit $n).
    We recursively call type inference to verify typing conditions. -/
def checkCondition (typeRules : List TypeRule) (bindings : List (String × Term))
    (cond : Term) : Bool :=
  match cond with
  | .con ":" [.var varName, expectedType] =>
    -- Find the term bound to this variable
    match bindings.find? (·.1 == varName.drop 1) with
    | none => false  -- Variable not bound
    | some (_, boundTerm) =>
      -- Substitute any variables in the expected type
      let expectedTypeSubst := applyTemplate bindings expectedType
      -- Infer the actual type of the bound term using type rules
      match typeRules.findSome? (·.apply boundTerm) with
      | some actualType =>
        -- Check if actual type matches expected type
        termStructuralEq actualType expectedTypeSubst
      | none =>
        -- If no type rule matches, check if term is a type itself (Univ-typed)
        -- For now, be permissive: if we can't infer type, assume ok
        true
  | .con "constraint" [.var varName, expectedType] =>
    -- Alternative form for constraint
    match bindings.find? (·.1 == varName.drop 1) with
    | none => false
    | some (_, boundTerm) =>
      let expectedTypeSubst := applyTemplate bindings expectedType
      match typeRules.findSome? (·.apply boundTerm) with
      | some actualType => termStructuralEq actualType expectedTypeSubst
      | none => true
  -- Side conditions: (predicate $var)
  | .con "sidePattern" [inner] =>
    -- Unwrap sidePattern wrapper and check the inner condition
    checkCondition typeRules bindings inner
  | .con "isNatLit" [.var varName] =>
    match bindings.find? (·.1 == varName.drop 1) with
    | none => false
    | some (_, boundTerm) => isNatLit boundTerm
  | .con "isIntLit" [.var varName] =>
    match bindings.find? (·.1 == varName.drop 1) with
    | none => false
    | some (_, boundTerm) => isIntLit boundTerm
  | .con "isRatLit" [.var varName] =>
    match bindings.find? (·.1 == varName.drop 1) with
    | none => false
    | some (_, boundTerm) => isRatLit boundTerm
  | .con "isRealLit" [.var varName] =>
    match bindings.find? (·.1 == varName.drop 1) with
    | none => false
    | some (_, boundTerm) => isRealLit boundTerm
  | .con "isDim" [.var varName] =>
    match bindings.find? (·.1 == varName.drop 1) with
    | none => false
    | some (_, boundTerm) => isDim boundTerm
  | .con "isMetaVar" [.var varName] =>
    match bindings.find? (·.1 == varName.drop 1) with
    | none => false
    | some (_, boundTerm) => isMetaVar boundTerm
  | .con "isIdent" [.var varName] =>
    match bindings.find? (·.1 == varName.drop 1) with
    | none => false
    | some (_, boundTerm) => isIdent boundTerm
  | .con "isString" [.var varName] =>
    match bindings.find? (·.1 == varName.drop 1) with
    | none => false
    | some (_, boundTerm) => isString boundTerm
  | .con "isNumber" [.var varName] =>
    match bindings.find? (·.1 == varName.drop 1) with
    | none => false
    | some (_, boundTerm) => isNumber boundTerm
  | .con "isLiteral" [.var varName] =>
    match bindings.find? (·.1 == varName.drop 1) with
    | none => false
    | some (_, boundTerm) => isLiteral boundTerm
  | _ => true  -- Unknown conditions pass by default

/-- Check all conditions of a type rule given the bindings.
    Returns true if all conditions are satisfied. -/
def checkConditions (typeRules : List TypeRule) (bindings : List (String × Term))
    (conditions : List Term) : Bool :=
  conditions.all (checkCondition typeRules bindings)

/-- Apply a type rule with full condition checking.
    Requires the list of all type rules for recursive type inference. -/
def TypeRule.applyWithCheck (tr : TypeRule) (typeRules : List TypeRule) (t : Term) : Option Term :=
  match tr.matches t with
  | some bindings =>
    if checkConditions typeRules bindings tr.conditions then
      some (applyTemplate bindings tr.type)
    else
      none  -- Conditions not satisfied
  | none => none

/-- Convert a TypeRule to an Iso for use with the meta-reducer.
    Forward: term → type (type inference)
    Backward: not meaningful for types, returns none -/
def TypeRule.toIso (tr : TypeRule) : Iso Term Term where
  forward := tr.apply
  backward := fun _ => none  -- typing is not reversible

/-! ## Type Inference via Meta-Reducer -/

/-- Combine type rules into a single Iso that tries each rule (first match wins) -/
def combineTypeRules (typeRules : List TypeRule) : Iso Term Term :=
  match typeRules with
  | [] => Iso.id
  | tr :: trs => trs.foldl (fun acc tr' => Iso.orElse acc tr'.toIso) tr.toIso

/-- Infer type of a term using combined type rules (first matching rule wins) -/
def inferType (typeRules : List TypeRule) (t : Term) : Option Term :=
  (combineTypeRules typeRules).forward t

/-- Recursively infer types for all subterms, building type environment -/
partial def inferTypes (typeRules : List TypeRule) (t : Term) : List (Term × Term) :=
  let self := match inferType typeRules t with
    | some ty => [(t, ty)]
    | none => []
  let children := match t with
    | .con _ args => args.flatMap (inferTypes typeRules)
    | _ => []
  self ++ children

/-- Extract the production name from a type rule subject.
    For `(typeof (Pi))` returns "Pi".
    For `(typeof (Add $a $b))` returns "Add". -/
def extractProdName (subject : Term) : Option String :=
  match subject with
  | .con "typeof" [inner] =>
    match inner with
    | .con name _ => some name  -- (typeof (Con args...))
    | .var _ => none            -- (typeof $x) - generic rule
    | _ => none
  | _ => none

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

/-- Get combined type inference from all type rules -/
def typeInferencer (lang : Language) : Iso Term Term :=
  combineTypeRules lang.allTypeRules

/-- Infer type using language's type rules -/
def inferTypeWith (lang : Language) (t : Term) : Option Term :=
  lang.typeInferencer.forward t

end Language

end Lego
