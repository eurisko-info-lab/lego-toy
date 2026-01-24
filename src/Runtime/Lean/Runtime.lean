/-
  Lego Runtime Library for Lean 4

  This module provides the core runtime infrastructure for Lego-generated Lean code.
  It includes:
  - Core types (Term, GrammarExpr, etc.) - re-exported
  - Parsing engine (parseGrammar, lexGrammar)
  - IO operations (readFile, writeFile)
  - Memoization (HashMap-based Packrat)

  Generated Rosetta code should: import Lego.Runtime
-/

import Std.Data.HashMap

namespace Lego.Runtime

/-! ## Core Types -/

/-- The universal Term type for AST representation -/
inductive Term where
  | var : String → Term
  | lit : String → Term
  | con : String → List Term → Term
  deriving BEq, Repr, Inhabited

instance : ToString Term where
  toString t := s!"{repr t}"

/-- Grammar expression algebra -/
inductive GrammarExpr where
  | empty : GrammarExpr
  | lit : String → GrammarExpr
  | ref : String → GrammarExpr
  | seq : GrammarExpr → GrammarExpr → GrammarExpr
  | alt : GrammarExpr → GrammarExpr → GrammarExpr
  | star : GrammarExpr → GrammarExpr
  | plus : GrammarExpr → GrammarExpr
  | opt : GrammarExpr → GrammarExpr
  | node : String → GrammarExpr → GrammarExpr
  deriving BEq, Repr, Inhabited

/-- Grammar production: (name, grammar, annotation) -/
structure Production where
  name : String
  grammar : GrammarExpr
  annotation : String := ""
  deriving BEq, Repr

/-- Production list type -/
abbrev Productions := List Production

/-- Rewrite rule: name, lhs pattern, rhs template -/
structure Rule where
  name : String
  lhs : Term
  rhs : Term
  deriving BEq, Repr

/-! ## Token Types -/

/-- Token types for lexing -/
inductive Token where
  | lit : String → Token      -- String literal "..."
  | ident : String → Token    -- Identifier
  | sym : String → Token      -- Symbol/operator
  | number : String → Token   -- Numeric literal
  deriving BEq, Repr, Inhabited

instance : ToString Token where
  toString
    | .lit s => s!"\"{s}\""
    | .ident s => s
    | .sym s => s
    | .number s => s

/-! ## Parse State -/

/-- Packrat memoization entry -/
structure MemoEntry where
  result : Option (Term × Nat × List (String × Term))
  deriving Repr

/-- Parse state -/
structure ParseState where
  tokens : List Token
  pos : Nat := 0
  memo : Std.HashMap (Nat × String) MemoEntry := Std.HashMap.emptyWithCapacity 256
  binds : List (String × Term) := []
  deriving Inhabited

/-- Parse result: (parsed term, new state) or failure -/
abbrev ParseResult := (Option (Term × ParseState)) × Std.HashMap (Nat × String) MemoEntry

/-! ## Lex State -/

/-- Lex state for character-level parsing -/
structure LexState where
  input : String
  pos : Nat := 0
  deriving Repr, Inhabited

/-- Lex result -/
abbrev LexResult := Option (String × LexState)

/-! ## Core Parsing Engine -/

/-- Find a production by name -/
def findProduction (prods : Productions) (name : String) : Option GrammarExpr :=
  prods.find? (·.name == name) |>.map (·.grammar)

/-- Find all productions with the same base name and combine with alt -/
def findAllProductions (prods : Productions) (name : String) : Option GrammarExpr :=
  let matching := prods.filter (·.name == name)
  match matching with
  | [] => none
  | [p] => some p.grammar
  | p :: ps => some (ps.foldl (fun acc prod => GrammarExpr.alt acc prod.grammar) p.grammar)

/-- Combine two terms in sequence -/
def combineSeq (t1 t2 : Term) : Term :=
  match t1, t2 with
  | .con "unit" [], t => t
  | t, .con "unit" [] => t
  | .con "seq" ts, t => .con "seq" (ts ++ [t])
  | t, .con "seq" ts => .con "seq" (t :: ts)
  | t1, t2 => .con "seq" [t1, t2]

/-- Wrap term in a constructor node -/
def wrapNode (name : String) (t : Term) : Term :=
  .con name [t]

/-- Parse grammar expression (main parsing engine)
    Uses fuel for termination and Packrat memoization for efficiency -/
partial def parseGrammar (fuel : Nat) (prods : Productions) (g : GrammarExpr) (st : ParseState) : ParseResult :=
  match fuel with
  | 0 => (none, st.memo)  -- fuel exhausted
  | fuel' + 1 =>
  match g with
  | .empty => (some (.con "unit" [], st), st.memo)

  | .lit s =>
    match st.tokens with
    | .lit l :: rest => if l == s then (some (.lit s, { st with tokens := rest, pos := st.pos + 1 }), st.memo) else (none, st.memo)
    | .sym l :: rest => if l == s then (some (.lit s, { st with tokens := rest, pos := st.pos + 1 }), st.memo) else (none, st.memo)
    | .ident l :: rest => if l == s then (some (.lit s, { st with tokens := rest, pos := st.pos + 1 }), st.memo) else (none, st.memo)
    | _ => (none, st.memo)

  | .ref name =>
    -- Handle built-in token types (TOKEN.*)
    if name.startsWith "TOKEN." then
      let tokType := name.drop 6
      match tokType, st.tokens with
      | "ident", .ident s :: rest => (some (.var s, { st with tokens := rest, pos := st.pos + 1 }), st.memo)
      | "string", .lit s :: rest =>
        if s.startsWith "\"" then (some (.lit s, { st with tokens := rest, pos := st.pos + 1 }), st.memo)
        else (none, st.memo)
      | "number", .number s :: rest => (some (.lit s, { st with tokens := rest, pos := st.pos + 1 }), st.memo)
      | "sym", .sym s :: rest => (some (.var s, { st with tokens := rest, pos := st.pos + 1 }), st.memo)
      | _, _ => (none, st.memo)
    else
      -- Packrat memoization for production references
      let key := (st.pos, name)
      match st.memo.get? key with
      | some entry =>
        match entry.result with
        | some (term, endPos, newBinds) =>
          let tokenCount := endPos - st.pos
          let newTokens := st.tokens.drop tokenCount
          (some (term, { st with tokens := newTokens, pos := endPos, binds := newBinds }), st.memo)
        | none => (none, st.memo)
      | none =>
        match findAllProductions prods name with
        | some g' =>
          let (result, memo') := parseGrammar fuel' prods g' st
          match result with
          | some (term, st') =>
            let entry := { result := some (term, st'.pos, st'.binds) : MemoEntry }
            let memo'' := memo'.insert key entry
            (some (term, { st' with memo := memo'' }), memo'')
          | none =>
            let entry := { result := none : MemoEntry }
            let memo'' := memo'.insert key entry
            (none, memo'')
        | none => (none, st.memo)

  | .seq g1 g2 =>
    let (r1, memo1) := parseGrammar fuel' prods g1 st
    match r1 with
    | some (t1, st1) =>
      let st1' := { st1 with memo := memo1 }
      let (r2, memo2) := parseGrammar fuel' prods g2 st1'
      match r2 with
      | some (t2, st2) => (some (combineSeq t1 t2, st2), memo2)
      | none => (none, memo2)
    | none => (none, memo1)

  | .alt g1 g2 =>
    let (r1, memo1) := parseGrammar fuel' prods g1 st
    match r1 with
    | some result => (some result, memo1)
    | none =>
      let st' := { st with memo := memo1 }
      parseGrammar fuel' prods g2 st'

  | .star g' =>
    let rec loop (acc : List Term) (st : ParseState) (memo : Std.HashMap (Nat × String) MemoEntry) (loopFuel : Nat) : ParseResult :=
      match loopFuel with
      | 0 =>
        let result := if acc.isEmpty then .con "unit" [] else .con "seq" acc.reverse
        (some (result, st), memo)
      | loopFuel' + 1 =>
        let st' := { st with memo := memo }
        let (r, memo') := parseGrammar fuel' prods g' st'
        match r with
        | some (t, st'') => loop (t :: acc) st'' memo' loopFuel'
        | none =>
          let result := if acc.isEmpty then .con "unit" [] else .con "seq" acc.reverse
          (some (result, { st with memo := memo' }), memo')
    loop [] st st.memo fuel'

  | .plus g' =>
    let (first, memo1) := parseGrammar fuel' prods g' st
    match first with
    | none => (none, memo1)
    | some (t, st') =>
      let (rest, memo2) := parseGrammar fuel' prods (.star g') { st' with memo := memo1 }
      match rest with
      | some (.con "unit" [], st'') => (some (t, st''), memo2)
      | some (ts, st'') => (some (combineSeq t ts, st''), memo2)
      | none => (some (t, st'), memo2)

  | .opt g' =>
    let (r, memo') := parseGrammar fuel' prods g' st
    match r with
    | some result => (some result, memo')
    | none => (some (.con "unit" [], { st with memo := memo' }), memo')

  | .node name g' =>
    let (r, memo') := parseGrammar fuel' prods g' st
    match r with
    | some (t, st') => (some (wrapNode name t, st'), memo')
    | none => (none, memo')

/-! ## IO Operations -/

/-- Read file contents -/
def readFile (path : String) : IO String := IO.FS.readFile path

/-- Write file contents -/
def writeFile (path : String) (content : String) : IO Unit := IO.FS.writeFile path content

/-- Check if file exists -/
def fileExists (path : String) : IO Bool := do
  try
    let _ ← IO.FS.metadata path
    return true
  catch _ =>
    return false

/-! ## Term Utilities -/

/-- Pattern match helper -/
def matchPattern (pattern : Term) (t : Term) : Option (List (String × Term)) :=
  match pattern, t with
  | .var x, t => some [(x, t)]
  | .lit s1, .lit s2 => if s1 == s2 then some [] else none
  | .con n1 args1, .con n2 args2 =>
    if n1 == n2 && args1.length == args2.length then
      let results := args1.zip args2 |>.map (fun (p, t) => matchPattern p t)
      if results.all Option.isSome then
        some (results.filterMap id |>.flatten)
      else none
    else none
  | _, _ => none

/-- Substitute bindings in a term -/
def substitute (binds : List (String × Term)) (t : Term) : Term :=
  match t with
  | .var x => binds.find? (·.1 == x) |>.map (·.2) |>.getD t
  | .lit s => .lit s
  | .con n args => .con n (args.map (substitute binds))

/-- Apply a single rewrite rule -/
def applyRule (rule : Rule) (t : Term) : Option Term :=
  match matchPattern rule.lhs t with
  | some binds => some (substitute binds rule.rhs)
  | none => none

/-- Normalize term using rewrite rules -/
partial def normalize (rules : List Rule) (t : Term) (fuel : Nat := 1000) : Term :=
  match fuel with
  | 0 => t
  | fuel' + 1 =>
    -- Try each rule
    let applied := rules.findSome? (fun r => applyRule r t)
    match applied with
    | some t' => normalize rules t' fuel'
    | none =>
      -- Recursively normalize children
      match t with
      | .con n args => .con n (args.map (normalize rules · fuel'))
      | other => other

end Lego.Runtime
