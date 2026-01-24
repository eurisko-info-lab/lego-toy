/-
  Lego.Interp: Bidirectional Grammar Interpretation

  Two grammar engines using the same GrammarExpr algebra:
  - Character level: CharStream ⇌ String (lexGrammar)
  - Token level:     TokenStream ⇌ Term  (parseGrammar)

  Helper functions (combineSeq, splitSeq, wrapNode, unwrapNode) are
  imported from BootstrapRules where they are defined alongside the
  equivalent rewrite rules from Bootstrap.lego.
-/

import Lego.Algebra
import BootstrapRules
import Std.Data.HashMap

namespace Lego

-- Import helper functions from generated rules module
open Lego.Generated.Bootstrap (combineSeq splitSeq wrapNode unwrapNode)

/-! ## Common Types -/

/-- Grammar productions map -/
abbrev Productions := List (String × GrammarExpr)

/-! ## Parse Error Tracking -/

/-- Source location with line and column (for parse errors) -/
structure ParseLoc where
  line : Nat
  column : Nat
  deriving Repr, BEq

instance : ToString ParseLoc where
  toString loc := s!"{loc.line}:{loc.column}"

/-- Compute line and column from byte offset in input.
    Line numbers are 1-based. Column is character count (not bytes) since last newline
    for user-friendly display. -/
def computeLineCol (input : String) (byteOffset : Nat) : ParseLoc :=
  -- Extract the prefix string up to the byte offset
  let prefixStr := String.Pos.Raw.extract input ⟨0⟩ ⟨byteOffset⟩
  -- Count newlines in the prefix (character-based)
  let newlineChars := prefixStr.toList.filter (· == '\n')
  let line := newlineChars.length + 1
  -- Column is characters since last newline (1-based)
  let charsAfterNewline := prefixStr.toList.reverse.takeWhile (· != '\n')
  let column := charsAfterNewline.length + 1
  { line, column }

/-- Find substring position (as byte offset) in string starting at byte offset.
    Returns byte offset for use with String.Pos.Raw operations. -/
def String.findSubstrFromBytes (s : String) (sub : String) (startByte : Nat := 0) : Option Nat :=
  let bytes := s.toUTF8
  let subBytes := sub.toUTF8
  if subBytes.isEmpty then some startByte
  else if startByte + subBytes.size > bytes.size then none
  else
    let rec go (i : Nat) (fuel : Nat) : Option Nat :=
      match fuel with
      | 0 => none
      | fuel' + 1 =>
        if i + subBytes.size > bytes.size then none
        else
          -- Check if bytes at position i match subBytes
          let slice := bytes.extract i (i + subBytes.size)
          if slice == subBytes then some i
          else go (i + 1) fuel'
    go startByte (bytes.size - startByte + 1)

/-- Find character offset by counting tokens from the beginning.
    Walks through the input counting tokens until reaching tokenPos. -/
def findCharOffsetByTokenCount (input : String) (tokenPos : Nat) : Nat :=
  -- Simple approximation: walk through, counting whitespace-separated tokens
  let rec go (chars : List Char) (pos : Nat) (count : Nat) (inToken : Bool) : Nat :=
    match chars with
    | [] => pos
    | c :: rest =>
      if count >= tokenPos then pos
      else if c.isWhitespace then
        if inToken then go rest (pos + 1) (count + 1) false
        else go rest (pos + 1) count false
      else
        go rest (pos + 1) count true
  go input.toList 0 0 false

/-- A parse error with context -/
structure ParseError where
  /-- Error message -/
  message : String
  /-- Token position (index in token stream) -/
  tokenPos : Nat
  /-- Source location (line:column) if available -/
  loc : Option ParseLoc := none
  /-- Production being parsed -/
  production : String
  /-- Expected tokens/patterns -/
  expected : List String
  /-- Actual token found -/
  actual : Option Token
  /-- Remaining tokens at error point -/
  remaining : List Token
  deriving Repr

instance : ToString ParseError where
  toString e :=
    let locStr := match e.loc with
      | some loc => s!"at {loc}"
      | none => s!"at token {e.tokenPos}"
    let actualStr := match e.actual with
      | some t => s!", found '{t.toString}'"
      | none => ", found end of input"
    let expectedStr := if e.expected.isEmpty then ""
      else s!", expected one of: {e.expected}"
    let remainingStr := if e.remaining.isEmpty then ""
      else s!"\n  next tokens: {e.remaining.take 5 |>.map (·.toString) |> String.intercalate " "}"
    s!"{e.message} {locStr} in {e.production}{expectedStr}{actualStr}{remainingStr}"

/-- Skip whitespace and comments in byte array starting at position.
    Returns the byte offset after whitespace/comments. -/
def skipWhitespaceBytes (bytes : ByteArray) (start : Nat) : Nat :=
  let rec go (i : Nat) (fuel : Nat) : Nat :=
    match fuel with
    | 0 => i
    | fuel' + 1 =>
      if i < bytes.size then
        let b := bytes[i]!
        if b == ' '.toUInt8 || b == '\t'.toUInt8 || b == '\n'.toUInt8 || b == '\r'.toUInt8 then
          go (i + 1) fuel'
        else i
      else i
  go start bytes.size

/-- Find position of a sequence of tokens in input, skipping whitespace between tokens.
    Returns byte offset. -/
partial def findTokenSeqPos (input : String) (tokens : List String) (start : Nat) : Option Nat :=
  let bytes := input.toUTF8
  match tokens with
  | [] => some start
  | tok :: rest =>
    -- Skip leading whitespace
    let startSkipped := skipWhitespaceBytes bytes start
    match String.findSubstrFromBytes input tok startSkipped with
    | none => none
    | some pos =>
      if rest.isEmpty then some pos
      else
        -- Skip whitespace after this token before searching for next
        let afterTok := pos + tok.toUTF8.size
        findTokenSeqPos input rest afterTok

/-- Add source location to a parse error by finding the token in input -/
def ParseError.withSourceLoc (e : ParseError) (input : String) : ParseError :=
  match e.remaining.head? with
  | none => { e with loc := some { line := 1, column := 1 } }
  | some tok =>
    -- Find the LAST occurrence of this token (error is usually near the end of parsing)
    let tokStr := tok.toString
    let inputBytes := input.toUTF8
    let rec findLast (fuel : Nat) (start : Nat) (lastFound : Option Nat) : Option Nat :=
      match fuel with
      | 0 => lastFound
      | fuel' + 1 =>
        match String.findSubstrFromBytes input tokStr start with
        | none => lastFound
        | some pos => findLast fuel' (pos + 1) (some pos)
    let byteOffset := findLast inputBytes.size 0 none |>.getD 0
    { e with loc := some (computeLineCol input byteOffset) }

/-- Result type with error tracking -/
inductive ParseResultE (α : Type)
  | ok : α → ParseResultE α
  | error : ParseError → ParseResultE α
  deriving Repr

/-- Get the furthest error (deepest position) -/
def furthestError (e1 e2 : ParseError) : ParseError :=
  if e1.tokenPos >= e2.tokenPos then e1 else e2

/-! ## Character Stream (for lexer) -/

abbrev CharStream := List Char

/-- Lexer state -/
structure LexState where
  chars : CharStream
  acc   : String := ""  -- accumulated characters for current token
  deriving Repr

/-- Result of lexing one token -/
abbrev LexResult := Option (String × LexState)

/-! ## Character-level Grammar Engine (Lexer) -/

/-- Extract character from 'x' format literal -/
def extractCharLit (s : String) : Option Char :=
  if s.startsWith "'" && s.endsWith "'" && s.length == 3 then
    s.toList[1]?
  else
    none

/-- Default fuel for grammar operations -/
def defaultFuel : Nat := 100000

/-- Interpret a GrammarExpr for lexing (CharStream → String)
    Single quotes in grammar match single characters.
    Uses fuel for termination. -/
def lexGrammar (fuel : Nat) (prods : Productions) (g : GrammarExpr) (st : LexState) : LexResult :=
  match fuel with
  | 0 => none  -- fuel exhausted
  | fuel' + 1 =>
  match g with
  | .mk .empty => some (st.acc, st)

  | .mk (.lit s) =>
    -- For token grammars, check for 'x' character literals first
    match extractCharLit s with
    | some expected =>
      match st.chars with
      | c :: rest =>
        if c == expected then
          some (st.acc.push c, { st with chars := rest, acc := st.acc.push c })
        else none
      | [] => none
    | none =>
      if s.length == 1 then
        match st.chars with
        | c :: rest =>
          if c == s.data[0]! then
            some (st.acc.push c, { st with chars := rest, acc := st.acc.push c })
          else none
        | [] => none
      else
        let rec matchChars (pat : List Char) (chars : CharStream) (acc : String) : Option (String × CharStream) :=
          match pat with
          | [] => some (acc, chars)
          | p :: ps =>
            match chars with
            | c :: rest => if c == p then matchChars ps rest (acc.push c) else none
            | [] => none
        match matchChars s.toList st.chars st.acc with
        | some (acc', rest) => some (acc', { st with chars := rest, acc := acc' })
        | none => none

  | .mk (.ref name) =>
    match prods.find? (·.1 == name) with
    | some (_, g') => lexGrammar fuel' prods g' st
    | none => none

  | .mk (.seq g1 g2) => do
    let (acc1, st1) ← lexGrammar fuel' prods g1 st
    let (acc2, st2) ← lexGrammar fuel' prods g2 { st1 with acc := acc1 }
    pure (acc2, st2)

  | .mk (.alt g1 g2) =>
    lexGrammar fuel' prods g1 st <|> lexGrammar fuel' prods g2 st

  | .mk (.star g') =>
    let rec go (f : Nat) (st : LexState) : LexResult :=
      match f with
      | 0 => some (st.acc, st)
      | f' + 1 =>
        match lexGrammar f' prods g' st with
        | some (acc', st') => go f' { st' with acc := acc' }
        | none => some (st.acc, st)
    go fuel' st

  | .mk (.bind _ g') => lexGrammar fuel' prods g' st

  | .mk (.node _ g') => lexGrammar fuel' prods g' st

  -- PEG extensions for lexer semantics

  | .mk (.cut g') =>
    -- Cut: commit point. Once g' succeeds, we can't backtrack.
    -- At the lexer level, this is the same as g' (backtracking is per-token)
    -- The cut semantics are enforced at the parser level.
    lexGrammar fuel' prods g' st

  | .mk (.ordered g1 g2) =>
    -- Ordered choice (PEG): try g1 first, only try g2 if g1 fails
    -- Unlike alt which is unordered, this is left-biased
    match lexGrammar fuel' prods g1 st with
    | some result => some result
    | none => lexGrammar fuel' prods g2 st

  | .mk (.longest gs) =>
    -- Maximal munch: try all alternatives, pick the one that consumes most input
    -- This is the key construct for proper tokenization (e.g., "::=" vs ":" ":" "=")
    let results := gs.filterMap (lexGrammar fuel' prods · st)
    match results with
    | [] => none
    | rs =>
      -- Pick the result with the longest consumed string
      rs.foldl (fun best (acc, st') =>
        match best with
        | none => some (acc, st')
        | some (bestAcc, bestSt) =>
          if acc.length > bestAcc.length then some (acc, st')
          else some (bestAcc, bestSt)
      ) none

/-! ## Grammar-Driven Tokenizer -/

/-- Try to lex a token using a specific production -/
def tryLexProd (prods : Productions) (prodName : String) (chars : CharStream) : Option (String × CharStream) :=
  match prods.find? (·.1 == prodName) with
  | some (_, g) =>
    match lexGrammar defaultFuel prods g { chars := chars, acc := "" } with
    | some (acc, st') => if acc.isEmpty then none else some (acc, st'.chars)
    | none => none
  | none => none

/-- Tokenize using grammar-driven lexing.
    tokenProds: all token productions
    mainProds: productions to try in priority order (longest/most-specific first)
    keywords: reserved words that should be tokenized as symbols, not identifiers
    Each production name determines the Token constructor:
    - ends with "ident" → Token.ident (unless it's a keyword → Token.sym)
    - ends with "number" → Token.number
    - ends with "string" → Token.lit
    - "ws" or "comment" → skip (no token emitted)
    - otherwise → Token.sym -/
def tokenizeWithGrammar (fuel : Nat) (prods : Productions) (mainProds : List String) (input : String) (keywords : List String := []) : TokenStream :=
  go fuel prods mainProds keywords input.toList []
where
  skipWhitespace : CharStream → CharStream
    | [] => []
    | c :: rest => if c.isWhitespace then skipWhitespace rest else c :: rest

  /-- Skip a line comment: from "--" to end of line (any unicode allowed) -/
  skipComment : CharStream → Option CharStream
    | '-' :: '-' :: rest =>
      -- Consume until newline or end
      let rec skipToEol : CharStream → CharStream
        | [] => []
        | '\n' :: rest => rest
        | _ :: rest => skipToEol rest
      some (skipToEol rest)
    | _ => none

  /-- Try to lex a string literal: "..." with any unicode content -/
  lexString : CharStream → Option (String × CharStream)
    | '"' :: rest =>
      let rec go (acc : List Char) : CharStream → Option (String × CharStream)
        | [] => none  -- Unterminated string
        | '"' :: rest => some (String.mk ('"' :: acc ++ ['"']), rest)
        | '\\' :: c :: rest => go (acc ++ ['\\', c]) rest
        | c :: rest => go (acc ++ [c]) rest
      go [] rest
    | _ => none

  /-- Try to lex a char literal: '.' with any unicode content -/
  lexChar : CharStream → Option (String × CharStream)
    | '\'' :: '\\' :: c :: '\'' :: rest =>
      -- Escaped char: '\n', '\'', etc.
      some (String.mk ['\'', '\\', c, '\''], rest)
    | '\'' :: c :: '\'' :: rest =>
      -- Single char (any unicode)
      some (String.mk ['\'', c, '\''], rest)
    | _ => none

  /-- Determine token type from production name -/
  prodToToken (keywords : List String) (prodName : String) (value : String) : Option Token :=
    let shortName := match prodName.splitOn "." with
      | [_, n] => n
      | _ => prodName
    -- Skip whitespace and comments
    if shortName == "ws" || shortName == "comment" then none
    else if shortName == "ident" then
      -- Check if this identifier is a reserved keyword
      if keywords.contains value then some (Token.sym value)
      else some (Token.ident value)
    else if shortName == "number" then some (Token.number value)
    else if shortName == "string" || shortName == "char" then some (Token.lit value)
    else some (Token.sym value)

  /-- Try each production in priority order -/
  tryTokenize (prods : Productions) (mainProds : List String) (keywords : List String) (chars : CharStream) : Option (Option Token × CharStream) :=
    mainProds.findSome? fun prodName =>
      match tryLexProd prods prodName chars with
      | some (value, rest) =>
        some (prodToToken keywords prodName value, rest)
      | none => none

  go (fuel : Nat) (prods : Productions) (mainProds : List String) (keywords : List String) (chars : CharStream) (acc : TokenStream) : TokenStream :=
    match fuel with
    | 0 => acc.reverse  -- fuel exhausted
    | fuel' + 1 =>
    match skipWhitespace chars with
    | [] => acc.reverse
    | chars' =>
      -- Handle comments specially (-- to EOL, any unicode)
      match skipComment chars' with
      | some rest => go fuel' prods mainProds keywords rest acc
      | none =>
        -- Handle strings specially (any unicode content)
        match lexString chars' with
        | some (str, rest) => go fuel' prods mainProds keywords rest (Token.lit str :: acc)
        | none =>
          -- Handle char literals specially (any unicode content)
          match lexChar chars' with
          | some (ch, rest) => go fuel' prods mainProds keywords rest (Token.lit ch :: acc)
          | none =>
            match tryTokenize prods mainProds keywords chars' with
            | some (some tok, rest) => go fuel' prods mainProds keywords rest (tok :: acc)
            | some (none, rest) => go fuel' prods mainProds keywords rest acc  -- ws: skip
            | none =>
              -- Unknown char - skip it
              match chars' with
              | _ :: rest => go fuel' prods mainProds keywords rest acc
              | [] => acc.reverse

/-! ## Token-level Parsing State -/

/-- Memo key: (position, production name) -/
abbrev MemoKey := (Nat × String)

/-- Memo entry: cached parse result -/
structure MemoEntry where
  result : Option (Term × Nat × List (String × Term))  -- (term, remaining pos, binds) or none
  deriving Repr

/-- Memo table for Packrat parsing -/
abbrev MemoTable := Std.HashMap MemoKey MemoEntry

/-- Parsing state with memoization -/
structure ParseState where
  tokens : TokenStream
  binds  : List (String × Term)
  memo   : MemoTable := {}  -- Packrat memo table
  pos    : Nat := 0         -- Current position for memo keys
  deriving Repr, Nonempty

/-- Result of grammar interpretation.
    Always returns (optionalResult, updatedMemo) to enable proper Packrat memoization
    where memo persists even through failures. -/
abbrev ParseResult := Option (Term × ParseState) × MemoTable

/-- Find all productions with a given name and combine them with alt.
    This is essential when multiple alternatives are defined separately:
      term ::= "a" → A ;
      term ::= "b" → B ;
    should behave as: term ::= "a" → A | "b" → B ; -/
def findAllProductions (prods : Productions) (name : String) : Option GrammarExpr :=
  let matching := prods.filter (·.1 == name)
  match matching with
  | [] => none
  | [(_, g)] => some g
  | (_, g) :: rest =>
    some (rest.foldl (fun acc (_, g') => .mk (.alt acc g')) g)

/-! ## Token-level Grammar Engine (Parser) -/

/-- Interpret a GrammarExpr for parsing (forward direction).
    Uses fuel for termination and Packrat memoization for efficiency.
    Returns (result, updatedMemo) where memo is updated even on failure. -/
partial def parseGrammar (fuel : Nat) (prods : Productions) (g : GrammarExpr) (st : ParseState) : ParseResult :=
  match fuel with
  | 0 => (none, st.memo)  -- fuel exhausted
  | fuel' + 1 =>
  match g with
  | .mk .empty => (some (.con "unit" [], st), st.memo)

  | .mk (.lit s) =>
    match st.tokens with
    | .lit l :: rest => if l == s then (some (.lit s, { st with tokens := rest, pos := st.pos + 1 }), st.memo) else (none, st.memo)
    | .sym l :: rest => if l == s then (some (.lit s, { st with tokens := rest, pos := st.pos + 1 }), st.memo) else (none, st.memo)
    | .ident l :: rest => if l == s then (some (.lit s, { st with tokens := rest, pos := st.pos + 1 }), st.memo) else (none, st.memo)
    | _ => (none, st.memo)

  | .mk (.ref name) =>
    -- Handle built-in token types (TOKEN.*)
    if name.startsWith "TOKEN." then
      let tokType := name.drop 6  -- Remove "TOKEN." prefix
      match tokType, st.tokens with
      | "ident",   .ident s :: rest  => (some (.var s, { st with tokens := rest, pos := st.pos + 1 }), st.memo)
      | "string",  .lit s :: rest    =>
        -- Match "..." string literals (not '...' char literals)
        if s.startsWith "\"" then
          (some (.lit s, { st with tokens := rest, pos := st.pos + 1 }), st.memo)
        else (none, st.memo)
      | "char",    .lit s :: rest    =>
        -- Match 'x' character literals
        if s.startsWith "'" && s.endsWith "'" then
          (some (.lit s, { st with tokens := rest, pos := st.pos + 1 }), st.memo)
        else (none, st.memo)
      | "number",  .number s :: rest => (some (.lit s, { st with tokens := rest, pos := st.pos + 1 }), st.memo)
      | "sym",     .sym s :: rest    => (some (.var s, { st with tokens := rest, pos := st.pos + 1 }), st.memo)
      | "special", .sym s :: rest    =>
        -- Match any <...> token
        if s.startsWith "<" && s.endsWith ">" then
          (some (.var s, { st with tokens := rest, pos := st.pos + 1 }), st.memo)
        else (none, st.memo)
      | _, _ => (none, st.memo)
    else
      -- Packrat memoization for production references
      let key := (st.pos, name)
      match st.memo.get? key with
      | some entry =>
        -- Cache hit - return cached result
        match entry.result with
        | some (term, endPos, newBinds) =>
          -- Reconstruct state from cached info
          let tokenCount := endPos - st.pos
          let newTokens := st.tokens.drop tokenCount
          (some (term, { st with tokens := newTokens, pos := endPos, binds := newBinds }), st.memo)
        | none => (none, st.memo)  -- Cached failure
      | none =>
        -- Cache miss - parse and cache
        -- Use findAllProductions to combine multiple alternatives
        match findAllProductions prods name with
        | some g' =>
          let (result, memo') := parseGrammar fuel' prods g' st
          match result with
          | some (term, st') =>
            -- Cache success
            let entry := { result := some (term, st'.pos, st'.binds) : MemoEntry }
            let memo'' := memo'.insert key entry
            (some (term, { st' with memo := memo'' }), memo'')
          | none =>
            -- Cache failure - now we CAN propagate memo on failure!
            let entry := { result := none : MemoEntry }
            let memo'' := memo'.insert key entry
            (none, memo'')
        | none => (none, st.memo)

  | .mk (.seq g1 g2) =>
    let (r1, memo1) := parseGrammar fuel' prods g1 st
    match r1 with
    | some (t1, st1) =>
      let st1' := { st1 with memo := memo1 }
      let (r2, memo2) := parseGrammar fuel' prods g2 st1'
      match r2 with
      | some (t2, st2) => (some (combineSeq t1 t2, st2), memo2)
      | none => (none, memo2)
    | none => (none, memo1)

  | .mk (.alt g1 g2) =>
    -- Try first alternative
    let (r1, memo1) := parseGrammar fuel' prods g1 st
    match r1 with
    | some result => (some result, memo1)
    | none =>
      -- First failed, try second with updated memo
      let st' := { st with memo := memo1 }
      parseGrammar fuel' prods g2 st'

  | .mk (.star g') =>
    let rec go (f : Nat) (acc : List Term) (st : ParseState) (memo : MemoTable) : ParseResult :=
      match f with
      | 0 => (some (.con "seq" acc, st), memo)
      | f' + 1 =>
        let st' := { st with memo := memo }
        let (r, memo') := parseGrammar f' prods g' st'
        match r with
        | some (t, st'') => go f' (acc ++ [t]) st'' memo'
        | none => (some (.con "seq" acc, st), memo')
    go fuel' [] st st.memo

  | .mk (.bind x g') =>
    let (r, memo') := parseGrammar fuel' prods g' st
    match r with
    | some (t, st') => (some (t, { st' with binds := (x, t) :: st'.binds }), memo')
    | none => (none, memo')

  | .mk (.node name g') =>
    let (r, memo') := parseGrammar fuel' prods g' st
    match r with
    | some (t, st') => (some (wrapNode name t, st'), memo')
    | none => (none, memo')

  -- PEG extensions

  | .mk (.cut g') =>
    -- Cut: once g' succeeds, the result is committed (no backtracking in caller)
    -- For now, parse like normal - full cut semantics would require continuation-passing
    parseGrammar fuel' prods g' st

  | .mk (.ordered g1 g2) =>
    -- Ordered choice (PEG): try g1 first, only try g2 if g1 fails completely
    let (r1, memo1) := parseGrammar fuel' prods g1 st
    match r1 with
    | some result => (some result, memo1)
    | none =>
      let st' := { st with memo := memo1 }
      parseGrammar fuel' prods g2 st'

  | .mk (.longest gs) =>
    -- At token level, try all alternatives and pick the longest (most tokens consumed)
    let results := gs.filterMap fun g =>
      let (r, _) := parseGrammar fuel' prods g st
      r
    match results with
    | [] => (none, st.memo)
    | rs =>
      let best := rs.foldl (fun best (t, st') =>
        match best with
        | none => some (t, st')
        | some (bestT, bestSt) =>
          if st'.pos > bestSt.pos then some (t, st')
          else some (bestT, bestSt)
      ) none
      (best, st.memo)

/-- Interpret a GrammarExpr for printing (backward direction).
    Uses fuel for termination. -/
def printGrammar (fuel : Nat) (prods : Productions) (g : GrammarExpr) (t : Term) (acc : List Token) : Option (List Token) :=
  match fuel with
  | 0 => none  -- fuel exhausted
  | fuel' + 1 =>
  match g with
  | .mk .empty => some acc

  | .mk (.lit s) => some (acc ++ [.sym s])

  | .mk (.ref name) =>
    -- Handle built-in token types (TOKEN.*) specially
    if name.startsWith "TOKEN." then
      let tokType := name.drop 6  -- Remove "TOKEN." prefix
      -- Unwrap single-element seq if present
      let t' := match t with
        | .con "seq" [x] => x
        | _ => t
      match tokType, t' with
      | "ident", .var s => some (acc ++ [.ident s])
      | "ident", .lit s => some (acc ++ [.ident s])  -- Also handle lit
      | "string", .lit s => some (acc ++ [.lit s])
      | "number", .lit s => some (acc ++ [.number s])
      | "sym", .var s => some (acc ++ [.sym s])
      | _, _ => none
    else
      -- Use findAllProductions to combine multiple alternatives
      match findAllProductions prods name with
      | some g' => printGrammar fuel' prods g' t acc
      | none => none

  | .mk (.seq g1 g2) =>
    let (t1, t2) := splitSeq t
    match printGrammar fuel' prods g1 t1 acc with
    | some acc' => printGrammar fuel' prods g2 t2 acc'
    | none => none

  | .mk (.alt g1 g2) =>
    printGrammar fuel' prods g1 t acc <|> printGrammar fuel' prods g2 t acc

  | .mk (.star g') =>
    match t with
    | .con "seq" ts =>
      let rec go (f : Nat) (ts : List Term) (acc : List Token) : Option (List Token) :=
        match f, ts with
        | 0, _ => some acc
        | _, [] => some acc
        | f' + 1, t' :: rest =>
          match printGrammar f' prods g' t' acc with
          | some acc' => go f' rest acc'
          | none => none
      go fuel' ts acc
    | _ => some acc

  | .mk (.bind _ g') => printGrammar fuel' prods g' t acc

  | .mk (.node name g') =>
    -- Only succeed if the term is a node with matching name
    match t with
    | .con n ts =>
      if n == name then
        let t' := Term.con "seq" ts
        printGrammar fuel' prods g' t' acc
      else none  -- Node name doesn't match
    | _ => none  -- Not a node

  -- PEG extensions

  | .mk (.cut g') =>
    -- For printing, cut has no effect (it's a parsing-only construct)
    printGrammar fuel' prods g' t acc

  | .mk (.ordered g1 g2) =>
    -- For printing, ordered choice is like regular alt
    printGrammar fuel' prods g1 t acc <|> printGrammar fuel' prods g2 t acc

  | .mk (.longest gs) =>
    -- For printing, longest is like trying alternatives
    gs.findSome? (printGrammar fuel' prods · t acc)

/-! ## Parameterized Grammar Interpretation (AST typeclass) -/

/-- ParseState parameterized over AST type -/
structure ParseStateT (α : Type) where
  tokens : TokenStream
  binds : List (String × α) := []

/-- Result of parameterized grammar interpretation -/
abbrev ParseResultT (α : Type) := Option (α × ParseStateT α)

/-- Combine two AST nodes into a sequence (parameterized) -/
def combineSeqT [AST α] (t1 t2 : α) : α := AST.seq t1 t2

/-- Wrap with node name (parameterized) -/
def wrapNodeT [AST α] (name : String) (inner : α) : α := AST.con name [inner]

mutual
/-- Parameterized grammar parser: builds into any AST type. Total via fuel. -/
def parseGrammarT [AST α] (fuel : Nat) (prods : Productions) (g : GrammarExpr)
    (st : ParseStateT α) : ParseResultT α :=
  match fuel with
  | 0 => none  -- fuel exhausted
  | fuel' + 1 =>
    match g with
    | .mk .empty => some (AST.unit, st)

    | .mk (.lit s) =>
      match st.tokens with
      | .lit l :: rest => if l == s then some (AST.lit s, { st with tokens := rest }) else none
      | .sym l :: rest => if l == s then some (AST.lit s, { st with tokens := rest }) else none
      | .ident l :: rest => if l == s then some (AST.lit s, { st with tokens := rest }) else none
      | _ => none

    | .mk (.ref name) =>
      -- Handle built-in token types (TOKEN.*)
      if name.startsWith "TOKEN." then
        let tokType := name.drop 6
        match tokType, st.tokens with
        | "ident",   .ident s :: rest  => some (AST.var s, { st with tokens := rest })
        | "string",  .lit s :: rest    =>
          -- Match "..." string literals (not '...' char literals)
          if s.startsWith "\"" then
            some (AST.lit s, { st with tokens := rest })
          else none
        | "char",    .lit s :: rest    =>
          if s.startsWith "'" && s.endsWith "'" then
            some (AST.lit s, { st with tokens := rest })
          else none
        | "number",  .number s :: rest => some (AST.lit s, { st with tokens := rest })
        | "special", .sym s :: rest    =>
          if s.startsWith "<" && s.endsWith ">" then
            some (AST.var s, { st with tokens := rest })
          else none
        | _, _ => none
      else
        match findAllProductions prods name with
        | some g' => parseGrammarT fuel' prods g' st
        | none => none

    | .mk (.seq g1 g2) =>
      match parseGrammarT fuel' prods g1 st with
      | some (t1, st1) =>
        match parseGrammarT fuel' prods g2 st1 with
        | some (t2, st2) => some (combineSeqT t1 t2, st2)
        | none => none
      | none => none

    | .mk (.alt g1 g2) =>
      parseGrammarT fuel' prods g1 st <|> parseGrammarT fuel' prods g2 st

    | .mk (.star g') =>
      parseStarT fuel' prods g' [] st

    | .mk (.bind x g') =>
      match parseGrammarT fuel' prods g' st with
      | some (t, st') => some (t, { st' with binds := (x, t) :: st'.binds })
      | none => none

    | .mk (.node name g') =>
      match parseGrammarT fuel' prods g' st with
      | some (t, st') => some (wrapNodeT name t, st')
      | none => none

    -- PEG extensions

    | .mk (.cut g') =>
      -- Cut: parse like normal (full cut semantics would need continuations)
      parseGrammarT fuel' prods g' st

    | .mk (.ordered g1 g2) =>
      -- Ordered choice: try g1 first, only try g2 if g1 fails
      match parseGrammarT fuel' prods g1 st with
      | some result => some result
      | none => parseGrammarT fuel' prods g2 st

    | .mk (.longest gs) =>
      -- Maximal munch at token level: try all, pick longest
      let results := gs.filterMap (parseGrammarT fuel' prods · st)
      match results with
      | [] => none
      | rs =>
        rs.foldl (fun best (t, st') =>
          match best with
          | none => some (t, st')
          | some (bestT, bestSt) =>
            if st'.tokens.length < bestSt.tokens.length then some (t, st')  -- fewer remaining = more consumed
            else some (bestT, bestSt)
        ) none
termination_by fuel

/-- Helper: parse a star (zero or more) with fuel -/
def parseStarT [AST α] (fuel : Nat) (prods : Productions) (g' : GrammarExpr)
    (acc : List α) (st : ParseStateT α) : ParseResultT α :=
  match fuel with
  | 0 => some (AST.con "seq" acc, st)
  | f + 1 =>
    match parseGrammarT f prods g' st with
    | some (t, st') => parseStarT f prods g' (acc ++ [t]) st'
    | none => some (AST.con "seq" acc, st)
termination_by fuel
end

/-- Convenience: parse with specific AST target -/
def parseGrammarAs (α : Type) [AST α] (prods : Productions) (g : GrammarExpr)
    (tokens : TokenStream) : Option α :=
  match parseGrammarT defaultFuel prods g ⟨tokens, []⟩ with
  | some (result, _) => some result
  | none => none

/-! ## Language Interpretation -/

/-- A Language gives us two Isos:
    1. Grammar: TokenStream ⇌ Term (syntax)
    2. Rules:   Term ⇌ Term        (semantics) -/
structure LangInterp where
  /-- Parse: tokens → term -/
  parse : TokenStream → Option Term
  /-- Print: term → tokens -/
  print : Term → Option TokenStream
  /-- Normalize: term → term (via rules) -/
  normalize : Term → Term
  /-- Expand: term → term (reverse normalize) -/
  expand : Term → Term

/-- Build interpreter from a Language -/
def Language.toInterp (lang : Language) (startProd : String) : LangInterp where
  parse := fun tokens =>
    let prods := lang.allGrammar
    let st : ParseState := { tokens := tokens, binds := [] }
    match prods.find? (·.1 == startProd) with
    | some (_, g) =>
      let (result, _) := parseGrammar defaultFuel prods g st
      match result with
      | some (t, st') => if st'.tokens.isEmpty then some t else none
      | none => none
    | none => none

  print := fun t =>
    let prods := lang.allGrammar
    match prods.find? (·.1 == startProd) with
    | some (_, g) => printGrammar defaultFuel prods g t []
    | none => none

  normalize := fun t =>
    let reducer := lang.interpreter
    reducer.forward t |>.getD t

  expand := fun t =>
    let reducer := lang.interpreter
    reducer.backward t |>.getD t

/-- Convert grammar interpretation to an Iso -/
def grammarToIso (prods : Productions) (startProd : String) : Iso TokenStream Term where
  forward := fun tokens =>
    let st : ParseState := { tokens := tokens, binds := [] }
    match prods.find? (·.1 == startProd) with
    | some (_, g) =>
      let (result, _) := parseGrammar defaultFuel prods g st
      match result with
      | some (t, st') => if st'.tokens.isEmpty then some t else none
      | none => none
    | none => none
  backward := fun t =>
    match prods.find? (·.1 == startProd) with
    | some (_, g) => printGrammar defaultFuel prods g t []
    | none => none

end Lego
