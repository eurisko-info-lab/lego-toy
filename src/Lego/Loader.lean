/-
  Lego.Loader: Load grammars from parsed .lego files

  This module converts parsed AST (DGrammar, DPiece nodes) back into
  executable Productions that can parse arbitrary input files.

  Key insight: The grammar is just data - we can interpret it at runtime.
-/

import Lego.Algebra
import Lego.Attr
import Lego.Interp
import Lego.Bootstrap
import Lego.Validation
import Lego.Util
import Std.Data.HashMap

namespace Lego.Loader

open Lego
open Lego.Validation
open Std (HashMap)

/-! ## Helper Functions -/

/-- Split a list of Terms by .lit "|" tokens (the alternation separator).
    Returns groups of terms that form each alternative.
    Each group is combined into a seq if multiple elements. -/
def splitByPipe (ts : List Term) : List Term :=
  let rec go (acc : List Term) (current : List Term) : List Term :=
    match current with
    | [] =>
      if acc.isEmpty then [] else [mkSeq acc.reverse]
    | .lit "|" :: rest =>
      mkSeq acc.reverse :: go [] rest
    | t :: rest =>
      go (t :: acc) rest
  go [] ts
where
  mkSeq : List Term → Term
  | [] => .con "empty" []
  | [t] => t
  | ts => .con "seq" ts

/-- Split a list of Terms by .lit "/" tokens (PEG ordered choice separator).
    Returns groups of terms that form each alternative.
    Each group is combined into a seq if multiple elements. -/
def splitBySlash (ts : List Term) : List Term :=
  let rec go (acc : List Term) (current : List Term) : List Term :=
    match current with
    | [] =>
      if acc.isEmpty then [] else [mkSeq acc.reverse]
    | .lit "/" :: rest =>
      mkSeq acc.reverse :: go [] rest
    | t :: rest =>
      go (t :: acc) rest
  go [] ts
where
  mkSeq : List Term → Term
  | [] => .con "empty" []
  | [t] => t
  | ts => .con "seq" ts

/-! ## Parent Extraction -/

/-- Extract parent language names from a DLang node.
    Structure: DLang [lang, ident(langName), imports?, :=, langBody]
    Where imports = DImports [(, ident(parent1), ...)]. -/
partial def extractParentNames (ast : Term) : List String :=
  go ast
where
  go (t : Term) : List String :=
    match t with
    | .con "DLang" args =>
      -- Look for DImports in args
      args.flatMap fun arg =>
        match arg with
        | .con "DImports" importArgs =>
          -- Extract all ident names from imports
          importArgs.filterMap fun ia =>
            match ia with
            | .con "ident" [.var name] => some name
            | _ => none
        | .con "seq" ts => ts.flatMap go
        | _ => []
    | .con "seq" ts => ts.flatMap go
    | .con _ ts => ts.flatMap go
    | _ => []

/-! ## AST → GrammarExpr -/

/-- Flatten nested seq terms into a list -/
partial def flattenSeq (t : Term) : List Term :=
  match t with
  | .con "seq" [left, right] => flattenSeq left ++ flattenSeq right
  | other => [other]

/-- Extract annotation (conName, rest) from flattened args ending in → ident -/
def extractAnnotationFromFlat (args : List Term) : Option (String × List Term) :=
  match args.reverse with
  | .con "ident" [.var conName] :: .lit "→" :: rest => some (conName, rest.reverse)
  | _ => none

/-- Resolve an unqualified reference name to its qualified form.
    nameMap maps unqualified names to qualified names (e.g., "defndecl" → "Definitions.defndecl").
    Returns the qualified name if found, otherwise the original name. -/
def resolveRefName (nameMap : HashMap String String) (name : String) : String :=
  -- Already qualified (contains dot) or is a TOKEN reference
  if name.contains '.' || name.startsWith "TOKEN." then name
  else
    -- Look up in name map
    match nameMap.get? name with
    | some qualName => qualName
    | none => name  -- keep as-is (might be a built-in like "ident")

/-- Convert a parsed grammar expression AST back to GrammarExpr.
    nameMap is used to resolve unqualified references to qualified names. -/
partial def astToGrammarExpr (nameMap : HashMap String String := HashMap.emptyWithCapacity) (t : Term) : Option GrammarExpr :=
  match t with
  -- Empty
  | .con "empty" _ => some GrammarExpr.empty

  -- Literal: (lit (string "..."))
  | .con "lit" [.con "string" [.lit s]] =>
    -- Strip quotes from string literal
    let s' := if s.startsWith "\"" && s.endsWith "\"" then
                s.drop 1 |>.dropRight 1
              else s
    some (GrammarExpr.lit s')

  -- Character literal: (chr (char "'x'")) or (chr (char "'\x'"))
  | .con "chr" [.con "char" [.lit s]] =>
    -- Strip quotes from char literal 'x' → x, '\n' → newline, etc.
    let inner := if s.startsWith "'" && s.endsWith "'" then
                   s.drop 1 |>.dropRight 1
                 else s
    -- Handle escape sequences
    let s' := if inner.startsWith "\\" && inner.length == 2 then
                let escaped := inner.data[1]!
                match escaped with
                | 'n' => "\n"
                | 't' => "\t"
                | 'r' => "\r"
                | '\\' => "\\"
                | '\'' => "'"
                | '"' => "\""
                | c => s!"{c}"  -- Unknown escape, keep as-is
              else inner
    some (GrammarExpr.lit s')

  -- Reference: (ref (ident name))
  | .con "ref" [.con "ident" [.var name]] =>
    -- Resolve unqualified references using the name map (parse-time resolution)
    let resolvedName := resolveRefName nameMap name
    some (GrammarExpr.ref resolvedName)

  -- Special: <ident>, <string>, etc.
  | .con "special" [.var special] =>
    -- Convert <ident> to TOKEN.ident
    if special.startsWith "<" && special.endsWith ">" then
      let inner := special.drop 1 |>.dropRight 1
      some (GrammarExpr.ref s!"TOKEN.{inner}")
    else
      some (GrammarExpr.ref special)

  -- Sequence: (seq g1 g2 ...)
  -- Build right-associated sequence: seq(a, seq(b, seq(c, d)))
  -- This is important for printing: seq(g1, g2) means g1 is first element, g2 is rest
  | .con "seq" gs =>
    match gs.filterMap (astToGrammarExpr nameMap) with
    | [] => some GrammarExpr.empty
    | [g] => some g
    | gs => some (gs.foldr GrammarExpr.seq GrammarExpr.empty)

  -- Alternative: (alt g1 "|" g2 "|" g3 ...)
  -- Split by .lit "|" tokens, then fold into nested alts
  | .con "alt" args =>
    let parts := splitByPipe args
    match parts with
    | [] => none
    | [single] => astToGrammarExpr nameMap single
    | first :: rest => do
      let first' ← astToGrammarExpr nameMap first
      rest.foldlM (fun acc part => do
        let g' ← astToGrammarExpr nameMap part
        pure (GrammarExpr.alt acc g')) first'

  -- Star: (star g "*")
  | .con "star" [g, _] => do
    let g' ← astToGrammarExpr nameMap g
    pure (GrammarExpr.star g')

  -- Plus: (plus g "+")
  | .con "plus" [g, _] => do
    let g' ← astToGrammarExpr nameMap g
    pure (GrammarExpr.plus g')

  -- Optional: (opt g "?")
  | .con "opt" [g, _] => do
    let g' ← astToGrammarExpr nameMap g
    pure (GrammarExpr.alt g' GrammarExpr.empty)

  -- PEG extensions

  -- Cut: (cut "!" g) - commit point
  | .con "cut" [_, g] => do
    let g' ← astToGrammarExpr nameMap g
    pure (GrammarExpr.cut g')
  | .con "cut" [g] => do
    let g' ← astToGrammarExpr nameMap g
    pure (GrammarExpr.cut g')

  -- Ordered choice: (ordered g1 "/" g2) - PEG-style first match wins
  | .con "ordered" args =>
    let parts := splitBySlash args
    match parts with
    | [] => none
    | [single] => astToGrammarExpr nameMap single
    | first :: rest => do
      let first' ← astToGrammarExpr nameMap first
      rest.foldlM (fun acc part => do
        let g' ← astToGrammarExpr nameMap part
        pure (GrammarExpr.ordered acc g')) first'

  -- Longest match: (longest "#longest" "[" g1 "," g2 "," ... "]")
  -- Note: The exprList grammar produces (expr (seq "," expr) (seq "," expr) ...)
  -- where each expr might itself be multiple tokens that need sequencing
  | .con "longest" args =>
    -- First, filter out #longest, [, ]
    let items := args.filter fun t =>
      match t with
      | .lit "#longest" => false
      | .lit "[" => false
      | .lit "]" => false
      | _ => true
    -- Group items: collect items until we see (seq "," ...), then start new group
    let (groups, current) := items.foldl (init := ([], [])) fun (groups, current) t =>
      match t with
      | .con "seq" seqArgs =>
        -- This is (seq "," expr1 expr2 ...) - finish current group, start new with seq contents
        let exprs := seqArgs.filter (· != .lit ",")
        if current.isEmpty then
          (groups, exprs)
        else
          (groups ++ [current], exprs)
      | other =>
        (groups, current ++ [other])
    let allGroups := if current.isEmpty then groups else groups ++ [current]
    -- Convert each group to a grammar expression (fold into sequence)
    let gexprs := allGroups.filterMap fun group =>
      let converted := group.filterMap (astToGrammarExpr nameMap)
      match converted with
      | [] => none
      | [g] => some g
      | gs => some (gs.foldr GrammarExpr.seq GrammarExpr.empty)  -- right-fold for printing
    if gexprs.isEmpty then none
    else some (GrammarExpr.longest gexprs)

  -- Group: (group "(" expr... ")")
  -- The group may contain multiple expressions that need to be sequenced
  | .con "group" args =>
    match args with
    | [] => none
    | [_] => none  -- just "(" - invalid
    | [_, _] => none  -- "(" ")" - invalid
    | [_, g, _] => astToGrammarExpr nameMap g  -- single expr
    | _ =>
      -- Multiple expressions: drop parens and convert middle to seq
      let middle := args.drop 1 |>.dropLast
      let gexprs := middle.filterMap (astToGrammarExpr nameMap)
      match gexprs with
      | [] => none
      | [g] => some g
      | gs => some (gs.foldr GrammarExpr.seq GrammarExpr.empty)  -- right-fold for printing

  -- Annotated: (annotated ... "→" (ident conName))
  -- This wraps a grammar expression with a constructor name
  | .con "annotated" args =>
    -- Flatten and find the → ident part
    let flatArgs := args.flatMap flattenSeq
    -- Look for → ident at end
    match extractAnnotationFromFlat flatArgs with
    | some (conName, rest) =>
      -- Recursively convert the rest as a sequence
      let gexprs := rest.filterMap (astToGrammarExpr nameMap)
      match gexprs with
      | [] => none
      | [g] => some (GrammarExpr.node conName g)
      | gs => some (GrammarExpr.node conName (gs.foldr GrammarExpr.seq GrammarExpr.empty))  -- right-fold
    | none => none  -- malformed annotated

  -- Layout annotations: @nl, @indent, @dedent, @sp, @nsp
  -- These are for pretty-printing - generate layout expressions
  | .con "layoutNl" _ => some (GrammarExpr.layout "nl")
  | .con "layoutIndent" _ => some (GrammarExpr.layout "indent")
  | .con "layoutDedent" _ => some (GrammarExpr.layout "dedent")
  | .con "layoutSpace" _ => some (GrammarExpr.layout "sp")
  | .con "layoutNoSpace" _ => some (GrammarExpr.layout "nsp")

  -- Fallback for unrecognized patterns
  | _ => none

/-- Extract production name from a grammar declaration -/
def extractProdName (pieceName : String) (gramDecl : Term) : Option String :=
  match gramDecl with
  | .con "DGrammar" args =>
    -- Flatten nested seq and look for ident at start
    let flatArgs := args.flatMap flattenSeq
    match flatArgs with
    | .con "ident" [.var prodName] :: _ => some s!"{pieceName}.{prodName}"
    | _ => none
  | _ => none

/-- Extract constructor annotation from flattened args (→ conName) if present -/
def extractConstructorAnnotation (args : List Term) : Option String :=
  -- Look for pattern: ... → ident ; at end of flattened seq
  match args.reverse with
  | .lit ";" :: .con "ident" [.var conName] :: .lit "→" :: _ => some conName
  | _ => none

/-- Strip constructor annotation from flattened args if present -/
def stripConstructorAnnotation (args : List Term) : List Term :=
  match args.reverse with
  | semi :: .con "ident" [_] :: .lit "→" :: rest => (semi :: rest).reverse
  | _ => args

/-- Extract grammar expression from a grammar declaration -/
def extractGrammarExpr (nameMap : HashMap String String) (gramDecl : Term) : Option GrammarExpr :=
  match gramDecl with
  | .con "DGrammar" args =>
    -- DGrammar now has a single nested seq child - flatten it first
    let flatArgs := args.flatMap flattenSeq
    -- Structure after flattening: [ident, "::=", expr1, expr2, ..., ("→" ident)?, ";"]
    if flatArgs.length < 4 then none  -- need at least: name, ::=, one expr, ;
    else
      -- Check for constructor annotation
      let conName := extractConstructorAnnotation flatArgs
      let cleanArgs := stripConstructorAnnotation flatArgs
      let exprArgs := cleanArgs.drop 2 |>.dropLast  -- skip name, ::=, ;
      let gexprs := exprArgs.filterMap (astToGrammarExpr nameMap)
      -- Build right-associated sequence for proper printing
      let baseExpr := match gexprs with
        | [] => none
        | [g] => some g  -- single expression
        | gs => some (gs.foldr GrammarExpr.seq GrammarExpr.empty)  -- right-fold for printing
      -- Wrap with node if constructor annotation present
      match conName, baseExpr with
      | some name, some g => some (GrammarExpr.node name g)
      | none, some g => some g
      | _, none => none
  | _ => none

/-- Extract all production names from a piece declaration (first pass) -/
def extractPieceProductionNames (pieceDecl : Term) : List (String × String) :=
  match pieceDecl with
  | .con "DPiece" (.lit _ :: .con "ident" [.var pieceName] :: gramDecls) =>
    gramDecls.filterMap fun g =>
      match extractProdName pieceName g with
      | some qualName =>
        -- Extract unqualified name (after the dot)
        let unqualName := match qualName.splitOn "." with
          | [_, n] => n
          | _ => qualName
        some (unqualName, qualName)
      | none => none
  | .con "DToken" (.lit _ :: .con "ident" [.var pieceName] :: gramDecls) =>
    gramDecls.filterMap fun g =>
      match extractProdName pieceName g with
      | some qualName =>
        let unqualName := match qualName.splitOn "." with
          | [_, n] => n
          | _ => qualName
        some (unqualName, qualName)
      | none => none
  | _ => []

/-- Extract all productions from a piece declaration (second pass, with name resolution) -/
def extractPieceProductions (nameMap : HashMap String String) (pieceDecl : Term) : List (String × GrammarExpr) :=
  match pieceDecl with
  | .con "DPiece" (.lit _ :: .con "ident" [.var pieceName] :: gramDecls) =>
    gramDecls.filterMap fun g =>
      match extractProdName pieceName g, extractGrammarExpr nameMap g with
      | some name, some expr => some (name, expr)
      | _, _ => none
  | .con "DToken" (.lit _ :: .con "ident" [.var pieceName] :: gramDecls) =>
    gramDecls.filterMap fun g =>
      match extractProdName pieceName g, extractGrammarExpr nameMap g with
      | some name, some expr => some (name, expr)
      | _, _ => none
  | _ => []

/-- Built-in productions available to all grammars -/
def builtinProductions : Productions := [
  -- name matches any identifier token
  ("Term.name", GrammarExpr.ref "TOKEN.ident"),
  -- Common aliases
  ("name", GrammarExpr.ref "TOKEN.ident"),
  ("ident", GrammarExpr.ref "TOKEN.ident"),
  ("string", GrammarExpr.ref "TOKEN.string"),
  ("number", GrammarExpr.ref "TOKEN.number"),
  -- Cross-file aliases for common Bootstrap productions
  ("template", GrammarExpr.ref "Template.template"),
  ("pattern", GrammarExpr.ref "Pattern.pattern"),
  ("term", GrammarExpr.ref "Term.term")
]

/-- First pass: collect all production names from AST (only piece, not token) -/
partial def collectProductionNames (ast : Term) : List (String × String) :=
  go ast
where
  go (t : Term) : List (String × String) :=
    match t with
    | .con "DLang" ts => ts.flatMap go
    | .con "DPiece" _ => extractPieceProductionNames t
    | .con "DToken" _ => []  -- Skip token productions - they don't affect parser name resolution
    | .con "seq" ts => ts.flatMap go
    | .con _ ts => ts.flatMap go
    | _ => []

/-- Build name resolution map from collected names -/
def buildNameMap (names : List (String × String)) : HashMap String String :=
  names.foldl (init := HashMap.emptyWithCapacity) fun acc (unqual, qual) =>
    acc.insert unqual qual

/-- Extract productions from a parsed .lego file AST (without builtins).
    Two-pass approach: first collect names, then extract with resolution. -/
partial def extractProductionsOnly (ast : Term) : Productions :=
  -- First pass: collect all production names
  let names := collectProductionNames ast
  let nameMap := buildNameMap names
  -- Second pass: extract productions with name resolution
  go nameMap ast
where
  go (nameMap : HashMap String String) (t : Term) : Productions :=
    match t with
    | .con "DLang" ts =>
      ts.flatMap (go nameMap)
    | .con "DPiece" _ =>
      extractPieceProductions nameMap t
    | .con "DToken" _ =>
      []  -- Skip token productions - they're handled by extractTokenProductions
    | .con "seq" ts =>
      ts.flatMap (go nameMap)
    | .con _ ts =>
      ts.flatMap (go nameMap)
    | _ => []

/-- Extract all productions from a parsed .lego file AST (includes builtins) -/
def extractAllProductions (ast : Term) : Productions :=
  builtinProductions ++ extractProductionsOnly ast

/-- Collect only token production names from AST (for token name resolution) -/
partial def collectTokenProductionNames (ast : Term) : List (String × String) :=
  go ast
where
  go (t : Term) : List (String × String) :=
    match t with
    | .con "DLang" ts => ts.flatMap go
    | .con "DToken" _ => extractPieceProductionNames t
    | .con "seq" ts => ts.flatMap go
    | .con _ ts => ts.flatMap go
    | _ => []

/-- Extract only token (lexer) productions from a parsed .lego file AST -/
partial def extractTokenProductions (ast : Term) : Productions :=
  -- First pass: collect all TOKEN production names (not piece names)
  let names := collectTokenProductionNames ast
  let nameMap := buildNameMap names
  -- Second pass: extract token productions with name resolution
  go nameMap ast
where
  go (nameMap : HashMap String String) (t : Term) : Productions :=
    match t with
    | .con "DLang" ts =>
      ts.flatMap (go nameMap)
    | .con "DToken" _ =>
      extractPieceProductions nameMap t
    | .con "seq" ts =>
      ts.flatMap (go nameMap)
    | .con _ ts =>
      ts.flatMap (go nameMap)
    | _ => []

/-- Main token production names - these are the top-level tokenizing productions.
    Token.operator uses #longest internally for maximal munch.
    Character class productions (digit, alpha, etc.) are NOT included - they're
    only used as building blocks for these main productions.
    Note: We support both old-style (op3, op2, sym) and new-style (operator). -/
def mainTokenProdNames : List String :=
  [ "Token.special"       -- <name> syntax
  , "Token.hashident"     -- Hash-prefixed keywords (#longest)
  , "Token.ident"         -- Identifiers
  , "Token.number"        -- Numbers
  , "Token.string"        -- String literals
  , "Token.char"          -- Character literals
  , "Token.ws"            -- Whitespace (skipped)
  , "Token.comment"       -- Line comments (skipped)
  , "Token.blockComment"  -- Block comments /- ... -/ (skipped)
  , "Token.operator"      -- All operators (new-style, uses #longest)
  , "Token.op3"           -- 3-char operators (old-style, for backwards compat)
  , "Token.op2"           -- 2-char operators (old-style)
  , "Token.sym"           -- Single symbol (old-style fallback)
  ]

/-- Get main token production names for tokenization.
    Filters to only include productions that actually exist in the grammar. -/
def getMainTokenProds (tokenProds : Productions) : List String :=
  let prodNames := tokenProds.map (·.1) |>.toArray
  mainTokenProdNames.filter fun name => prodNames.contains name

/-! ## Symbol Extraction for Tokenization -/

/-- Extract all literal symbols from a grammar expression -/
partial def extractSymbols (g : GrammarExpr) : List String :=
  match g with
  | .mk .empty => []
  | .mk (.lit s) => [s]
  | .mk (.ref _) => []
  | .mk (.seq g1 g2) => extractSymbols g1 ++ extractSymbols g2
  | .mk (.alt g1 g2) => extractSymbols g1 ++ extractSymbols g2
  | .mk (.star g') => extractSymbols g'
  | .mk (.bind _ g') => extractSymbols g'
  | .mk (.node _ g') => extractSymbols g'
  -- PEG extensions
  | .mk (.cut g') => extractSymbols g'
  | .mk (.ordered g1 g2) => extractSymbols g1 ++ extractSymbols g2
  | .mk (.longest gs) => gs.flatMap extractSymbols
  -- Layout annotations
  | .mk (.layout _) => []

/-- Extract all symbols from productions -/
def extractAllSymbols (prods : Productions) : List String :=
  prods.flatMap (fun (_, g) => extractSymbols g) |>.eraseDups


/-- Extract literals that appear at the START of a grammar expression -/
partial def extractStartLiterals (g : GrammarExpr) : List String :=
  match g with
  | .mk .empty => []
  | .mk (.lit s) => [s]
  | .mk (.ref _) => []
  | .mk (.seq g1 _) => extractStartLiterals g1  -- only look at start
  | .mk (.alt g1 g2) => extractStartLiterals g1 ++ extractStartLiterals g2
  | .mk (.star g') => extractStartLiterals g'
  | .mk (.bind _ g') => extractStartLiterals g'
  | .mk (.node _ g') => extractStartLiterals g'
  -- PEG extensions
  | .mk (.cut g') => extractStartLiterals g'
  | .mk (.ordered g1 g2) => extractStartLiterals g1 ++ extractStartLiterals g2
  | .mk (.longest gs) => gs.flatMap extractStartLiterals
  -- Layout annotations
  | .mk (.layout _) => []

/-- Check if a grammar expression ends with a star (greedy) -/
partial def endsWithStar : GrammarExpr → Bool
  | .mk .empty => false
  | .mk (.lit _) => false
  | .mk (.ref _) => false
  | .mk (.seq _ g2) => endsWithStar g2
  | .mk (.alt g1 g2) => endsWithStar g1 || endsWithStar g2
  | .mk (.star _) => true
  | .mk (.bind _ g') => endsWithStar g'
  | .mk (.node _ g') => endsWithStar g'
  -- PEG extensions
  | .mk (.cut g') => endsWithStar g'
  | .mk (.ordered g1 g2) => endsWithStar g1 || endsWithStar g2
  | .mk (.longest gs) => gs.any endsWithStar
  -- Layout annotations
  | .mk (.layout _) => false

/-- Helper: check if a grammar can end via ref to a star-ending production -/
partial def canEndViaRef (starEnds : List String) (g : GrammarExpr) : Bool :=
  match g with
  | .mk .empty => false
  | .mk (.lit _) => false
  | .mk (.ref name) => starEnds.contains name
  | .mk (.seq _ g2) => canEndViaRef starEnds g2
  | .mk (.alt g1 g2) => canEndViaRef starEnds g1 || canEndViaRef starEnds g2
  | .mk (.star _) => true
  | .mk (.bind _ g') => canEndViaRef starEnds g'
  | .mk (.node _ g') => canEndViaRef starEnds g'
  -- PEG extensions
  | .mk (.cut g') => canEndViaRef starEnds g'
  | .mk (.ordered g1 g2) => canEndViaRef starEnds g1 || canEndViaRef starEnds g2
  | .mk (.longest gs) => gs.any (canEndViaRef starEnds ·)
  -- Layout annotations
  | .mk (.layout _) => false

/-- Compute which productions can transitively end with a star.
    Returns a set of production names that can end with star.
    Uses iterative fixed-point computation for efficiency. -/
def computeStarEndingProds (prods : Productions) : List String :=
  -- Build prodMap for O(1) lookup
  let prodMap := prods.foldl (init := HashMap.emptyWithCapacity prods.length) fun acc (name, g) =>
    acc.insert name g
  -- Initialize: all productions that DIRECTLY end with star
  let directEnds := prods.filterMap fun (name, g) =>
    if endsWithStar g then some name else none
  -- Fixed-point: add productions that end with a ref to a star-ending prod
  go 20 prodMap directEnds
where
  go : Nat → HashMap String GrammarExpr → List String → List String
    | 0, _, starEnds => starEnds
    | fuel+1, prodMap, starEnds =>
      -- Find new productions that end via ref to star-ending prod
      let newEnds := prodMap.fold (init := starEnds) fun acc name g =>
        if acc.contains name then acc
        else if canEndViaRef starEnds g then name :: acc
        else acc
      -- Fixed point?
      if newEnds.length == starEnds.length then starEnds
      else go fuel prodMap newEnds

/-- Check if a production (transitively) can end with a star.
    Uses pre-computed set for O(1) lookup. -/
def canEndWithStar (starEndingProds : List String) (prodName : String) : Bool :=
  starEndingProds.contains prodName

/-- Extract the reference at the END of a grammar expression, if any -/
partial def extractEndRef : GrammarExpr → Option String
  | .mk .empty => none
  | .mk (.lit _) => none
  | .mk (.ref name) => some name
  | .mk (.seq _ g2) => extractEndRef g2  -- look at the end
  | .mk (.alt g1 g2) =>
    -- Both branches must end with same ref (or we return none)
    match extractEndRef g1, extractEndRef g2 with
    | some r1, some r2 => if r1 == r2 then some r1 else none
    | _, _ => none
  | .mk (.star _) => none  -- star doesn't have a fixed end ref
  | .mk (.bind _ g') => extractEndRef g'
  | .mk (.node _ g') => extractEndRef g'
  -- PEG extensions
  | .mk (.cut g') => extractEndRef g'
  | .mk (.ordered g1 g2) =>
    match extractEndRef g1, extractEndRef g2 with
    | some r1, some r2 => if r1 == r2 then some r1 else none
    | _, _ => none
  | .mk (.longest gs) =>
    match gs.filterMap extractEndRef |>.eraseDups with
    | [r] => some r
    | _ => none
  -- Layout annotations
  | .mk (.layout _) => none

/-- Find literals that follow a reference in a grammar.
    Returns pairs of (refName, literalThatFollows).
    Looks for patterns where a ref is at the END of g1 in (seq g1 g2). -/
partial def findRefFollows (g : GrammarExpr) : List (String × String) :=
  match g with
  | .mk .empty => []
  | .mk (.lit _) => []
  | .mk (.ref _) => []
  | .mk (.seq g1 g2) =>
    let fromRest := findRefFollows g1 ++ findRefFollows g2
    -- If g1 ENDS with a ref, g2's start literals follow it
    match extractEndRef g1 with
    | some name =>
      let follows := extractStartLiterals g2
      follows.map (fun lit => (name, lit)) ++ fromRest
    | none => fromRest
  | .mk (.alt g1 g2) => findRefFollows g1 ++ findRefFollows g2
  | .mk (.star g') => findRefFollows g'
  | .mk (.bind _ g') => findRefFollows g'
  | .mk (.node _ g') => findRefFollows g'
  -- PEG extensions
  | .mk (.cut g') => findRefFollows g'
  | .mk (.ordered g1 g2) => findRefFollows g1 ++ findRefFollows g2
  | .mk (.longest gs) => gs.flatMap findRefFollows
  -- Layout annotations
  | .mk (.layout _) => []

/-- Extract keywords that need to be reserved.

    A keyword needs reservation when:
    1. It follows a reference R in some production
    2. R (transitively) can end with a star

    This finds FOLLOW conflicts where a greedy star could consume
    a keyword that's meant to be a delimiter.

    Example: `letin ::= ... letinvalue "in" ...` where letinvalue
    transitively references appexpr which ends with `appitem*`. -/
def extractKeywords (prods : Productions) : List String :=
  -- Pre-compute which productions can end with star (fixed-point)
  let starEndingProds := computeStarEndingProds prods
  -- Step 1: Find all (ref, followingLiteral) pairs
  let refFollows := prods.flatMap fun (_, g) => findRefFollows g
  -- Step 2: Filter to pairs where the ref can transitively end with star
  let conflictingLits := refFollows.filterMap fun (refName, lit) =>
    if canEndWithStar starEndingProds refName then some lit else none
  -- Step 3: Filter to keyword-like strings
  -- Note: Language-specific keywords should be added by the caller
  conflictingLits.filter Util.isKeywordLikeWithDash |>.eraseDups
where
  /-- Check if a grammar contains a specific literal -/
  containsLiteral (g : GrammarExpr) (lit : String) : Bool :=
    -- Use fold to avoid termination issues
    let allLits := extractAllLiterals g
    allLits.contains lit
  extractAllLiterals (g : GrammarExpr) : List String :=
    match g with
    | .mk .empty => []
    | .mk (.lit s) => [s]
    | .mk (.ref _) => []
    | .mk (.seq g1 g2) => extractAllLiterals g1 ++ extractAllLiterals g2
    | .mk (.alt g1 g2) => extractAllLiterals g1 ++ extractAllLiterals g2
    | .mk (.star g') => extractAllLiterals g'
    | .mk (.bind _ g') => extractAllLiterals g'
    | .mk (.node _ g') => extractAllLiterals g'
    | .mk (.cut g') => extractAllLiterals g'
    | .mk (.ordered g1 g2) => extractAllLiterals g1 ++ extractAllLiterals g2
    | .mk (.longest gs) => gs.flatMap extractAllLiterals
    | .mk (.layout _) => []

/-! ## Validation Helpers -/

/-- Convert Productions list to HashMap for validation -/
def productionsToHashMap (prods : Productions) : HashMap String GrammarExpr :=
  prods.foldl (init := HashMap.emptyWithCapacity) fun acc (name, g) =>
    acc.insert name g

/-- Validate productions and return result -/
def validateProductions (prods : Productions) : ValidationResult :=
  let grammarMap := productionsToHashMap prods
  validateGrammar grammarMap

/-- Validate a full piece (grammar + rules) -/
def validatePiece (prods : Productions) (rules : List Rule) : ValidationResult :=
  let grammarMap := productionsToHashMap prods
  validate grammarMap rules

/-! ## Grammar Loading -/

/-- A loaded grammar ready for parsing -/
structure LoadedGrammar where
  productions : Productions
  tokenProductions : Productions  -- Token-level (lexer) productions
  symbols : List String           -- All literal symbols
  keywords : List String          -- Reserved keywords (identifiers that must be tokenized as symbols)
  startProd : String
  validation : ValidationResult := ValidationResult.empty
  deriving Repr

/-- Load a grammar from parsed AST -/
def loadGrammarFromAST (ast : Term) (startProd : String) : LoadedGrammar :=
  let prods := extractAllProductions ast
  let tokenProds := extractTokenProductions ast
  let symbols := extractAllSymbols prods
  let keywords := extractKeywords prods
  let validationResult := validateProductions prods
  { productions := prods, tokenProductions := tokenProds, symbols := symbols, keywords := keywords, startProd := startProd, validation := validationResult }

/-! ## Parsing with Loaded Grammar -/

/-- Tokenize input using the loaded grammar's token productions.
    NOTE: Grammar inheritance ensures token rules flow from parent to child.
    If tokenProductions is empty, the grammar may not have been loaded correctly. -/
def tokenizeForGrammar (grammar : LoadedGrammar) (input : String) : List Token :=
  if grammar.tokenProductions.isEmpty then
    -- Warning: No token rules found - this usually means grammar wasn't loaded with inheritance
    -- Return empty for now (parser will fail with clear error)
    []
  else
    -- Use grammar-driven tokenizer with keyword reservation
    let mainProds := getMainTokenProds grammar.tokenProductions
    tokenizeWithGrammar defaultFuel grammar.tokenProductions mainProds input grammar.keywords

/-- Parse input using a loaded grammar (uses grammar-driven tokenizer) -/
def parseWithGrammar (grammar : LoadedGrammar) (input : String) : Option Term :=
  let tokens := tokenizeForGrammar grammar input
  let st : ParseState := { tokens := tokens, binds := [] }
  match findAllProductions grammar.productions grammar.startProd with
  | some g =>
    let (result, _) := parseGrammar defaultFuel grammar.productions g st
    match result with
    | some (t, st') => if st'.tokens.isEmpty then some t else none
    | none => none
  | none => none

/-- Parse input with detailed error reporting (uses grammar-driven tokenizer or Bootstrap fallback) -/
def parseWithGrammarE (grammar : LoadedGrammar) (input : String) : Except ParseError Term :=
  let tokens := tokenizeForGrammar grammar input
  let st : ParseState := { tokens := tokens, binds := [], maxPos := 0 }
  match findAllProductions grammar.productions grammar.startProd with
  | some g =>
    let (result, memo) := parseGrammar defaultFuel grammar.productions g st
    match result with
    | some (t, st') =>
      if st'.tokens.isEmpty then
        .ok t
      else
        -- Incomplete parse: use maxPos (furthest position reached) for error location
        let furthestPos := max st'.pos st'.maxPos
        -- Also check memo table for furthest attempted position
        let memoMaxPos := memo.fold (init := furthestPos) fun acc (pos, _) _ => max acc pos
        let errorPos := max furthestPos memoMaxPos
        let remainingAtError := tokens.drop errorPos
        let err : ParseError := {
          message := s!"Incomplete parse at token {errorPos}"
          tokenPos := errorPos
          production := grammar.startProd
          expected := []
          actual := remainingAtError.head?
          remaining := remainingAtError
        }
        .error (err.withSourceLoc input)
    | none =>
      -- Parse failed - find furthest position from memo table
      let memoMaxPos := memo.fold (init := 0) fun acc (pos, _) _ => max acc pos
      let remainingTokens := tokens.drop memoMaxPos
      let err : ParseError := {
        message := s!"Parse failed at token {memoMaxPos}"
        tokenPos := memoMaxPos
        production := grammar.startProd
        expected := []
        actual := remainingTokens.head?
        remaining := remainingTokens
      }
      .error (err.withSourceLoc input)
  | none =>
    .error {
      message := s!"Unknown start production: {grammar.startProd}"
      tokenPos := 0
      production := grammar.startProd
      expected := []
      actual := none
      remaining := []
    }

/-- Parse a file using a loaded grammar -/
def parseFileWithGrammar (grammar : LoadedGrammar) (path : String) : IO (Option Term) := do
  try
    let content ← IO.FS.readFile path
    pure (parseWithGrammar grammar content)
  catch _ =>
    pure none

/-- Parse a file with detailed error reporting -/
def parseFileWithGrammarE (grammar : LoadedGrammar) (path : String) : IO (Except ParseError Term) := do
  try
    let content ← IO.FS.readFile path
    pure (parseWithGrammarE grammar content)
  catch e =>
    pure (.error {
      message := s!"File error: {e}"
      tokenPos := 0
      production := grammar.startProd
      expected := []
      actual := none
      remaining := []
    })

/-! ## Parameterized Parsing (AST typeclass) -/

/-- Parse input using a loaded grammar, building into any AST type -/
def parseWithGrammarAs (α : Type) [AST α] (grammar : LoadedGrammar) (input : String) : Option α :=
  let tokens := Bootstrap.tokenize input
  let st : ParseStateT α := { tokens := tokens, binds := [] }
  match grammar.productions.find? (·.1 == grammar.startProd) with
  | some (_, g) =>
    match parseGrammarT defaultFuel grammar.productions g st with
    | some (t, st') => if st'.tokens.isEmpty then some t else none
    | none => none
  | none => none

/-- Parse and build GrammarExpr directly from grammar source -/
def parseAsGrammarExpr (grammar : LoadedGrammar) (input : String) : Option GrammarExpr :=
  parseWithGrammarAs GrammarExpr grammar input

/-! ## Printing with Loaded Grammar -/

/-- Print a term back to tokens using a loaded grammar -/
def printWithGrammar (grammar : LoadedGrammar) (prodName : String) (t : Term) : Option (List Token) :=
  match findAllProductions grammar.productions prodName with
  | some g => printGrammar defaultFuel grammar.productions g t []
  | none => none
def printToString (grammar : LoadedGrammar) (prodName : String) (t : Term) : Option String :=
  match printWithGrammar grammar prodName t with
  | some tokens =>
    dbg_trace s!"printToString tokens ({tokens.length})"
    some (Token.renderTokens tokens)
  | none => none

/-! ## Bootstrap Loading -/

/-- Load Bootstrap.lego and extract productions (without builtins).
    This allows comparing with the hard-coded Bootstrap.

    NOTE: This function intentionally uses Bootstrap.parseLegoFile because
    it's specifically for loading and testing Bootstrap.lego itself.
    For parsing ANY OTHER .lego file, use Runtime.parseLegoFile instead. -/
def loadBootstrapProductions (path : String := "./test/lego/Bootstrap.lego") : IO (Option Productions) := do
  try
    let content ← IO.FS.readFile path
    match Bootstrap.parseLegoFile content with
    | some ast => pure (some (extractProductionsOnly ast))
    | none => pure none
  catch _ =>
    pure none

/-- Compare two productions lists for equivalence (by name) -/
def compareProductionNames (p1 p2 : Productions) : Bool × List String × List String :=
  let names1 := p1.map (·.1) |>.eraseDups
  let names2 := p2.map (·.1) |>.eraseDups
  let onlyIn1 := names1.filter (fun n => !names2.contains n)
  let onlyIn2 := names2.filter (fun n => !names1.contains n)
  (onlyIn1.isEmpty && onlyIn2.isEmpty, onlyIn1, onlyIn2)

/-- Check if p1 is a subset of p2 (by production name) -/
def isSubsetOfProductions (p1 p2 : Productions) : Bool × List String :=
  let names1 := p1.map (·.1) |>.eraseDups
  let names2 := p2.map (·.1) |>.eraseDups
  let missing := names1.filter (fun n => !names2.contains n)
  (missing.isEmpty, missing)

/-! ## Rule Extraction -/

/-- Convert a parsed pattern AST to a Term for pattern matching.
    Handles various formats from the grammar:
    - (var "$" (ident name)) for $name metavars (generated grammar)
    - (var (ident name)) for $name metavars (old format)
    - (con (ident name) args...) for (name args...)
    - (seq ...) wrapper nodes to be stripped
    - Punctuation ($, parens) to be filtered out
-/
partial def patternAstToTerm (t : Term) : Term :=
  match t with
  -- Number handling: (num (number "n")) → .lit "n"
  | .con "num" [.con "number" [.lit n]] => .lit n
  | .con "num" [.lit n] => .lit n
  -- Rest variable pattern with full structure from grammar: "$" ident "..." → restVar
  -- Produces (restVar "$" (ident name) "...") or (restVar (ident name) "...") after filtering
  -- We normalize to (restVar (ident (var name))) for matching
  | .con "restVar" args =>
    -- Filter out "$" and "..." to get just the identifier
    let filtered := args.filter (fun a => match a with
      | .lit "$" => false
      | .lit "..." => false
      | _ => true)
    match filtered with
    | [.con "ident" [.var name]] =>
      .con "restVar" [.con "ident" [.var name]]
    | [.con "ident" [.lit name]] =>
      .con "restVar" [.con "ident" [.var name]]
    | [.var name] =>
      .con "restVar" [.con "ident" [.var name]]
    | [.con name []] =>  -- bare identifier became nullary con
      .con "restVar" [.con "ident" [.var name]]
    | _ =>
      -- Keep whatever we have (may be already processed)
      .con "restVar" (filtered.map patternAstToTerm)
  -- Map expression: (@map wrapper $items...) for transforming lists
  | .con "mapExpr" args =>
    .con "mapExpr" (args.map patternAstToTerm)
  -- NEW format from generated grammar: (var "$" (ident name)) → .var "$name"
  | .con "var" [.lit "$", .con "ident" [.var name]] =>
    .var s!"${name}"
  -- seq with $ prefix → metavar
  | .con "seq" [.lit "$", .con "var" [.con "ident" [.var name]]] =>
    .var s!"${name}"
  | .con "seq" (.lit "$" :: rest) =>
    -- Extract the var from the rest
    match rest.find? (fun t => match t with | .var _ => true | .con "var" _ => true | _ => false) with
    | some (.var name) => .var s!"${name}"
    | some (.con "var" [.con "ident" [.var name]]) => .var s!"${name}"
    | _ => .con "seq" (rest.map patternAstToTerm)
  -- seq with parens → unwrap the con inside
  | .con "seq" (.lit "(" :: rest) =>
    let inner := rest.filter (· != .lit "(") |>.filter (· != .lit ")")
    match inner with
    | [x] => patternAstToTerm x
    | xs => .con "seq" (xs.map patternAstToTerm)
  -- Old clean format: (var (ident name)) → .var "$name"
  | .con "var" [.con "ident" [.var name]] =>
    .var s!"${name}"
  -- New format with parens: (con "(" (ident name) args... ")") → .con name [args...]
  | .con "con" (.lit "(" :: rest) =>
    let filtered := rest.filter (· != .lit "(") |>.filter (· != .lit ")")
    match filtered with
    | .con "ident" [.var conName] :: args =>
      .con conName (args.map patternAstToTerm)
    | _ => .con "con" (rest.map patternAstToTerm)
  -- New clean format: (con (ident/sym name) args...) → .con name [args...]
  | .con "con" (.con "ident" [.var conName] :: args) =>
    .con conName (args.map patternAstToTerm)
  | .con "con" (.con "sym" [.lit conName] :: args) =>
    .con conName (args.map patternAstToTerm)
  -- New clean format: (lit (string "...")) → .lit ...
  | .con "lit" [.con "string" [.lit s]] =>
    .lit (s.drop 1 |>.dropRight 1)  -- strip quotes
  -- Regular con with ident first child (common case)
  | .con c (.con "ident" [.var name] :: args) =>
    -- c is the outer structure, name is the actual constructor name
    if c == "con" then .con name (args.map patternAstToTerm)
    else .con c ((.var name) :: args.map patternAstToTerm)
  -- ident node without $ prefix → nullary constructor, not a variable
  -- Variables in patterns start with $ (e.g., $x)
  | .con "ident" [.var name] =>
    if name.startsWith "$" then .var name
    else .con name []  -- Treat bare idents as nullary constructors
  -- Plain constructor application
  | .con c args =>
    let cleanArgs := args.filter (· != .lit "(") |>.filter (· != .lit ")")
                        |>.filter (· != .lit "$") |>.filter (· != .lit ";")
    .con c (cleanArgs.map patternAstToTerm)
  | .lit s => .lit s
  | .var s => .var s

/-- Convert a parsed template AST to a Term for substitution.
    Same structure handling as patterns.
-/
partial def templateAstToTerm (t : Term) : Term :=
  match t with
  -- Number handling: (num (number "n")) → .lit "n"
  | .con "num" [.con "number" [.lit n]] => .lit n
  | .con "num" [.lit n] => .lit n
  -- Rest variable pattern with full structure from grammar: "$" ident "..." → restVar
  -- Produces (restVar "$" (ident name) "...") or (restVar (ident name) "...") after filtering
  -- We normalize to (restVar (ident (var name))) for matching
  | .con "restVar" args =>
    -- Filter out "$" and "..." to get just the identifier
    let filtered := args.filter (fun a => match a with
      | .lit "$" => false
      | .lit "..." => false
      | _ => true)
    match filtered with
    | [.con "ident" [.var name]] =>
      .con "restVar" [.con "ident" [.var name]]
    | [.con "ident" [.lit name]] =>
      .con "restVar" [.con "ident" [.var name]]
    | [.var name] =>
      .con "restVar" [.con "ident" [.var name]]
    | [.con name []] =>  -- bare identifier became nullary con
      .con "restVar" [.con "ident" [.var name]]
    | _ =>
      -- Keep whatever we have (may be already processed)
      .con "restVar" (filtered.map templateAstToTerm)
  -- Map expression: (@map wrapper $items...) for transforming lists
  | .con "mapExpr" args =>
    .con "mapExpr" (args.map templateAstToTerm)
  -- NEW format from generated grammar: (var "$" (ident name)) → .var "$name"
  | .con "var" [.lit "$", .con "ident" [.var name]] =>
    .var s!"${name}"
  -- seq with $ prefix → metavar
  | .con "seq" [.lit "$", .con "var" [.con "ident" [.var name]]] =>
    .var s!"${name}"
  | .con "seq" (.lit "$" :: rest) =>
    match rest.find? (fun t => match t with | .var _ => true | .con "var" _ => true | _ => false) with
    | some (.var name) => .var s!"${name}"
    | some (.con "var" [.con "ident" [.var name]]) => .var s!"${name}"
    | _ => .con "seq" (rest.map templateAstToTerm)
  -- seq with parens → unwrap the con inside
  | .con "seq" (.lit "(" :: rest) =>
    let inner := rest.filter (· != .lit "(") |>.filter (· != .lit ")")
    match inner with
    | [x] => templateAstToTerm x
    | xs => .con "seq" (xs.map templateAstToTerm)
  -- Bare var (without explicit $ token): (var (ident name)) → nullary constructor
  -- This handles cases like "Real", "Int" which are type names, not metavars.
  -- Metavars have explicit "$" token: (var "$" (ident name)) handled above.
  | .con "var" [.con "ident" [.var name]] =>
    .con name []  -- Treat bare idents as nullary constructors
  -- New format with parens: (con "(" (ident name) args... ")") → .con name [args...]
  | .con "con" (.lit "(" :: rest) =>
    let filtered := rest.filter (· != .lit "(") |>.filter (· != .lit ")")
    match filtered with
    | .con "ident" [.var conName] :: args =>
      -- Convert args and flatten grouping cons (nullary idents adjacent to other terms)
      -- but NOT application cons (var applied to args)
      let convertedArgs := args.map templateAstToTerm
      let flatArgs := convertedArgs.flatMap fun a =>
        match a with
        -- Flatten grouping con: con [nullary, other...] → [nullary, other...]
        -- But NOT application con: con [var, args...] → keep as con
        | .con "con" children =>
          match children with
          | .var _ :: _ => [a]  -- Application - keep wrapped
          | _ => children  -- Grouping - flatten
        | other => [other]
      .con conName flatArgs
    | .con "var" _ :: _ =>
      -- Application where function is a variable: ($ma args...)
      -- This is HOAS application: (con [var, args...])
      let convertedArgs := filtered.map templateAstToTerm
      .con "con" convertedArgs
    | _ =>
      -- Other cases: filter and convert
      let convertedArgs := filtered.map templateAstToTerm
      .con "con" convertedArgs
  -- New clean format: (con (ident name) args...) → .con name [args...]
  | .con "con" (.con "ident" [.var conName] :: args) =>
    -- Check if the first arg is a parenthesized expression (starts with "(")
    -- If so, it's a separate application, not arguments to conName
    match args with
    | .con "con" (.lit "(" :: _) :: _ =>
      -- conName is a nullary constructor, rest are siblings
      .con "con" ((.con conName []) :: args.map templateAstToTerm)
    | _ =>
      .con conName (args.map templateAstToTerm)
  -- New clean format: (lit (string "...")) → .lit ...
  | .con "lit" [.con "string" [.lit s]] =>
    .lit (s.drop 1 |>.dropRight 1)  -- strip quotes
  -- Regular con with ident first child (common case)
  | .con c (.con "ident" [.var name] :: args) =>
    -- Check if the first arg is a parenthesized expression
    match args with
    | .con "con" (.lit "(" :: _) :: _ =>
      -- name is a nullary constructor, rest are siblings
      if c == "con" then
        .con "con" ((.con name []) :: args.map templateAstToTerm)
      else
        .con c ((.con name []) :: args.map templateAstToTerm)
    | _ =>
      if c == "con" then .con name (args.map templateAstToTerm)
      else .con c ((.var name) :: args.map templateAstToTerm)
  -- ident node without $ prefix → nullary constructor, not a variable
  -- Variables in templates start with $ (e.g., $x)
  | .con "ident" [.var name] =>
    if name.startsWith "$" then .var name
    else .con name []  -- Treat bare idents as nullary constructors
  -- Plain constructor application
  | .con c args =>
    let cleanArgs := args.filter (· != .lit "(") |>.filter (· != .lit ")")
                        |>.filter (· != .lit "$") |>.filter (· != .lit ";")
    .con c (cleanArgs.map templateAstToTerm)
  | .lit s => .lit s
  | .var s => .var s

/-- Extract guard term from a guard AST node -/
def extractGuard (guardNode : Term) : Option Term :=
  match guardNode with
  | .con "guard" args =>
    -- Guard contains side conditions: (guard "when" cond1 "," cond2 ...)
    let filtered := args.filter (· != .lit "when") |>.filter (· != .lit ",")
    -- For now, use the first condition as the guard
    match filtered with
    | [cond] => unwrapSidePattern cond
    | cond :: _ => unwrapSidePattern cond  -- multiple conditions - just take first
    | [] => none
  | _ => none
where
  /-- Unwrap a sidePattern wrapper and convert to term -/
  unwrapSidePattern (t : Term) : Option Term :=
    match t with
    | .con "sidePattern" [inner] => some (templateAstToTerm inner)
    | other => some (templateAstToTerm other)

/-- Extract a Rule from a DRule AST node -/
def extractRule (ruleDecl : Term) : Option Rule :=
  match ruleDecl with
  | .con "DRule" args =>
    -- First, check for guard node (con "guard" [...])
    let guardNode := args.find? fun t =>
      match t with
      | .con "guard" _ => true
      | _ => false
    let guard := guardNode.bind extractGuard

    -- Filter out keywords, punctuation, empty guard, and the guard node
    let filtered := args.filter (· != .lit "rule") |>.filter (· != .lit ":")
                       |>.filter (· != .lit "~>") |>.filter (· != .lit "~~>")
                       |>.filter (· != .lit ";")
                       |>.filter (· != .lit "(") |>.filter (· != .lit ")")
                       |>.filter (· != .lit "$")
                       |>.filter (· != .con "unit" [])  -- empty guard
                       |>.filter fun t =>
                         match t with
                         | .con "guard" _ => false  -- remove guard node from filtered
                         | _ => true
    -- Find the name (first ident) and separate pattern/template parts
    match filtered with
    | .con "ident" [.var name] :: rest =>
      -- Find where pattern ends and template begins
      -- Pattern is everything until we hit a 'var' or 'con' that's not inside the pattern
      -- Simple heuristic: first item is pattern, last item is template
      match rest with
      | [pat] =>
        -- Just a pattern, template is same (identity rule)
        some {
          name := name
          pattern := patternAstToTerm pat
          template := patternAstToTerm pat
          guard := guard
        }
      | [pat, tmpl] =>
        some {
          name := name
          pattern := patternAstToTerm pat
          template := templateAstToTerm tmpl
          guard := guard
        }
      | _ => none
    | _ => none
  | _ => none

/-- Extract all rules from a parsed .lego file AST -/
partial def extractRules (ast : Term) : List Rule :=
  go ast
where
  go (t : Term) : List Rule :=
    match t with
    | .con "DRule" _ =>
      match extractRule t with
      | some r => [r]
      | none => []
    | .con "DLang" ts => ts.flatMap go
    | .con "seq" ts => ts.flatMap go
    | .con _ ts => ts.flatMap go
    | _ => []

/-! ## Type Rule Extraction -/

/-- Extract a TypeRule from a DType AST node
    Format: type name: subject : type when cond1, cond2, ... ;
    AST: (DType "type" (ident name) ":" subject ":" type whenClause? ";")
-/
def extractTypeRule (typeDecl : Term) : Option TypeRule :=
  match typeDecl with
  | .con "DType" args =>
    -- Filter out keywords and punctuation
    let filtered := args.filter fun t =>
      t != .lit "type" && t != .lit ":" && t != .lit ";" && t != .con "unit" []
    match filtered with
    | [.con "ident" [.var name], subject, typ] =>
      some {
        name := name
        subject := patternAstToTerm subject
        type := templateAstToTerm typ
        conditions := []
      }
    | [.con "ident" [.var name], subject, typ, .con "when" conds] =>
      -- Filter out "when" and "," from conditions
      let cleanConds := conds.filter fun t =>
        t != .lit "when" && t != .lit ","
      some {
        name := name
        subject := patternAstToTerm subject
        type := templateAstToTerm typ
        conditions := cleanConds.map templateAstToTerm
      }
    | _ => none
  | _ => none

/-- Extract all type rules from a parsed .lego file AST -/
partial def extractTypeRules (ast : Term) : List TypeRule :=
  go ast
where
  go (t : Term) : List TypeRule :=
    match t with
    | .con "DType" _ =>
      match extractTypeRule t with
      | some tr => [tr]
      | none => []
    | .con "DLang" ts => ts.flatMap go
    | .con "seq" ts => ts.flatMap go
    | .con _ ts => ts.flatMap go
    | _ => []

/-! ## Attribute Grammar Extraction -/

/-- Parse an AttrFlow from AST -/
def parseAttrFlow (t : Term) : AttrFlow :=
  match t with
  | .con "syn" _ => .syn
  | .con "inh" _ => .inh
  | .lit "syn" => .syn
  | .lit "inh" => .inh
  | _ => .syn  -- default

/-- Parse an AttrPath from AST (e.g., "Lam.body.env") -/
def parseAttrPath (t : Term) : AttrPath :=
  -- Recursively collect all ident names from the path structure
  let rec collect (term : Term) : List String :=
    match term with
    | .con "ident" [.var name] => [name]
    | .con "attrPath" args => args.flatMap collect
    | .con "seq" args => args.flatMap collect
    | .var name => if name != "." then [name] else []
    | .lit _ => []  -- skip punctuation
    | .con _ args => args.flatMap collect
  collect t

/-- Extract an AttrDef from a DAttr AST node.
    Syntax: syn/inh name : type ; -/
def extractAttrDef (attrDecl : Term) : Option AttrDef :=
  match attrDecl with
  | .con "DAttr" args =>
    -- Filter out punctuation
    let filtered := args.filter (· != .lit ":") |>.filter (· != .lit ";")
    match filtered with
    | [flowTerm, .con "ident" [.var name], typeTerm] =>
      some {
        name := name
        flow := parseAttrFlow flowTerm
        type := some typeTerm
        rules := []  -- Rules added separately
      }
    | [flowTerm, .con "ident" [.var name]] =>
      some {
        name := name
        flow := parseAttrFlow flowTerm
        type := none
        rules := []
      }
    | _ => none
  | _ => none

/-- Extract an AttrRule from a DAttrRule AST node.
    Syntax: path = expr ; -/
def extractAttrRule (ruleDecl : Term) : Option AttrRule :=
  match ruleDecl with
  | .con "DAttrRule" args =>
    -- Filter out punctuation
    let filtered := args.filter (· != .lit "=") |>.filter (· != .lit ";")
    match filtered with
    | [pathTerm, exprTerm] =>
      let path := parseAttrPath pathTerm
      -- Split path into production + target
      -- E.g., ["Lam", "body", "env"] → prod = "Lam", target = ["body", "env"]
      match path with
      | prod :: target =>
        some {
          prod := prod
          target := target
          expr := exprTerm
        }
      | _ => none
    | _ => none
  | _ => none

/-- Extract all attribute definitions from a parsed .lego file AST -/
partial def extractAttrDefs (ast : Term) : List AttrDef :=
  go ast
where
  go (t : Term) : List AttrDef :=
    match t with
    | .con "DAttr" _ =>
      match extractAttrDef t with
      | some a => [a]
      | none => []
    | .con "DLang" ts => ts.flatMap go
    | .con "seq" ts => ts.flatMap go
    | .con _ ts => ts.flatMap go
    | _ => []

/-- Extract all attribute rules from a parsed .lego file AST -/
partial def extractAttrRules (ast : Term) : List AttrRule :=
  go ast
where
  go (t : Term) : List AttrRule :=
    match t with
    | .con "DAttrRule" _ =>
      match extractAttrRule t with
      | some r => [r]
      | none => []
    | .con "DLang" ts => ts.flatMap go
    | .con "seq" ts => ts.flatMap go
    | .con _ ts => ts.flatMap go
    | _ => []

/-- Combine attribute definitions with their rules.
    Rules are matched to definitions by attribute name (from path). -/
def combineAttrsWithRules (defs : List AttrDef) (rules : List AttrRule) : List AttrDef :=
  defs.map fun def_ =>
    -- Find rules that target this attribute
    -- A rule targets an attr if the last element of path matches attr name
    let attrName := def_.name
    let matchingRules := rules.filter fun r =>
      match r.target.getLast? with
      | some last => last == attrName
      | none => r.prod == attrName  -- Direct reference
    { def_ with rules := matchingRules }

/-- Extract a complete set of attribute definitions with their rules -/
def extractAttributes (ast : Term) : List AttrDef :=
  let defs := extractAttrDefs ast
  let rules := extractAttrRules ast
  combineAttrsWithRules defs rules

/-! ## Test Extraction -/

/-- A test case extracted from a .lego file -/
structure TestCase where
  name      : String
  input     : Term
  expected  : Option Term  -- None if test just checks parsing
  pieceName : String := ""  -- The piece this test belongs to (for type dispatch)
  deriving Repr, Inhabited

/-- Strip surrounding quotes from a string if present -/
def stripQuotes (s : String) : String :=
  let s := if s.startsWith "\"" then s.drop 1 else s
  if s.endsWith "\"" then s.dropRight 1 else s

/-- Extract a test case from a DTest AST node.
    Syntax: test "name" : input ~~> expected ; -/
def extractTestCase (testDecl : Term) : Option TestCase :=
  match testDecl with
  | .con "DTest" args =>
    -- DTest [lit "test", string "name", lit ":", input, lit "~~>", expected, lit ";"]
    -- or     [lit "test", string "name", lit ":", input, lit ";"]
    -- Filter out punctuation and extract parts
    let filtered := args.filter fun t =>
      t != .lit "test" && t != .lit ":" && t != .lit "~~>" && t != .lit ";"
    match filtered with
    | [.con "string" [.lit name], input, expected] =>
      some { name := stripQuotes name, input := input, expected := some expected }
    | [.con "string" [.lit name], input] =>
      some { name := stripQuotes name, input := input, expected := none }
    | [.lit name, input, expected] =>  -- Direct lit for name
      some { name := stripQuotes name, input := input, expected := some expected }
    | [.lit name, input] =>
      some { name := stripQuotes name, input := input, expected := none }
    | _ => none
  | _ => none

/-- Extract all test cases from a parsed .lego file AST -/
partial def extractTests (ast : Term) : List TestCase :=
  go "" ast
where
  go (currentPiece : String) (t : Term) : List TestCase :=
    match t with
    | .con "DPiece" args =>
      -- Extract piece name and recurse with it
      let pieceName := args.findSome? fun a =>
        match a with
        | .con "ident" [.var n] => some n
        | _ => none
      let piece := pieceName.getD currentPiece
      args.flatMap (go piece)
    | .con "DTest" _ =>
      match extractTestCase t with
      | some tc => [{ tc with pieceName := currentPiece }]
      | none => []
    | .con "DTestsBlock" args =>
      -- Tests block: tests { testCase+ }
      args.flatMap (go currentPiece)
    | .con "testCase" args =>
      -- Individual test case within a tests block
      -- testCase [string "name", lit "~~>", expected]
      let filtered := args.filter fun t =>
        t != .lit "~~>" && t != .lit ";"
      match filtered with
      | [.con "string" [.lit name], expected] =>
        [{ name := stripQuotes name, input := .con "unit" [], expected := some expected, pieceName := currentPiece }]
      | [.lit name, expected] =>
        [{ name := stripQuotes name, input := .con "unit" [], expected := some expected, pieceName := currentPiece }]
      | _ => []
    | .con "DLang" ts => ts.flatMap (go currentPiece)
    | .con "seq" ts => ts.flatMap (go currentPiece)
    | .con _ ts => ts.flatMap (go currentPiece)
    | _ => []

/-- Extract test cases grouped by piece name -/
partial def extractTestsByPiece (ast : Term) : List (String × List TestCase) :=
  go "" ast
where
  go (currentPiece : String) (t : Term) : List (String × List TestCase) :=
    match t with
    | .con "DPiece" (.lit _ :: .con "ident" [.var pieceName] :: rest) =>
      -- Recursively extract tests from this piece
      let tests := rest.flatMap (go pieceName)
      let directTests := rest.flatMap fun r =>
        match r with
        | .con "DTest" _ =>
          match extractTestCase r with
          | some tc => [tc]
          | none => []
        | _ => []
      if directTests.isEmpty then tests
      else (pieceName, directTests) :: tests
    | .con "DTest" _ =>
      if currentPiece.isEmpty then []
      else
        match extractTestCase t with
        | some tc => [(currentPiece, [tc])]
        | none => []
    | .con "DLang" ts => ts.flatMap (go currentPiece)
    | .con "seq" ts => ts.flatMap (go currentPiece)
    | .con _ ts => ts.flatMap (go currentPiece)
    | _ => []

end Lego.Loader
