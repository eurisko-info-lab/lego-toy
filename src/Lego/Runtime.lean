/-
  Lego.Runtime: True Runtime Bootstrap

  This module implements the proper bootstrap chain:
  1. Hardcoded minimal grammar parses Bootstrap.lego ONLY
  2. Bootstrap.lego provides the full grammar
  3. Full grammar parses all other .lego files

  The hardcoded grammar is ERASED after loading Bootstrap.lego.
  This is true self-hosting: modify Bootstrap.lego and it takes effect
  immediately without regenerating any Lean code.

  Architecture:
    Hardcoded Grammar ─── parses ──→ Bootstrap.lego
                                          │
                                          ▼
                                    Full Grammar ─── parses ──→ *.lego
-/

import Lego.Algebra
import Lego.Interp
import Lego.Loader
import Lego.Bootstrap

namespace Lego.Runtime

open Lego

/-! ## Runtime State -/

/-- The runtime holds the loaded bootstrap grammar -/
structure Runtime where
  /-- The loaded grammar from Bootstrap.lego -/
  grammar : Loader.LoadedGrammar
  /-- Loaded rules for normalization -/
  rules : List Rule

/-! ## Bootstrap Loading -/

/-- Default path to Bootstrap.lego -/
def defaultBootstrapPath : String := "./test/Bootstrap.lego"

/-- Load Bootstrap.lego using the hardcoded grammar, return the full grammar -/
def loadBootstrap (path : String := defaultBootstrapPath) : IO (Except String Runtime) := do
  try
    let content ← IO.FS.readFile path
    -- Verify this is actually Bootstrap.lego
    if !path.endsWith "Bootstrap.lego" then
      return Except.error s!"loadBootstrap only accepts Bootstrap.lego, got: {path}"
    -- Step 1: Parse Bootstrap.lego with hardcoded grammar
    match Bootstrap.parseLegoFile content with
    | none => return Except.error s!"Failed to parse {path} with hardcoded grammar"
    | some ast =>
      -- Step 2: Extract the full grammar from parsed Bootstrap.lego
      let prods := Loader.extractAllProductions ast
      let tokenProds := Loader.extractTokenProductions ast
      let symbols := Loader.extractAllSymbols prods
      let rules := Loader.extractRules ast
      let validation := Loader.validateProductions prods
      let grammar : Loader.LoadedGrammar := {
        productions := prods
        tokenProductions := tokenProds
        symbols := symbols
        startProd := "File.legoFile"
        validation := validation
      }
      -- Step 3: Create runtime with loaded grammar
      let runtime : Runtime := {
        grammar := grammar
        rules := rules
      }
      return Except.ok runtime
  catch e =>
    return Except.error s!"Error loading {path}: {e}"

/-- Load bootstrap, failing if Bootstrap.lego cannot be loaded.
    Lego does not use fallbacks - if Bootstrap.lego fails, that's a fatal error. -/
def loadBootstrapOrError (path : String := defaultBootstrapPath) : IO Runtime := do
  match ← loadBootstrap path with
  | Except.ok rt => return rt
  | Except.error e =>
    IO.eprintln s!"FATAL: {e}"
    IO.eprintln "Bootstrap.lego must be loadable for Lego to function."
    IO.Process.exit 1

/-! ## Parsing with Runtime Grammar -/

/-- Parse a .lego file using a runtime-loaded grammar (NOT the hardcoded one) -/
def parseLegoFile (rt : Runtime) (content : String) : Option Term :=
  Loader.parseWithGrammar rt.grammar content

/-- Parse a .lego file with detailed error reporting -/
def parseLegoFileE (rt : Runtime) (content : String) : Except ParseError Term :=
  Loader.parseWithGrammarE rt.grammar content

/-- Parse a .lego file from path -/
def parseLegoFilePath (rt : Runtime) (path : String) : IO (Option Term) := do
  let content ← IO.FS.readFile path
  return parseLegoFile rt content

/-- Parse a .lego file from path with detailed error reporting -/
def parseLegoFilePathE (rt : Runtime) (path : String) : IO (Except ParseError Term) := do
  let content ← IO.FS.readFile path
  return parseLegoFileE rt content

/-- Load a language from a .lego file -/
def loadLanguage (rt : Runtime) (path : String) : IO (Except String Loader.LoadedGrammar) := do
  let content ← IO.FS.readFile path
  match parseLegoFileE rt content with
  | .error e => return Except.error s!"Failed to parse {path}: {e}"
  | .ok ast =>
    let prods := Loader.extractAllProductions ast
    let tokenProds := Loader.extractTokenProductions ast
    let symbols := Loader.extractAllSymbols prods
    let validation := Loader.validateProductions prods
    -- Find the start production (first piece's first production, or File.legoFile)
    let startProd := match prods.head? with
      | some (name, _) => name
      | none => "File.legoFile"
    return Except.ok {
      productions := prods
      tokenProductions := tokenProds
      symbols := symbols
      startProd := startProd
      validation := validation
    }

/-! ## Normalization with Runtime Rules -/

/-- Normalize a term using runtime-loaded rules -/
partial def normalize (rt : Runtime) (t : Term) : Term :=
  normalizeWith 1000 rt.rules t
where
  normalizeWith (fuel : Nat) (rules : List Rule) (t : Term) : Term :=
    match fuel with
    | 0 => t
    | n + 1 =>
      match rules.findSome? (·.apply t) with
      | some t' => normalizeWith n rules t'
      | none =>
        match t with
        | .con c args => .con c (args.map (normalizeWith n rules))
        | _ => t

/-! ## Pretty Printing -/

/-- Print a term back to source using the runtime grammar -/
def printTerm (rt : Runtime) (t : Term) (prodName : String) : Option String :=
  match Loader.printWithGrammar rt.grammar prodName t with
  | some tokens => some (tokens.map Token.toString |> String.intercalate " ")
  | none => none

/-! ## Transform Pipeline -/

/-- Load transform rules from a .lego file -/
def loadTransformRules (rt : Runtime) (path : String) : IO (Except String (List Rule)) := do
  let content ← IO.FS.readFile path
  match parseLegoFileE rt content with
  | .error e => return Except.error s!"Failed to parse {path}: {e}"
  | .ok ast =>
    return Except.ok (Loader.extractRules ast)

/-- Apply a transformation: load rules, apply to term -/
partial def transform (rules : List Rule) (t : Term) : Term :=
  go 1000 t
where
  go (fuel : Nat) (t : Term) : Term :=
    match fuel with
    | 0 => t
    | n + 1 =>
      match rules.findSome? (·.apply t) with
      | some t' => go n t'
      | none =>
        match t with
        | .con c args => .con c (args.map (go n))
        | _ => t

/-! ## Complete Pipeline: Lego → Lean -/

/-- Pipeline for transforming .lego to Lean AST:
    1. Load source .lego file
    2. Load lego2rosetta rules
    3. Transform to Rosetta IR
    4. Load rosetta2lean rules
    5. Transform to Lean AST
    6. Print using Lean grammar -/
def lego2lean (rt : Runtime) (sourcePath : String) (rosettaPath : String := "./src/Rosetta/lego2rosetta.lego")
    (leanPath : String := "./src/Rosetta/rosetta2lean.lego") : IO (Except String Term) := do
  -- Step 1: Parse source
  match ← parseLegoFilePathE rt sourcePath with
  | .error e => return Except.error s!"Failed to parse {sourcePath}: {e}"
  | .ok sourceAst =>
    -- Step 2: Load lego2rosetta rules
    match ← loadTransformRules rt rosettaPath with
    | Except.error e => return Except.error e
    | Except.ok rules1 =>
      -- Step 3: Transform to Rosetta IR
      let rosettaAst := transform rules1 sourceAst
      -- Step 4: Load rosetta2lean rules
      match ← loadTransformRules rt leanPath with
      | Except.error e => return Except.error e
      | Except.ok rules2 =>
        -- Step 5: Transform to Lean AST
        let leanAst := transform rules2 rosettaAst
        return Except.ok leanAst

/-! ## Global Initialization -/

/-- Initialize the Lego runtime by loading Bootstrap.lego.
    This MUST be called before parsing any user .lego files.
    Returns the runtime that should be used for all subsequent parsing.

    The bootstrap chain is:
      Hardcoded Grammar → parses → Bootstrap.lego → Full Grammar → parses → *.lego

    IMPORTANT: Only Bootstrap.lego should be parsed with the hardcoded grammar.
    All other .lego files must use the runtime returned by this function. -/
def init (bootstrapPath : String := defaultBootstrapPath) : IO Runtime := do
  IO.println s!"[Lego] Loading Bootstrap.lego from {bootstrapPath}..."
  let rt ← loadBootstrapOrError bootstrapPath
  IO.println s!"[Lego] Runtime initialized with {rt.grammar.productions.length} productions"
  return rt

/-- Convenience: Initialize and parse a file in one step.
    Use this when you just need to parse a single file. -/
def initAndParse (path : String) (bootstrapPath : String := defaultBootstrapPath) : IO (Except String Term) := do
  let rt ← init bootstrapPath
  let content ← IO.FS.readFile path
  match parseLegoFileE rt content with
  | .error e => return .error (toString e)
  | .ok ast => return .ok ast

/-- Convenience: Initialize and load a language in one step -/
def initAndLoadLanguage (path : String) (bootstrapPath : String := defaultBootstrapPath) : IO (Except String (Runtime × Loader.LoadedGrammar)) := do
  let rt ← init bootstrapPath
  match ← loadLanguage rt path with
  | .error e => return .error e
  | .ok grammar => return .ok (rt, grammar)

end Lego.Runtime
