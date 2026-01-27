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

/-- The runtime holds the loaded grammars from the bootstrap chain -/
structure Runtime where
  /-- The loaded grammar from Lego.lego (extends Bootstrap) for .lego files -/
  grammar : Loader.LoadedGrammar
  /-- The loaded grammar from Rosetta.lego (extends Lego) for .rosetta files -/
  rosettaGrammar : Loader.LoadedGrammar
  /-- The loaded grammar from Lean.lego for .lean files -/
  leanGrammar : Loader.LoadedGrammar
  /-- Loaded rules for normalization -/
  rules : List Rule

/-! ## Bootstrap Loading -/

/-- Default path to Bootstrap.lego -/
def defaultBootstrapPath : String := "./test/lego/Bootstrap.lego"

/-- Default path to Lego.lego -/
def defaultLegoPath : String := "./src/Lego/Lego.lego"

/-- Default path to Rosetta.lego -/
def defaultRosettaPath : String := "./src/Rosetta/Rosetta.lego"

/-- Default path to Lean.lego -/
def defaultLeanPath : String := "./src/Rosetta/Lean.lego"

/-- Load Bootstrap.lego using the hardcoded grammar, return Bootstrap's grammar -/
def loadBootstrapOnly (path : String := defaultBootstrapPath) : IO (Except String Loader.LoadedGrammar) := do
  try
    let content ← IO.FS.readFile path
    if !path.endsWith "Bootstrap.lego" then
      return Except.error s!"loadBootstrapOnly only accepts Bootstrap.lego, got: {path}"
    match Bootstrap.parseLegoFile content with
    | none => return Except.error s!"Failed to parse {path} with hardcoded grammar"
    | some ast =>
      let prods := Loader.extractAllProductions ast
      let tokenProds := Loader.extractTokenProductions ast
      let symbols := Loader.extractAllSymbols prods
      let keywords := Loader.extractKeywords prods
      let validation := Loader.validateProductions prods
      let grammar : Loader.LoadedGrammar := {
        productions := prods
        tokenProductions := tokenProds
        symbols := symbols
        keywords := keywords
        startProd := "File.legoFile"
        validation := validation
      }
      return Except.ok grammar
  catch e =>
    return Except.error s!"Error loading {path}: {e}"

/-- Load the full bootstrap chain: Hardcoded → Bootstrap.lego → Lego.lego → Rosetta.lego → Lean.lego
    Returns a Runtime with grammars for parsing .lego, .rosetta, and .lean files -/
def loadBootstrap (bootstrapPath : String := defaultBootstrapPath)
                  (legoPath : String := defaultLegoPath)
                  (rosettaPath : String := defaultRosettaPath)
                  (leanPath : String := defaultLeanPath) : IO (Except String Runtime) := do
  -- Step 1: Load Bootstrap.lego with hardcoded grammar
  match ← loadBootstrapOnly bootstrapPath with
  | .error e => return Except.error s!"Failed to load Bootstrap.lego: {e}"
  | .ok bootstrapGrammar =>
    -- Step 2: Parse Lego.lego with Bootstrap's grammar
    try
      let legoContent ← IO.FS.readFile legoPath
      match Loader.parseWithGrammarE bootstrapGrammar legoContent with
      | .error e => return Except.error s!"Failed to parse {legoPath} with Bootstrap grammar: {e}"
      | .ok legoAst =>
        -- Step 3: Extract Lego.lego's productions and merge with Bootstrap
        let legoProds := Loader.extractAllProductions legoAst
        let legoTokenProds := Loader.extractTokenProductions legoAst
        let legoRules := Loader.extractRules legoAst
        -- Merge: Lego productions + Bootstrap productions (Lego overrides)
        let mergedLegoProds := legoProds ++ bootstrapGrammar.productions
        let mergedLegoTokenProds := legoTokenProds ++ bootstrapGrammar.tokenProductions
        let mergedLegoSymbols := Loader.extractAllSymbols mergedLegoProds
        -- Lego-specific keywords: none needed beyond the heuristic
        let mergedLegoKeywords := Loader.extractKeywords mergedLegoProds
        let legoGrammar : Loader.LoadedGrammar := {
          productions := mergedLegoProds
          tokenProductions := mergedLegoTokenProds
          symbols := mergedLegoSymbols
          keywords := mergedLegoKeywords
          startProd := "File.legoFile"
        }
        -- Step 4: Parse Rosetta.lego with Lego's grammar
        let rosettaContent ← IO.FS.readFile rosettaPath
        match Loader.parseWithGrammarE legoGrammar rosettaContent with
        | .error e => return Except.error s!"Failed to parse {rosettaPath} with Lego grammar: {e}"
        | .ok rosettaAst =>
          -- Step 5: Extract Rosetta.lego's productions and merge with Lego
          let rosettaProds := Loader.extractAllProductions rosettaAst
          let rosettaTokenProds := Loader.extractTokenProductions rosettaAst
          let rosettaRules := Loader.extractRules rosettaAst
          -- Merge: Rosetta productions + Lego productions
          let mergedRosettaProds := rosettaProds ++ mergedLegoProds
          let mergedRosettaTokenProds := rosettaTokenProds ++ mergedLegoTokenProds
          let mergedRosettaSymbols := Loader.extractAllSymbols mergedRosettaProds
          -- Rosetta-specific keywords: none needed beyond the heuristic
          let mergedRosettaKeywords := Loader.extractKeywords mergedRosettaProds
          let rosettaGrammar : Loader.LoadedGrammar := {
            productions := mergedRosettaProds
            tokenProductions := mergedRosettaTokenProds
            symbols := mergedRosettaSymbols
            keywords := mergedRosettaKeywords
            startProd := "File.rosettaFile"  -- Rosetta files use rosettaFile start
          }
          -- Step 6: Parse Lean.lego with Lego's grammar
          let leanContent ← IO.FS.readFile leanPath
          match Loader.parseWithGrammarE legoGrammar leanContent with
          | .error e => return Except.error s!"Failed to parse {leanPath} with Lego grammar: {e}"
          | .ok leanAst =>
            -- Step 7: Extract Lean.lego's productions and merge with Lego
            let leanProds := Loader.extractAllProductions leanAst
            let leanTokenProds := Loader.extractTokenProductions leanAst
            let leanRules := Loader.extractRules leanAst
            -- Merge: Lean productions + Lego productions
            let mergedLeanProds := leanProds ++ mergedLegoProds
            let mergedLeanTokenProds := leanTokenProds ++ mergedLegoTokenProds
            let mergedLeanSymbols := Loader.extractAllSymbols mergedLeanProds
            -- Lean-specific keywords: needed to prevent identifier confusion
            let leanSpecificKeywords := [
              -- Control flow
              "for", "while", "repeat", "unless", "return",
              -- Expression starters
              "match", "if", "let", "fun", "do", "by",
              -- Type keywords
              "Type", "Prop", "Sort",
              -- Literal keywords (needed for pattern matching)
              "some", "none", "true", "false",
              -- Definition keywords
              "def", "theorem", "lemma", "example", "abbrev",
              "inductive", "structure", "class", "instance",
              "namespace", "section", "import", "open", "variable",
              "private", "protected", "partial",
              -- Tactic keywords
              "rfl", "sorry", "trivial", "decide", "assumption",
              "exact", "apply", "intro", "cases", "induction", "simp", "rewrite"
            ]
            let baseKeywords := Loader.extractKeywords mergedLeanProds
            let mergedLeanKeywords := (baseKeywords ++ leanSpecificKeywords).eraseDups
            let leanGrammar : Loader.LoadedGrammar := {
              productions := mergedLeanProds
              tokenProductions := mergedLeanTokenProds
              symbols := mergedLeanSymbols
              keywords := mergedLeanKeywords
              startProd := "Module.module"  -- Lean files use module start
            }
            let runtime : Runtime := {
              grammar := legoGrammar
              rosettaGrammar := rosettaGrammar
              leanGrammar := leanGrammar
              rules := legoRules ++ rosettaRules ++ leanRules
            }
            return Except.ok runtime
    catch e =>
      return Except.error s!"Error loading: {e}"

/-- Load bootstrap chain, failing if any grammar file cannot be loaded.
    Lego does not use fallbacks - if any fails, that's a fatal error. -/
def loadBootstrapOrError (bootstrapPath : String := defaultBootstrapPath)
                         (legoPath : String := defaultLegoPath)
                         (rosettaPath : String := defaultRosettaPath)
                         (leanPath : String := defaultLeanPath) : IO Runtime := do
  match ← loadBootstrap bootstrapPath legoPath rosettaPath leanPath with
  | Except.ok rt => return rt
  | Except.error e =>
    IO.eprintln s!"FATAL: {e}"
    IO.eprintln "Bootstrap.lego, Lego.lego, Rosetta.lego and Lean.lego must be loadable for Lego to function."
    IO.Process.exit 1

/-! ## Parsing with Runtime Grammar -/

/-- Parse a .lego file using Lego.lego's grammar (NOT hardcoded or Bootstrap alone) -/
def parseLegoFile (rt : Runtime) (content : String) : Option Term :=
  Loader.parseWithGrammar rt.grammar content

/-- Parse a .lego file with detailed error reporting -/
def parseLegoFileE (rt : Runtime) (content : String) : Except ParseError Term :=
  Loader.parseWithGrammarE rt.grammar content

/-- Parse a file from path using a specific grammar -/
def parseWithGrammarPath (grammar : Loader.LoadedGrammar) (path : String) : IO (Option Term) := do
  let content ← IO.FS.readFile path
  return Loader.parseWithGrammar grammar content

/-- Parse a file from path with detailed error reporting using a specific grammar -/
def parseWithGrammarPathE (grammar : Loader.LoadedGrammar) (path : String) : IO (Except ParseError Term) := do
  let content ← IO.FS.readFile path
  return Loader.parseWithGrammarE grammar content

/-- Parse a .lego file from path -/
def parseLegoFilePath (rt : Runtime) (path : String) : IO (Option Term) := do
  parseWithGrammarPath rt.grammar path

/-- Parse a .lego file from path with detailed error reporting -/
def parseLegoFilePathE (rt : Runtime) (path : String) : IO (Except ParseError Term) := do
  parseWithGrammarPathE rt.grammar path

/-- Parse a .rosetta file using Rosetta.lego's grammar -/
def parseRosettaFile (rt : Runtime) (content : String) : Option Term :=
  Loader.parseWithGrammar rt.rosettaGrammar content

/-- Parse a .rosetta file with detailed error reporting -/
def parseRosettaFileE (rt : Runtime) (content : String) : Except ParseError Term :=
  Loader.parseWithGrammarE rt.rosettaGrammar content

/-- Parse a .rosetta file from path -/
def parseRosettaFilePath (rt : Runtime) (path : String) : IO (Option Term) := do
  parseWithGrammarPath rt.rosettaGrammar path

/-- Parse a .rosetta file from path with detailed error reporting -/
def parseRosettaFilePathE (rt : Runtime) (path : String) : IO (Except ParseError Term) := do
  parseWithGrammarPathE rt.rosettaGrammar path

/-- Parse a .lean file using Lean.lego's grammar -/
def parseLeanFile (rt : Runtime) (content : String) : Option Term :=
  Loader.parseWithGrammar rt.leanGrammar content

/-- Parse a .lean file with detailed error reporting -/
def parseLeanFileE (rt : Runtime) (content : String) : Except ParseError Term :=
  Loader.parseWithGrammarE rt.leanGrammar content

/-- Parse a .lean file from path -/
def parseLeanFilePath (rt : Runtime) (path : String) : IO (Option Term) := do
  parseWithGrammarPath rt.leanGrammar path

/-- Parse a .lean file from path with detailed error reporting -/
def parseLeanFilePathE (rt : Runtime) (path : String) : IO (Except ParseError Term) := do
  parseWithGrammarPathE rt.leanGrammar path

/-- Load a language from a .lego file with grammar inheritance.
    When a language declares `lang X (Parent) :=`, we:
    1. Load the parent grammar(s) recursively
    2. Merge parent productions into child grammar
    This way token definitions flow through the inheritance chain. -/
partial def loadLanguage (rt : Runtime) (path : String) : IO (Except String Loader.LoadedGrammar) := do
  loadLanguageWithParents rt path #[]
where
  /-- Resolve parent path - looks in standard locations -/
  resolveParentPath (parentName : String) (childPath : String) : IO (Option String) := do
    -- Get directory of child file
    let childDir := System.FilePath.mk childPath |>.parent |>.getD (System.FilePath.mk ".")
    -- Standard locations to search
    let candidates := [
      -- Same directory as child
      childDir / (parentName ++ ".lego"),
      -- test/ directory (Bootstrap.lego)
      System.FilePath.mk "test" / (parentName ++ ".lego"),
      -- src/Lego/ directory (Lego.lego)
      System.FilePath.mk "src" / "Lego" / (parentName ++ ".lego"),
      -- src/Rosetta/ directory
      System.FilePath.mk "src" / "Rosetta" / (parentName ++ ".lego")
    ]
    for c in candidates do
      if ← c.pathExists then
        return some c.toString
    return none

  /-- Load language with parent inheritance -/
  loadLanguageWithParents (rt : Runtime) (path : String) (visited : Array String) : IO (Except String Loader.LoadedGrammar) := do
    -- Prevent cycles
    if visited.contains path then
      return Except.error s!"Circular language inheritance detected: {path}"

    let content ← IO.FS.readFile path

    -- First, do a quick parse with bootstrap to extract parent names
    -- This works because 'lang X (Parent) :=' syntax is in Bootstrap
    let parentNames := match Loader.parseWithGrammarE rt.grammar content with
      | .error _ => []  -- If bootstrap can't parse it, assume no parents
      | .ok ast => Loader.extractParentNames ast

    -- Load parent grammars recursively
    let mut inheritedTokenProds : Productions := []
    let mut inheritedProds : Productions := []

    for parentName in parentNames do
      -- Bootstrap is special - its grammar is already in the runtime, don't load again
      if parentName == "Bootstrap" then
        inheritedTokenProds := rt.grammar.tokenProductions ++ inheritedTokenProds
        inheritedProds := rt.grammar.productions ++ inheritedProds
      else
        match ← resolveParentPath parentName path with
        | none =>
          return Except.error s!"Cannot find parent language: {parentName}"
        | some parentPath =>
          match ← loadLanguageWithParents rt parentPath (visited.push path) with
          | .error e => return Except.error s!"Failed to load parent {parentName}: {e}"
          | .ok parentGrammar =>
            inheritedTokenProds := parentGrammar.tokenProductions ++ inheritedTokenProds
            inheritedProds := parentGrammar.productions ++ inheritedProds

    -- Now parse with the merged grammar (parents + bootstrap)
    let mergedProds := inheritedProds ++ rt.grammar.productions
    let parsingGrammar : Loader.LoadedGrammar := {
      productions := mergedProds
      tokenProductions := inheritedTokenProds ++ rt.grammar.tokenProductions
      symbols := Loader.extractAllSymbols mergedProds
      keywords := Loader.extractKeywords mergedProds
      startProd := "File.legoFile"
    }

    let ast ← match Loader.parseWithGrammarE parsingGrammar content with
      | .error e => return Except.error s!"Failed to parse {path}: {e}"
      | .ok ast => pure ast

    -- Extract child's own productions
    let childProds := Loader.extractAllProductions ast
    let childTokenProds := Loader.extractTokenProductions ast

    -- Merge: bootstrap + inherited parents + child (child overrides)
    let mergedProds := rt.grammar.productions ++ inheritedProds ++ childProds
    let mergedTokenProds := rt.grammar.tokenProductions ++ inheritedTokenProds ++ childTokenProds

    let symbols := Loader.extractAllSymbols mergedProds
    let keywords := Loader.extractKeywords mergedProds
    let validation := Loader.validateProductions mergedProds

    -- Keep File.legoFile as start so merged grammar can parse .lego files
    return Except.ok {
      productions := mergedProds
      tokenProductions := mergedTokenProds
      symbols := symbols
      keywords := keywords
      startProd := "File.legoFile"
      validation := validation
    }

/-! ## Normalization with Runtime Rules -/

/-- Configuration for normalization -/
structure NormalizeConfig where
  /-- Maximum reduction steps (fuel) -/
  maxSteps : Nat := 1000
  /-- Whether to enable built-in operations (subst, etc.) -/
  enableBuiltins : Bool := true
  deriving Inhabited

/-- Result of normalization with optional trace -/
structure NormalizeResult where
  /-- The normalized term -/
  term : Term
  /-- Trace of (ruleName, intermediate term) pairs if tracing enabled -/
  trace : List (String × Term) := []
  deriving Inhabited

/-- Apply built-in substitution: (subst x val body) → body[x := val] -/
partial def applySubst (x : String) (val : Term) (body : Term) : Term :=
  match body with
  | .var name => if name == x then val else body
  | .con "var" [.var name] => if name == x then val else body
  | .con "var" [.con name []] => if name == x then val else body
  | .lit _ => body
  | .con name args => .con name (args.map (applySubst x val))

/-- Apply built-in reductions (subst evaluation) -/
def stepBuiltin (t : Term) : Option Term :=
  match t with
  | .con "subst" [.var x, val, body] =>
    some (applySubst x val body)
  | .con "subst" [.con x [], val, body] =>
    some (applySubst x val body)
  | _ => none

/-! ## Generic Rule Application (works with Rule and TypeRule) -/

/-- Apply a single step with any matching rule from a list, returning the rule name if matched.
    Works with any type that implements Applicable (Rule, TypeRule, etc.) -/
def applyOnceWithName [Lego.Applicable R] (rules : List R) (enableBuiltins : Bool) (t : Term) : Option (Term × String) :=
  match rules.findSome? (fun r => Lego.Applicable.apply r t |>.map (·, Lego.Applicable.name r)) with
  | some result => some result
  | none => if enableBuiltins then stepBuiltin t |>.map (·, "builtin") else none

/-- Apply rules to subterms recursively with tracing (single step).
    Works with any type that implements Applicable. -/
partial def applyDeepWithTrace [Lego.Applicable R] (rules : List R) (enableBuiltins : Bool) (t : Term) : Option (Term × String) :=
  match applyOnceWithName rules enableBuiltins t with
  | some result => some result
  | none =>
    match t with
    | .con name args =>
      let rec tryArgs (before : List Term) (after : List Term) : Option (Term × String) :=
        match after with
        | [] => none
        | arg :: rest =>
          match applyDeepWithTrace rules enableBuiltins arg with
          | some (arg', ruleName) => some (.con name (before.reverse ++ [arg'] ++ rest), ruleName)
          | none => tryArgs (arg :: before) rest
      tryArgs [] args
    | _ => none

/-- Generic normalize with tracing: returns final term and list of (ruleName, intermediate term).
    Works with any type that implements Applicable (Rule, TypeRule, etc.) -/
partial def applyRulesWithTrace [Lego.Applicable R] (config : NormalizeConfig) (rules : List R) (t : Term) : NormalizeResult :=
  go config.maxSteps t []
where
  go (fuel : Nat) (t : Term) (acc : List (String × Term)) : NormalizeResult :=
    match fuel with
    | 0 => { term := t, trace := acc.reverse }
    | n + 1 =>
      match applyDeepWithTrace rules config.enableBuiltins t with
      | some (t', ruleName) => go n t' ((ruleName, t') :: acc)
      | none => { term := t, trace := acc.reverse }

/-! ## Rewrite Rule Normalization -/

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
        -- Try builtin step
        match stepBuiltin t with
        | some t' => normalizeWith n rules t'
        | none =>
          match t with
          | .con c args => .con c (args.map (normalizeWith n rules))
          | _ => t

/-- Normalize with tracing for rewrite rules (legacy API, uses generic applyRulesWithTrace) -/
def normalizeWithTrace (config : NormalizeConfig) (rules : List Rule) (t : Term) : NormalizeResult :=
  applyRulesWithTrace config rules t

/-- Normalize with tracing using runtime rules -/
def normalizeWithTraceRt (rt : Runtime) (t : Term) (config : NormalizeConfig := {}) : NormalizeResult :=
  normalizeWithTrace config rt.rules t

/-! ## Type Inference with Tracing -/

/-- Infer the type of a term using type rules with tracing.
    For type inference, we only apply rules at the top level (no deep recursion).
    Returns the inferred type and trace of which type rule matched. -/
def inferTypeWithTrace (_config : NormalizeConfig) (typeRules : List TypeRule) (t : Term) : NormalizeResult :=
  -- Type inference typically only needs one step (find the matching type rule)
  match applyOnceWithName typeRules false t with
  | some (ty, ruleName) => { term := ty, trace := [(ruleName, ty)] }
  | none => { term := .con "error" [.lit "no type rule matched"], trace := [] }

/-! ## Pretty Printing -/

/-- Print a term back to source using the runtime grammar -/
def printTerm (rt : Runtime) (t : Term) (prodName : String) : Option String :=
  match Loader.printWithGrammar rt.grammar prodName t with
  | some tokens => some (Token.renderTokens tokens)
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

/-! ## Complete Pipeline: Lego → Rosetta IR -/

/-- Pipeline for transforming .lego to Rosetta IR:
    1. Load source .lego file
    2. Load lego2rosetta rules
    3. Transform to Rosetta IR
    The Rosetta IR is then pretty-printed using the target grammar -/
def lego2rosetta (rt : Runtime) (sourcePath : String) (rosettaPath : String := "./src/Rosetta/lego2rosetta.lego")
    : IO (Except String Term) := do
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
      return Except.ok rosettaAst

/-! ## Global Initialization -/

/-- Initialize the Lego runtime by loading Bootstrap.lego → Lego.lego → Rosetta.lego → Lean.lego.
    This MUST be called before parsing any user .lego, .rosetta, or .lean files.
    Returns the runtime that should be used for all subsequent parsing.

    The bootstrap chain is:
      Hardcoded Grammar → parses → Bootstrap.lego
      Bootstrap Grammar → parses → Lego.lego
      Lego Grammar → parses → Rosetta.lego
      Lego Grammar → parses → Lean.lego
      Lego Grammar → parses → *.lego files
      Rosetta Grammar → parses → *.rosetta files
      Lean Grammar → parses → *.lean files

    IMPORTANT: Only Bootstrap.lego is parsed with hardcoded grammar.
    Only Lego.lego is parsed with Bootstrap grammar.
    Only Rosetta.lego and Lean.lego are parsed with Lego grammar.
    All other .lego files are parsed with Lego.lego's grammar.
    All .rosetta files are parsed with Rosetta.lego's grammar.
    All .lean files are parsed with Lean.lego's grammar. -/
def init (bootstrapPath : String := defaultBootstrapPath)
         (legoPath : String := defaultLegoPath)
         (rosettaPath : String := defaultRosettaPath)
         (leanPath : String := defaultLeanPath) : IO Runtime := do
  IO.println s!"[Lego] Loading Bootstrap.lego from {bootstrapPath}..."
  IO.println s!"[Lego] Loading Lego.lego from {legoPath}..."
  IO.println s!"[Lego] Loading Rosetta.lego from {rosettaPath}..."
  IO.println s!"[Lego] Loading Lean.lego from {leanPath}..."
  let rt ← loadBootstrapOrError bootstrapPath legoPath rosettaPath leanPath
  IO.println s!"[Lego] Runtime initialized with {rt.grammar.productions.length} lego, {rt.rosettaGrammar.productions.length} rosetta, {rt.leanGrammar.productions.length} lean productions"
  return rt

/-- Quiet initialization (no logging). -/
def initQuiet (bootstrapPath : String := defaultBootstrapPath)
             (legoPath : String := defaultLegoPath)
             (rosettaPath : String := defaultRosettaPath)
             (leanPath : String := defaultLeanPath) : IO Runtime := do
  let rt ← loadBootstrapOrError bootstrapPath legoPath rosettaPath leanPath
  return rt

/-! ## Singleton Initialization (optional) -/

initialize runtimeCache : IO.Ref (Option Runtime) ← IO.mkRef none

/-- Initialize once and reuse the runtime (reduces repeated loading/log spam). -/
def initSingleton (bootstrapPath : String := defaultBootstrapPath)
                  (legoPath : String := defaultLegoPath)
                  (rosettaPath : String := defaultRosettaPath)
                  (leanPath : String := defaultLeanPath)
                  (quiet : Bool := true) : IO Runtime := do
  let cached ← runtimeCache.get
  match cached with
  | some rt => return rt
  | none =>
    let rt ← if quiet
      then initQuiet bootstrapPath legoPath rosettaPath leanPath
      else init bootstrapPath legoPath rosettaPath leanPath
    runtimeCache.set (some rt)
    return rt

/-- Convenience: Initialize and parse a file in one step.
    Use this when you just need to parse a single file. -/
def initAndParse (path : String)
                 (bootstrapPath : String := defaultBootstrapPath)
                 (legoPath : String := defaultLegoPath)
                 (rosettaPath : String := defaultRosettaPath)
                 (leanPath : String := defaultLeanPath) : IO (Except String Term) := do
  let rt ← init bootstrapPath legoPath rosettaPath leanPath
  let content ← IO.FS.readFile path
  -- Choose grammar based on file extension
  if path.endsWith ".rosetta" then
    match parseRosettaFileE rt content with
    | .error e => return .error (toString e)
    | .ok ast => return .ok ast
  else if path.endsWith ".lean" then
    match parseLeanFileE rt content with
    | .error e => return .error (toString e)
    | .ok ast => return .ok ast
  else
    match parseLegoFileE rt content with
    | .error e => return .error (toString e)
    | .ok ast => return .ok ast

/-- Convenience: Initialize and load a language in one step -/
def initAndLoadLanguage (path : String)
                        (bootstrapPath : String := defaultBootstrapPath)
                        (legoPath : String := defaultLegoPath)
                        (rosettaPath : String := defaultRosettaPath)
                        (leanPath : String := defaultLeanPath) : IO (Except String (Runtime × Loader.LoadedGrammar)) := do
  let rt ← init bootstrapPath legoPath rosettaPath leanPath
  match ← loadLanguage rt path with
  | .error e => return .error e
  | .ok grammar => return .ok (rt, grammar)

end Lego.Runtime
