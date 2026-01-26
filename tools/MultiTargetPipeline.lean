/-
  MultiTargetPipeline.lean
  Multi-target code generation: .rosetta/.lego → Lean/Scala/Haskell/Rust

  Usage:
    lake exe multi-target <source.rosetta|source.lego> [--out <dir>] [--targets lean,scala,haskell,rust]

  All the real work is done by:
    - GrammarDrivenPipeline.lean (transform & print infrastructure)
    - <L>.lego grammars (print mode via layout annotations)
    - rosetta2<L>.lego (transformation rules)
-/

import Lego.Runtime
import Lego.Loader
import GrammarDrivenPipeline

open Lego.Runtime
open Lego.Loader
open Lego

namespace MultiTargetPipeline

/-- Parse target language from string -/
def parseTarget (s : String) : Option TargetLang :=
  match s.toLower with
  | "lean" => some .Lean
  | "scala" => some .Scala
  | "haskell" | "hs" => some .Haskell
  | "rust" | "rs" => some .Rust
  | _ => none

/-- Parse comma-separated targets -/
def parseTargets (s : String) : List TargetLang :=
  s.splitOn "," |>.filterMap parseTarget

/-- Print usage information -/
def printUsage : IO Unit := do
  IO.println "╔══════════════════════════════════════════════════════════════════╗"
  IO.println "║  Rosetta Multi-Target Code Generator                             ║"
  IO.println "╚══════════════════════════════════════════════════════════════════╝"
  IO.println ""
  IO.println "Usage: lake exe multi-target <source...> [options]"
  IO.println ""
  IO.println "Arguments:"
  IO.println "  <source...>           One or more .rosetta or .lego source files"
  IO.println ""
  IO.println "Options:"
  IO.println "  --out, -o <dir>       Output directory (default: ./generated/Rosetta)"
  IO.println "  --targets, -t <list>  Comma-separated targets: lean,scala,haskell,rust"
  IO.println "                        (default: all four)"
  IO.println "  --combined            Combine all sources into single file (legacy mode)"
  IO.println "  --separate            Generate separate files per module (default)"
  IO.println "  --quiet, -q           Suppress verbose output"
  IO.println "  --help, -h            Show this help message"
  IO.println ""
  IO.println "Examples:"
  IO.println "  lake exe multi-target src/Lego/Lego.rosetta"
  IO.println "  lake exe multi-target src/Lego/*.rosetta -o ./out"
  IO.println "  lake exe multi-target examples/Arith.lego -o ./out -t lean,rust"
  IO.println "  lake exe multi-target src/Lego/*.rosetta --combined  # single file per lang"
  IO.println ""

/-- Output mode: separate files per module or combined into one -/
inductive OutputMode where
  | Separate  -- One file per source module per language (default)
  | Combined  -- Single file per language (legacy)
  deriving Repr, BEq

/-- Command line arguments -/
structure Args where
  sourcePaths : List String
  outDir : String := "./generated/Rosetta"
  targets : List TargetLang := [.Lean, .Scala, .Haskell, .Rust]
  quiet : Bool := false
  outputMode : OutputMode := .Separate
  deriving Repr

/-- Parse command line arguments -/
def parseArgs (args : List String) : IO (Option Args) := do
  if args.isEmpty || args.contains "--help" || args.contains "-h" then
    printUsage
    return none

  let mut sourcePaths : List String := []
  let mut outDir := "./generated/Rosetta"
  let mut targets := [TargetLang.Lean, .Scala, .Haskell, .Rust]
  let mut quiet := false
  let mut outputMode := OutputMode.Separate
  let mut i := 0

  while i < args.length do
    let arg := args[i]!
    if arg == "--out" || arg == "-o" then
      if i + 1 < args.length then
        outDir := args[i + 1]!
        i := i + 2
      else
        IO.eprintln "Error: --out requires a directory argument"
        return none
    else if arg == "--targets" || arg == "-t" then
      if i + 1 < args.length then
        targets := parseTargets args[i + 1]!
        if targets.isEmpty then
          IO.eprintln s!"Error: Invalid targets: {args[i + 1]!}"
          return none
        i := i + 2
      else
        IO.eprintln "Error: --targets requires a list argument"
        return none
    else if arg == "--quiet" || arg == "-q" then
      quiet := true
      i := i + 1
    else if arg == "--combined" then
      outputMode := .Combined
      i := i + 1
    else if arg == "--separate" then
      outputMode := .Separate
      i := i + 1
    else if !arg.startsWith "-" then
      sourcePaths := sourcePaths ++ [arg]
      i := i + 1
    else
      IO.eprintln s!"Error: Unknown option: {arg}"
      printUsage
      return none

  if sourcePaths.isEmpty then
    IO.eprintln "Error: No source file specified"
    printUsage
    return none

  return some { sourcePaths, outDir, targets, quiet, outputMode }

/-! ## Rosetta → Target Language AST Transformations

    Transformation rules are defined in .lego files:
    - src/Rosetta/rosetta2lean.lego for Lean
    - (TODO) rosetta2scala.lego, rosetta2haskell.lego, rosetta2rust.lego

    The rules are loaded at runtime and applied using Lego.Runtime.transform.
-/

/-- Cache for loaded transformation rules to avoid reloading -/
abbrev TransformCache := Std.HashMap String (List Rule)

/-- Load transformation rules for a target language.
    Returns cached rules if already loaded. -/
def loadTransformRulesForTarget (rt : Runtime) (lang : TargetLang)
    (cache : IO.Ref TransformCache) : IO (Except String (List Rule)) := do
  let path := match lang with
    | .Lean => "./src/Rosetta/rosetta2lean.lego"
    | .Scala => "./src/Rosetta/rosetta2scala.lego"  -- TODO: create these
    | .Haskell => "./src/Rosetta/rosetta2haskell.lego"
    | .Rust => "./src/Rosetta/rosetta2rust.lego"

  -- Check cache first
  let cached ← cache.get
  if let some rules := cached.get? path then
    return .ok rules

  -- Load from file
  match ← Runtime.loadTransformRules rt path with
  | .error e => return .error s!"Failed to load transform rules from {path}: {e}"
  | .ok rules =>
    -- Cache for future use
    cache.modify (·.insert path rules)
    return .ok rules

/-- Transform Rosetta AST for a specific target language using rule-based transformation -/
def transformForTargetWithRules (rules : List Rule) (ast : Term) : Term :=
  Runtime.transform rules ast

/-- Get the name of an ADT definition -/
def getAdtName (t : Term) : Option String :=
  match t with
  | .con "adtDef" args =>
    if args.length >= 2 then
      match args[1]! with
      | .var n => some n
      | .lit s => some s
      | _ => none
    else none
  | _ => none

/-- Get constructor names from an ADT -/
def getConstructorNames (t : Term) : List String :=
  match t with
  | .con "adtDef" args =>
    let constrs := args.drop 3 |>.dropLast
    constrs.flatMap (fun c =>
      match c with
      | .con "constr" cargs =>
        match cargs with
        | (.var name) :: _ => [name]
        | (.lit name) :: _ => [name]
        | _ => []
      | .con "seq" inner => inner.flatMap (fun c' =>
          match c' with
          | .con "constr" [(.var name), _, _] => [name]
          | .con "constr" [(.lit name), _, _] => [name]
          | _ => [])
      | _ => [])
  | _ => []

/-- Rename a constructor within an ADT definition -/
def renameConstructor (t : Term) (oldName newName : String) : Term :=
  match t with
  | .con "constr" args =>
    match args with
    | [.var n, colon, ty] =>
      if n == oldName then .con "constr" [.var newName, colon, ty]
      else t
    | [.lit n, colon, ty] =>
      if n == oldName then .con "constr" [.lit newName, colon, ty]
      else t
    | _ => t
  | .con name inner =>
    .con name (inner.map (renameConstructor · oldName newName))
  | _ => t

/-- Get rewrite rule name from a term -/
def getRewriteRuleName (t : Term) : Option String :=
  match t with
  | .con "rewriteRule" args =>
    match args with
    | [_, .var name, _, _, _, _, _, _] => some name
    | _ => none
  | _ => none

/-- Reserved type names that conflict with target language built-ins - these are skipped -/
def reservedTypeNames : Std.HashSet String :=
  Std.HashSet.emptyWithCapacity 16
    |>.insert "Option"  -- Lean, Rust, Scala
    |>.insert "Unit"    -- Lean, Scala

/-- Deduplicate terms by ADT name and rewrite rule name (keeps first occurrence) -/
def deduplicateAdts (terms : List Term) : List Term :=
  let init : (Std.HashSet String × Std.HashSet String × Std.HashSet String × List Term) :=
    (Std.HashSet.emptyWithCapacity 32, Std.HashSet.emptyWithCapacity 64, Std.HashSet.emptyWithCapacity 128, [])
  let (_, _, _, result) := terms.foldl (fun (seenAdts, seenCtors, seenRules, acc) t =>
    -- Check if it's a rewrite rule
    match getRewriteRuleName t with
    | some ruleName =>
      if seenRules.contains ruleName then (seenAdts, seenCtors, seenRules, acc)
      else (seenAdts, seenCtors, seenRules.insert ruleName, acc ++ [t])
    | none =>
      -- Check if it's an ADT
      match getAdtName t with
      | some adtName =>
        -- Skip reserved names entirely (use built-in types)
        if reservedTypeNames.contains adtName then (seenAdts.insert adtName, seenCtors, seenRules, acc)
        else if seenAdts.contains adtName then (seenAdts, seenCtors, seenRules, acc)
        else
          -- Check for constructor name conflicts and rename if needed
          let ctorNames := getConstructorNames t
          let (newSeenCtors, finalT) := ctorNames.foldl (fun (ctors, term) ctorName =>
            if ctors.contains ctorName then
              -- Conflict! Rename to AdtNameCtorName (no underscore for Rust compatibility)
              let newCtorName := s!"{adtName}{ctorName}"
              (ctors.insert newCtorName, renameConstructor term ctorName newCtorName)
            else
              (ctors.insert ctorName, term)
          ) (seenCtors, t)
          (seenAdts.insert adtName, newSeenCtors, seenRules, acc ++ [finalT])
      | none => (seenAdts, seenCtors, seenRules, acc ++ [t])
  ) init
  result

/-- Merge multiple ASTs into a single AST by combining their children -/
def mergeAsts (asts : List Term) : Term :=
  -- Combine all children from all ASTs into one seq
  let allChildren := asts.flatMap (fun ast =>
    match ast with
    | .con _ args => args
    | _ => [ast])
  -- Deduplicate ADT definitions (common types like Term appear in multiple files)
  let dedupedChildren := deduplicateAdts allChildren
  .con "seq" dedupedChildren

/-- Extract module name from source path (e.g., "src/Lego/Algebra.rosetta" -> "Algebra") -/
def extractModuleName (sourcePath : String) : String :=
  let filename := sourcePath.splitOn "/" |>.getLast!
  let basename := filename.splitOn "." |>.head!
  basename

/-- Get ADT names defined in a Term (for dependency analysis) -/
def getDefinedAdtNames (t : Term) : List String :=
  match t with
  | .con "seq" children => children.flatMap getDefinedAdtNames
  | .con "adtDef" args =>
    if args.length >= 2 then
      match args[1]! with
      | .var n => [n]
      | .lit s => [s]
      | _ => []
    else []
  | .con _ children => children.flatMap getDefinedAdtNames
  | _ => []

/-- Extract import declarations from a Term AST -/
def getImports (t : Term) : List String :=
  match t with
  | .con "seq" children => children.flatMap getImports
  -- Rosetta grammar produces: con "DImport" [lit "import", con "modulePath" [con "ident" [var name]], lit ";"]
  | .con "DImport" args =>
    args.filterMap (fun arg =>
      match arg with
      | .con "modulePath" [.con "ident" [.var name]] => some name
      | .con "modulePath" [.con "ident" [.lit name]] => some name
      | .con "ident" [.var name] => some name
      | .con "ident" [.lit name] => some name
      | .var name => some name
      | .lit name => if name != "import" && name != ";" then some name else none
      | _ => none
    )
  -- Also check for importDecl (in case the grammar changed)
  | .con "importDecl" args =>
    args.filterMap (fun arg =>
      match arg with
      | .var name => some name
      | .lit name => if name != "import" && name != ";" then some name else none
      | _ => none
    )
  | .con _ children => children.flatMap getImports
  | _ => []

/-- Check if string starts with uppercase -/
def startsWithUpper (s : String) : Bool :=
  match s.data.head? with
  | some c => c.isUpper
  | none => false

/-- Get type references from type annotations only (not patterns) -/
partial def getTypeRefs (t : Term) : List String :=
  match t with
  -- Type reference nodes
  | .con "typeRef" [.var n] => [n]
  | .con "typeRef" [.lit s] => [s]
  -- Arrow types: a -> b
  | .con "arrow" args => args.flatMap getTypeRefs
  -- Type applications: List a, Option b
  | .con "typeApp" args => args.flatMap getTypeRefs
  | .con "listType" args => args.flatMap getTypeRefs
  -- Constructor field types in ADT definitions
  | .con "constr" args =>
    -- Skip first arg (constructor name), process rest (types)
    args.drop 1 |>.flatMap getTypeRefs
  -- ADT definitions - extract from constructor types only
  | .con "adtDef" args =>
    -- args[0]=keyword, args[1]=name, args[2]=params, args[3..n-1]=constructors, args[n]=end
    args.drop 3 |>.dropLast |>.flatMap getTypeRefs
  -- Sequence of declarations
  | .con "seq" args => args.flatMap getTypeRefs
  -- Inductive (Lean)
  | .con "inductiveDecl" args => args.flatMap getTypeRefs
  -- Data (Haskell)
  | .con "dataDecl" args => args.flatMap getTypeRefs
  -- Sealed trait/case class (Scala)
  | .con "sealedTrait" args => args.flatMap getTypeRefs
  | .con "caseClass" args => args.flatMap getTypeRefs
  -- Enum (Rust)
  | .con "enumDecl" args => args.flatMap getTypeRefs
  -- Type variable or type name in type position
  | .var n => if startsWithUpper n then [n] else []
  | .lit s => if startsWithUpper s then [s] else []
  -- DON'T recurse into patterns, function definitions, etc.
  | _ => []

/-- Get external type dependencies (types referenced but not defined in this module) -/
def getExternalDeps (ast : Term) : List String :=
  let defined := getDefinedAdtNames ast |> Std.HashSet.ofList
  let refs := getTypeRefs ast
  -- Filter: referenced but not defined, starts with uppercase
  refs.filter (fun r => !defined.contains r && startsWithUpper r)
    |>.eraseDups

/-- Get constructor names defined in an ADT -/
def getDefinedConstructors (t : Term) : List String :=
  match t with
  | .con "seq" children => children.flatMap getDefinedConstructors
  | .con "adtDef" args =>
    let constrs := args.drop 3 |>.dropLast
    constrs.flatMap (fun c =>
      match c with
      | .con "constr" cargs =>
        match cargs with
        | (.var name) :: _ => [name]
        | (.lit name) :: _ => [name]
        | _ => []
      | .con "seq" inner => inner.flatMap (fun c' =>
          match c' with
          | .con "constr" [(.var name), _, _] => [name]
          | .con "constr" [(.lit name), _, _] => [name]
          | _ => [])
      | _ => [])
  | .con _ children => children.flatMap getDefinedConstructors
  | _ => []

/-- Get constructor references from patterns (e.g., .Con "x" [...]) -/
partial def getConstructorRefs (t : Term) : List String :=
  match t with
  | .con "matchArm" args => args.flatMap getConstructorRefs
  | .con "patternApp" ((.var n) :: rest) => n :: rest.flatMap getConstructorRefs
  | .con "patternApp" ((.lit s) :: rest) =>
    if startsWithUpper s then s :: rest.flatMap getConstructorRefs
    else rest.flatMap getConstructorRefs
  -- Detect .Constructor patterns in generated code
  | .lit s => if s.startsWith "." && s.length > 1 && startsWithUpper (s.drop 1) then [s.drop 1] else []
  | .con _ args => args.flatMap getConstructorRefs
  | _ => []

/-- Get external constructor dependencies -/
def getExternalConstructorDeps (ast : Term) : List String :=
  let definedCtors := getDefinedConstructors ast |> Std.HashSet.ofList
  let refs := getConstructorRefs ast
  refs.filter (!definedCtors.contains ·) |>.eraseDups

/-- Built-in types that don't need imports -/
def builtinTypes : Std.HashSet String :=
  Std.HashSet.emptyWithCapacity 32
    |>.insert "Bool" |>.insert "Int" |>.insert "Nat" |>.insert "String" |>.insert "Char"
    |>.insert "Float" |>.insert "List" |>.insert "Option" |>.insert "Unit" |>.insert "Type"
    |>.insert "IO" |>.insert "Array"

/-- Generate import statement for a target language -/
def genImport (lang : TargetLang) (moduleName : String) (packagePrefix : String) : String :=
  match lang with
  | .Lean => s!"import {packagePrefix}.{moduleName}"
  | .Scala => s!"import {packagePrefix.toLower}.{moduleName}._"
  | .Haskell => s!"import {moduleName}"
  | .Rust => s!"use super::{moduleName.toLower}::*;"

/-- Generate module header with imports for separate file mode -/
def genModuleHeader (lang : TargetLang) (moduleName : String) (imports : List String) (packagePrefix : String) : String :=
  let importLines := imports.map (genImport lang · packagePrefix) |> "\n".intercalate
  match lang with
  | .Lean => importLines ++ (if imports.isEmpty then "" else "\n\n")
  | .Scala =>
    -- Each Scala module gets its own sub-package to avoid name collisions
    let pkg := s!"package {packagePrefix.toLower}.{moduleName.toLower}\n\n"
    pkg ++ importLines ++ (if imports.isEmpty then "" else "\n\n")
  | .Haskell =>
    let modDecl := s!"module {moduleName} where\n\n"
    modDecl ++ importLines ++ (if imports.isEmpty then "" else "\n\n")
  | .Rust =>
    "#![allow(dead_code)]\n#![allow(unused_variables)]\n\n" ++
    importLines ++ (if imports.isEmpty then "" else "\n\n")

/-- Result for a single module generation -/
structure ModuleResult where
  moduleName : String
  lang : TargetLang
  code : String
  outPath : String
  definedTypes : List String
  definedConstructors : List String
  externalDeps : List String
  externalCtorDeps : List String
  deriving Repr

/-- Run pipeline for a single source file, generating per-module output -/
def runForModule (rt : Runtime) (sourceAst : Term) (sourcePath : String) (lang : TargetLang)
    (outDir : String) (packagePrefix : String) (transformRules : List Rule) (_quiet : Bool := false)
    : IO (Except String ModuleResult) := do
  let moduleName := extractModuleName sourcePath

  -- 1. Load target grammar
  let grammar ← match ← loadLanguage rt lang.grammarPath with
    | .error e => return .error s!"Failed to load grammar: {e}"
    | .ok g => pure g

  -- 2. Analyze dependencies on the source AST
  let definedTypes := getDefinedAdtNames sourceAst
  let definedConstructors := getDefinedConstructors sourceAst
  let externalDeps := getExternalDeps sourceAst |>.filter (!builtinTypes.contains ·)
  let externalCtorDeps := getExternalConstructorDeps sourceAst

  -- 3. Transform AST for target language using .lego transformation rules
  -- Rules are loaded from src/Rosetta/rosetta2<target>.lego
  let targetAst := if transformRules.isEmpty then sourceAst
                   else transformForTargetWithRules transformRules sourceAst
  dbg_trace s!"sourceAst: {sourceAst}"
  dbg_trace s!"targetAst: {targetAst}"

  -- 4. Pretty-print using grammar interpreter
  -- The grammar's layout annotations (@nl, @indent, etc.) control formatting
  -- For Lean, use native Lean grammar. For others, try RosettaIR piece.
  let code := match lang with
    | .Lean =>
      -- Wrap declarations in a module node for the Lean grammar
      -- Lean grammar: module ::= decl* → module
      -- targetAst is (seq decl1 decl2 ...) or (inductiveDecl ...) for single decl
      let moduleAst := match targetAst with
        | .con "seq" children => Term.con "module" children
        | .con "module" _ => targetAst  -- Already a module
        | single => Term.con "module" [single]  -- Single declaration

      dbg_trace s!"Attempting to print Lean AST: {moduleAst}"
      match printToString grammar "Module.module" moduleAst with
      | some s =>
        dbg_trace s!"Printed with Module.module"
        s
      | none =>
        dbg_trace s!"Module.module failed, trying module..."
        match printToString grammar "module" moduleAst with
        | some s =>
          dbg_trace s!"Printed with module"
          s
        | none =>
          dbg_trace s!"module failed, trying decl on original..."
          -- Try individual declarations from original targetAst
          match targetAst with
          | .con "seq" children =>
            dbg_trace s!"Found seq with {children.length} children"
            let printed := children.filterMap fun child =>
              dbg_trace s!"Trying to print child"
              printToString grammar "Declarations.decl" child
                <|> printToString grammar "decl" child
            if printed.isEmpty then
              s!"-- Failed to print Lean AST\n-- AST: {targetAst}"
            else
              "\n".intercalate printed
          | _ =>
            s!"-- Failed to print Lean AST\n-- AST: {targetAst}"
    | _ =>
      -- For other targets, use RosettaIR piece
      match printToString grammar "RosettaIR.rosettaFile" sourceAst with
      | some s => s
      | none =>
        match printToString grammar "rosettaFile" sourceAst with
        | some s => s
        | none =>
          match printToString grammar "file" sourceAst with
          | some s => s
          | none =>
            match printToString grammar "module" sourceAst with
            | some s => s
            | none =>
              match printToString grammar "program" sourceAst with
              | some s => s
              | none => s!"-- Failed to print AST for {lang}\n-- AST: {sourceAst}"

  -- 5. Build result (header will be added later when we know which modules exist)
  let outPath := match lang with
    | .Rust => s!"{outDir}/{moduleName.toLower}{lang.ext}"
    | _ => s!"{outDir}/{moduleName}{lang.ext}"

  return .ok { moduleName, lang, code, outPath, definedTypes, definedConstructors, externalDeps, externalCtorDeps }

/-- Resolve which modules provide which types and constructors (first definition wins) -/
def buildTypeToModuleMap (results : List ModuleResult) : Std.HashMap String String :=
  let typeMap := results.foldl (fun m r =>
    r.definedTypes.foldl (fun m' t =>
      -- Only add if not already mapped (first wins)
      if m'.contains t then m' else m'.insert t r.moduleName
    ) m
  ) (Std.HashMap.emptyWithCapacity 64)
  -- Also add constructors to module map (first wins)
  results.foldl (fun m r =>
    r.definedConstructors.foldl (fun m' c =>
      if m'.contains c then m' else m'.insert c r.moduleName
    ) m
  ) typeMap

/-- Get the modules that a given module should import -/
def getRequiredImports (result : ModuleResult) (typeToModule : Std.HashMap String String) : List String :=
  -- Imports from type dependencies
  let typeImports := result.externalDeps.filterMap (typeToModule.get? ·)
  -- Imports from constructor dependencies, but only if we don't define that constructor ourselves
  let ctorImports := result.externalCtorDeps.filterMap (fun ctor =>
    -- Skip if this module also defines this constructor (avoid circular imports from duplicates)
    if result.definedConstructors.contains ctor then none
    else typeToModule.get? ctor
  )
  -- Combine and deduplicate
  (typeImports ++ ctorImports)
    |>.filter (· != result.moduleName)  -- Don't import self
    |>.eraseDups

/-- Resolve import name to file path (assumes import in same directory as source) -/
def resolveImportPath (sourcePath : String) (importName : String) : String :=
  let dir := sourcePath.splitOn "/" |>.dropLast |> "/".intercalate
  s!"{dir}/{importName}.rosetta"

/-- Extract ADT definitions from AST as a list of (name, Term) pairs -/
def extractAdtDefs (t : Term) : List (String × Term) :=
  match t with
  | .con "seq" children => children.flatMap extractAdtDefs
  | .con "adtDef" args =>
    if args.length >= 2 then
      match args[1]! with
      | .var n => [(n, t)]
      | .lit s => [(s, t)]
      | _ => []
    else []
  | .con _ children => children.flatMap extractAdtDefs
  | _ => []

/-- Remove import declarations from AST (they're handled separately) -/
partial def stripImports (t : Term) : Term :=
  match t with
  | .con "seq" children =>
    let filtered := children.filter (fun c =>
      match c with
      | .con "importDecl" _ => false
      | _ => true)
    .con "seq" (filtered.map stripImports)
  | .con name children => .con name (children.map stripImports)
  | other => other

/-- Run pipeline in separate files mode -/
def runSeparate (rt : Runtime) (args : Args) : IO (Except String (List TargetResult)) := do
  let { sourcePaths, outDir, targets, quiet, .. } := args

  unless quiet do
    IO.println "╔══════════════════════════════════════════════════════════════════╗"
    IO.println "║  Rosetta Multi-Target Code Generator (Separate Files Mode)       ║"
    IO.println "╚══════════════════════════════════════════════════════════════════╝"
    IO.println ""
    IO.println s!"  Sources: {sourcePaths.length} file(s)"
    for p in sourcePaths do
      IO.println s!"           - {p}"
    IO.println s!"  Output:  {outDir}"
    IO.println s!"  Targets: {targets.map toString |> ", ".intercalate}"
    IO.println ""

  -- Load Rosetta grammar if needed
  let hasRosettaFiles := sourcePaths.any (·.endsWith ".rosetta")
  let rosettaGrammar ← if hasRosettaFiles then do
    unless quiet do IO.println "      Loading Rosetta grammar..."
    match ← loadLanguage rt "./src/Rosetta/Rosetta.lego" with
    | .error e => return .error s!"Failed to load Rosetta grammar: {e}"
    | .ok grammar => pure (some grammar)
  else pure none

  -- Parse all source files
  unless quiet do IO.println s!"[1/4] Parsing {sourcePaths.length} source file(s)..."
  let mut sourceAsts : List (String × Term) := []
  let mut importedTypes : Std.HashMap String Term := Std.HashMap.emptyWithCapacity 16

  -- Helper to parse a rosetta file
  let parseRosettaFile : String → IO (Except String Term) := fun path => do
    match rosettaGrammar with
    | some grammar =>
      let content ← IO.FS.readFile path
      -- Use rosettaFile start production for .rosetta files
      let rosettaParseGrammar := { grammar with startProd := "File.rosettaFile" }
      match Loader.parseWithGrammarE rosettaParseGrammar content with
      | .error e => return .error s!"Parse error in {path}: {e}"
      | .ok ast => return .ok ast
    | none => return .error "Rosetta grammar not loaded"

  for sourcePath in sourcePaths do
    let ast ← do
      if sourcePath.endsWith ".rosetta" then
        match ← parseRosettaFile sourcePath with
        | .error e => return .error e
        | .ok ast =>
          -- Extract imports and load them
          let imports := getImports ast
          for importName in imports do
            if !importedTypes.contains importName then
              let importPath := resolveImportPath sourcePath importName
              unless quiet do IO.println s!"      → Loading import: {importName}"
              match ← parseRosettaFile importPath with
              | .error e =>
                unless quiet do IO.println s!"      ⚠ Warning: Could not load import {importName}: {e}"
              | .ok importAst =>
                -- Store the entire import AST for later
                importedTypes := importedTypes.insert importName importAst
          unless quiet do IO.println s!"      ✓ {sourcePath}"
          pure ast
      else
        match ← parseLegoFilePathE rt sourcePath with
        | .error e => return .error s!"Parse error in {sourcePath}: {e}"
        | .ok ast =>
          unless quiet do IO.println s!"      ✓ {sourcePath}"
          pure ast
    sourceAsts := sourceAsts ++ [(sourcePath, ast)]

  -- Generate for each target
  unless quiet do IO.println s!"[2/4] Generating code for {targets.length} target(s) × {sourcePaths.length} module(s)..."

  let mut allResults : List TargetResult := []
  let packagePrefix := "Generated"

  -- Create a cache for transformation rules
  let transformCache ← IO.mkRef (Std.HashMap.emptyWithCapacity 4 : TransformCache)

  for lang in targets do
    -- Load transformation rules for this target language
    let transformRules ← match ← loadTransformRulesForTarget rt lang transformCache with
      | .ok rules =>
        unless quiet do IO.println s!"      Loaded {rules.length} transformation rules for {lang}"
        pure rules
      | .error e =>
        unless quiet do IO.println s!"      ⚠ No transformation rules for {lang}: {e}"
        pure []

    -- Generate all modules for this language
    let mut moduleResults : List ModuleResult := []
    for (sourcePath, ast) in sourceAsts do
      -- Get imports for this module
      let imports := getImports ast
      -- Strip imports from AST and prepend imported type definitions
      let strippedAst := stripImports ast
      let importedDefs : List Term := imports.filterMap (fun imp => importedTypes.get? imp)
      -- Create combined AST with imported types first
      let combinedAst := if importedDefs.isEmpty then strippedAst else
        match strippedAst with
        | .con "seq" children => .con "seq" (importedDefs ++ children)
        | other => .con "seq" (importedDefs ++ [other])

      match ← runForModule rt combinedAst sourcePath lang outDir packagePrefix transformRules quiet with
      | .error e =>
        unless quiet do IO.println s!"      ✗ {lang}/{extractModuleName sourcePath}: {e}"
      | .ok r =>
        moduleResults := moduleResults ++ [r]

    -- Generate standalone files (imports already inlined)
    for r in moduleResults do
      let header := genModuleHeader lang r.moduleName [] packagePrefix

      let finalCode := header ++ r.code
      allResults := allResults ++ [{ lang := r.lang, code := finalCode, outPath := r.outPath }]
      unless quiet do IO.println s!"      ✓ {lang}/{r.moduleName}"

  -- Write outputs
  unless quiet do IO.println s!"[3/4] Writing {allResults.length} file(s)..."
  IO.FS.createDirAll outDir
  for r in allResults do
    IO.FS.writeFile r.outPath r.code
    unless quiet do IO.println s!"      ✓ {r.outPath}"

  -- Generate mod.rs for Rust (required for multi-file modules)
  if targets.contains .Rust then
    let rustModules := allResults.filter (·.lang == .Rust) |>.map (·.outPath)
    let modNames := rustModules.map (fun p =>
      let filename := p.splitOn "/" |>.getLast!
      filename.splitOn "." |>.head!)
    let modRs := modNames.map (s!"pub mod {·};") |> "\n".intercalate
    let modPath := s!"{outDir}/mod.rs"
    IO.FS.writeFile modPath modRs
    unless quiet do IO.println s!"      ✓ {modPath} (module index)"

  unless quiet do IO.println "[4/4] Done!"

  return .ok allResults

/-- Run pipeline in combined mode (legacy) -/
def runCombined (rt : Runtime) (args : Args) : IO (Except String (List TargetResult)) := do
  let { sourcePaths, outDir, targets, quiet, .. } := args

  unless quiet do
    IO.println "╔══════════════════════════════════════════════════════════════════╗"
    IO.println "║  Rosetta Multi-Target Code Generator (Combined Mode)             ║"
    IO.println "╚══════════════════════════════════════════════════════════════════╝"
    IO.println ""
    IO.println s!"  Sources: {sourcePaths.length} file(s)"
    for p in sourcePaths do
      IO.println s!"           - {p}"
    IO.println s!"  Output:  {outDir}"
    IO.println s!"  Targets: {targets.map toString |> ", ".intercalate}"
    IO.println ""

  -- Parse all source files
  unless quiet do IO.println s!"[1/3] Parsing {sourcePaths.length} source file(s)..."
  let mut allAsts : List Term := []

  -- For .rosetta files, we need to load the Rosetta grammar first
  let hasRosettaFiles := sourcePaths.any (·.endsWith ".rosetta")
  let rosettaGrammar ← if hasRosettaFiles then do
    unless quiet do IO.println "      Loading Rosetta grammar..."
    match ← loadLanguage rt "./src/Rosetta/Rosetta.lego" with
    | .error e => return .error s!"Failed to load Rosetta grammar: {e}"
    | .ok grammar => pure (some grammar)
  else pure none

  for sourcePath in sourcePaths do
    let ast ← do
      if sourcePath.endsWith ".rosetta" then
        -- Use Rosetta grammar for .rosetta files
        match rosettaGrammar with
        | some grammar =>
          let content ← IO.FS.readFile sourcePath
          match Loader.parseWithGrammarE grammar content with
          | .error e => return .error s!"Parse error in {sourcePath}: {e}"
          | .ok ast =>
            unless quiet do IO.println s!"      ✓ {sourcePath} (Rosetta)"
            pure ast
        | none => return .error "Rosetta grammar not loaded"
      else
        -- Use lego grammar for .lego files
        match ← parseLegoFilePathE rt sourcePath with
        | .error e => return .error s!"Parse error in {sourcePath}: {e}"
        | .ok ast =>
          unless quiet do IO.println s!"      ✓ {sourcePath}"
          pure ast
    allAsts := allAsts ++ [ast]

  -- Merge all ASTs
  let sourceAst := mergeAsts allAsts

  -- Generate for each target
  unless quiet do IO.println s!"[2/3] Generating code for {targets.length} target(s)..."

  let mut results : List TargetResult := []
  for lang in targets do
    match ← runForTarget rt sourceAst lang outDir quiet with
    | .error e =>
      unless quiet do IO.println s!"      ✗ {lang}: {e}"
    | .ok r =>
      results := results ++ [r]
      unless quiet do IO.println s!"      ✓ {lang}: {r.code.length} chars"

  -- Write outputs
  unless quiet do IO.println s!"[3/3] Writing {results.length} file(s)..."
  IO.FS.createDirAll outDir
  for r in results do
    IO.FS.writeFile r.outPath r.code
    unless quiet do IO.println s!"      ✓ {r.outPath}"

  return .ok results

/-- Main entry point - dispatches to separate or combined mode -/
def run (rt : Runtime) (args : Args) : IO (Except String (List TargetResult)) := do
  match args.outputMode with
  | .Separate => runSeparate rt args
  | .Combined => runCombined rt args

end MultiTargetPipeline

def main (args : List String) : IO Unit := do
  match ← MultiTargetPipeline.parseArgs args with
  | none => return  -- Help was shown or error occurred
  | some parsedArgs =>
    let rt ← Lego.Runtime.init

    match ← MultiTargetPipeline.run rt parsedArgs with
    | .error e =>
      IO.eprintln s!"Error: {e}"
      IO.Process.exit 1
    | .ok results =>
      unless parsedArgs.quiet do
        IO.println ""
        IO.println s!"✓ Generated {results.length} file(s) successfully"
