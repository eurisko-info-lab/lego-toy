/-
  Lego.LanguageRegistry: Dynamic Language Registration System
  
  This module provides a flexible way to register and load grammar files
  for different target languages without modifying Runtime.lean.
  
  Usage:
    -- Register a new language
    let registry := LanguageRegistry.empty
      |>.register "python" {
          grammarPath := "./languages/Python.lego"
          fileExtension := ".py"
          startProduction := "Module.module"
        }
    
    -- Load all registered grammars
    let (rt, grammars) ← registry.loadAll rt
    
    -- Parse a file with the appropriate grammar
    let result ← registry.parseFile grammars "example.py"
-/

import Lego.Loader
import Lego.Interp

namespace Lego.LanguageRegistry

open Lego

/-- Configuration for a language grammar -/
structure LanguageConfig where
  /-- Path to the .lego grammar file -/
  grammarPath : String
  /-- File extension this grammar parses (e.g., ".py", ".rs") -/
  fileExtension : String
  /-- The start production name (e.g., "Module.module") -/
  startProduction : String
  /-- Optional: list of file path patterns to exclude from parsing tests -/
  excludePatterns : List String := []
  /-- Optional: description of the language -/
  description : String := ""
  deriving Repr, Inhabited

/-- A loaded language with its grammar -/
structure LoadedLanguage where
  config : LanguageConfig
  grammar : Loader.LoadedGrammar
  deriving Repr

/-- Registry of language configurations -/
structure Registry where
  languages : List (String × LanguageConfig)
  deriving Repr, Inhabited

namespace Registry

/-- Create an empty registry -/
def empty : Registry := { languages := [] }

/-- Register a new language -/
def register (r : Registry) (name : String) (config : LanguageConfig) : Registry :=
  { languages := (name, config) :: r.languages }

/-- Get a language config by name -/
def get (r : Registry) (name : String) : Option LanguageConfig :=
  r.languages.find? (·.1 == name) |>.map (·.2)

/-- Get a language config by file extension -/
def getByExtension (r : Registry) (ext : String) : Option (String × LanguageConfig) :=
  r.languages.find? (·.2.fileExtension == ext)

/-- List all registered language names -/
def names (r : Registry) : List String :=
  r.languages.map (·.1)

end Registry

/-- Default registry with built-in languages -/
def defaultRegistry : Registry :=
  Registry.empty
    |>.register "lego" {
        grammarPath := "./src/Lego/Lego.lego"
        fileExtension := ".lego"
        startProduction := "File.legoFile"
        excludePatterns := [
          "./test/lego/Bootstrap.lego",
          "./src/Lego/Lego.lego",
          "./src/Rosetta/Rosetta.lego",
          "./src/Rosetta/Lean.lego"
        ]
        description := "Lego grammar and rule files"
      }
    |>.register "rosetta" {
        grammarPath := "./src/Rosetta/Rosetta.lego"
        fileExtension := ".rosetta"
        startProduction := "File.rosettaFile"
        description := "Rosetta IR files for multi-target codegen"
      }
    |>.register "lean" {
        grammarPath := "./src/Rosetta/Lean.lego"
        fileExtension := ".lean"
        startProduction := "Module.module"
        excludePatterns := ["./.lake/*", "./.cache/*"]
        description := "Lean 4 source files"
      }

/-- Loaded grammars map -/
abbrev LoadedGrammars := List (String × LoadedLanguage)

/-- Load a single language grammar using the base Lego grammar -/
def loadLanguage (baseGrammar : Loader.LoadedGrammar) (_name : String) (config : LanguageConfig) 
    : IO (Except String LoadedLanguage) := do
  try
    let content ← IO.FS.readFile config.grammarPath
    match Loader.parseWithGrammarE baseGrammar content with
    | .error e => return .error s!"Failed to parse {config.grammarPath}: {e}"
    | .ok ast =>
      let prods := Loader.extractAllProductions ast
      let tokenProds := Loader.extractTokenProductions ast
      -- Merge with base grammar
      let mergedProds := prods ++ baseGrammar.productions
      let mergedTokenProds := tokenProds ++ baseGrammar.tokenProductions
      let symbols := Loader.extractAllSymbols mergedProds
      let grammar : Loader.LoadedGrammar := {
        productions := mergedProds
        tokenProductions := mergedTokenProds
        symbols := symbols
        startProd := config.startProduction
      }
      return .ok { config := config, grammar := grammar }
  catch e =>
    return .error s!"Error loading {config.grammarPath}: {e}"

/-- Load all languages in the registry -/
def loadAll (r : Registry) (baseGrammar : Loader.LoadedGrammar) : IO (Except String LoadedGrammars) := do
  let mut loaded : LoadedGrammars := []
  for (name, config) in r.languages do
    match ← loadLanguage baseGrammar name config with
    | .error e => return .error e
    | .ok lang => loaded := (name, lang) :: loaded
  return .ok loaded

/-- Get a loaded grammar by name -/
def getGrammar (grammars : LoadedGrammars) (name : String) : Option LoadedLanguage :=
  grammars.find? (·.1 == name) |>.map (·.2)

/-- Get a loaded grammar by file extension -/
def getGrammarByExtension (grammars : LoadedGrammars) (ext : String) : Option (String × LoadedLanguage) :=
  grammars.find? (·.2.config.fileExtension == ext)

/-- Parse a file using the appropriate grammar based on extension -/
def parseFile (grammars : LoadedGrammars) (path : String) : IO (Except String Term) := do
  -- Determine extension
  let ext := if path.endsWith ".lego" then ".lego"
             else if path.endsWith ".rosetta" then ".rosetta"
             else if path.endsWith ".lean" then ".lean"
             else System.FilePath.extension (System.FilePath.mk path) |>.getD ""
  
  match getGrammarByExtension grammars ext with
  | none => return .error s!"No grammar registered for extension: {ext}"
  | some (_, lang) =>
    let content ← IO.FS.readFile path
    match Loader.parseWithGrammarE lang.grammar content with
    | .error e => return .error (toString e)
    | .ok ast => return .ok ast

/-- Parse file with detailed error -/
def parseFileE (grammars : LoadedGrammars) (path : String) : IO (Except ParseError Term) := do
  let ext := if path.endsWith ".lego" then ".lego"
             else if path.endsWith ".rosetta" then ".rosetta"
             else if path.endsWith ".lean" then ".lean"
             else System.FilePath.extension (System.FilePath.mk path) |>.getD ""
  
  match getGrammarByExtension grammars ext with
  | none => return .error { 
      message := s!"No grammar registered for extension: {ext}"
      tokenPos := 0
      production := ""
      expected := []
      actual := none
      remaining := []
    }
  | some (_, lang) =>
    let content ← IO.FS.readFile path
    return Loader.parseWithGrammarE lang.grammar content

end Lego.LanguageRegistry
