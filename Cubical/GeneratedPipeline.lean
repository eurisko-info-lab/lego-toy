/-
  GeneratedPipeline.lean
  Convert generated/*.lego files to .lean files

  Pipeline: .lego → Parse → Transform → Print .lean

  The transformation minimizes distance to hand-written target .lean files.
-/

import Lego.Runtime
import Lego.Bootstrap
import Lego.Loader
import Lego.Interp

open Lego.Runtime
open Lego.Bootstrap
open Lego.Loader
open Lego

/-! ## String Utilities -/

def stringContains (s : String) (sub : String) : Bool :=
  (s.splitOn sub).length > 1

def hasPrefix (s : String) (pre : String) : Bool :=
  s.startsWith pre

/-! ## Preprocessing

    Fix syntax differences between generated .lego files and Bootstrap grammar.
-/

/-- Preprocess .lego content to match Bootstrap grammar -/
def preprocessLegoContent (content : String) : String :=
  -- Replace () with (nil) - Bootstrap requires conname in patterns
  let content := content.replace "()" "(nil)"
  -- Replace ? in identifiers (not in Bootstrap ident grammar)
  let content := content.replace "?" "_Q"

  let lines := content.splitOn "\n"

  -- Process lines with state tracking for multi-line declarations
  let (processedLines, _) := lines.foldl (fun (acc, inComment) line =>
    let trimmed := line.trimLeft

    -- If we're skipping a multi-line declaration
    if inComment then
      if stringContains line ";" then
        (acc ++ [s!"-- {line}"], false)
      else
        (acc ++ [s!"-- {line}"], true)

    -- Comment out import statements
    else if hasPrefix trimmed "import " then
      (acc ++ [s!"-- {line}"], false)

    -- Comment out rules with "when" guards using $ (Bootstrap uses term not pattern)
    else if hasPrefix trimmed "rule " && stringContains line " when " && stringContains line "$" then
      if stringContains line ";" then
        (acc ++ [s!"-- {line}"], false)
      else
        (acc ++ [s!"-- {line}"], true)

    -- Comment out type declarations with $ (Bootstrap uses term not pattern)
    else if hasPrefix trimmed "type " && stringContains line "$" then
      if stringContains line ";" then
        (acc ++ [s!"-- {line}"], false)
      else
        (acc ++ [s!"-- {line}"], true)

    -- Comment out continuation lines starting with "when"
    else if hasPrefix trimmed "when " then
      if stringContains line ";" then
        (acc ++ [s!"-- {line}"], false)
      else
        (acc ++ [s!"-- {line}"], true)

    -- Fix lang declaration with imports: "lang Name (A B C) :=" → "lang Name :="
    else if hasPrefix trimmed "lang " && stringContains line "(" && stringContains line ":=" then
      let parts := line.splitOn "("
      if parts.length >= 1 then
        let beforeParen := parts[0]!
        let rest := line.splitOn ":="
        if rest.length >= 2 then
          (acc ++ [s!"{beforeParen}:={rest[1]!}"], false)
        else (acc ++ [line], false)
      else (acc ++ [line], false)

    else (acc ++ [line], false)
  ) ([], false)

  String.intercalate "\n" processedLines

/-! ## AST Extraction

    Extract declarations from parsed .lego AST.
-/

/-- Extract production (grammar) declarations -/
partial def extractProductionDecls (t : Term) : List (String × Term) :=
  match t with
  | .con "seq" args => args.flatMap extractProductionDecls
  | .con "DLang" args => args.flatMap extractProductionDecls
  | .con "DPiece" ((.lit "piece") :: (.con "ident" [.var pieceName]) :: items) =>
    items.flatMap fun item =>
      match item with
      | .con "DGrammar" [.con "ident" [.var prodName], _, expr, _] =>
        [(s!"{pieceName}.{prodName}", expr)]
      | _ => extractProductionDecls item
  | .con _ args => args.flatMap extractProductionDecls
  | _ => []

/-- Extract rule declarations -/
partial def extractRuleDecls (t : Term) : List (String × Term × Term) :=
  match t with
  | .con "seq" args => args.flatMap extractRuleDecls
  | .con "DLang" args => args.flatMap extractRuleDecls
  | .con "DPiece" ((.lit "piece") :: _ :: items) =>
    items.flatMap fun item =>
      match item with
      | .con "DRule" [_, .con "ident" [.var ruleName], _, pattern, _, template, _, _] =>
        [(ruleName, pattern, template)]
      | _ => extractRuleDecls item
  | .con _ args => args.flatMap extractRuleDecls
  | _ => []

/-- Extract test declarations -/
partial def extractTestDecls (t : Term) : List (String × Term × Option Term) :=
  match t with
  | .con "seq" args => args.flatMap extractTestDecls
  | .con "DLang" args => args.flatMap extractTestDecls
  | .con "DPiece" ((.lit "piece") :: _ :: items) =>
    items.flatMap fun item =>
      match item with
      | .con "DTest" [_, .con "string" [.lit testName], _, input, _, expected, _] =>
        [(testName, input, some expected)]
      | _ => extractTestDecls item
  | .con _ args => args.flatMap extractTestDecls
  | _ => []

/-! ## Lean Code Generation

    Transform extracted AST to Lean code that matches hand-written style.
-/

/-- Convert pattern Term to Lean pattern string -/
partial def patternToLean : Term → String
  | .var s => if s.startsWith "$" then s.drop 1 else s
  | .lit s => s!"\"{s}\""
  | .con "ident" [.var name] => name
  | .con "var" [_, .con "ident" [.var name]] => name  -- $name pattern
  | .con "con" [.con "ident" [.var name]] => s!".{name}"  -- bare constructor
  | .con "con" ((.lit "(") :: (.con "ident" [.var name]) :: args) =>
    let argStrs := args.filterMap fun a =>
      match a with
      | .lit ")" => none
      | _ => some (patternToLean a)
    if argStrs.isEmpty then s!".{name}"
    else s!".{name} {String.intercalate " " argStrs}"
  | .con name args =>
    let argStrs := args.map patternToLean |>.filter (· != "")
    if argStrs.isEmpty then name
    else s!"({name} {String.intercalate " " argStrs})"
  | t => toString (repr t).take 50

/-- Convert template Term to Lean expression string -/
partial def templateToLean : Term → String
  | .var s => if s.startsWith "$" then s.drop 1 else s
  | .lit s => s!"\"{s}\""
  | .con "ident" [.var name] => name
  | .con "var" [_, .con "ident" [.var name]] => name
  | .con "con" [.con "ident" [.var name]] => name
  | .con "con" ((.lit "(") :: (.con "ident" [.var name]) :: args) =>
    let argStrs := args.filterMap fun a =>
      match a with
      | .lit ")" => none
      | _ => some (templateToLean a)
    if argStrs.isEmpty then name
    else s!"{name} {String.intercalate " " argStrs}"
  | .con "num" [.con "number" [.lit n]] => n
  | .con name args =>
    let argStrs := args.map templateToLean |>.filter (· != "")
    if argStrs.isEmpty then name
    else s!"({name} {String.intercalate " " argStrs})"
  | t => toString (repr t).take 50

/-- Generate a Lean function from a rule -/
def ruleToLeanDef (ruleName : String) (pattern : Term) (template : Term) : String :=
  let patStr := patternToLean pattern
  let templStr := templateToLean template
  s!"/-- Rule: {ruleName} -/
def {ruleName} : Expr → Option Expr
  | {patStr} => some ({templStr})
  | _ => none
"

/-- Generate Lean code from extracted declarations -/
def generateLeanFromLego (moduleName : String) (ast : Term) : String :=
  let prods := extractProductionDecls ast
  let rules := extractRuleDecls ast
  let tests := extractTestDecls ast

  let header := s!"/-
  Generated from {moduleName}.lego

  Productions: {prods.length}
  Rules: {rules.length}
  Tests: {tests.length}
-/

import Lego.Cubical.Core

namespace Lego.Cubical.{moduleName}

open Lego.Core
open Lego.Core.Expr

"

  -- Generate comments for productions (grammar info)
  let prodSection :=
    if prods.isEmpty then ""
    else
      let prodDefs := prods.map fun (name, _) => s!"-- Grammar: {name}"
      "/-! ## Grammar Productions -/\n\n" ++ String.intercalate "\n" prodDefs ++ "\n\n"

  -- Generate stub functions from rules
  let ruleSection :=
    if rules.isEmpty then ""
    else
      let ruleDefs := rules.map fun (name, pat, templ) =>
        let patStr := patternToLean pat
        let templStr := templateToLean templ
        s!"/-- {name}: {patStr.take 40} ~> {templStr.take 40} -/
def {name} := sorry -- TODO: implement"
      "/-! ## Rewrite Rules -/\n\n" ++ String.intercalate "\n\n" ruleDefs ++ "\n\n"

  -- Generate test stubs
  let testSection :=
    if tests.isEmpty then ""
    else
      let testDefs := tests.map fun (name, _, _) =>
        s!"#check {name.replace "\"" ""} -- test"
      "/-! ## Tests -/\n\n" ++ String.intercalate "\n" testDefs ++ "\n\n"

  let footer := s!"end Lego.Cubical.{moduleName}
"

  header ++ prodSection ++ ruleSection ++ testSection ++ footer

/-! ## Pipeline -/

/-- Process a single .lego file -/
def processLegoFile (rt : Runtime) (inputPath : String) (outputDir : String) : IO Bool := do
  let fileName := inputPath.splitOn "/" |>.getLast!
  let moduleName := fileName.replace ".lego" "" |>.replace "-" "_"

  IO.println s!"  Processing {fileName}..."

  -- Read and preprocess
  let content ← IO.FS.readFile inputPath
  let content := preprocessLegoContent content

  -- Parse
  let result ← IO.ofExcept (parseLegoFileE rt content)

  -- Generate Lean code
  let leanCode := generateLeanFromLego moduleName result

  -- Write output
  let outPath := s!"{outputDir}/{moduleName}.lean"
  IO.FS.writeFile outPath leanCode
  IO.println s!"    ✓ Generated {outPath}"
  return true

/-- Find all .lego files in a directory -/
def findLegoFiles (dir : String) : IO (List String) := do
  let entries ← System.FilePath.readDir dir
  let legoFiles := entries.toList.filterMap fun entry =>
    let name := entry.fileName
    if name.endsWith ".lego" then some s!"{dir}/{name}" else none
  return legoFiles

def main (args : List String) : IO Unit := do
  IO.println "═══════════════════════════════════════════════════════════════"
  IO.println "Generated Pipeline: .lego → Parse → Transform → .lean"
  IO.println "═══════════════════════════════════════════════════════════════"

  let inputDir := args[0]? |>.getD "./src/Lego/Cubical/generated"
  let outputDir := args[1]? |>.getD "./generated/Cubical"

  -- Initialize Runtime
  IO.println "\n[0] Initializing Lego Runtime..."
  let rt ← Lego.Runtime.init
  IO.println s!"  ✓ Runtime initialized with {rt.grammar.productions.length} productions"

  -- Find .lego files
  IO.println s!"\n[1] Scanning {inputDir} for .lego files..."
  let legoFiles ← findLegoFiles inputDir
  IO.println s!"  Found {legoFiles.length} .lego files"

  -- Create output directory
  IO.println s!"\n[2] Creating output directory {outputDir}..."
  IO.FS.createDirAll outputDir
  IO.println "  ✓ Directory ready"

  -- Process each file
  IO.println "\n[3] Processing files..."
  let mut successCount := 0
  let mut failCount := 0

  for legoFile in legoFiles do
    try
      if ← processLegoFile rt legoFile outputDir then
        successCount := successCount + 1
    catch e =>
      IO.println s!"    ✗ Error: {e}"
      failCount := failCount + 1

  IO.println "\n═══════════════════════════════════════════════════════════════"
  IO.println s!"Summary: {successCount} succeeded, {failCount} failed"
  if failCount > 0 then
    IO.println "⚠ Some files failed to process"

end Lego.Cubical.GeneratedPipeline
