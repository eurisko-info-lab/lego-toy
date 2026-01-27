/-
  TestCool: CoolTT-specific tests for Lego

  Tests for CoolTT library parsing.
  Run with: lake exe lego-test-cool

  NOTE: This test suite uses Runtime.init to ensure Bootstrap.lego
  is loaded first, providing the correct grammar for all .lego file parsing.
-/

import Lego
import Lego.Bootstrap
import Lego.Loader
import Lego.Runtime

open Lego
open Lego.Loader
open Lego.Runtime

/-! ## Test Framework -/

structure TestResult where
  name : String
  passed : Bool
  message : String := ""

def assertTrue (name : String) (cond : Bool) : TestResult :=
  { name := name, passed := cond, message := if cond then "✓" else "✗ expected true" }

/-! ## CoolTT Parsing Utilities -/

-- Add containsSubstr helper
def String.containsSubstr (s sub : String) : Bool :=
  (s.splitOn sub).length > 1

/-- Get the main token productions to try in priority order -/
def getMainTokenProdsOrdered (tokenProds : Productions) : List String :=
  let names := tokenProds.map (·.1)
  -- Priority: comments/whitespace first (to skip), then longest operators first
  -- op10 before op7 before op5 before op3 before op2 before sym to ensure longest match
  -- Note: Cooltt uses Token.operator instead of Token.sym
  let priority := ["Token.comment", "Token.ws", "Token.string",
                   "Token.op10", "Token.op7", "Token.op5", "Token.op3", "Token.op2",
                   "Token.ident", "Token.number", "Token.operator", "Token.sym"]
  priority.filter names.contains

/-- Remove block comments /-...-/ from content (handles nesting) -/
def stripBlockComments (content : String) : String := Id.run do
  let mut result := ""
  let mut depth := 0
  let chars := content.toList
  let mut i := 0
  while i < chars.length do
    let c := chars[i]!
    let nextC := if i + 1 < chars.length then chars[i + 1]! else ' '
    if c == '/' && nextC == '-' then
      depth := depth + 1
      i := i + 2
    else if c == '-' && nextC == '/' then
      depth := max 0 (depth - 1)
      i := i + 2
    else if depth == 0 then
      result := result.push c
      i := i + 1
    else
      i := i + 1
  result

/-- Split a .cooltt file into individual top-level declarations -/
def splitCoolttDecls (content : String) : List String := Id.run do
  -- First strip block comments
  let noBlockComments := stripBlockComments content
  let noComments := noBlockComments.splitOn "\n"
    |>.map (fun line =>
      match line.splitOn "--" with
      | [] => ""
      | first :: _ => first)
    |> String.intercalate "\n"
  let lines := noComments.splitOn "\n"
  let mut decls : List String := []
  let mut current := ""
  let mut bracketDepth := 0  -- Track [ ] depth
  let mut braceDepth := 0    -- Track { } depth
  let mut beginEndDepth := 0 -- Track begin/end and sig/struct depth
  for line in lines do
    let trimmed := line.trimLeft
    -- Reset and recalculate depths from current content
    bracketDepth := 0
    braceDepth := 0
    beginEndDepth := 0
    -- Count brackets and braces
    for c in current.toList do
      if c == '[' then bracketDepth := bracketDepth + 1
      else if c == ']' then bracketDepth := bracketDepth - 1
      else if c == '{' then braceDepth := braceDepth + 1
      else if c == '}' then braceDepth := braceDepth - 1
    -- Count begin/end and sig/struct blocks (word-based)
    -- sig/struct that start multiline blocks (not [...]) are followed by 'end'
    -- Properly tokenize by replacing all whitespace with spaces, then splitting
    let normalizedWs := current.toList.map (fun c => if c == '\n' || c == '\t' then ' ' else c)
      |> String.mk
    let words := normalizedWs.splitOn " " |>.filter (·.length > 0)
    for w in words do
      let wt := w.trim
      if wt == "begin" || wt == "sig" || wt == "struct" then beginEndDepth := beginEndDepth + 1
      else if wt == "end" then beginEndDepth := max 0 (beginEndDepth - 1)
    -- Adjust for inline forms: sig [...] and struct [...] don't need end
    -- Each "sig [" or "struct [" pattern decreases effective depth
    let sigBracketCount := (current.splitOn "sig [").length - 1
    let structBracketCount := (current.splitOn "struct [").length - 1
    beginEndDepth := if beginEndDepth > sigBracketCount + structBracketCount
                    then beginEndDepth - sigBracketCount - structBracketCount
                    else 0
    -- Check if current declaration has a body (contains :=) AND is complete
    let currentHasBody := current.containsSubstr ":="
    let bodyComplete := currentHasBody && bracketDepth <= 0 && braceDepth <= 0 && beginEndDepth <= 0
    -- Only treat as top-level declaration start if we're not inside a block
    let insideBlock := beginEndDepth > 0 || bracketDepth > 0 || braceDepth > 0
    -- More precisely: check if trimmed contains " in " or ends with " in"
    let looksLikeUnfoldExpr := trimmed.startsWith "unfold " &&
                               (trimmed.containsSubstr " in " || trimmed.endsWith " in")
    -- CoolTT top-level declarations start with these keywords
    -- But NOT if we're inside a sig/struct/begin block!
    let isDeclStart := !insideBlock && (trimmed.startsWith "import " || trimmed.startsWith "def " ||
       trimmed.startsWith "axiom " || trimmed.startsWith "#print " ||
       trimmed.startsWith "#normalize " || trimmed.startsWith "#fail " ||
       trimmed.startsWith "#debug " || trimmed.startsWith "#quit" ||
       trimmed.startsWith "section " || trimmed.startsWith "view " ||
       trimmed.startsWith "export " || trimmed.startsWith "repack " ||
       -- Handle !export, !view, !repack (shorthand for shadowing)
       trimmed.startsWith "!export " || trimmed.startsWith "!view " ||
       trimmed.startsWith "!repack " ||
       -- Handle modifier + decl on same line
       trimmed.startsWith "shadowing def " || trimmed.startsWith "abstract def " ||
       trimmed.startsWith "shadowing axiom " || trimmed.startsWith "abstract axiom " ||
       trimmed.startsWith "shadowing export " || trimmed.startsWith "shadowing view " ||
       trimmed.startsWith "shadowing repack " || trimmed.startsWith "shadowing section " ||
       -- unfold without "in" at top level is a declaration (unfoldmod) or modifier
       -- Only treat as decl start if body is complete (balanced brackets)
       (trimmed.startsWith "unfold " && !looksLikeUnfoldExpr && (bodyComplete || !currentHasBody)))
    -- Standalone modifiers: "abstract" alone - only at top level
    let isModifierOnly := !insideBlock && (bodyComplete || !currentHasBody) && trimmed == "abstract"
    -- Helper to check if a string is just modifiers
    let isJustModifiers := fun (s : String) =>
      let lns := s.splitOn "\n"
      lns.all fun l =>
        let t := l.trimLeft
        t.isEmpty || t == "abstract"
        -- Note: "unfold X" is NOT just a modifier - it can be a standalone command
        -- We only combine it when followed by def/axiom (handled below)
    -- Check if this line starts a def/axiom (the things modifiers modify)
    let isDefOrAxiomStart := trimmed.startsWith "def " || trimmed.startsWith "axiom " ||
       trimmed.startsWith "shadowing def " || trimmed.startsWith "abstract def " ||
       trimmed.startsWith "shadowing axiom " || trimmed.startsWith "abstract axiom "
    -- Check if current is just unfold (potential modifier OR standalone)
    let isJustUnfold := fun (s : String) =>
      let lns := s.splitOn "\n"
      lns.all fun l =>
        let t := l.trimLeft
        t.isEmpty || (t.startsWith "unfold " && !t.containsSubstr " in ")
    if isDeclStart then
      if !current.isEmpty then
        let currentTrim := current.trim
        -- If current is just pure modifiers (abstract), combine with any decl
        -- If current is just unfold, only combine with def/axiom (otherwise unfold is standalone)
        let shouldCombine := isJustModifiers currentTrim ||
                            (isJustUnfold currentTrim && isDefOrAxiomStart)
        if shouldCombine then
          current := current ++ "\n" ++ line
        else
          decls := decls ++ [currentTrim]
          current := line
      else
        current := line
    else if isModifierOnly then
      -- Modifier line (abstract alone)
      if current.isEmpty then
        current := line
      else
        let currentTrim := current.trim
        -- If current is just modifiers, accumulate
        if isJustModifiers currentTrim then
          current := current ++ "\n" ++ line
        else
          -- Current has a real declaration, save it and start fresh with modifier
          decls := decls ++ [currentTrim]
          current := line
    else
      current := current ++ "\n" ++ line
  if !current.isEmpty then
    decls := decls ++ [current.trim]
  return decls.filter (fun s => !s.isEmpty)

/-- Fuel for CoolTT parsing - lower than defaultFuel to avoid stack overflow
    The CoolTT grammar has deep recursion; 10000 is enough for most declarations -/
def coolttFuel : Nat := 50000

/-- Debug parsing for a single CoolTT declaration, returning details -/
def debugCoolttParse (rt : Runtime) (decl : String) : IO Unit := do
  try
    let content ← IO.FS.readFile "./examples/Cubical/syntax/Cooltt.lego"
    match Runtime.parseLegoFile rt content with
    | none => IO.println "Failed to load Cooltt.lego"
    | some ast =>
      let coolttProds := extractAllProductions ast
      let tokenProds := extractTokenProductions ast
      let coolttKeywords := ["abstract", "shadowing", "def", "axiom", "import",
                             "let", "in", "elim", "with", "section", "view", "export", "repack",
                             "begin", "end", "as", "sig", "struct", "open", "renaming",
                             "generalize", "unfold", "ext", "sub", "coe", "com", "hcom", "hfill",
                             "∨", "\\/", "∧", "/\\",
                             "+", "-", "*", "_"]
      let keywords := (extractKeywords coolttProds ++ coolttKeywords).eraseDups
      let mainProds := getMainTokenProdsOrdered tokenProds
      let tokens := tokenizeWithGrammar coolttFuel tokenProds mainProds decl keywords
      IO.println s!"Tokens ({tokens.length}): {tokens.take 30 |>.map reprToken}"

      let declProd := "File.topdecl"
      match coolttProds.find? (·.1 == declProd) with
      | none => IO.println "No File.topdecl production found"
      | some (_, g) =>
        let st : ParseState := { tokens := tokens, binds := [] }
        let (result, _) := parseGrammar coolttFuel coolttProds g st
        match result with
        | none => IO.println s!"Parse failed"
        | some (_, st') =>
          IO.println s!"Parse succeeded"
          IO.println s!"Remaining tokens ({st'.tokens.length}): {st'.tokens.take 20 |>.map reprToken}"
  catch e => IO.println s!"Error: {e}"

where
  reprToken : Token → String
    | .ident s => s!"id({s})"
    | .lit s => s!"lit({s})"
    | .sym s => s!"sym({s})"
    | .number s => s!"num({s})"
    | .sp => "sp"
    | .nl => "nl"
    | .indent => "indent"
    | .dedent => "dedent"

/-- Parse a single .cooltt file declaration using Cooltt grammar -/
def parseCoolttDecl (coolttProds : List (String × GrammarExpr))
                    (tokenProds : List (String × GrammarExpr))
                    (keywords : List String)
                    (decl : String) : Bool :=
  let declProd := "File.topdecl"
  let tokens := if tokenProds.isEmpty then
    Lego.Bootstrap.tokenizeBootstrap decl
  else
    let mainProds := getMainTokenProdsOrdered tokenProds
    tokenizeWithGrammar coolttFuel tokenProds mainProds decl keywords
  match coolttProds.find? (·.1 == declProd) with
  | some (_, g) =>
    let st : ParseState := { tokens := tokens, binds := [] }
    let (result, _) := parseGrammar coolttFuel coolttProds g st
    match result with
    | some (_, st') => st'.tokens.isEmpty
    | none => false
  | none => false

/-- Parse a .cooltt file and return (passed, total, list of failures) -/
def parseCoolttFileVerbose (coolttProds : List (String × GrammarExpr))
                           (tokenProds : List (String × GrammarExpr))
                           (keywords : List String)
                           (path : String) : IO (Nat × Nat × List String) := do
  try
    let content ← IO.FS.readFile path
    let decls := splitCoolttDecls content
    let mut passed := 0
    let mut total := 0
    let mut failures : List String := []
    for decl in decls do
      total := total + 1
      if parseCoolttDecl coolttProds tokenProds keywords decl then
        passed := passed + 1
      else
        let preview := if decl.length > 200 then decl.take 200 else decl
        let oneLine := preview.replace "\n" " "
        failures := failures ++ [oneLine]
    pure (passed, total, failures)
  catch _ =>
    pure (0, 0, [])

/-- Recursively find all .cooltt files in a directory -/
partial def findCoolttFiles (dir : String) : IO (List String) := do
  let mut files : List String := []
  try
    let entries ← System.FilePath.readDir dir
    for entry in entries do
      let path := entry.path.toString
      if ← System.FilePath.isDir entry.path then
        let subFiles ← findCoolttFiles path
        files := files ++ subFiles
      else if path.endsWith ".cooltt" then
        files := files ++ [path]
  catch _ =>
    pure ()
  pure files

/-! ## CoolTT Library Parsing Tests -/

def runCoolttParsingTests (rt : Runtime) : IO (List TestResult) := do
  let grammarResult ← do
    try
      let content ← IO.FS.readFile "./examples/Cubical/syntax/Cooltt.lego"
      pure (Runtime.parseLegoFile rt content)
    catch _ =>
      pure none

  match grammarResult with
  | none => pure [{ name := "cooltt_library_parse", passed := false, message := "✗ Cooltt.lego failed to load" }]
  | some ast =>
    let coolttProds := extractAllProductions ast
    let tokenProds := extractTokenProductions ast
    -- Use extractKeywordsWithTokens to get keywords from both main and token productions
    -- Also add operators that can be function names
    let baseKeywords := extractKeywordsWithTokens coolttProds tokenProds
    let extraKeywords := ["∨", "\\/", "∧", "/\\", "+", "-", "*", "_"]
    let keywords := (baseKeywords ++ extraKeywords).eraseDups

    IO.println s!"  Loaded {coolttProds.length} productions, {keywords.length} keywords"

    let testPath := "../vendor/cooltt/test"
    let testFiles ← findCoolttFiles testPath
    let sortedFiles := testFiles.toArray.qsort (· < ·) |>.toList

    let mut totalParsed := 0
    let mut totalDecls := 0

    let mut failCount := 0
    IO.println "  Parsing failures (first 100):"
    for filePath in sortedFiles do
      let (parsed, total, failures) ← parseCoolttFileVerbose coolttProds tokenProds keywords filePath
      totalParsed := totalParsed + parsed
      totalDecls := totalDecls + total
      for failure in failures do
        if failCount < 100 then
          IO.println s!"  FAIL [{filePath}]: {failure.take 120}..."
          failCount := failCount + 1

    let overallRate := if totalDecls > 0 then (totalParsed * 100) / totalDecls else 0
    let allPassed := overallRate = 100
    let checkMark := if allPassed then "✓" else "✗"
    let summaryTest := {
      name := "cooltt_library"
      passed := overallRate = 100
      message := s!"{checkMark} ({totalParsed}/{totalDecls} = {overallRate}%) across {sortedFiles.length} files"
    }

    pure [summaryTest]

/-! ## Test Runner -/

def printTestGroup (name : String) (tests : List TestResult) : IO (Nat × Nat) := do
  IO.println s!"\n── {name} ──"
  let mut passed := 0
  let mut failed := 0
  for test in tests do
    if test.passed then
      -- Show message even on success if it contains stats
      if test.message.isEmpty then
        IO.println s!"  ✓ {test.name}"
      else
        IO.println s!"  ✓ {test.name}: {test.message}"
      passed := passed + 1
    else
      IO.println s!"  ✗ {test.name}: {test.message}"
      failed := failed + 1
  pure (passed, failed)

def main (args : List String) : IO Unit := do
  IO.println "╔═══════════════════════════════════════════════════════════════╗"
  IO.println "║            CoolTT Tests for Lego                              ║"
  IO.println "╚═══════════════════════════════════════════════════════════════╝"

  -- CRITICAL: Initialize runtime by loading Bootstrap.lego FIRST
  -- This ensures all .lego file parsing uses the correct grammar
  let rt ← Runtime.init

  let mut totalPassed := 0
  let mut totalFailed := 0

  let coolttTests ← runCoolttParsingTests rt
  let (p, f) ← printTestGroup "Cooltt Library Parsing Tests" coolttTests
  totalPassed := totalPassed + p; totalFailed := totalFailed + f

  IO.println ""
  IO.println "═══════════════════════════════════════════════════════════════"
  IO.println s!"Total: {totalPassed + totalFailed} tests, {totalPassed} passed, {totalFailed} failed"
  if totalFailed == 0 then
    IO.println "All tests passed! ✓"
  else
    IO.println s!"FAILED: {totalFailed} tests"
    IO.Process.exit 1
