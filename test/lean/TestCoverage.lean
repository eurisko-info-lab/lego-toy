/-
  TestCoverage: Analyze test coverage for Lego codebase

  Scans source files for public definitions and cross-references
  with test files to identify untested code.

  Run with: lake exe lego-coverage [options]

  Options:
    --summary     Show only summary (default)
    --untested    Show untested functions
    --tested      Show tested functions
    --all         Show all functions
    --by-file     Group by source file
    --deps        Show dependency graph with coverage priority
    --help        Show help
-/

open System

/-! ## Types -/

structure Definition where
  name : String
  file : String
  line : Nat
  kind : String  -- "def", "structure", "inductive", etc.
  deriving Repr, BEq, Hashable

/-! ## Dependency Graph -/

/-- File dependency information -/
structure FileDeps where
  file : String
  imports : List String
  dependents : Nat  -- how many files depend on this one
  deriving Repr

/-- Extract module imports from file content -/
def extractImports (content : String) : List String :=
  let lines := content.splitOn "\n"
  lines.filterMap fun line =>
    let trimmed := line.trim
    if trimmed.startsWith "import Lego." then
      some (trimmed.drop 12)  -- "import Lego." length
    else
      none

/-- Build dependency graph from src/Lego files -/
def buildDepGraph (srcDir : FilePath) : IO (List FileDeps) := do
  let mut fileImports : List (String × List String) := []
  let entries ← srcDir.readDir
  for entry in entries do
    if entry.path.extension == some "lean" then
      let fileName := entry.path.fileName.getD ""
      let moduleName := fileName.dropRight 5  -- remove .lean
      let content ← IO.FS.readFile entry.path
      let imports := extractImports content
      fileImports := (moduleName, imports) :: fileImports

  -- Count dependents for each file
  let allModules := fileImports.map (·.1)
  let mut result : List FileDeps := []
  for (moduleName, imports) in fileImports do
    -- Count how many other files import this one
    let dependentCount := fileImports.filter (fun (_, imps) => imps.contains moduleName) |>.length
    result := { file := moduleName, imports := imports, dependents := dependentCount } :: result

  return result.reverse

/-- Calculate priority score: files with more dependents are more critical -/
def priorityScore (deps : FileDeps) (testedPct : Nat) : Nat :=
  -- Weight: dependents × (100 - coverage%)
  -- Higher score = more critical to test
  (deps.dependents + 1) * (100 - testedPct)

structure CoverageResult where
  totalDefs : Nat
  testedDefs : Nat
  untestedDefs : List Definition
  testedList : List Definition
  byFile : List (String × Nat × Nat)  -- (file, tested, total)
  deriving Repr

/-! ## Parsing -/

/-- Extract definition name from a line like "def foo" or "structure Bar" -/
def extractDefName (line : String) : Option (String × String) := do
  let trimmed := line.trimLeft
  -- Check various definition patterns
  let patterns : List (String × String) := [
    ("def ", "def"),
    ("partial def ", "def"),
    ("private def ", "def"),
    ("protected def ", "def"),
    ("theorem ", "theorem"),
    ("lemma ", "lemma"),
    ("structure ", "structure"),
    ("inductive ", "inductive"),
    ("class ", "class"),
    ("instance ", "instance"),
    ("abbrev ", "abbrev")
  ]
  for p in patterns do
    let pfx := p.1
    let kind := p.2
    if trimmed.startsWith pfx then
      let rest := trimmed.drop pfx.length
      -- Extract name (until space, colon, or where)
      let name := rest.takeWhile (fun c => c.isAlphanum || c == '_' || c == '\'')
      if name.length > 0 then
        return (name, kind)
  none

/-- Scan a file for definitions -/
def scanFileForDefs (path : FilePath) : IO (List Definition) := do
  let content ← IO.FS.readFile path
  let lines := content.splitOn "\n"
  let fileName := path.toString
  let mut defs : List Definition := []
  let mut lineNum := 0
  for line in lines do
    lineNum := lineNum + 1
    -- Skip comments and empty lines
    let trimmed := line.trimLeft
    if trimmed.startsWith "--" || trimmed.startsWith "/-" || trimmed.isEmpty then
      continue
    -- Try to extract a definition
    match extractDefName line with
    | some (name, kind) =>
      -- Skip internal/generated names
      if !name.startsWith "_" && !name.startsWith "match_" then
        defs := defs ++ [{ name := name, file := fileName, line := lineNum, kind := kind }]
    | none => continue
  return defs

/-- Scan test files for mentioned function names -/
def scanTestsForMentions (testDir : FilePath) : IO (List String) := do
  let mut mentions : List String := []
  let entries ← testDir.readDir
  for entry in entries do
    if entry.path.extension == some "lean" then
      let content ← IO.FS.readFile entry.path
      -- Extract all identifiers that look like they could be function references
      let words := content.splitOn " " ++ content.splitOn "\n" ++ content.splitOn "("
      for word in words do
        let cleaned := word.trim.takeWhile (fun c => c.isAlphanum || c == '_')
        if cleaned.length > 2 || cleaned == "id" then
          let chars := cleaned.toList
          if let some c := chars.head? then
            if c.isAlpha then
              mentions := mentions ++ [cleaned]
  return mentions.eraseDups

/-! ## Analysis -/

/-- Check if a definition appears to be tested -/
def isTested (def_ : Definition) (testMentions : List String) : Bool :=
  -- Check if the function name is mentioned in tests
  testMentions.contains def_.name ||
  -- Check common test naming patterns
  testMentions.contains s!"test{def_.name.capitalize}" ||
  testMentions.contains s!"Test{def_.name.capitalize}"

/-- Analyze coverage -/
def analyzeCoverage (srcDirs : List FilePath) (testDir : FilePath) : IO CoverageResult := do
  -- Collect all definitions
  let mut allDefs : List Definition := []
  for srcDir in srcDirs do
    if ← srcDir.pathExists then
      let entries ← srcDir.readDir
      for entry in entries do
        if entry.path.extension == some "lean" then
          let defs ← scanFileForDefs entry.path
          allDefs := allDefs ++ defs

  -- Scan tests for mentions
  let testMentions ← scanTestsForMentions testDir

  -- Categorize
  let mut tested : List Definition := []
  let mut untested : List Definition := []

  for def_ in allDefs do
    if isTested def_ testMentions then
      tested := tested ++ [def_]
    else
      untested := untested ++ [def_]

  -- Group by file
  let files := allDefs.map (·.file) |>.eraseDups
  let mut byFile : List (String × Nat × Nat) := []
  for file in files do
    let fileDefs := allDefs.filter (·.file == file)
    let fileTestedCount := fileDefs.filter (fun d => tested.contains d) |>.length
    byFile := byFile ++ [(file, fileTestedCount, fileDefs.length)]

  return {
    totalDefs := allDefs.length
    testedDefs := tested.length
    untestedDefs := untested
    testedList := tested
    byFile := byFile
  }

/-! ## Output -/

/-- Format a percentage -/
def formatPercent (n d : Nat) : String :=
  if d == 0 then "N/A"
  else
    let pct := (n * 100) / d
    s!"{pct}%"

/-- Print summary -/
def printSummary (result : CoverageResult) : IO Unit := do
  IO.println "═══════════════════════════════════════════════════════════════"
  IO.println "                    Test Coverage Analysis"
  IO.println "═══════════════════════════════════════════════════════════════"
  IO.println ""
  IO.println s!"  Total definitions:   {result.totalDefs}"
  IO.println s!"  Tested definitions:  {result.testedDefs}"
  IO.println s!"  Untested definitions: {result.untestedDefs.length}"
  IO.println s!"  Coverage:            {formatPercent result.testedDefs result.totalDefs}"
  IO.println ""

/-- Print by-file breakdown -/
def printByFile (result : CoverageResult) : IO Unit := do
  IO.println "── Coverage by File ──"
  IO.println ""
  for (file, tested, total) in result.byFile.toArray.qsort (fun a b => a.1 < b.1) do
    let shortFile := file.splitOn "/" |>.getLast!
    let pct := formatPercent tested total
    let status := if tested == total then "✓" else if tested > 0 then "◐" else "○"
    let paddedFile := shortFile ++ String.mk (List.replicate (25 - min 25 shortFile.length) ' ')
    IO.println s!"  {status} {paddedFile} {tested}/{total} ({pct})"
  IO.println ""

/-- Print untested functions -/
def printUntested (result : CoverageResult) : IO Unit := do
  IO.println "── Untested Definitions ──"
  IO.println ""
  -- Group by file manually
  let files := result.untestedDefs.map (·.file) |>.eraseDups
  for file in files.toArray.qsort (· < ·) do
    let defs := result.untestedDefs.filter (·.file == file)
    let shortFile := file.splitOn "/" |>.getLast!
    IO.println s!"  {shortFile}:"
    for def_ in defs do
      IO.println s!"    - {def_.name} ({def_.kind}, line {def_.line})"
  IO.println ""

/-- Print tested functions -/
def printTested (result : CoverageResult) : IO Unit := do
  IO.println "── Tested Definitions ──"
  IO.println ""
  for def_ in result.testedList.toArray.qsort (fun a b => a.name < b.name) do
    IO.println s!"  ✓ {def_.name}"
  IO.println ""

/-- Print dependency graph with coverage priority -/
def printDepsGraph (result : CoverageResult) : IO Unit := do
  IO.println "── Dependency Graph & Test Priority ──"
  IO.println ""
  IO.println "  Priority is based on: (dependents + 1) × (100 - coverage%)"
  IO.println "  Higher score = more critical to test"
  IO.println ""

  -- Build dependency graph
  let depGraph ← buildDepGraph ⟨"src/Lego"⟩

  -- Combine with coverage data
  let mut priorityList : List (String × Nat × Nat × Nat × Nat) := []  -- (file, tested, total, dependents, priority)
  for (file, tested, total) in result.byFile do
    let shortFile := file.splitOn "/" |>.getLast! |>.dropRight 5  -- remove .lean
    let deps := depGraph.find? (·.file == shortFile)
    let dependentCount := deps.map (·.dependents) |>.getD 0
    let coveragePct := if total > 0 then (tested * 100) / total else 100
    let priority := (dependentCount + 1) * (100 - coveragePct)
    priorityList := (shortFile, tested, total, dependentCount, priority) :: priorityList

  -- Sort by priority (highest first)
  let sorted := priorityList.toArray.qsort (fun a b => a.2.2.2.2 > b.2.2.2.2)

  IO.println "  File                    Coverage    Deps  Priority"
  IO.println "  ────────────────────────────────────────────────────"
  for (file, tested, total, deps, priority) in sorted do
    let pct := formatPercent tested total
    let paddedFile := file ++ String.mk (List.replicate (20 - min 20 file.length) ' ')
    let paddedPct := pct ++ String.mk (List.replicate (8 - min 8 pct.length) ' ')
    let priorityStr := if priority > 200 then s!"🔴 {priority}" else if priority > 100 then s!"🟡 {priority}" else s!"🟢 {priority}"
    IO.println s!"  {paddedFile} {tested}/{total} ({paddedPct})  {deps}     {priorityStr}"
  IO.println ""
  IO.println "  Legend: 🔴 High priority  🟡 Medium  🟢 Low"
  IO.println ""

/-! ## CLI -/

structure Config where
  showSummary : Bool := true
  showUntested : Bool := false
  showTested : Bool := false
  showByFile : Bool := false
  showDeps : Bool := false
  showHelp : Bool := false

def parseArgs (args : List String) : Config :=
  let rec go (cfg : Config) : List String → Config
    | [] => cfg
    | "--summary" :: rest => go { cfg with showSummary := true } rest
    | "--untested" :: rest => go { cfg with showUntested := true, showSummary := true } rest
    | "--tested" :: rest => go { cfg with showTested := true, showSummary := true } rest
    | "--by-file" :: rest => go { cfg with showByFile := true, showSummary := true } rest
    | "--deps" :: rest => go { cfg with showDeps := true, showSummary := true } rest
    | "--all" :: rest => go { cfg with showUntested := true, showTested := true, showByFile := true, showDeps := true, showSummary := true } rest
    | "--help" :: rest => go { cfg with showHelp := true } rest
    | "-h" :: rest => go { cfg with showHelp := true } rest
    | _ :: rest => go cfg rest
  go {} args

def showHelp : IO Unit := do
  IO.println "Usage: lake exe lego-coverage [options]"
  IO.println ""
  IO.println "Analyze test coverage for Lego source files."
  IO.println ""
  IO.println "Options:"
  IO.println "  --summary     Show only summary (default)"
  IO.println "  --untested    Show untested functions"
  IO.println "  --tested      Show tested functions"
  IO.println "  --by-file     Show coverage breakdown by file"
  IO.println "  --deps        Show dependency graph with test priority"
  IO.println "  --all         Show all information"
  IO.println "  --help, -h    Show this help"
  IO.println ""
  IO.println "Note: This is a heuristic analysis based on name matching."
  IO.println "A function is considered 'tested' if its name appears in test files."

def main (args : List String) : IO UInt32 := do
  let cfg := parseArgs args

  if cfg.showHelp then
    showHelp
    return 0

  -- Analyze src/Lego against test/lean
  let result ← analyzeCoverage [⟨"src/Lego"⟩] ⟨"test/lean"⟩

  if cfg.showSummary then
    printSummary result

  if cfg.showByFile then
    printByFile result

  if cfg.showDeps then
    printDepsGraph result

  if cfg.showUntested then
    printUntested result

  if cfg.showTested then
    printTested result

  -- Return non-zero if coverage is below threshold
  let coveragePct := (result.testedDefs * 100) / result.totalDefs
  if coveragePct < 20 then
    IO.println "⚠️  Coverage is below 20% threshold"
    return 1
  else
    return 0
