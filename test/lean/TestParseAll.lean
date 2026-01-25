/-
  TestParseAll: Comprehensive file parsing test for all Lego language grammars
  
  Usage:
    lake exe lego-test-parse              # Test all file types
    lake exe lego-test-parse --lego       # Test only .lego files
    lake exe lego-test-parse --rosetta    # Test only .rosetta files
    lake exe lego-test-parse --lean       # Test only .lean files
    lake exe lego-test-parse --verbose    # Show all files (including passing)
    lake exe lego-test-parse --help       # Show usage
-/

import Lego

namespace TestParseAll

structure FailedFile where
  path : String
  reason : String
  deriving Repr

structure TestConfig where
  testLego : Bool := true
  testRosetta : Bool := true
  testLean : Bool := true
  verbose : Bool := false
  deriving Repr

def parseArgs (args : List String) : TestConfig :=
  let rec go (cfg : TestConfig) : List String → TestConfig
    | [] => cfg
    | "--lego" :: rest => go { cfg with testLego := true, testRosetta := false, testLean := false } rest
    | "--rosetta" :: rest => go { cfg with testLego := false, testRosetta := true, testLean := false } rest
    | "--lean" :: rest => go { cfg with testLego := false, testRosetta := false, testLean := true } rest
    | "--verbose" :: rest => go { cfg with verbose := true } rest
    | "-v" :: rest => go { cfg with verbose := true } rest
    | "--all" :: rest => go { cfg with testLego := true, testRosetta := true, testLean := true } rest
    | "--help" :: _ => { testLego := false, testRosetta := false, testLean := false }  -- Will trigger help
    | "-h" :: _ => { testLego := false, testRosetta := false, testLean := false }
    | _ :: rest => go cfg rest
  -- If any specific flag was given, start with all false
  let hasSpecific := args.any fun a => a == "--lego" || a == "--rosetta" || a == "--lean"
  let initial := if hasSpecific then { testLego := false, testRosetta := false, testLean := false } else {}
  go initial args

def showHelp : IO Unit := do
  IO.println "Usage: lake exe lego-test-parse [OPTIONS]"
  IO.println ""
  IO.println "Test parsing of all .lego, .rosetta, and .lean files in the workspace."
  IO.println ""
  IO.println "Options:"
  IO.println "  --lego       Test only .lego files"
  IO.println "  --rosetta    Test only .rosetta files"
  IO.println "  --lean       Test only .lean files"
  IO.println "  --all        Test all file types (default)"
  IO.println "  --verbose    Show all files including passing ones"
  IO.println "  -v           Same as --verbose"
  IO.println "  --help, -h   Show this help message"
  IO.println ""
  IO.println "Examples:"
  IO.println "  lake exe lego-test-parse              # Test all file types"
  IO.println "  lake exe lego-test-parse --lego       # Test only .lego files"
  IO.println "  lake exe lego-test-parse --lean -v    # Test .lean files with verbose output"

/-- Find files matching a pattern, excluding certain paths -/
def findFiles (pattern : String) (excludes : List String) : IO (List String) := do
  let baseArgs := #[".", "-name", pattern, "-type", "f"]
  let excludeArgs := excludes.foldl (fun acc ex => acc ++ #["!", "-path", ex]) #[]
  let result ← IO.Process.run { cmd := "find", args := baseArgs ++ excludeArgs }
  return result.splitOn "\n" |>.filter (·.length > 0)

/-- Test a single file with a parser function -/
def testFile (parser : String → IO (Except Lego.ParseError Lego.Term)) (path : String) : IO (Option FailedFile) := do
  match ← parser path with
  | .ok _ => return none
  | .error e => return some { path := path, reason := toString e }

/-- Run tests for a file type and return results -/
def testFileType (name : String) (files : List String) (parser : String → IO (Except Lego.ParseError Lego.Term)) 
    (verbose : Bool) : IO (Nat × Nat × Array FailedFile) := do
  if files.isEmpty then
    return (0, 0, #[])
  
  IO.println s!"Testing {files.length} .{name} files..."
  let mut failed : Array FailedFile := #[]
  let mut passed := 0
  
  for path in files do
    match ← testFile parser path with
    | none => 
      passed := passed + 1
      if verbose then IO.println s!"  ✓ {path}"
    | some f => 
      failed := failed.push f
      if verbose then IO.println s!"  ✗ {path}"
  
  return (passed, files.length, failed)

/-- Print failed files section -/
def printFailedFiles (fileType : String) (failed : Array FailedFile) : IO Unit := do
  if failed.size > 0 then
    IO.println ""
    IO.println "═══════════════════════════════════════════════════════════════"
    IO.println s!"FAILED .{fileType} FILES ({failed.size})"
    IO.println "═══════════════════════════════════════════════════════════════"
    for f in failed do
      IO.println s!"\n{f.path}"
      IO.println s!"  {f.reason}"

def main (args : List String) : IO UInt32 := do
  let cfg := parseArgs args
  
  -- Show help if requested or no tests selected
  if args.contains "--help" || args.contains "-h" then
    showHelp
    return 0
  
  if !cfg.testLego && !cfg.testRosetta && !cfg.testLean then
    showHelp
    return 0
  
  IO.println "═══════════════════════════════════════════════════════════════"
  IO.println "Lego File Parsing Test Suite"
  IO.println "═══════════════════════════════════════════════════════════════"
  IO.println ""
  
  -- Initialize runtime
  let rt ← Lego.Runtime.init
  IO.println ""
  
  -- Collect results
  let mut totalPassed := 0
  let mut totalFiles := 0
  let mut legoFailed : Array FailedFile := #[]
  let mut rosettaFailed : Array FailedFile := #[]
  let mut leanFailed : Array FailedFile := #[]
  let mut legoPassed := 0
  let mut legoTotal := 0
  let mut rosettaPassed := 0
  let mut rosettaTotal := 0
  let mut leanPassed := 0
  let mut leanTotal := 0
  
  -- Test .lego files
  if cfg.testLego then
    let legoFiles ← findFiles "*.lego" [
      "./tmp/*",
      "./test/lego/Bootstrap.lego",
      "./src/Lego/Lego.lego",
      "./src/Rosetta/Rosetta.lego",
      "./src/Rosetta/Lean.lego"
    ]
    let (p, t, f) ← testFileType "lego" legoFiles 
      (fun path => do
        let content ← IO.FS.readFile path
        return Lego.Runtime.parseLegoFileE rt content)
      cfg.verbose
    legoPassed := p
    legoTotal := t
    legoFailed := f
    totalPassed := totalPassed + p
    totalFiles := totalFiles + t
  
  -- Test .rosetta files
  if cfg.testRosetta then
    let rosettaFiles ← findFiles "*.rosetta" []
    let (p, t, f) ← testFileType "rosetta" rosettaFiles
      (fun path => do
        let content ← IO.FS.readFile path
        return Lego.Runtime.parseRosettaFileE rt content)
      cfg.verbose
    rosettaPassed := p
    rosettaTotal := t
    rosettaFailed := f
    totalPassed := totalPassed + p
    totalFiles := totalFiles + t
  
  -- Test .lean files
  if cfg.testLean then
    let leanFiles ← findFiles "*.lean" [
      "./.lake/*",
      "./tmp/*",
      "./.cache/*"
    ]
    let (p, t, f) ← testFileType "lean" leanFiles
      (fun path => do
        let content ← IO.FS.readFile path
        return Lego.Runtime.parseLeanFileE rt content)
      cfg.verbose
    leanPassed := p
    leanTotal := t
    leanFailed := f
    totalPassed := totalPassed + p
    totalFiles := totalFiles + t
  
  -- Print summary
  IO.println ""
  IO.println "═══════════════════════════════════════════════════════════════"
  IO.println "RESULTS"
  IO.println "═══════════════════════════════════════════════════════════════"
  IO.println ""
  
  if cfg.testLego then
    IO.println s!".lego files:    {legoPassed}/{legoTotal} passed"
  if cfg.testRosetta then
    IO.println s!".rosetta files: {rosettaPassed}/{rosettaTotal} passed"
  if cfg.testLean then
    IO.println s!".lean files:    {leanPassed}/{leanTotal} passed"
  
  IO.println ""
  IO.println s!"Total: {totalPassed}/{totalFiles} passed"
  
  -- Print failures
  if cfg.testLego then printFailedFiles "lego" legoFailed
  if cfg.testRosetta then printFailedFiles "rosetta" rosettaFailed
  if cfg.testLean then printFailedFiles "lean" leanFailed
  
  -- Return exit code
  let totalFailed := legoFailed.size + rosettaFailed.size + leanFailed.size
  if totalFailed > 0 then return 1 else return 0

end TestParseAll

def main (args : List String) : IO UInt32 := TestParseAll.main args
