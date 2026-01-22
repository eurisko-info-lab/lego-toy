/-
  GeneratedPipeline: Convert generated/*.lego to .lean files

  Uses the proper Lego approach:
  1. Parse with Bootstrap grammar (via Runtime)
  2. Transform AST (rules → Lean functions)
  3. Print using Lean grammar
-/

import Lego.Runtime
import Lego.Loader

namespace GeneratedPipeline

open Lego

/-! ## Rule Extraction -/

/-- Extract rules from parsed AST -/
partial def extractRules (t : Term) : List Rule :=
  Loader.extractRules t

/-! ## Lean Code Generation -/

/-- Strip $ prefix from variable names -/
def stripDollar (s : String) : String :=
  if s.startsWith "$" then s.drop 1 else s

/-- Convert a Term pattern to Lean pattern syntax -/
partial def termToLeanPattern (t : Term) : String :=
  match t with
  | .var x => stripDollar x  -- Pattern variable becomes Lean variable
  | .lit s => s!"(Term.lit \"{s}\")"
  | .con name args =>
    if args.isEmpty then
      s!"(Term.con \"{name}\" [])"
    else
      let argStrs := args.map termToLeanPattern
      s!"(Term.con \"{name}\" [{", ".intercalate argStrs}])"

/-- Convert a Term template to Lean expression syntax -/
partial def termToLeanExpr (t : Term) : String :=
  match t with
  | .var x => stripDollar x  -- Variable reference
  | .lit s => s!"(Term.lit \"{s}\")"
  | .con name args =>
    if args.isEmpty then
      s!"(Term.con \"{name}\" [])"
    else
      let argStrs := args.map termToLeanExpr
      s!"(Term.con \"{name}\" [{", ".intercalate argStrs}])"

/-- Group rules by their function name (first constructor in pattern) -/
def groupRulesByFunction (rules : List Rule) : List (String × List Rule) :=
  let funcs := rules.filterMap fun r =>
    match r.pattern with
    | .con name _ => some name
    | _ => none
  let uniqueFuncs := funcs.eraseDups
  uniqueFuncs.map fun fn =>
    (fn, rules.filter fun r =>
      match r.pattern with
      | .con name _ => name == fn
      | _ => false)

/-- Determine the arity of a function from its rules -/
def functionArity (rules : List Rule) : Nat :=
  rules.foldl (fun acc r =>
    match r.pattern with
    | .con _ args => max acc args.length
    | _ => acc) 0

/-- Collect all variables in a pattern -/
partial def collectVars (t : Term) : List String :=
  match t with
  | .var x => [stripDollar x]
  | .lit _ => []
  | .con _ args => args.flatMap collectVars

/-- Make variable names unique by appending numbers to duplicates -/
def makeUnique (vars : List String) : List (String × String) :=
  -- First pass: count occurrences of each variable
  let counts := vars.foldl (fun (acc : List (String × Nat)) v =>
    match acc.find? (·.1 == v) with
    | some _ => acc.map fun (v', n) => if v' == v then (v', n + 1) else (v', n)
    | none => acc ++ [(v, 1)]
  ) []
  -- Second pass: assign unique names
  let (result, _) := vars.foldl (fun (acc : List (String × String) × List (String × Nat)) v =>
    let (result, seenCounts) := acc
    let totalCount := (counts.find? (·.1 == v)).map (·.2) |>.getD 1
    if totalCount == 1 then
      -- Unique variable - keep original name
      (result ++ [(v, v)], seenCounts)
    else
      -- Duplicate - need to number it
      let seenSoFar := (seenCounts.find? (·.1 == v)).map (·.2) |>.getD 0
      let newName := s!"{v}{seenSoFar + 1}"
      let newSeenCounts := if seenSoFar == 0
        then seenCounts ++ [(v, 1)]
        else seenCounts.map fun (v', n) => if v' == v then (v', n + 1) else (v', n)
      (result ++ [(v, newName)], newSeenCounts)
  ) ([], [])
  result

/-- Rename variables in a pattern (statefully consumes renames) -/
partial def renameVarsAux (renames : List (String × String)) (t : Term) : List (String × String) × Term :=
  match t with
  | .var x =>
    let x' := stripDollar x
    match renames.findIdx? (·.1 == x') with
    | some idx =>
      let (_, newName) := renames[idx]!
      -- Remove this rename so next occurrence uses next one
      let remaining := renames.eraseIdx idx
      (remaining, .var newName)
    | none => (renames, .var x')
  | .lit s => (renames, .lit s)
  | .con name args =>
    let (remaining, renamedArgs) := args.foldl (fun (acc : List (String × String) × List Term) arg =>
      let (rem, result) := acc
      let (newRem, renamedArg) := renameVarsAux rem arg
      (newRem, result ++ [renamedArg])
    ) (renames, [])
    (remaining, .con name renamedArgs)

def renameVars (renames : List (String × String)) (t : Term) : Term :=
  (renameVarsAux renames t).2

/-- Generate equality guards for duplicate variables -/
def generateGuards (renames : List (String × String)) : List String :=
  -- Group by original variable name
  let grouped := renames.foldl (fun (acc : List (String × List String)) (orig, renamed) =>
    match acc.find? (·.1 == orig) with
    | some _ => acc.map fun (o, ns) => if o == orig then (o, ns ++ [renamed]) else (o, ns)
    | none => acc ++ [(orig, [renamed])]
  ) []
  -- Generate equality checks for variables that appear multiple times
  grouped.filterMap fun (_, names) =>
    if names.length > 1 then
      -- Generate pairwise comparisons: r1 == r2, r2 == r3, etc
      let pairs := names.zip (names.drop 1)
      let eqs := pairs.map fun (a, b) => s!"{a} == {b}"
      some (" && ".intercalate eqs)
    else none

/-- Check if a term is all constructors (no variables) -/
partial def isSpecific (t : Term) : Bool :=
  match t with
  | .var _ => false
  | .lit _ => true
  | .con _ args => args.all isSpecific

/-- Calculate specificity score: higher = more specific -/
def patternSpecificity (args : List Term) : Nat :=
  args.foldl (fun acc t => if isSpecific t then acc + 10 else acc) 0

/-- Check if rule has duplicate variable constraints (will need guards) -/
def hasGuards (args : List Term) : Bool :=
  let vars := args.flatMap collectVars
  vars.length != vars.eraseDups.length

/-- Sort rules by specificity: specific patterns first, guarded patterns last -/
def sortRules (rules : List Rule) : List Rule :=
  rules.toArray.qsort (fun r1 r2 =>
    match r1.pattern, r2.pattern with
    | .con _ args1, .con _ args2 =>
      let spec1 := patternSpecificity args1
      let spec2 := patternSpecificity args2
      let guard1 := hasGuards args1
      let guard2 := hasGuards args2
      -- Guarded patterns go last
      if guard1 && !guard2 then false
      else if !guard1 && guard2 then true
      -- Then by specificity (higher first)
      else spec1 > spec2
    | _, _ => true
  ) |>.toList

/-- Collect all variables used in a template -/
partial def collectTemplateVars (t : Term) : List String :=
  match t with
  | .var x => [stripDollar x]
  | .lit _ => []
  | .con _ args => args.flatMap collectTemplateVars

/-- Check for unbound variables in template -/
def checkUnbound (patternVars : List String) (template : Term) : List String :=
  let templateVars := collectTemplateVars template
  templateVars.filter (fun v => !patternVars.contains v)

/-- Generate a case for a single rule -/
def generateCase (r : Rule) : Option String :=
  match r.pattern with
  | .con _ args =>
    if args.isEmpty then none  -- Skip rules with no pattern args
    else
      -- Collect and rename duplicate variables
      let vars := args.flatMap collectVars
      -- Check for unbound variables in template
      let unbound := checkUnbound vars r.template
      if !unbound.isEmpty then
        -- Report as comment since unbound vars are errors in source
        some s!"  -- SKIPPED {r.name}: unbound variables {unbound}"
      else
        let renames := makeUnique vars
        -- Rename all args together, threading state
        let (_, renamedArgs) := args.foldl (fun (acc : List (String × String) × List Term) arg =>
          let (rem, result) := acc
          let (newRem, renamed) := renameVarsAux rem arg
          (newRem, result ++ [renamed])
        ) (renames, [])
        let pats := renamedArgs.map termToLeanPattern
        let guards := generateGuards renames
        -- For template, map original names to first renamed name
        let firstNames := renames.foldl (fun (acc : List (String × String)) (orig, renamed) =>
          if acc.any (·.1 == orig) then acc else acc ++ [(orig, renamed)]
        ) []
        let renamedTemplate := renameVars firstNames r.template
        let body := termToLeanExpr renamedTemplate
        -- Multi-arg patterns are separated by commas in Lean
        let patStr := ", ".intercalate pats
        if guards.isEmpty then
          some s!"  | {patStr} => {body}"
        else
          let guardStr := " && ".intercalate guards
          some s!"  | {patStr} => if {guardStr} then {body} else Term.con \"error\" []"
  | _ => some s!"  | _ => sorry -- {r.name}"

/-- Check if a rule is a catch-all (all variables in pattern) -/
def isCatchAll (r : Rule) : Bool :=
  match r.pattern with
  | .con _ args => args.all (fun t => match t with | .var _ => true | _ => false)
  | _ => false

/-- Generate a Lean function from grouped rules -/
def generateFunction (funcName : String) (rules : List Rule) : String :=
  let arity := functionArity rules
  -- Sort rules: specific patterns first, guarded patterns last
  let sortedRules := sortRules rules
  let cases := sortedRules.filterMap generateCase
  if cases.isEmpty then
    s!"-- {funcName}: no valid cases"
  else
    -- Generate type signature based on arity
    let argTypes := List.replicate arity "Term"
    let typeStr := " → ".intercalate (argTypes ++ ["Term"])
    let header := s!"/-- {funcName} -/\ndef {funcName} : {typeStr}"
    -- Only add default case if no catch-all pattern exists
    let hasCatchAll := sortedRules.any isCatchAll
    if hasCatchAll then
      s!"{header}\n{"\n".intercalate cases}"
    else
      let defaultCase := if arity == 1 then "  | _ => Term.con \"error\" []"
                         else s!"  | {", ".intercalate (List.replicate arity "_")} => Term.con \"error\" []"
      s!"{header}\n{"\n".intercalate cases}\n{defaultCase}"

/-- Generate Lean module from rules -/
def generateLean (langName : String) (rules : List Rule) : String :=
  let header := s!"/-
  Lego.Cubical.{langName}: Generated from {langName}.lego

  DO NOT EDIT - regenerate with:
    lake exe generated-pipeline {langName}.lego
-/

import Lego.Algebra

set_option linter.unusedVariables false

namespace Lego.Cubical.{langName}

open Lego (Term)
"

  let grouped := groupRulesByFunction rules
  let functions := grouped.map fun (fn, rs) => generateFunction fn rs

  let footer := s!"
end Lego.Cubical.{langName}
"

  header ++ "\n".intercalate functions ++ footer

/-! ## Pipeline -/

/-- Process a .lego file -/
def processFile (rt : Runtime.Runtime) (path : String) : IO String := do
  let content ← IO.FS.readFile path
  match Runtime.parseLegoFileE rt content with
  | .error e => throw (IO.userError s!"Failed to parse {path}: {e}")
  | .ok ast =>
    let rules := extractRules ast
    let langName := path.splitOn "/" |>.getLast! |>.dropRight 5  -- remove .lego
    return generateLean langName rules

end GeneratedPipeline

/-! ## Main -/

def main (args : List String) : IO UInt32 := do
  -- Load Bootstrap grammar
  let rt ← Lego.Runtime.loadBootstrapOrError "./test/Bootstrap.lego"

  match args with
  | [] =>
    IO.println "Usage: generated-pipeline <file.lego> [output.lean]"
    IO.println "       generated-pipeline --all"
    return 1
  | ["--all"] =>
    let dir := "./src/Lego/Cubical/generated"
    let entries ← System.FilePath.readDir dir
    let legoFiles := entries.filter (·.fileName.endsWith ".lego")
    IO.FS.createDirAll "./src/Lego/Cubical/gen"
    for entry in legoFiles do
      let inPath := s!"{dir}/{entry.fileName}"
      let outName := entry.fileName.dropRight 5 ++ ".lean"
      let outPath := s!"./src/Lego/Cubical/gen/{outName}"
      IO.println s!"Processing {entry.fileName}..."
      try
        let result ← GeneratedPipeline.processFile rt inPath
        IO.FS.writeFile outPath result
        IO.println s!"  → {outPath}"
      catch e =>
        IO.println s!"  ERROR: {e}"
    return 0
  | [inPath] =>
    let result ← GeneratedPipeline.processFile rt inPath
    IO.println result
    return 0
  | [inPath, outPath] =>
    let result ← GeneratedPipeline.processFile rt inPath
    IO.FS.writeFile outPath result
    IO.println s!"Generated: {outPath}"
    return 0
  | _ =>
    IO.println "Too many arguments"
    return 1
