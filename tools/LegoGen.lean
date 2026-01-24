/-
  LegoGen: Code generation CLI

  Usage:
    lake exe lego-gen <Grammar.sexpr> --target=redtt
    lake exe lego-gen <Grammar.sexpr> --target=cooltt
    lake exe lego-gen <Grammar.sexpr> --target=lean
    lake exe lego-gen <Grammar.sexpr> --all
-/

import Cubical

open Cubical

def printUsage : IO Unit := do
  IO.println "Usage: lego-gen <Grammar.sexpr> [options]"
  IO.println ""
  IO.println "Options:"
  IO.println "  --target=redtt   Generate RedTT code (proofs)"
  IO.println "  --target=cooltt  Generate CoolTT code (proofs)"
  IO.println "  --target=lean    Generate Lean 4 code (execution)"
  IO.println "  --all            Generate all targets"
  IO.println "  --core           Output core type definitions"
  IO.println "  --module=NAME    Module name for Lean output (default: Generated)"
  IO.println ""
  IO.println "Examples:"
  IO.println "  lego-gen prelude/lego/Grammar.sexpr --target=redtt"
  IO.println "  lego-gen prelude/lego/Grammar.sexpr --all"

def parseTarget (s : String) : Option Target :=
  match s with
  | "redtt"  => some .redtt
  | "cooltt" => some .cooltt
  | "lean"   => some .lean
  | _ => none

structure Options where
  inputFile : Option String := none
  target    : Option Target := none
  all       : Bool := false
  core      : Bool := false
  moduleName : String := "Generated"
  deriving Repr

def parseArgs (args : List String) : Options :=
  args.foldl (fun opts arg =>
    if arg.startsWith "--target=" then
      let targetStr := arg.drop 9
      match parseTarget targetStr with
      | some t => { opts with target := some t }
      | none => opts
    else if arg == "--all" then
      { opts with all := true }
    else if arg == "--core" then
      { opts with core := true }
    else if arg.startsWith "--module=" then
      { opts with moduleName := arg.drop 9 }
    else if arg.startsWith "--" || arg.startsWith "-" then
      opts  -- ignore unknown flags
    else
      { opts with inputFile := some arg }
  ) {}

def main (args : List String) : IO UInt32 := do
  if args.isEmpty then
    printUsage
    return 0

  let opts := parseArgs args

  -- Handle --core flag (no input file needed)
  if opts.core then
    match opts.target with
    | some t =>
      IO.println (coreTypes t)
      return 0
    | none =>
      IO.println "-- RedTT Core Types"
      IO.println (coreTypes .redtt)
      IO.println "\n-- CoolTT Core Types"
      IO.println (coreTypes .cooltt)
      IO.println "\n-- Lean Core Implementation"
      IO.println (coreTypes .lean)
      return 0

  -- Need input file for generation
  match opts.inputFile with
  | none =>
    IO.eprintln "Error: No input file specified"
    printUsage
    return 1
  | some path =>
    let content ← IO.FS.readFile path

    if opts.all then
      -- Generate all targets
      match generateAll content opts.moduleName with
      | some (redtt, cooltt, lean) =>
        let basePath := path.dropRight 6  -- remove .sexpr
        IO.FS.writeFile (basePath ++ ".red") redtt
        IO.println s!"Generated {basePath}.red"
        IO.FS.writeFile (basePath ++ ".cooltt") cooltt
        IO.println s!"Generated {basePath}.cooltt"
        IO.FS.writeFile (basePath ++ ".lean") lean
        IO.println s!"Generated {basePath}.lean"
        return 0
      | none =>
        IO.eprintln s!"Error: Failed to parse {path}"
        return 1
    else
      -- Generate single target
      match opts.target with
      | none =>
        IO.eprintln "Error: No target specified. Use --target=redtt|cooltt|lean or --all"
        return 1
      | some target =>
        match generate content target opts.moduleName with
        | some output =>
          IO.println output
          return 0
        | none =>
          IO.eprintln s!"Error: Failed to generate code from {path}"
          return 1
