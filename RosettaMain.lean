/-
  Rosetta CLI: Generate Lean code from .lego files
-/

import Rosetta.Rosetta

open Rosetta

def main (args : List String) : IO UInt32 := do
  match args with
  | [legoFile, outDir] =>
    let success ← generatePieceFiles legoFile outDir
    return if success then 0 else 1
  | [legoFile] =>
    match ← generateFromFile legoFile with
    | some code =>
      IO.println code
      return 0
    | none =>
      return 1
  | _ =>
    IO.eprintln "Usage: rosetta <file.lego> [outDir]"
    IO.eprintln ""
    IO.eprintln "Examples:"
    IO.eprintln "  rosetta src/Lego/Cubical/Red.lego generated/Red"
    IO.eprintln "  rosetta src/Lego/Cubical/Cool.lego generated/Cool"
    return 1
