import Lego.Bootstrap
import Lego.Algebra

def main : IO Unit := do
  for t in ["let x := 1 in x"] do
    IO.println s!"\n{t}"
    let toks := Lego.Bootstrap.tokenize t
    for tok in toks do
      IO.println s!"  {repr tok}"

#eval main
