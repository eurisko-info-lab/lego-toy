import Lego.Runtime
import Lego.Loader
import GrammarDrivenPipeline

/-!
# Grammar-Driven Pipeline Test

Test the GrammarDrivenPipeline with print rules.
-/

open Lego.Runtime
open Lego.Loader
open Lego

def testMain : IO Unit := do
  IO.println "=== Grammar-Driven Pipeline Test ==="
  IO.println ""

  -- Initialize runtime
  IO.println "1. Initializing runtime..."
  let rt ← Lego.Runtime.init

  -- Test parsing the source
  IO.println "2. Parsing test source..."
  match ← parseLegoFilePathE rt "./test/MinimalBootstrap.lego" with
  | .error e => IO.println s!"Parse error: {e}"
  | .ok ast =>
    IO.println s!"   Parsed AST: {ast.toString.take 200}..."
    IO.println ""

    -- Test running for Lean target
    IO.println "3. Testing Lean target..."
    match ← runForTarget rt ast .Lean "./generated" with
    | .error e => IO.println s!"   Error: {e}"
    | .ok result =>
      IO.println s!"   Output path: {result.outPath}"
      IO.println s!"   Generated code ({result.code.length} chars):"
      IO.println "   ---"
      IO.println (result.code.take 500)
      IO.println "   ---"

    IO.println ""
    IO.println "Done!"
