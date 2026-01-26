/-
  TestCodeGen.lean: Test CodeGen.Frag rendering
-/

import Rosetta.CodeGen

open CodeGen

/-- Check if a string contains a substring -/
def String.containsSubstr (s : String) (sub : String) : Bool :=
  (s.splitOn sub).length > 1

-- Test basic Frag rendering
def testRawFrag : IO Unit := do
  let f := Frag.Raw "hello world"
  let s := render f
  if s != "hello world" then
    IO.eprintln s!"FAIL: Raw render: expected 'hello world', got '{s}'"
  else
    IO.println "✓ Raw render"

def testSeqFrag : IO Unit := do
  let f := Frag.FSeq [.Raw "def ", .Ident "foo", .Raw " : ", .Ident "Nat"]
  let s := render f
  if s != "def foo : Nat" then
    IO.eprintln s!"FAIL: Seq render: expected 'def foo : Nat', got '{s}'"
  else
    IO.println "✓ Seq render"

def testLineFrag : IO Unit := do
  let f := Frag.Lines [.Line (.Raw "line1"), .Line (.Raw "line2")]
  let s := render f
  if !s.containsSubstr "line1" || !s.containsSubstr "line2" then
    IO.eprintln s!"FAIL: Lines render: got '{s}'"
  else
    IO.println "✓ Lines render"

def testSepFrag : IO Unit := do
  let f := Frag.Sep ", " [.Raw "a", .Raw "b", .Raw "c"]
  let s := render f
  if s != "a, b, c" then
    IO.eprintln s!"FAIL: Sep render: expected 'a, b, c', got '{s}'"
  else
    IO.println "✓ Sep render"

def testIndentFrag : IO Unit := do
  let inner := Frag.Lines [.Line (.Raw "inner1"), .Line (.Raw "inner2")]
  let f := Frag.Indent inner
  let s := render f
  if !s.containsSubstr "  inner1" || !s.containsSubstr "  inner2" then
    IO.eprintln s!"FAIL: Indent render: got '{s}'"
  else
    IO.println "✓ Indent render"

def testNestedIndent : IO Unit := do
  let level2 := Frag.Indent (.Line (.Raw "deep"))
  let level1 := Frag.Indent (.Lines [.Line (.Raw "outer"), level2])
  let s := render level1
  if !s.containsSubstr "    deep" then
    IO.eprintln s!"FAIL: Nested indent render: got '{s}'"
  else
    IO.println "✓ Nested indent render"

def main : IO Unit := do
  IO.println "=== CodeGen.Frag Rendering Tests ==="
  IO.println ""

  IO.println "--- Basic Frag Rendering ---"
  testRawFrag
  testSeqFrag
  testLineFrag
  testSepFrag
  testIndentFrag
  testNestedIndent

  IO.println ""
  IO.println "=== Tests Complete ==="
