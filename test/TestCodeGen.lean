/-
  TestCodeGen.lean: Quick test of CodeGen and UnifiedCodeGen modules
-/

import Rosetta.CodeGen
import Rosetta.UnifiedCodeGen

open CodeGen
open UnifiedCodeGen

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

-- Test UnifiedCodeGen with sample Terms
open Lego (Term)

def testRewriteRule : IO Unit := do
  -- Simple rule: (Add (Zero) $n) ~> $n
  let lhs := Term.con "Add" [Term.con "Zero" [], Term.var "$n"]
  let rhs := Term.var "$n"

  let frag := emitLeanRewriteRule "addZeroLeft" lhs rhs
  let code := render frag

  if !code.containsSubstr "def addZeroLeft" then
    IO.eprintln s!"FAIL: emitLeanRewriteRule: missing 'def addZeroLeft'"
    IO.eprintln s!"Got:\n{code}"
  else if !code.containsSubstr "Option Term" then
    IO.eprintln s!"FAIL: emitLeanRewriteRule: missing 'Option Term'"
    IO.eprintln s!"Got:\n{code}"
  else
    IO.println "✓ emitLeanRewriteRule"
    IO.println "  Generated:"
    for line in code.splitOn "\n" do
      IO.println s!"    {line}"

def testInductive : IO Unit := do
  let ctors := [
    ("Zero", []),
    ("Succ", ["Nat"])
  ]
  let frag := emitLeanInductive "Nat" ctors
  let code := render frag

  if !code.containsSubstr "inductive Nat where" then
    IO.eprintln s!"FAIL: emitLeanInductive: missing 'inductive Nat where'"
    IO.eprintln s!"Got:\n{code}"
  else
    IO.println "✓ emitLeanInductive"
    IO.println "  Generated:"
    for line in code.splitOn "\n" do
      IO.println s!"    {line}"

def testScalaADT : IO Unit := do
  let ctors := [
    ("Zero", []),
    ("Succ", ["Nat"])
  ]
  let frag := emitScalaADT "Nat" ctors
  let code := render frag

  if !code.containsSubstr "sealed trait Nat" then
    IO.eprintln s!"FAIL: emitScalaADT: missing 'sealed trait Nat'"
    IO.eprintln s!"Got:\n{code}"
  else
    IO.println "✓ emitScalaADT"
    IO.println "  Generated:"
    for line in code.splitOn "\n" do
      IO.println s!"    {line}"

def testHaskellADT : IO Unit := do
  let ctors := [
    ("Zero", []),
    ("Succ", ["Nat"])
  ]
  let frag := emitHaskellADT "Nat" ctors
  let code := render frag

  if !code.containsSubstr "data Nat" then
    IO.eprintln s!"FAIL: emitHaskellADT: missing 'data Nat'"
    IO.eprintln s!"Got:\n{code}"
  else
    IO.println "✓ emitHaskellADT"
    IO.println "  Generated:"
    for line in code.splitOn "\n" do
      IO.println s!"    {line}"

def testRustADT : IO Unit := do
  let ctors := [
    ("Zero", []),
    ("Succ", ["Nat"])
  ]
  let frag := emitRustADT "Nat" ctors
  let code := render frag

  if !code.containsSubstr "pub enum Nat" then
    IO.eprintln s!"FAIL: emitRustADT: missing 'pub enum Nat'"
    IO.eprintln s!"Got:\n{code}"
  else
    IO.println "✓ emitRustADT"
    IO.println "  Generated:"
    for line in code.splitOn "\n" do
      IO.println s!"    {line}"

def main : IO Unit := do
  IO.println "=== CodeGen Module Tests ==="
  IO.println ""

  IO.println "--- Basic Frag Rendering ---"
  testRawFrag
  testSeqFrag
  testLineFrag
  testSepFrag

  IO.println ""
  IO.println "--- UnifiedCodeGen Emitters ---"
  testRewriteRule
  IO.println ""
  testInductive
  IO.println ""
  testScalaADT
  IO.println ""
  testHaskellADT
  IO.println ""
  testRustADT

  IO.println ""
  IO.println "=== Tests Complete ==="
