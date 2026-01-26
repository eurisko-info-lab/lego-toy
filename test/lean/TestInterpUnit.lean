/-
  TestInterp: Tests for grammar interpretation and parsing utilities

  Tests the second highest priority module (4 dependents):
  - computeLineCol: Source location tracking
  - findCharOffsetByTokenCount: Token position mapping
  - skipWhitespaceBytes: Whitespace handling
  - extractCharLit: Character literal parsing
  - ParseError: Error handling and formatting
  - furthestError: Error prioritization

  Run with: lake exe lego-test-interp
-/

import Lego.Interp
import TestUtils

open Lego
open Lego.Test

/-! ## computeLineCol Tests -/

def computeLineColTests : List TestResult :=
  -- Single line, beginning
  let r1 := computeLineCol "hello world" 0

  -- Single line, middle
  let r2 := computeLineCol "hello world" 6

  -- Multiple lines, first line
  let r3 := computeLineCol "line1\nline2\nline3" 3

  -- Multiple lines, second line start
  let r4 := computeLineCol "line1\nline2\nline3" 6

  -- Multiple lines, third line
  let r5 := computeLineCol "line1\nline2\nline3" 12

  -- Empty string
  let r6 := computeLineCol "" 0

  [
    assertEq "first char line" r1.line 1,
    assertEq "first char col" r1.column 1,
    assertEq "middle of line" r2.column 7,
    assertEq "still line 1" r3.line 1,
    assertEq "line 2 start" r4.line 2,
    assertEq "line 2 col" r4.column 1,
    assertEq "line 3" r5.line 3,
    assertEq "empty string" r6.line 1
  ]

/-! ## skipWhitespaceBytes Tests -/

def skipWhitespaceBytesTests : List TestResult :=
  -- No whitespace
  let bytes1 := "hello".toUTF8
  let r1 := skipWhitespaceBytes bytes1 0

  -- Leading spaces
  let bytes2 := "   hello".toUTF8
  let r2 := skipWhitespaceBytes bytes2 0

  -- Tabs and newlines
  let bytes3 := "\t\n  hello".toUTF8
  let r3 := skipWhitespaceBytes bytes3 0

  -- From middle position
  let bytes4 := "ab  cd".toUTF8
  let r4 := skipWhitespaceBytes bytes4 2

  -- All whitespace
  let bytes5 := "   ".toUTF8
  let r5 := skipWhitespaceBytes bytes5 0

  -- Empty
  let bytes6 := "".toUTF8
  let r6 := skipWhitespaceBytes bytes6 0

  [
    assertEq "no ws start" r1 0,
    assertEq "skip spaces" r2 3,
    assertEq "skip tabs/newlines" r3 4,
    assertEq "from middle" r4 4,
    assertEq "all whitespace" r5 3,
    assertEq "empty" r6 0
  ]

/-! ## extractCharLit Tests -/

def extractCharLitTests : List TestResult :=
  let r1 := extractCharLit "'a'"
  let r2 := extractCharLit "'Z'"
  let r3 := extractCharLit "'1'"
  let r4 := extractCharLit "'+'"
  let r5 := extractCharLit "'ab'"  -- Too long
  let r6 := extractCharLit "a"     -- No quotes
  let r7 := extractCharLit "''"    -- Empty

  [
    assertSome "lowercase a" r1,
    assertTrue "is a" (r1 == some 'a'),
    assertSome "uppercase Z" r2,
    assertTrue "is Z" (r2 == some 'Z'),
    assertSome "digit 1" r3,
    assertTrue "is 1" (r3 == some '1'),
    assertSome "symbol +" r4,
    assertTrue "is +" (r4 == some '+'),
    assertNone "too long" r5,
    assertNone "no quotes" r6,
    assertNone "empty char" r7
  ]

/-! ## furthestError Tests -/

def furthestErrorTests : List TestResult :=
  let e1 : ParseError := {
    message := "error at position 5"
    tokenPos := 5
    production := "expr"
    expected := ["number"]
    actual := some (Token.ident "x")
    remaining := []
  }
  let e2 : ParseError := {
    message := "error at position 10"
    tokenPos := 10
    production := "term"
    expected := ["operator"]
    actual := some (Token.sym ")")
    remaining := []
  }
  let e3 : ParseError := {
    message := "error at position 5 (same)"
    tokenPos := 5
    production := "factor"
    expected := ["("]
    actual := some (Token.sym ";")
    remaining := []
  }

  let r1 := furthestError e1 e2
  let r2 := furthestError e2 e1
  let r3 := furthestError e1 e3

  [
    assertEq "e2 is further" r1.tokenPos 10,
    assertEq "still e2 further" r2.tokenPos 10,
    assertEq "equal pos, first wins" r3.tokenPos 5,
    assertTrue "first wins msg" (r3.message == "error at position 5")
  ]

/-! ## findCharOffsetByTokenCount Tests -/

def findCharOffsetTests : List TestResult :=
  -- Simple tokens
  let r1 := findCharOffsetByTokenCount "foo bar baz" 0
  let r2 := findCharOffsetByTokenCount "foo bar baz" 1
  let r3 := findCharOffsetByTokenCount "foo bar baz" 2

  -- Multiple spaces (token 1 found after first token boundary)
  let r4 := findCharOffsetByTokenCount "a   b   c" 1

  -- Empty string
  let r5 := findCharOffsetByTokenCount "" 0

  -- Past end
  let r6 := findCharOffsetByTokenCount "one two" 5

  [
    assertEq "token 0" r1 0,
    assertGe "token 1 after foo" r2 3,
    assertGe "token 2 after bar" r3 7,
    assertEq "skip multiple spaces" r4 2,
    assertEq "empty string" r5 0,
    assertGe "past end returns end" r6 7
  ]

/-! ## ParseLoc Tests -/

def parseLocTests : List TestResult :=
  let loc1 := ParseLoc.mk 1 1
  let loc2 := ParseLoc.mk 10 25
  let loc3 := ParseLoc.mk 1 1

  [
    assertEq "line 1" loc1.line 1,
    assertEq "column 1" loc1.column 1,
    assertEq "toString 1:1" (toString loc1) "1:1",
    assertEq "toString 10:25" (toString loc2) "10:25",
    assertTrue "equality" (loc1 == loc3),
    assertFalse "inequality" (loc1 == loc2)
  ]

/-! ## ParseError Formatting Tests -/

def parseErrorTests : List TestResult :=
  let err1 : ParseError := {
    message := "unexpected token"
    tokenPos := 5
    loc := some { line := 2, column := 10 }
    production := "expression"
    expected := ["number", "identifier"]
    actual := some (Token.sym "+")
    remaining := []
  }

  let errNoLoc : ParseError := {
    message := "syntax error"
    tokenPos := 0
    loc := none
    production := "statement"
    expected := ["let"]
    actual := some (Token.ident "if")
    remaining := []
  }

  let formatted1 := toString err1
  let formatted2 := toString errNoLoc

  [
    assertTrue "contains line:col" (formatted1.containsSubstr "2:10"),
    assertTrue "contains production" (formatted1.containsSubstr "expression"),
    assertTrue "contains expected" (formatted1.containsSubstr "number"),
    assertTrue "no loc uses tokenPos" (formatted2.containsSubstr "statement")
  ]

/-! ## Test Runner -/

def main : IO UInt32 := do
  let groups := [
    ("computeLineCol", computeLineColTests),
    ("skipWhitespaceBytes", skipWhitespaceBytesTests),
    ("extractCharLit", extractCharLitTests),
    ("furthestError", furthestErrorTests),
    ("findCharOffsetByTokenCount", findCharOffsetTests),
    ("ParseLoc", parseLocTests),
    ("ParseError formatting", parseErrorTests)
  ]

  runAllTests "Interp Module Tests (4 Dependents)" groups
