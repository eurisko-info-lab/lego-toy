/-
  TestLoader: Tests for grammar loading and parsing utilities

  Tests the third most depended-on module (3 dependents):
  - splitByPipe/splitBySlash: Grammar expression splitting
  - extractParentNames: Language inheritance
  - flattenSeq: AST normalization
  - extractProdName: Production name extraction
  - parseWithGrammar: Grammar-driven parsing
  - extractRule/extractTestCase: Rule and test extraction

  Run with: lake exe lego-test-loader
-/

import Lego.Loader
import TestUtils

open Lego
open Lego.Test
open Lego.Loader

/-! ## Test Helpers -/

def term (s : String) : Term := Term.var s
def lit (s : String) : Term := Term.lit s
def con (name : String) (args : List Term) : Term := Term.con name args

/-! ## splitByPipe Tests -/

def splitByPipeTests : List TestResult :=
  -- Empty list
  let r1 := splitByPipe []
  
  -- Single term (no pipe)
  let r2 := splitByPipe [term "a"]
  
  -- Two alternatives
  let r3 := splitByPipe [term "a", lit "|", term "b"]
  
  -- Three alternatives  
  let r4 := splitByPipe [term "a", lit "|", term "b", lit "|", term "c"]
  
  -- Multiple terms in one alternative (becomes seq)
  let r5 := splitByPipe [term "a", term "b", lit "|", term "c"]
  
  [
    assertEq "empty list" r1 [],
    assertEq "single term" r2 [term "a"],
    assertEq "two alternatives" r3.length 2,
    assertTrue "first alt is a" (r3.head? == some (term "a")),
    assertEq "three alternatives" r4.length 3,
    assertEq "sequence in alt" r5.length 2,
    assertTrue "first alt is seq" (match r5.head? with | some (.con "seq" _) => true | _ => false)
  ]

/-! ## splitBySlash Tests -/

def splitBySlashTests : List TestResult :=
  -- Empty list
  let r1 := splitBySlash []
  
  -- Single term (no slash)
  let r2 := splitBySlash [term "a"]
  
  -- Two alternatives (PEG ordered)
  let r3 := splitBySlash [term "a", lit "/", term "b"]
  
  -- Mixed with sequence
  let r4 := splitBySlash [term "a", term "b", lit "/", term "c"]
  
  [
    assertEq "empty list" r1 [],
    assertEq "single term" r2 [term "a"],
    assertEq "two alternatives" r3.length 2,
    assertTrue "first is a" (r3.head? == some (term "a")),
    assertEq "sequence in PEG alt" r4.length 2
  ]

/-! ## flattenSeq Tests -/

def flattenSeqTests : List TestResult :=
  -- Non-seq term
  let r1 := flattenSeq (term "a")
  
  -- Simple seq
  let r2 := flattenSeq (con "seq" [term "a", term "b"])
  
  -- Nested seq (left-nested)
  let r3 := flattenSeq (con "seq" [con "seq" [term "a", term "b"], term "c"])
  
  -- Nested seq (right-nested)  
  let r4 := flattenSeq (con "seq" [term "a", con "seq" [term "b", term "c"]])
  
  -- Other constructor not flattened
  let r5 := flattenSeq (con "other" [term "a", term "b"])
  
  [
    assertEq "non-seq unchanged" r1 [term "a"],
    assertEq "simple seq" r2.length 2,
    assertEq "left-nested seq" r3.length 3,
    assertEq "right-nested seq" r4.length 3,
    assertEq "other con not flattened" r5.length 1
  ]

/-! ## extractParentNames Tests -/

def extractParentNamesTests : List TestResult :=
  -- No imports
  let noImports := con "DLang" [lit "lang", con "ident" [term "MyLang"], lit ":=", term "body"]
  let r1 := extractParentNames noImports
  
  -- With imports
  let withImports := con "DLang" [
    lit "lang",
    con "ident" [term "MyLang"],
    con "DImports" [con "ident" [term "Parent1"], con "ident" [term "Parent2"]],
    lit ":=",
    term "body"
  ]
  let r2 := extractParentNames withImports
  
  -- Single import
  let singleImport := con "DLang" [
    lit "lang",
    con "ident" [term "Child"],
    con "DImports" [con "ident" [term "Base"]],
    lit ":=",
    term "body"
  ]
  let r3 := extractParentNames singleImport
  
  [
    assertEq "no imports" r1 [],
    assertEq "two parents" r2.length 2,
    assertTrue "has Parent1" (r2.contains "Parent1"),
    assertTrue "has Parent2" (r2.contains "Parent2"),
    assertEq "single parent" r3 ["Base"]
  ]

/-! ## extractProdName Tests -/

def extractProdNameTests : List TestResult :=
  -- Valid production - direct children, not wrapped in seq
  let valid := con "DGrammar" [con "ident" [term "expr"], lit "::=", term "body", lit ";"]
  let r1 := extractProdName "Piece" valid
  
  -- Another valid
  let valid2 := con "DGrammar" [con "ident" [term "term"], lit "::=", term "body", lit ";"]
  let r2 := extractProdName "Core" valid2
  
  -- Invalid (no ident)
  let invalid := con "DGrammar" [lit "something"]
  let r3 := extractProdName "Piece" invalid
  
  [
    assertSome "valid prod name" r1,
    assertTrue "qualified name" (r1 == some "Piece.expr"),
    assertTrue "another qualified" (r2 == some "Core.term"),
    assertNone "invalid returns none" r3
  ]

/-! ## extractAnnotationFromFlat Tests -/

def extractAnnotationTests : List TestResult :=
  -- With annotation
  let withAnno := [term "a", term "b", lit "→", con "ident" [term "MyNode"]]
  let r1 := extractAnnotationFromFlat withAnno
  
  -- Without annotation
  let noAnno := [term "a", term "b", term "c"]
  let r2 := extractAnnotationFromFlat noAnno
  
  -- Just arrow without ident
  let partialArg := [term "a", lit "→"]
  let r3 := extractAnnotationFromFlat partialArg
  
  [
    assertSome "has annotation" r1,
    assertTrue "extracted name" (r1.map (·.1) == some "MyNode"),
    assertNone "no annotation" r2,
    assertNone "partial fails" r3
  ]

/-! ## stripQuotes Tests -/

def stripQuotesTests : List TestResult :=
  let r1 := stripQuotes "\"hello\""
  let r2 := stripQuotes "noquotes"
  let r3 := stripQuotes "\"\""
  -- Note: stripQuotes only handles double quotes, not single quotes
  
  [
    assertEq "double quotes" r1 "hello",
    assertEq "no quotes unchanged" r2 "noquotes",
    assertEq "empty quotes" r3 ""
  ]

/-! ## isKeywordLike Tests -/

def isKeywordLikeTests : List TestResult := [
  assertTrue "keyword if" (isKeywordLike "if"),
  assertTrue "keyword then" (isKeywordLike "then"),
  assertTrue "keyword let" (isKeywordLike "let"),
  assertFalse "not keyword 123" (isKeywordLike "123"),
  assertFalse "not keyword =>" (isKeywordLike "=>"),
  assertFalse "operator +" (isKeywordLike "+")
]

/-! ## Test Runner -/

def main : IO UInt32 := do
  let groups := [
    ("splitByPipe", splitByPipeTests),
    ("splitBySlash", splitBySlashTests),
    ("flattenSeq", flattenSeqTests),
    ("extractParentNames", extractParentNamesTests),
    ("extractProdName", extractProdNameTests),
    ("extractAnnotationFromFlat", extractAnnotationTests),
    ("stripQuotes", stripQuotesTests),
    ("isKeywordLike", isKeywordLikeTests)
  ]

  runAllTests "Loader Module Tests (3 Dependents)" groups
