/-
  TestBootstrapUnit: Tests for Bootstrap seed grammar utilities

  Tests the bootstrap seed module (2 dependents):
  - metaGrammar/metaInterp
  - tokenizeBootstrap
  - parseLegoFile (bootstrap-only parsing)

  Run with: lake exe lego-test-bootstrap
-/

import Lego.Bootstrap
import TestUtils

open Lego
open Lego.Test

/-! ## Pure Tests -/

def bootstrapPureTests : List TestResult :=
  let tokens := Lego.Bootstrap.tokenizeBootstrap "lang X := token T ";
  [
    assertEq "meta grammar name" Lego.Bootstrap.metaGrammar.name "Meta",
    assertNotEmpty "allPieces non-empty" Lego.Bootstrap.allPieces,
    assertNotEmpty "tokenizeBootstrap non-empty" tokens
  ]

/-! ## Test Runner (includes IO-derived tests) -/

def main : IO UInt32 := do
  let content ← IO.FS.readFile "test/lego/Bootstrap.lego"
  let parsed := Lego.Bootstrap.parseLegoFile content
  let ioTests : List TestResult := [
    assertSome "parseLegoFile Bootstrap.lego" parsed
  ]

  let groups := [
    ("bootstrap pure", bootstrapPureTests),
    ("bootstrap io", ioTests)
  ]

  runAllTests "Bootstrap Module Tests (2 Dependents)" groups
