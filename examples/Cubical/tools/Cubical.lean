/-
  Cubical: Single Source of Truth Code Generation

  Architecture:
    Grammar.sexpr (source of truth)
         │
    ┌────┴────┬───────┐
    ▼         ▼       ▼
  .red     .cooltt  .lean
  (proof)  (proof)  (exec)

  This module provides the unified interface for generating
  code to multiple targets from a single grammar specification.
-/

import Cubical.SExpr
import Cubical.ToRedTT
import Cubical.ToCoolTT
import Cubical.ToLean

namespace Cubical

/-- Target language for code generation -/
inductive Target where
  | redtt   : Target  -- RedTT (proofs)
  | cooltt  : Target  -- CoolTT (proofs, better UX)
  | lean    : Target  -- Lean 4 (execution)
  deriving Repr, BEq

/-- Generate code for a specific target -/
def generate (content : String) (target : Target) (moduleName : String := "Generated") : Option String :=
  match target with
  | .redtt  => ToRedTT.generate content
  | .cooltt => ToCoolTT.generate content
  | .lean   => ToLean.generate content moduleName

/-- Generate code for all targets -/
def generateAll (content : String) (moduleName : String := "Generated")
    : Option (String × String × String) := do
  let redtt ← ToRedTT.generate content
  let cooltt ← ToCoolTT.generate content
  let lean ← ToLean.generate content moduleName
  some (redtt, cooltt, lean)

/-- Core type definitions for each target -/
def coreTypes (target : Target) : String :=
  match target with
  | .redtt  => ToRedTT.coreTypes
  | .cooltt => ToCoolTT.coreTypes
  | .lean   => ToLean.coreImpl

/-! ## Extract from Verified Code -/

/-- Extraction status -/
inductive ExtractionStatus where
  | notVerified : ExtractionStatus
  | verified    : ExtractionStatus
  | extracted   : ExtractionStatus
  deriving Repr, BEq

/-- Extract executable Lean code from verified RedTT/CoolTT -/
def extractFromVerified (_redttCode : String) : Option String :=
  -- TODO: Implement extraction after verification
  none

end Cubical
