/-
  Lego.Normalize: Shared normalization config/result types
-/

import Lego.Algebra

namespace Lego

/-- Configuration for normalization -/
structure NormalizeConfig where
  /-- Maximum reduction steps (fuel) -/
  maxSteps : Nat := 1000
  /-- Whether to enable built-in operations (subst, etc.) -/
  enableBuiltins : Bool := true
  deriving Inhabited

/-- Result of normalization with optional trace -/
structure NormalizeResult where
  /-- The normalized term -/
  term : Term
  /-- Trace of (ruleName, intermediate term) pairs if tracing enabled -/
  trace : List (String × Term) := []
  deriving Inhabited

end Lego
