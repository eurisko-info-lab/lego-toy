/-
  Lego.Util: Shared utility helpers

  Small, dependency-free helpers used across multiple modules to
  reduce duplication.
-/

namespace Lego.Util

/-- Helper: map with index -/
def mapWithIndex {α β : Type} (f : Nat → α → β) (xs : List α) : List β :=
  let rec go (i : Nat) : List α → List β
    | [] => []
    | x :: xs => f i x :: go (i + 1) xs
  go 0 xs

/-- Enumerate a list with indices: [(0, x0), (1, x1), ...] -/
def enumerate {α : Type} (xs : List α) : List (Nat × α) :=
  mapWithIndex (fun i x => (i, x)) xs

/-- Zip a list with indices: [(x0, 0), (x1, 1), ...] -/
def zipWithIndex {α : Type} (xs : List α) : List (α × Nat) :=
  mapWithIndex (fun i x => (x, i)) xs

/-- Check if a character is alphabetic or underscore -/
def isAlphaLike (c : Char) : Bool :=
  c.isAlpha || c == '_'

/-- Check if a string looks like a keyword (all alphabetic or underscore) -/
def isKeywordLike (s : String) : Bool :=
  !s.isEmpty && s.all isAlphaLike

/-- Check if a string looks like a keyword (alphabetic/underscore/dash) -/
def isKeywordLikeWithDash (s : String) : Bool :=
  !s.isEmpty && s.all (fun c => isAlphaLike c || c == '-')

end Lego.Util
