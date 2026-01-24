/-
  Lego.Cubical.Cofibration: Generated from Cofibration.lego

  DO NOT EDIT - regenerate with:
    lake exe generated-pipeline Cofibration.lego
-/

import Lego.Algebra

set_option linter.unusedVariables false

namespace Lego.Cubical.Cofibration

open Lego (Term)
/-- isDim0 -/
def isDim0 : Term → Term
  | (Term.con "dim1" []) => (Term.con "false" [])
  | (Term.con "dim0" []) => (Term.con "true" [])
  | (Term.con "dimVar" [n]) => (Term.con "false" [])
  | _ => Term.con "error" []
/-- isDim1 -/
def isDim1 : Term → Term
  | (Term.con "dim1" []) => (Term.con "true" [])
  | (Term.con "dim0" []) => (Term.con "false" [])
  | (Term.con "dimVar" [n]) => (Term.con "false" [])
  | _ => Term.con "error" []
/-- dimEq -/
def dimEq : Term → Term → Term
  | (Term.con "dim1" []), (Term.con "dim1" []) => (Term.con "true" [])
  | (Term.con "dim0" []), (Term.con "dim0" []) => (Term.con "true" [])
  | (Term.con "dimVar" [n]), (Term.con "dimVar" [m]) => (Term.con "eq" [n, m])
  | _, _ => Term.con "error" []
-- top: no valid cases
-- bot: no valid cases
/-- cofEq -/
def cofEq : Term → Term → Term
  | (Term.con "dim1" []), (Term.con "dim0" []) => (Term.con "cof_bot" [])
  | (Term.con "dim0" []), (Term.con "dim1" []) => (Term.con "cof_bot" [])
  | r1, r2 => if r1 == r2 then (Term.con "cof_top" []) else Term.con "error" []
/-- cofLe -/
def cofLe : Term → Term → Term
  | r, s => (Term.con "cof_or" [(Term.con "cof_eq" [r, (Term.con "dim0" [])]), (Term.con "cof_eq" [s, (Term.con "dim1" [])])])
/-- boundary -/
def boundary : Term → Term
  | r => (Term.con "cof_or" [(Term.con "cof_eq" [r, (Term.con "dim0" [])]), (Term.con "cof_eq" [r, (Term.con "dim1" [])])])
/-- cof_and -/
def cof_and : Term → Term → Term
  | (Term.con "cof_bot" []), φ => (Term.con "cof_bot" [])
  | (Term.con "cof_top" []), φ => φ
  | φ, (Term.con "cof_top" []) => φ
  | φ, (Term.con "cof_bot" []) => (Term.con "cof_bot" [])
  | φ1, φ2 => if φ1 == φ2 then φ1 else Term.con "error" []
/-- cof_or -/
def cof_or : Term → Term → Term
  | (Term.con "cof_top" []), φ => (Term.con "cof_top" [])
  | (Term.con "cof_bot" []), φ => φ
  | φ, (Term.con "cof_bot" []) => φ
  | φ, (Term.con "cof_top" []) => (Term.con "cof_top" [])
  | φ1, φ2 => if φ1 == φ2 then φ1 else Term.con "error" []
/-- normCof -/
def normCof : Term → Term
  | (Term.con "cof_bot" []) => (Term.con "cof_bot" [])
  | (Term.con "cof_top" []) => (Term.con "cof_top" [])
  | (Term.con "cof_or" [φ, ψ]) => (Term.con "cof_or" [(Term.con "normCof" [φ]), (Term.con "normCof" [ψ])])
  | (Term.con "cof_eq" [r, s]) => (Term.con "cofEq" [r, s])
  | (Term.con "cof_and" [φ, ψ]) => (Term.con "cof_and" [(Term.con "normCof" [φ]), (Term.con "normCof" [ψ])])
  | _ => Term.con "error" []
/-- cofTrue -/
def cofTrue : Term → Term
  | (Term.con "cof_bot" []) => (Term.con "false" [])
  | (Term.con "cof_top" []) => (Term.con "true" [])
  | (Term.con "cof_or" [φ, ψ]) => (Term.con "or" [(Term.con "cofTrue" [φ]), (Term.con "cofTrue" [ψ])])
  | (Term.con "cof_eq" [r, s]) => (Term.con "dimEq" [r, s])
  | (Term.con "cof_and" [φ, ψ]) => (Term.con "and" [(Term.con "cofTrue" [φ]), (Term.con "cofTrue" [ψ])])
  | _ => Term.con "error" []
/-- cofFalse -/
def cofFalse : Term → Term
  | φ => (Term.con "not" [(Term.con "cofTrue" [φ])])
/-- entails -/
def entails : Term → Term → Term
  | φ, ψ => (Term.con "cofTrue" [(Term.con "cof_or" [(Term.con "cof_not" [φ]), ψ])])
/-- cof_not -/
def cof_not : Term → Term
  | (Term.con "cof_bot" []) => (Term.con "cof_top" [])
  | (Term.con "cof_top" []) => (Term.con "cof_bot" [])
  | _ => Term.con "error" []
/-- substCof -/
def substCof : Term → Term → Term → Term
  | n, r, (Term.con "cof_bot" []) => (Term.con "cof_bot" [])
  | n, r, (Term.con "cof_top" []) => (Term.con "cof_top" [])
  | n, r, (Term.con "cof_or" [φ, ψ]) => (Term.con "cof_or" [(Term.con "substCof" [n, r, φ]), (Term.con "substCof" [n, r, ψ])])
  | n, r, (Term.con "cof_eq" [s, t]) => (Term.con "cof_eq" [(Term.con "substDimInDim" [n, r, s]), (Term.con "substDimInDim" [n, r, t])])
  | n, r, (Term.con "cof_and" [φ, ψ]) => (Term.con "cof_and" [(Term.con "substCof" [n, r, φ]), (Term.con "substCof" [n, r, ψ])])
  | _, _, _ => Term.con "error" []
/-- substDimInDim -/
def substDimInDim : Term → Term → Term → Term
  | n, r, (Term.con "dim1" []) => (Term.con "dim1" [])
  | n, r, (Term.con "dim0" []) => (Term.con "dim0" [])
  | n1, r, (Term.con "dimVar" [n2]) => if n1 == n2 then r else Term.con "error" []
  | _, _, _ => Term.con "error" []
/-- forallDim -/
def forallDim : Term → Term → Term
  | i, φ => (Term.con "cof_and" [(Term.con "substCof" [i, (Term.con "dim0" []), φ]), (Term.con "substCof" [i, (Term.con "dim1" []), φ])])
/-- existsDim -/
def existsDim : Term → Term → Term
  | i, φ => (Term.con "cof_or" [(Term.con "substCof" [i, (Term.con "dim0" []), φ]), (Term.con "substCof" [i, (Term.con "dim1" []), φ])])
end Lego.Cubical.Cofibration
