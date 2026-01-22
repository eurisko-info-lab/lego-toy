/-
  Lego.Cubical.Domain: Generated from Domain.lego

  DO NOT EDIT - regenerate with:
    lake exe generated-pipeline Domain.lego
-/

import Lego.Algebra

set_option linter.unusedVariables false

namespace Lego.Cubical.Domain

open Lego (Term)
-- dzero: no valid cases
-- done: no valid cases
/-- ofLevel -/
def ofLevel : Term → Term
  | (Term.con "lzero" []) => (Term.con "dzero" [])
  | (Term.con "lvar" [n]) => (Term.con "dlvar" [n])
  | (Term.con "lsuc" [l]) => (Term.con "dsuc" [(Term.con "ofLevel" [l])])
  | (Term.con "lmax" [l1, l2]) => (Term.con "dmax" [(Term.con "ofLevel" [l1]), (Term.con "ofLevel" [l2])])
  | _ => Term.con "error" []
/-- dimOfExpr -/
def dimOfExpr : Term → Term
  | (Term.con "dim1" []) => (Term.con "some" [(Term.con "ddim1" [])])
  | (Term.con "dim0" []) => (Term.con "some" [(Term.con "ddim0" [])])
  | e => (Term.con "none" [])
  | (Term.con "dimVar" [n]) => (Term.con "some" [(Term.con "dvar" [n])])
/-- dimToExpr -/
def dimToExpr : Term → Term
  | (Term.con "ddim1" []) => (Term.con "dim1" [])
  | (Term.con "ddim0" []) => (Term.con "dim0" [])
  | (Term.con "dvar" [n]) => (Term.con "dimVar" [n])
  | _ => Term.con "error" []
/-- dimEqD -/
def dimEqD : Term → Term → Term
  | (Term.con "ddim1" []), (Term.con "ddim1" []) => (Term.con "true" [])
  | (Term.con "ddim0" []), (Term.con "ddim0" []) => (Term.con "true" [])
  | (Term.con "dvar" [n]), (Term.con "dvar" [m]) => (Term.con "eq" [n, m])
  | _, _ => Term.con "error" []
/-- dCofIsTrue -/
def dCofIsTrue : Term → Term
  | (Term.con "dcof_bot" []) => (Term.con "false" [])
  | (Term.con "dcof_top" []) => (Term.con "true" [])
  | (Term.con "dcof_meet" [φ, ψ]) => (Term.con "and" [(Term.con "dCofIsTrue" [φ]), (Term.con "dCofIsTrue" [ψ])])
  | (Term.con "dcof_eq" [d1, d2]) => (Term.con "dimEqD" [d1, d2])
  | (Term.con "dcof_join" [φ, ψ]) => (Term.con "or" [(Term.con "dCofIsTrue" [φ]), (Term.con "dCofIsTrue" [ψ])])
  | _ => Term.con "error" []
/-- dCofIsFalse -/
def dCofIsFalse : Term → Term
  | φ => (Term.con "not" [(Term.con "dCofIsTrue" [φ])])
/-- denvLookup -/
def denvLookup : Term → Term → Term
  | n, (Term.con "denvNil" []) => (Term.con "none" [])
  | (Term.con "num" [(Term.con "number" [(Term.lit "0")])]), (Term.con "denvCons" [v, rest]) => (Term.con "some" [v])
  | (Term.con "suc" [n]), (Term.con "denvCons" [v, rest]) => (Term.con "denvLookup" [n, rest])
  | _, _ => Term.con "error" []
/-- denvExtend -/
def denvExtend : Term → Term → Term
  | v, env => (Term.con "denvCons" [v, env])
/-- dCloApply -/
def dCloApply : Term → Term → Term
  | (Term.con "dclo" [body, env]), arg => (Term.con "deval" [(Term.con "denvCons" [arg, env]), body])
  | _, _ => Term.con "error" []
/-- deval -/
def deval : Term → Term → Term
  | env, (Term.con "circle" []) => (Term.con "dcircle" [])
  | env, (Term.con "nat" []) => (Term.con "dnat" [])
  | env, (Term.con "zero" []) => (Term.con "dzeroN" [])
  | env, (Term.con "base" []) => (Term.con "dbase" [])
  | env, (Term.con "loop" [r]) => (Term.con "dloop" [(Term.con "dimOfExprForce" [r])])
  | env, (Term.con "pi" [A, B]) => (Term.con "dpi" [(Term.con "dtpOf" [(Term.con "deval" [env, A])]), (Term.con "dclo" [B, env])])
  | env, (Term.con "sigma" [A, B]) => (Term.con "dsigma" [(Term.con "dtpOf" [(Term.con "deval" [env, A])]), (Term.con "dclo" [B, env])])
  | env, (Term.con "pair" [a, b]) => (Term.con "dpair" [(Term.con "deval" [env, a]), (Term.con "deval" [env, b])])
  | env, (Term.con "fst" [p]) => (Term.con "dFst" [(Term.con "deval" [env, p])])
  | env, (Term.con "snd" [p]) => (Term.con "dSnd" [(Term.con "deval" [env, p])])
  | env, (Term.con "univ" [l]) => (Term.con "duniv" [(Term.con "ofLevel" [l])])
  | env, (Term.con "path" [A, a, b]) => (Term.con "dpath" [(Term.con "dtpOf" [(Term.con "deval" [env, A])]), (Term.con "deval" [env, a]), (Term.con "deval" [env, b])])
  | env, (Term.con "plam" [body]) => (Term.con "dplam" [(Term.con "dclo" [body, env])])
  | env, (Term.con "papp" [p, r]) => (Term.con "dPApp" [(Term.con "deval" [env, p]), (Term.con "dimOfExprForce" [r])])
  | env, (Term.con "refl" [a]) => (Term.con "drefl" [(Term.con "deval" [env, a])])
  | env, (Term.con "ix" [n]) => (Term.con "fromOption" [(Term.con "denvLookup" [n, env]), (Term.con "dneu" [(Term.con "dcut" [(Term.con "dneuVar" [n]), (Term.con "dtpUnknown" [])])])])
  | env, (Term.con "lit" [s]) => (Term.con "dlit" [s])
  | env, (Term.con "suc" [n]) => (Term.con "dsucN" [(Term.con "deval" [env, n])])
  | env, (Term.con "lam" [body]) => (Term.con "dlam" [(Term.con "dclo" [body, env])])
  | env, (Term.con "app" [f, a]) => (Term.con "dApply" [(Term.con "deval" [env, f]), (Term.con "deval" [env, a])])
  | _, _ => Term.con "error" []
/-- dApply -/
def dApply : Term → Term → Term
  | (Term.con "dneu" [(Term.con "dcut" [neu, tp])]), arg => (Term.con "dneu" [(Term.con "dcut" [(Term.con "dneuApp" [neu, arg]), (Term.con "dtpApply" [tp, arg])])])
  | (Term.con "dlam" [clo]), arg => (Term.con "dCloApply" [clo, arg])
  | _, _ => Term.con "error" []
/-- dFst -/
def dFst : Term → Term
  | (Term.con "dneu" [(Term.con "dcut" [neu, tp])]) => (Term.con "dneu" [(Term.con "dcut" [(Term.con "dneuFst" [neu]), (Term.con "dtpFst" [tp])])])
  | (Term.con "dpair" [a, b]) => a
  | _ => Term.con "error" []
/-- dSnd -/
def dSnd : Term → Term
  | (Term.con "dneu" [(Term.con "dcut" [neu, tp])]) => (Term.con "dneu" [(Term.con "dcut" [(Term.con "dneuSnd" [neu]), (Term.con "dtpSnd" [tp])])])
  | (Term.con "dpair" [a, b]) => b
  | _ => Term.con "error" []
/-- dPApp -/
def dPApp : Term → Term → Term
  | (Term.con "dneu" [(Term.con "dcut" [neu, tp])]), d => (Term.con "dneu" [(Term.con "dcut" [(Term.con "dneuPApp" [neu, d]), (Term.con "dtpPApp" [tp, d])])])
  | (Term.con "dplam" [clo]), d => (Term.con "dCloApplyDim" [clo, d])
  | (Term.con "drefl" [a]), d => a
  | _, _ => Term.con "error" []
end Lego.Cubical.Domain
