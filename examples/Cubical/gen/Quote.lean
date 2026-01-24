/-
  Lego.Cubical.Quote: Generated from Quote.lego

  DO NOT EDIT - regenerate with:
    lake exe generated-pipeline Quote.lego
-/

import Lego.Algebra

set_option linter.unusedVariables false

namespace Lego.Cubical.Quote

open Lego (Term)
-- qenvEmpty: no valid cases
/-- qenvSucc -/
def qenvSucc : Term → Term
  | (Term.con "qenv" [l, dl]) => (Term.con "qenv" [(Term.con "suc" [l]), dl])
  | _ => Term.con "error" []
/-- qenvSuccDim -/
def qenvSuccDim : Term → Term
  | (Term.con "qenv" [l, dl]) => (Term.con "qenv" [l, (Term.con "suc" [dl])])
  | _ => Term.con "error" []
/-- levelToIndex -/
def levelToIndex : Term → Term → Term
  | (Term.con "qenv" [l, dl]), lvl => (Term.con "sub" [(Term.con "sub" [l, lvl]), (Term.con "num" [(Term.con "number" [(Term.lit "1")])])])
  | _, _ => Term.con "error" []
/-- dimLevelToIndex -/
def dimLevelToIndex : Term → Term → Term
  | (Term.con "qenv" [l, dl]), lvl => (Term.con "sub" [(Term.con "sub" [dl, lvl]), (Term.con "num" [(Term.con "number" [(Term.lit "1")])])])
  | _, _ => Term.con "error" []
/-- generic -/
def generic : Term → Term
  | (Term.con "qenv" [l, dl]) => (Term.con "ix" [l])
  | _ => Term.con "error" []
/-- genericDim -/
def genericDim : Term → Term
  | (Term.con "qenv" [l, dl]) => (Term.con "dimVar" [dl])
  | _ => Term.con "error" []
/-- shiftFrom -/
def shiftFrom : Term → Term → Term → Term
  | (Term.con "univ" [l]), n, cutoff => (Term.con "univ" [l])
  | (Term.con "ix" [k]), n, cutoff => (Term.con "if" [(Term.con "geq" [k, cutoff]), (Term.con "ix" [(Term.con "add" [k, n])]), (Term.con "ix" [k])])
  | (Term.con "lam" [body]), n, cutoff => (Term.con "lam" [(Term.con "shiftFrom" [body, n, (Term.con "suc" [cutoff])])])
  | (Term.con "app" [f, a]), n, cutoff => (Term.con "app" [(Term.con "shiftFrom" [f, n, cutoff]), (Term.con "shiftFrom" [a, n, cutoff])])
  | (Term.con "pi" [A, B]), n, cutoff => (Term.con "pi" [(Term.con "shiftFrom" [A, n, cutoff]), (Term.con "shiftFrom" [B, n, (Term.con "suc" [cutoff])])])
  | (Term.con "sigma" [A, B]), n, cutoff => (Term.con "sigma" [(Term.con "shiftFrom" [A, n, cutoff]), (Term.con "shiftFrom" [B, n, (Term.con "suc" [cutoff])])])
  | (Term.con "pair" [a, b]), n, cutoff => (Term.con "pair" [(Term.con "shiftFrom" [a, n, cutoff]), (Term.con "shiftFrom" [b, n, cutoff])])
  | (Term.con "fst" [p]), n, cutoff => (Term.con "fst" [(Term.con "shiftFrom" [p, n, cutoff])])
  | (Term.con "snd" [p]), n, cutoff => (Term.con "snd" [(Term.con "shiftFrom" [p, n, cutoff])])
  | (Term.con "plam" [body]), n, cutoff => (Term.con "plam" [(Term.con "shiftFrom" [body, n, cutoff])])
  | (Term.con "papp" [p, r]), n, cutoff => (Term.con "papp" [(Term.con "shiftFrom" [p, n, cutoff]), r])
  | (Term.con "lit" [s]), n, cutoff => (Term.con "lit" [s])
  | _, _, _ => Term.con "error" []
/-- quoteCon -/
def quoteCon : Term → Term → Term
  | env, (Term.con "dcircle" []) => (Term.con "circle" [])
  | env, (Term.con "dnat" []) => (Term.con "nat" [])
  | env, (Term.con "dzeroN" []) => (Term.con "zero" [])
  | env, (Term.con "dbase" []) => (Term.con "base" [])
  | env, (Term.con "dneu" [cut]) => (Term.con "quoteNeutral" [env, cut])
  | env, (Term.con "dpi" [A, (Term.con "dclo" [B, cloEnv])]) => (Term.con "pi" [(Term.con "quoteTp" [env, A]), (Term.con "quoteCon" [(Term.con "qenvSucc" [env]), (Term.con "deval" [(Term.con "denvCons" [(Term.con "dneu" [(Term.con "dcut" [(Term.con "dneuVar" [(Term.con "qenvLevel" [env])]), A])]), cloEnv]), B])])])
  | env, (Term.con "dsigma" [A, (Term.con "dclo" [B, cloEnv])]) => (Term.con "sigma" [(Term.con "quoteTp" [env, A]), (Term.con "quoteCon" [(Term.con "qenvSucc" [env]), (Term.con "deval" [(Term.con "denvCons" [(Term.con "dneu" [(Term.con "dcut" [(Term.con "dneuVar" [(Term.con "qenvLevel" [env])]), A])]), cloEnv]), B])])])
  | env, (Term.con "dpath" [A, a, b]) => (Term.con "path" [(Term.con "quoteTp" [env, A]), (Term.con "quoteCon" [env, a]), (Term.con "quoteCon" [env, b])])
  | env, (Term.con "dplam" [(Term.con "dclo" [body, cloEnv])]) => (Term.con "plam" [(Term.con "quoteCon" [(Term.con "qenvSuccDim" [env]), (Term.con "deval" [(Term.con "denvCons" [(Term.con "dneu" [(Term.con "dcut" [(Term.con "dneuVar" [(Term.con "qenvDimLevel" [env])]), (Term.con "dtpI" [])])]), cloEnv]), body])])])
  | env, (Term.con "drefl" [a]) => (Term.con "refl" [(Term.con "quoteCon" [env, a])])
  | env, (Term.con "dlit" [s]) => (Term.con "lit" [s])
  | env, (Term.con "dlam" [(Term.con "dclo" [body, cloEnv])]) => (Term.con "lam" [(Term.con "quoteCon" [(Term.con "qenvSucc" [env]), (Term.con "deval" [(Term.con "denvCons" [(Term.con "dneu" [(Term.con "dcut" [(Term.con "dneuVar" [(Term.con "qenvLevel" [env])]), (Term.con "dtpUnknown" [])])]), cloEnv]), body])])])
  | env, (Term.con "dsucN" [n]) => (Term.con "suc" [(Term.con "quoteCon" [env, n])])
  | env, (Term.con "dpair" [a, b]) => (Term.con "pair" [(Term.con "quoteCon" [env, a]), (Term.con "quoteCon" [env, b])])
  | env, (Term.con "duniv" [l]) => (Term.con "univ" [(Term.con "quoteLevel" [l])])
  | env, (Term.con "dloop" [d]) => (Term.con "loop" [(Term.con "quoteDim" [d])])
  | _, _ => Term.con "error" []
/-- quoteTp -/
def quoteTp : Term → Term → Term
  | env, (Term.con "dtpCircle" []) => (Term.con "circle" [])
  | env, (Term.con "dtpNat" []) => (Term.con "nat" [])
  | env, (Term.con "dtpNeu" [cut]) => (Term.con "quoteNeutral" [env, cut])
  | env, (Term.con "dtpSigma" [A, clo]) => (Term.con "sigma" [(Term.con "quoteTp" [env, A]), (Term.con "quoteTpClo" [(Term.con "qenvSucc" [env]), clo])])
  | env, (Term.con "dtpPath" [A, a, b]) => (Term.con "path" [(Term.con "quoteTp" [env, A]), (Term.con "quoteCon" [env, a]), (Term.con "quoteCon" [env, b])])
  | env, (Term.con "dtpUniv" [l]) => (Term.con "univ" [(Term.con "quoteLevel" [l])])
  | env, (Term.con "dtpPi" [A, clo]) => (Term.con "pi" [(Term.con "quoteTp" [env, A]), (Term.con "quoteTpClo" [(Term.con "qenvSucc" [env]), clo])])
  | _, _ => Term.con "error" []
/-- quoteNeutral -/
def quoteNeutral : Term → Term → Term
  | env, (Term.con "dcut" [(Term.con "dneuCircleElim" [P, b, l, neu]), tp]) => (Term.con "circleElim" [(Term.con "quoteCon" [env, P]), (Term.con "quoteCon" [env, b]), (Term.con "quoteCon" [env, l]), (Term.con "quoteNeutral" [env, (Term.con "dcut" [neu, (Term.con "dtpCircle" [])])])])
  | env, (Term.con "dcut" [(Term.con "dneuVar" [l]), tp]) => (Term.con "ix" [(Term.con "levelToIndex" [env, l])])
  | env, (Term.con "dcut" [(Term.con "dneuApp" [neu, arg]), tp]) => (Term.con "app" [(Term.con "quoteNeutral" [env, (Term.con "dcut" [neu, (Term.con "dtpUnknown" [])])]), (Term.con "quoteCon" [env, arg])])
  | env, (Term.con "dcut" [(Term.con "dneuFst" [neu]), tp]) => (Term.con "fst" [(Term.con "quoteNeutral" [env, (Term.con "dcut" [neu, (Term.con "dtpUnknown" [])])])])
  | env, (Term.con "dcut" [(Term.con "dneuSnd" [neu]), tp]) => (Term.con "snd" [(Term.con "quoteNeutral" [env, (Term.con "dcut" [neu, (Term.con "dtpUnknown" [])])])])
  | env, (Term.con "dcut" [(Term.con "dneuPApp" [neu, d]), tp]) => (Term.con "papp" [(Term.con "quoteNeutral" [env, (Term.con "dcut" [neu, (Term.con "dtpUnknown" [])])]), (Term.con "quoteDim" [d])])
  | env, (Term.con "dcut" [(Term.con "dneuNatElim" [P, z, s, neu]), tp]) => (Term.con "natElim" [(Term.con "quoteCon" [env, P]), (Term.con "quoteCon" [env, z]), (Term.con "quoteCon" [env, s]), (Term.con "quoteNeutral" [env, (Term.con "dcut" [neu, (Term.con "dtpNat" [])])])])
  | _, _ => Term.con "error" []
/-- quoteLevel -/
def quoteLevel : Term → Term
  | (Term.con "dsuc" [l]) => (Term.con "lsuc" [(Term.con "quoteLevel" [l])])
  | (Term.con "dconst" [n]) => (Term.con "ofNat" [n])
  | (Term.con "dlvar" [n]) => (Term.con "lvar" [n])
  | (Term.con "dmax" [l1, l2]) => (Term.con "lmax" [(Term.con "quoteLevel" [l1]), (Term.con "quoteLevel" [l2])])
  | _ => Term.con "error" []
/-- ofNat -/
def ofNat : Term → Term
  | (Term.con "num" [(Term.con "number" [(Term.lit "0")])]) => (Term.con "lzero" [])
  | (Term.con "suc" [n]) => (Term.con "lsuc" [(Term.con "ofNat" [n])])
  | _ => Term.con "error" []
/-- quoteDim -/
def quoteDim : Term → Term
  | (Term.con "ddim1" []) => (Term.con "dim1" [])
  | (Term.con "ddim0" []) => (Term.con "dim0" [])
  | (Term.con "dvar" [n]) => (Term.con "dimVar" [n])
  | _ => Term.con "error" []
/-- nbe -/
def nbe : Term → Term
  | t => (Term.con "quoteCon" [(Term.con "qenvEmpty" []), (Term.con "deval" [(Term.con "denvNil" []), t])])
/-- nbeWithEnv -/
def nbeWithEnv : Term → Term → Term
  | env, t => (Term.con "quoteCon" [(Term.con "qenvEmpty" []), (Term.con "deval" [env, t])])
end Lego.Cubical.Quote
