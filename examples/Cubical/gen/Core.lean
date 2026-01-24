/-
  Lego.Cubical.Core: Generated from Core.lego

  DO NOT EDIT - regenerate with:
    lake exe generated-pipeline Core.lego
-/

import Lego.Algebra

set_option linter.unusedVariables false

namespace Lego.Cubical.Core

open Lego (Term)
/-- lmax -/
def lmax : Term → Term → Term
  | l, (Term.con "lzero" []) => l
  | (Term.con "lzero" []), l => l
  | (Term.con "lsuc" [l1]), (Term.con "lsuc" [l2]) => (Term.con "lsuc" [(Term.con "lmax" [l1, l2])])
  | l1, l2 => if l1 == l2 then l1 else Term.con "error" []
/-- app -/
def app : Term → Term → Term
  | (Term.con "lam" [body]), arg => (Term.con "subst" [(Term.con "num" [(Term.con "number" [(Term.lit "0")])]), arg, body])
  | _, _ => Term.con "error" []
/-- fst -/
def fst : Term → Term
  | (Term.con "pair" [a, b]) => a
  | _ => Term.con "error" []
/-- snd -/
def snd : Term → Term
  | (Term.con "pair" [a, b]) => b
  | _ => Term.con "error" []
/-- letE -/
def letE : Term → Term → Term → Term
  | ty, val, body => (Term.con "subst" [(Term.con "num" [(Term.con "number" [(Term.lit "0")])]), val, body])
/-- cof_eq -/
def cof_eq : Term → Term → Term
  | (Term.con "dim1" []), (Term.con "dim0" []) => (Term.con "cof_bot" [])
  | (Term.con "dim0" []), (Term.con "dim1" []) => (Term.con "cof_bot" [])
  | r1, r2 => if r1 == r2 then (Term.con "cof_top" []) else Term.con "error" []
/-- cof_and -/
def cof_and : Term → Term → Term
  | (Term.con "cof_bot" []), φ => (Term.con "cof_bot" [])
  | (Term.con "cof_top" []), φ => φ
  | _, _ => Term.con "error" []
/-- cof_or -/
def cof_or : Term → Term → Term
  | (Term.con "cof_bot" []), φ => φ
  | (Term.con "cof_top" []), φ => (Term.con "cof_top" [])
  | _, _ => Term.con "error" []
/-- papp -/
def papp : Term → Term → Term
  | (Term.con "plam" [body]), (Term.con "dim1" []) => (Term.con "substDim" [(Term.con "num" [(Term.con "number" [(Term.lit "0")])]), (Term.con "dim1" []), body])
  | (Term.con "plam" [body]), (Term.con "dim0" []) => (Term.con "substDim" [(Term.con "num" [(Term.con "number" [(Term.lit "0")])]), (Term.con "dim0" []), body])
  | (Term.con "refl" [a]), r => a
  | _, _ => Term.con "error" []
/-- coe -/
def coe : Term → Term → Term → Term → Term
  | r1, r2, A, a => if r1 == r2 then a else Term.con "error" []
/-- hcom -/
def hcom : Term → Term → Term → Term → Term → Term
  | r1, r2, A, φ, cap => if r1 == r2 then cap else Term.con "error" []
/-- vin -/
def vin : Term → Term → Term → Term
  | (Term.con "dim1" []), a, b => b
  | (Term.con "dim0" []), a, b => a
  | _, _, _ => Term.con "error" []
/-- natElim -/
def natElim : Term → Term → Term → Term → Term
  | P, z, s, (Term.con "zero" []) => z
  | P, z, s, (Term.con "suc" [n]) => (Term.con "app" [(Term.con "app" [s, n]), (Term.con "natElim" [P, z, s, n])])
  | _, _, _, _ => Term.con "error" []
/-- loop -/
def loop : Term → Term
  | (Term.con "dim1" []) => (Term.con "base" [])
  | (Term.con "dim0" []) => (Term.con "base" [])
  | _ => Term.con "error" []
/-- circleElim -/
def circleElim : Term → Term → Term → Term → Term
  | P, b, l, (Term.con "base" []) => b
  | _, _, _, _ => Term.con "error" []
/-- subOut -/
def subOut : Term → Term
  | (Term.con "subIn" [e]) => e
  | _ => Term.con "error" []
/-- shift -/
def shift : Term → Term → Term → Term
  | k, n, (Term.con "pi" [A, B]) => (Term.con "pi" [(Term.con "shift" [k, n, A]), (Term.con "shift" [(Term.con "add" [k, (Term.con "num" [(Term.con "number" [(Term.lit "1")])])]), n, B])])
  | k, n, (Term.con "ix" [m]) => (Term.con "ix" [(Term.con "if" [(Term.con "geq" [m, k]), (Term.con "add" [m, n]), m])])
  | k, n, (Term.con "lam" [body]) => (Term.con "lam" [(Term.con "shift" [(Term.con "add" [k, (Term.con "num" [(Term.con "number" [(Term.lit "1")])])]), n, body])])
  | k, n, (Term.con "app" [f, a]) => (Term.con "app" [(Term.con "shift" [k, n, f]), (Term.con "shift" [k, n, a])])
  | _, _, _ => Term.con "error" []
/-- subst -/
def subst : Term → Term → Term → Term
  | k, v, (Term.con "app" [f, a]) => (Term.con "app" [(Term.con "subst" [k, v, f]), (Term.con "subst" [k, v, a])])
  | k, v, (Term.con "lam" [body]) => (Term.con "lam" [(Term.con "subst" [(Term.con "add" [k, (Term.con "num" [(Term.con "number" [(Term.lit "1")])])]), (Term.con "shift" [(Term.con "num" [(Term.con "number" [(Term.lit "0")])]), (Term.con "num" [(Term.con "number" [(Term.lit "1")])]), v]), body])])
  | k1, v, (Term.con "ix" [k2]) => if k1 == k2 then v else Term.con "error" []
  | _, _, _ => Term.con "error" []
/-- normalize -/
def normalize : Term → Term → Term
  | (Term.con "num" [(Term.con "number" [(Term.lit "0")])]), t => t
  | _, _ => Term.con "error" []
/-- normalizeStep -/
def normalizeStep : Term → Term → Term
  -- SKIPPED normalizeStepNone: unbound variables [t]
  | fuel, (Term.con "some" [t]) => (Term.con "normalize" [fuel, t])
  | _, _ => Term.con "error" []
end Lego.Cubical.Core
