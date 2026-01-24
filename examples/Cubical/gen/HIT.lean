/-
  Lego.Cubical.HIT: Generated from HIT.lego

  DO NOT EDIT - regenerate with:
    lake exe generated-pipeline HIT.lego
-/

import Lego.Algebra

set_option linter.unusedVariables false

namespace Lego.Cubical.HIT

open Lego (Term)
/-- hitKindToString -/
def hitKindToString : Term → Term
  | (Term.con "circleHIT" []) => (Term.lit "Circle")
  | (Term.con "natHIT" []) => (Term.lit "Nat")
  | _ => Term.con "error" []
/-- isNatHIT -/
def isNatHIT : Term → Term
  | (Term.con "natHIT" []) => (Term.con "true" [])
  | k => (Term.con "false" [])
/-- isCircleHIT -/
def isCircleHIT : Term → Term
  | (Term.con "circleHIT" []) => (Term.con "true" [])
  | k => (Term.con "false" [])
/-- hcomNat -/
def hcomNat : Term → Term → Term → Term → Term → Term
  | r, r', φ, tubes, base => (Term.con "hcomNatStep" [φ, tubes, base])
  | r1, r2, φ, tubes, base => if r1 == r2 then base else Term.con "error" []
/-- hcomNatStep -/
def hcomNatStep : Term → Term → Term → Term
  | (Term.con "cof_top" []), tubes, base => (Term.con "app" [(Term.con "app" [tubes, (Term.con "dim1" [])]), (Term.con "lit" [(Term.lit "trivial-proof")])])
  | (Term.con "cof_bot" []), tubes, base => base
  | φ, tubes, base => (Term.con "hcom_nat" [φ, tubes, base])
/-- coeNat -/
def coeNat : Term → Term → Term → Term → Term
  | r, r', (Term.con "lam" [(Term.con "nat" [])]), v => v
  | _, _, _, _ => Term.con "error" []
/-- coeNatSimple -/
def coeNatSimple : Term → Term → Term → Term
  | r, r', v => v
-- natZero: no valid cases
/-- natSucc -/
def natSucc : Term → Term
  | n => (Term.con "intro" [(Term.con "succ" [n])])
/-- isNatIntro -/
def isNatIntro : Term → Term
  | (Term.con "intro" [(Term.con "zero" [])]) => (Term.con "true" [])
  | e => (Term.con "false" [])
  | (Term.con "intro" [(Term.con "succ" [n])]) => (Term.con "true" [])
/-- natIntroVal -/
def natIntroVal : Term → Term
  | (Term.con "intro" [(Term.con "zero" [])]) => (Term.con "zero" [])
  | (Term.con "intro" [(Term.con "succ" [n])]) => (Term.con "succ" [n])
  | _ => Term.con "error" []
/-- natElim -/
def natElim : Term → Term → Term → Term → Term
  | P, z, s, (Term.con "intro" [(Term.con "zero" [])]) => z
  | P, z, s, n => (Term.con "elim" [(Term.con "nat" []), P, z, s, n])
  | P, z, s, (Term.con "intro" [(Term.con "succ" [n])]) => (Term.con "app" [(Term.con "app" [s, n]), (Term.con "natElim" [P, z, s, n])])
/-- hcomCircle -/
def hcomCircle : Term → Term → Term → Term → Term → Term
  | r, r', φ, tubes, cap => (Term.con "hcomCircleBody" [r, r', φ, tubes, cap])
  | r1, r2, φ, tubes, cap => if r1 == r2 then cap else Term.con "error" []
/-- hcomCircleBody -/
def hcomCircleBody : Term → Term → Term → Term → Term → Term
  | r, r', φ, tubes, (Term.con "intro" [(Term.con "base" [])]) => (Term.con "intro" [(Term.con "base" [])])
  | r, r', φ, tubes, cap => (Term.con "hcom_circle" [r, r', φ, tubes, cap])
  | r, r', φ, tubes, (Term.con "intro" [(Term.con "loop" [i])]) => (Term.con "hcom_circle" [r, r', φ, tubes, (Term.con "intro" [(Term.con "loop" [i])])])
/-- coeCircle -/
def coeCircle : Term → Term → Term → Term → Term
  | r, r', (Term.con "lam" [(Term.con "S1" [])]), v => v
  | _, _, _, _ => Term.con "error" []
/-- coeCircleSimple -/
def coeCircleSimple : Term → Term → Term → Term
  | r, r', v => v
-- circleBase: no valid cases
/-- circleLoop -/
def circleLoop : Term → Term
  | i => (Term.con "intro" [(Term.con "loop" [i])])
/-- isCircleIntro -/
def isCircleIntro : Term → Term
  | (Term.con "intro" [(Term.con "base" [])]) => (Term.con "true" [])
  | e => (Term.con "false" [])
  | (Term.con "intro" [(Term.con "loop" [i])]) => (Term.con "true" [])
/-- circleIntroKind -/
def circleIntroKind : Term → Term
  | (Term.con "intro" [(Term.con "base" [])]) => (Term.con "base" [])
  | (Term.con "intro" [(Term.con "loop" [i])]) => (Term.con "loop" [])
  | _ => Term.con "error" []
/-- circleElim -/
def circleElim : Term → Term → Term → Term → Term
  | P, b, l, (Term.con "intro" [(Term.con "base" [])]) => b
  | P, b, l, x => (Term.con "elim" [(Term.con "circle" []), P, b, l, x])
  | P, b, l, (Term.con "intro" [(Term.con "loop" [i])]) => (Term.con "papp" [l, i])
-- loopRefl: no valid cases
-- loopPath: no valid cases
/-- loopConcat -/
def loopConcat : Term → Term → Term
  | p, q => (Term.con "plam" [(Term.con "lit" [(Term.lit "i")]), (Term.con "hcom" [(Term.con "S1" []), (Term.con "dim0" []), (Term.con "dim1" []), (Term.con "cof_disj" [(Term.con "cof_eq" [(Term.con "ix" [(Term.con "num" [(Term.con "number" [(Term.lit "0")])])]), (Term.con "dim0" [])]), (Term.con "cof_eq" [(Term.con "ix" [(Term.con "num" [(Term.con "number" [(Term.lit "0")])])]), (Term.con "dim1" [])])]), (Term.con "lam" [(Term.con "lam" [(Term.con "cofSplit" [(Term.con "ix" [(Term.con "num" [(Term.con "number" [(Term.lit "1")])])]), (Term.con "cof_eq" [(Term.con "ix" [(Term.con "num" [(Term.con "number" [(Term.lit "1")])])]), (Term.con "dim0" [])]), (Term.con "papp" [(Term.con "shift" [(Term.con "num" [(Term.con "number" [(Term.lit "0")])]), (Term.con "num" [(Term.con "number" [(Term.lit "2")])]), p]), (Term.con "ix" [(Term.con "num" [(Term.con "number" [(Term.lit "0")])])])]), (Term.con "cof_eq" [(Term.con "ix" [(Term.con "num" [(Term.con "number" [(Term.lit "1")])])]), (Term.con "dim1" [])]), (Term.con "papp" [(Term.con "shift" [(Term.con "num" [(Term.con "number" [(Term.lit "0")])]), (Term.con "num" [(Term.con "number" [(Term.lit "2")])]), q]), (Term.con "ix" [(Term.con "num" [(Term.con "number" [(Term.lit "0")])])])])])])]), (Term.con "intro" [(Term.con "base" [])])])])
/-- loopInverse -/
def loopInverse : Term → Term
  | p => (Term.con "plam" [(Term.con "lit" [(Term.lit "i")]), (Term.con "papp" [p, (Term.con "dim_neg" [(Term.con "ix" [(Term.con "num" [(Term.con "number" [(Term.lit "0")])])])])])])
/-- hitHcom -/
def hitHcom : Term → Term → Term → Term → Term → Term → Term
  | (Term.con "circleHIT" []), r, r', φ, tubes, cap => (Term.con "hcomCircle" [r, r', φ, tubes, cap])
  | (Term.con "natHIT" []), r, r', φ, tubes, cap => (Term.con "hcomNat" [r, r', φ, tubes, cap])
  | _, _, _, _, _, _ => Term.con "error" []
/-- hitCoe -/
def hitCoe : Term → Term → Term → Term → Term → Term
  | (Term.con "circleHIT" []), r, r', line, v => (Term.con "coeCircleSimple" [r, r', v])
  | (Term.con "natHIT" []), r, r', line, v => (Term.con "coeNatSimple" [r, r', v])
  | _, _, _, _, _ => Term.con "error" []
/-- loopBoundary -/
def loopBoundary : Term → Term
  | (Term.con "intro" [(Term.con "loop" [(Term.con "dim1" [])])]) => (Term.con "intro" [(Term.con "base" [])])
  | (Term.con "intro" [(Term.con "loop" [(Term.con "dim0" [])])]) => (Term.con "intro" [(Term.con "base" [])])
  | _ => Term.con "error" []
/-- checkLoopBoundary -/
def checkLoopBoundary : Term → Term → Term
  | (Term.con "intro" [(Term.con "base" [])]), (Term.con "intro" [(Term.con "base" [])]) => (Term.con "true" [])
  | _, _ => Term.con "error" []
/-- hitCheckBoundary -/
def hitCheckBoundary : Term → Term → Term → Term
  | (Term.con "circleHIT" []), ctor, bounds => (Term.con "checkCircleBoundary" [ctor, bounds])
  | (Term.con "natHIT" []), ctor, bounds => (Term.con "true" [])
  | _, _, _ => Term.con "error" []
/-- checkCircleBoundary -/
def checkCircleBoundary : Term → Term → Term
  | (Term.con "base" []), bounds => (Term.con "true" [])
  | (Term.con "loop" [i]), bounds => (Term.con "and" [(Term.con "eq" [(Term.con "subst" [(Term.con "num" [(Term.con "number" [(Term.lit "0")])]), (Term.con "dim0" []), bounds]), (Term.con "intro" [(Term.con "base" [])])]), (Term.con "eq" [(Term.con "subst" [(Term.con "num" [(Term.con "number" [(Term.lit "0")])]), (Term.con "dim1" []), bounds]), (Term.con "intro" [(Term.con "base" [])])])])
  | _, _ => Term.con "error" []
/-- quoteHIT -/
def quoteHIT : Term → Term → Term
  | (Term.con "circleHIT" []), (Term.con "intro" [(Term.con "base" [])]) => (Term.con "surface" [(Term.con "base" [])])
  | (Term.con "natHIT" []), (Term.con "intro" [(Term.con "zero" [])]) => (Term.con "surface" [(Term.con "zero" [])])
  | (Term.con "circleHIT" []), (Term.con "intro" [(Term.con "loop" [i])]) => (Term.con "surface" [(Term.con "loop" [(Term.con "quoteDim" [i])])])
  | (Term.con "natHIT" []), (Term.con "intro" [(Term.con "succ" [n])]) => (Term.con "surface" [(Term.con "succ" [(Term.con "quoteHIT" [(Term.con "natHIT" []), n])])])
  | _, _ => Term.con "error" []
/-- normalizeHIT -/
def normalizeHIT : Term → Term → Term
  | (Term.con "circleHIT" []), (Term.con "intro" [(Term.con "loop" [(Term.con "dim1" [])])]) => (Term.con "intro" [(Term.con "base" [])])
  | (Term.con "circleHIT" []), (Term.con "intro" [(Term.con "base" [])]) => (Term.con "intro" [(Term.con "base" [])])
  | (Term.con "natHIT" []), (Term.con "intro" [(Term.con "zero" [])]) => (Term.con "intro" [(Term.con "zero" [])])
  | (Term.con "circleHIT" []), (Term.con "intro" [(Term.con "loop" [(Term.con "dim0" [])])]) => (Term.con "intro" [(Term.con "base" [])])
  | (Term.con "natHIT" []), (Term.con "intro" [(Term.con "succ" [n])]) => (Term.con "intro" [(Term.con "succ" [(Term.con "normalizeHIT" [(Term.con "natHIT" []), n])])])
  | (Term.con "circleHIT" []), (Term.con "intro" [(Term.con "loop" [i])]) => (Term.con "intro" [(Term.con "loop" [(Term.con "normalizeDim" [i])])])
  | _, _ => Term.con "error" []
end Lego.Cubical.HIT
