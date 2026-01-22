/-
  AUTO-GENERATED from .lego files
  Do not edit directly.
-/

import Lego.Algebra

open Lego

namespace HIT

  section HITKind

    def hitKindToString (t : Term) : Term :=
      match t with
      | .con "app" [.var "hitKindToString", .con "natHIT" []] => Term.con "terminal" [Term.lit "Nat"]
      | _ => t

    def hitKindToStringCircle (t : Term) : Term :=
      match t with
      | .con "app" [.var "hitKindToString", .con "circleHIT" []] => Term.con "terminal" [Term.lit "Circle"]
      | _ => t

    def isNatHIT (t : Term) : Term :=
      match t with
      | .con "app" [.var "isNatHIT", .con "natHIT" []] => Term.con "true" []
      | _ => t

    def isNatHITOther (t : Term) : Term :=
      match t with
      | .con "app" [.var "isNatHIT", k] => Term.con "false" []
      | _ => t

    def isCircleHIT (t : Term) : Term :=
      match t with
      | .con "app" [.var "isCircleHIT", .con "circleHIT" []] => Term.con "true" []
      | _ => t

    def isCircleHITOther (t : Term) : Term :=
      match t with
      | .con "app" [.var "isCircleHIT", k] => Term.con "false" []
      | _ => t

  end HITKind

  section NatKan

    def hcomNatEq (t : Term) : Term :=
      match t with
      | .con "hcomNat" [r, r_dup, φ, tubes, base] => base
      | _ => t

    def hcomNat (t : Term) : Term :=
      match t with
      | .con "hcomNat" [r, r', φ, tubes, base] => Term.con "hcomNatStep" [φ, tubes, base]
      | _ => t

    def hcomNatStep (t : Term) : Term :=
      match t with
      | .con "hcomNatStep" [.con "cof_bot" [], tubes, base] => base
      | _ => t

    def hcomNatStepTrue (t : Term) : Term :=
      match t with
      | .con "hcomNatStep" [.con "cof_top" [], tubes, base] => Term.con "app" [Term.con "app" [tubes, Term.con "dim1" []], Term.con "app" [Term.var "lit", Term.con "terminal" [Term.lit "trivial-proof"]]]
      | _ => t

    def hcomNatStepOther (t : Term) : Term :=
      match t with
      | .con "hcomNatStep" [φ, tubes, base] => Term.con "hcom_nat" [φ, tubes, base]
      | _ => t

    def coeNat (t : Term) : Term :=
      match t with
      | .con "coeNat" [r, r', .con "app" [.var "lam", .con "nat" []], v] => v
      | _ => t

    def coeNatSimple (t : Term) : Term :=
      match t with
      | .con "coeNatSimple" [r, r', v] => v
      | _ => t

  end NatKan

  section NatIntro

    def natZero (t : Term) : Term :=
      match t with
      | .con "natZero" [] => Term.con "app" [Term.var "intro", Term.con "zero" []]
      | _ => t

    def natSucc (t : Term) : Term :=
      match t with
      | .con "app" [.var "natSucc", n] => Term.con "app" [Term.var "intro", Term.con "app" [Term.var "succ", n]]
      | _ => t

    def isNatIntro (t : Term) : Term :=
      match t with
      | .con "app" [.var "isNatIntro", .con "app" [.var "intro", .con "zero" []]] => Term.con "true" []
      | _ => t

    def isNatIntroSucc (t : Term) : Term :=
      match t with
      | .con "app" [.var "isNatIntro", .con "app" [.var "intro", .con "app" [.var "succ", n]]] => Term.con "true" []
      | _ => t

    def isNatIntroOther (t : Term) : Term :=
      match t with
      | .con "app" [.var "isNatIntro", e] => Term.con "false" []
      | _ => t

    def natIntroVal (t : Term) : Term :=
      match t with
      | .con "app" [.var "natIntroVal", .con "app" [.var "intro", .con "zero" []]] => Term.con "zero" []
      | _ => t

    def natIntroValSucc (t : Term) : Term :=
      match t with
      | .con "app" [.var "natIntroVal", .con "app" [.var "intro", .con "app" [.var "succ", n]]] => Term.con "app" [Term.var "succ", n]
      | _ => t

  end NatIntro

  section NatElim

    def natElim (t : Term) : Term :=
      match t with
      | .con "natElim" [P, z, s, .con "app" [.var "intro", .con "zero" []]] => z
      | _ => t

    def natElimSucc (t : Term) : Term :=
      match t with
      | .con "natElim" [P, z, s, .con "app" [.var "intro", .con "app" [.var "succ", n]]] => Term.con "app" [Term.con "app" [s, n], Term.con "natElim" [P, z, s, n]]
      | _ => t

    def natElimNeutral (t : Term) : Term :=
      match t with
      | .con "natElim" [P, z, s, n] => Term.con "elim" [Term.con "nat" [], P, z, s, n]
      | _ => t

  end NatElim

  section CircleKan

    def hcomCircleEq (t : Term) : Term :=
      match t with
      | .con "hcomCircle" [r, r_dup, φ, tubes, cap] => cap
      | _ => t

    def hcomCircle (t : Term) : Term :=
      match t with
      | .con "hcomCircle" [r, r', φ, tubes, cap] => Term.con "hcomCircleBody" [r, r', φ, tubes, cap]
      | _ => t

    def hcomCircleBody (t : Term) : Term :=
      match t with
      | .con "hcomCircleBody" [r, r', φ, tubes, .con "app" [.var "intro", .con "base" []]] => Term.con "app" [Term.var "intro", Term.con "base" []]
      | _ => t

    def hcomCircleBodyLoop (t : Term) : Term :=
      match t with
      | .con "hcomCircleBody" [r, r', φ, tubes, .con "app" [.var "intro", .con "app" [.var "loop", i]]] => Term.con "hcom_circle" [r, r', φ, tubes, Term.con "app" [Term.var "intro", Term.con "app" [Term.var "loop", i]]]
      | _ => t

    def hcomCircleBodyOther (t : Term) : Term :=
      match t with
      | .con "hcomCircleBody" [r, r', φ, tubes, cap] => Term.con "hcom_circle" [r, r', φ, tubes, cap]
      | _ => t

    def coeCircle (t : Term) : Term :=
      match t with
      | .con "coeCircle" [r, r', .con "app" [.var "lam", .con "S1" []], v] => v
      | _ => t

    def coeCircleSimple (t : Term) : Term :=
      match t with
      | .con "coeCircleSimple" [r, r', v] => v
      | _ => t

  end CircleKan

  section CircleIntro

    def circleBase (t : Term) : Term :=
      match t with
      | .con "circleBase" [] => Term.con "app" [Term.var "intro", Term.con "base" []]
      | _ => t

    def circleLoop (t : Term) : Term :=
      match t with
      | .con "app" [.var "circleLoop", i] => Term.con "app" [Term.var "intro", Term.con "app" [Term.var "loop", i]]
      | _ => t

    def isCircleIntro (t : Term) : Term :=
      match t with
      | .con "app" [.var "isCircleIntro", .con "app" [.var "intro", .con "base" []]] => Term.con "true" []
      | _ => t

    def isCircleIntroLoop (t : Term) : Term :=
      match t with
      | .con "app" [.var "isCircleIntro", .con "app" [.var "intro", .con "app" [.var "loop", i]]] => Term.con "true" []
      | _ => t

    def isCircleIntroOther (t : Term) : Term :=
      match t with
      | .con "app" [.var "isCircleIntro", e] => Term.con "false" []
      | _ => t

    def circleIntroKind (t : Term) : Term :=
      match t with
      | .con "app" [.var "circleIntroKind", .con "app" [.var "intro", .con "base" []]] => Term.con "base" []
      | _ => t

    def circleIntroKindLoop (t : Term) : Term :=
      match t with
      | .con "app" [.var "circleIntroKind", .con "app" [.var "intro", .con "app" [.var "loop", i]]] => Term.con "loop" []
      | _ => t

  end CircleIntro

  section CircleElim

    def circleElim (t : Term) : Term :=
      match t with
      | .con "circleElim" [P, b, l, .con "app" [.var "intro", .con "base" []]] => b
      | _ => t

    def circleElimLoop (t : Term) : Term :=
      match t with
      | .con "circleElim" [P, b, l, .con "app" [.var "intro", .con "app" [.var "loop", i]]] => Term.con "papp" [l, i]
      | _ => t

    def circleElimNeutral (t : Term) : Term :=
      match t with
      | .con "circleElim" [P, b, l, x] => Term.con "elim" [Term.con "circle" [], P, b, l, x]
      | _ => t

  end CircleElim

  section LoopSpace

    def loopRefl (t : Term) : Term :=
      match t with
      | .con "loopRefl" [] => Term.con "plam" [Term.con "app" [Term.var "lit", Term.con "terminal" [Term.lit "_"]], Term.con "app" [Term.var "intro", Term.con "base" []]]
      | _ => t

    def loopPath (t : Term) : Term :=
      match t with
      | .con "loopPath" [] => Term.con "plam" [Term.con "app" [Term.var "lit", Term.con "terminal" [Term.lit "i"]], Term.con "app" [Term.var "intro", Term.con "app" [Term.var "loop", Term.con "app" [Term.var "ix", Term.con "num" [Term.con "number" [Term.lit "0"]]]]]]
      | _ => t

    def loopConcat (t : Term) : Term :=
      match t with
      | .con "loopConcat" [p, q] => Term.con "plam" [Term.con "app" [Term.var "lit", Term.con "terminal" [Term.lit "i"]], Term.con "hcom" [Term.con "S1" [], Term.con "dim0" [], Term.con "dim1" [Term.con "paren" [Term.lit "(", Term.con "cof_disj" [Term.con "paren" [Term.lit "(", Term.con "cof_eq" [Term.con "app" [Term.var "ix", Term.con "num" [Term.con "number" [Term.lit "0"]]], Term.var "dim0"], Term.lit ")"], Term.con "paren" [Term.lit "(", Term.con "cof_eq" [Term.con "app" [Term.var "ix", Term.con "num" [Term.con "number" [Term.lit "0"]]], Term.var "dim1"], Term.lit ")"]], Term.lit ")"], Term.con "paren" [Term.lit "(", Term.con "lam" [Term.con "paren" [Term.lit "(", Term.con "lam" [Term.con "paren" [Term.lit "(", Term.con "cofSplit" [Term.con "app" [Term.var "ix", Term.con "num" [Term.con "number" [Term.lit "1"]]], Term.con "paren" [Term.lit "(", Term.con "cof_eq" [Term.con "app" [Term.var "ix", Term.con "num" [Term.con "number" [Term.lit "1"]]], Term.var "dim0"], Term.lit ")"], Term.con "paren" [Term.lit "(", Term.con "papp" [Term.con "shift" [Term.con "num" [Term.con "number" [Term.lit "0"]], Term.con "num" [Term.con "number" [Term.lit "2"]], p], Term.con "app" [Term.var "ix", Term.con "num" [Term.con "number" [Term.lit "0"]]]], Term.lit ")"], Term.con "paren" [Term.lit "(", Term.con "cof_eq" [Term.con "app" [Term.var "ix", Term.con "num" [Term.con "number" [Term.lit "1"]]], Term.var "dim1"], Term.lit ")"], Term.con "paren" [Term.lit "(", Term.con "papp" [Term.con "shift" [Term.con "num" [Term.con "number" [Term.lit "0"]], Term.con "num" [Term.con "number" [Term.lit "2"]], q], Term.con "app" [Term.var "ix", Term.con "num" [Term.con "number" [Term.lit "0"]]]], Term.lit ")"]], Term.lit ")"]], Term.lit ")"]], Term.lit ")"], Term.con "app" [Term.var "intro", Term.con "base" []]]]]
      | _ => t

    def loopInverse (t : Term) : Term :=
      match t with
      | .con "app" [.var "loopInverse", p] => Term.con "plam" [Term.con "app" [Term.var "lit", Term.con "terminal" [Term.lit "i"]], Term.con "papp" [p, Term.con "app" [Term.var "dim_neg", Term.con "app" [Term.var "ix", Term.con "num" [Term.con "number" [Term.lit "0"]]]]]]
      | _ => t

  end LoopSpace

  section HITDispatch

    def hitHcom (t : Term) : Term :=
      match t with
      | .con "hitHcom" [.con "natHIT" [], r, r', φ, tubes, cap] => Term.con "hcomNat" [r, r', φ, tubes, cap]
      | _ => t

    def hitHcomCircle (t : Term) : Term :=
      match t with
      | .con "hitHcom" [.con "circleHIT" [], r, r', φ, tubes, cap] => Term.con "hcomCircle" [r, r', φ, tubes, cap]
      | _ => t

    def hitCoe (t : Term) : Term :=
      match t with
      | .con "hitCoe" [.con "natHIT" [], r, r', line, v] => Term.con "coeNatSimple" [r, r', v]
      | _ => t

    def hitCoeCircle (t : Term) : Term :=
      match t with
      | .con "hitCoe" [.con "circleHIT" [], r, r', line, v] => Term.con "coeCircleSimple" [r, r', v]
      | _ => t

  end HITDispatch

  section HITBoundary

    def loopBoundary0 (t : Term) : Term :=
      match t with
      | .con "app" [.var "loopBoundary", .con "app" [.var "intro", .con "app" [.var "loop", .con "dim0" []]]] => Term.con "app" [Term.var "intro", Term.con "base" []]
      | _ => t

    def loopBoundary1 (t : Term) : Term :=
      match t with
      | .con "app" [.var "loopBoundary", .con "app" [.var "intro", .con "app" [.var "loop", .con "dim1" []]]] => Term.con "app" [Term.var "intro", Term.con "base" []]
      | _ => t

    def loopBoundaryOk (t : Term) : Term :=
      match t with
      | .con "checkLoopBoundary" [.con "app" [.var "intro", .con "base" []], .con "app" [.var "intro", .con "base" []]] => Term.con "true" []
      | _ => t

    def hitCheckBoundaryNat (t : Term) : Term :=
      match t with
      | .con "hitCheckBoundary" [.con "natHIT" [], ctor, bounds] => Term.con "true" []
      | _ => t

    def hitCheckBoundaryCircle (t : Term) : Term :=
      match t with
      | .con "hitCheckBoundary" [.con "circleHIT" [], ctor, bounds] => Term.con "checkCircleBoundary" [ctor, bounds]
      | _ => t

    def checkCircleBoundary (t : Term) : Term :=
      match t with
      | .con "checkCircleBoundary" [.con "base" [], bounds] => Term.con "true" []
      | _ => t

    def checkCircleBoundaryLoop (t : Term) : Term :=
      match t with
      | .con "checkCircleBoundary" [.con "app" [.var "loop", i], bounds] => Term.con "and" [Term.con "eq" [Term.con "subst" [Term.con "num" [Term.con "number" [Term.lit "0"]], Term.con "dim0" [], bounds], Term.con "app" [Term.var "intro", Term.con "base" []]], Term.con "eq" [Term.con "subst" [Term.con "num" [Term.con "number" [Term.lit "0"]], Term.con "dim1" [], bounds], Term.con "app" [Term.var "intro", Term.con "base" []]]]
      | _ => t

  end HITBoundary

  section HITQuote

    def quoteNat (t : Term) : Term :=
      match t with
      | .con "quoteHIT" [.con "natHIT" [], .con "app" [.var "intro", .con "zero" []]] => Term.con "app" [Term.var "surface", Term.con "zero" []]
      | _ => t

    def quoteNatSucc (t : Term) : Term :=
      match t with
      | .con "quoteHIT" [.con "natHIT" [], .con "app" [.var "intro", .con "app" [.var "succ", n]]] => Term.con "app" [Term.var "surface", Term.con "app" [Term.var "succ", Term.con "quoteHIT" [Term.con "natHIT" [], n]]]
      | _ => t

    def quoteCircle (t : Term) : Term :=
      match t with
      | .con "quoteHIT" [.con "circleHIT" [], .con "app" [.var "intro", .con "base" []]] => Term.con "app" [Term.var "surface", Term.con "base" []]
      | _ => t

    def quoteCircleLoop (t : Term) : Term :=
      match t with
      | .con "quoteHIT" [.con "circleHIT" [], .con "app" [.var "intro", .con "app" [.var "loop", i]]] => Term.con "app" [Term.var "surface", Term.con "app" [Term.var "loop", Term.con "app" [Term.var "quoteDim", i]]]
      | _ => t

  end HITQuote

  section HITNormalize

    def normalizeNat (t : Term) : Term :=
      match t with
      | .con "normalizeHIT" [.con "natHIT" [], .con "app" [.var "intro", .con "zero" []]] => Term.con "app" [Term.var "intro", Term.con "zero" []]
      | _ => t

    def normalizeNatSucc (t : Term) : Term :=
      match t with
      | .con "normalizeHIT" [.con "natHIT" [], .con "app" [.var "intro", .con "app" [.var "succ", n]]] => Term.con "app" [Term.var "intro", Term.con "app" [Term.var "succ", Term.con "normalizeHIT" [Term.con "natHIT" [], n]]]
      | _ => t

    def normalizeCircle (t : Term) : Term :=
      match t with
      | .con "normalizeHIT" [.con "circleHIT" [], .con "app" [.var "intro", .con "base" []]] => Term.con "app" [Term.var "intro", Term.con "base" []]
      | _ => t

    def normalizeCircleLoop (t : Term) : Term :=
      match t with
      | .con "normalizeHIT" [.con "circleHIT" [], .con "app" [.var "intro", .con "app" [.var "loop", i]]] => Term.con "app" [Term.var "intro", Term.con "app" [Term.var "loop", Term.con "app" [Term.var "normalizeDim", i]]]
      | _ => t

    def normalizeCircleLoop0 (t : Term) : Term :=
      match t with
      | .con "normalizeHIT" [.con "circleHIT" [], .con "app" [.var "intro", .con "app" [.var "loop", .con "dim0" []]]] => Term.con "app" [Term.var "intro", Term.con "base" []]
      | _ => t

    def normalizeCircleLoop1 (t : Term) : Term :=
      match t with
      | .con "normalizeHIT" [.con "circleHIT" [], .con "app" [.var "intro", .con "app" [.var "loop", .con "dim1" []]]] => Term.con "app" [Term.var "intro", Term.con "base" []]
      | _ => t

    -- Derived substitution for term
    -- Binders: [lam, pi, sigma, plam, pathLam, extLam, let, glue]
    mutual
    partial def substterm (k : Nat) (v : Term) (t : Term) : Term :=
      match t with
      | Term.con "ix" [Term.con "number" [Term.lit n]] =>
        let idx := n.toNat!
        if idx == k then v
        else if idx > k then Term.con "ix" [Term.con "number" [Term.lit (toString (idx - 1))]]
        else t
      | Term.con tag args =>
        let isBinder := ["lam", "pi", "sigma", "plam", "pathLam", "extLam", "let", "glue"].contains tag
        if isBinder && args.length > 0 then
          Term.con tag (args.dropLast.map (substterm k v) ++ [substterm (k + 1) (shiftterm 0 1 v) args.getLast!])
        else
          Term.con tag (args.map (substterm k v))
      | _ => t
    
    partial def shiftterm (c : Nat) (n : Int) (t : Term) : Term :=
      match t with
      | Term.con "ix" [Term.con "number" [Term.lit m]] =>
        let idx := m.toNat!
        if idx >= c then Term.con "ix" [Term.con "number" [Term.lit (toString (Int.toNat (idx + n)))]]
        else t
      | Term.con tag args =>
        let isBinder := ["lam", "pi", "sigma", "plam", "pathLam", "extLam", "let", "glue"].contains tag
        if isBinder && args.length > 0 then
          Term.con tag (args.dropLast.map (shiftterm c n) ++ [shiftterm (c + 1) n args.getLast!])
        else
          Term.con tag (args.map (shiftterm c n))
      | _ => t
    end

    -- Derived normalizer for term with fuel=1000
    mutual
    partial def normalizeterm (fuel : Nat) (t : Term) : Term :=
      if fuel == 0 then t else
      let t' := stepterm t
      if t' == t then t else normalizeterm (fuel - 1) t'
    
    partial def stepterm (t : Term) : Term :=
      match t with
      | Term.con "app" [Term.con "lam" [body], arg] => substterm 0 arg body
      | Term.con "fst" [Term.con "pair" [a, _]] => a
      | Term.con "snd" [Term.con "pair" [_, b]] => b
      | Term.con tag args => Term.con tag (args.map stepterm)
      | _ => t
    end

  end HITNormalize

end HIT