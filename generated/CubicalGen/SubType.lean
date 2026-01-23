/-
  AUTO-GENERATED from .lego files
  Do not edit directly.
-/

import Lego.Algebra

set_option linter.unusedVariables false

open Lego

namespace SubType

  section SubInfo

    def subInfoBase (t : Term) : Term :=
      match t with
      | .con "app" [.var "subInfoBase", .con "subInfo" [.con "labeledArg" [.var "base", .lit ":", b], .con "labeledArg" [.var "cof", .lit ":", c], .con "labeledArg" [.var "bdry", .lit ":", d]]] => b
      | _ => t

    def subInfoCof (t : Term) : Term :=
      match t with
      | .con "app" [.var "subInfoCof", .con "subInfo" [.con "labeledArg" [.var "base", .lit ":", b], .con "labeledArg" [.var "cof", .lit ":", c], .con "labeledArg" [.var "bdry", .lit ":", d]]] => c
      | _ => t

    def subInfoBdry (t : Term) : Term :=
      match t with
      | .con "app" [.var "subInfoBdry", .con "subInfo" [.con "labeledArg" [.var "base", .lit ":", b], .con "labeledArg" [.var "cof", .lit ":", c], .con "labeledArg" [.var "bdry", .lit ":", d]]] => d
      | _ => t

    def subInfoFromExpr (t : Term) : Term :=
      match t with
      | .con "app" [.var "subInfoFromExpr", .con "sub" [ty, cof, bdry]] => Term.con "app" [Term.var "some", Term.con "subInfo" [Term.con "labeledArg" [Term.var "base", Term.lit ":", ty], Term.con "labeledArg" [Term.var "cof", Term.lit ":", cof], Term.con "labeledArg" [Term.var "bdry", Term.lit ":", bdry]]]
      | _ => t

    def subInfoFromExprOther (t : Term) : Term :=
      match t with
      | .con "app" [.var "subInfoFromExpr", e] => Term.con "none" []
      | _ => t

    def subInfoToExpr (t : Term) : Term :=
      match t with
      | .con "app" [.var "subInfoToExpr", .con "subInfo" [.con "labeledArg" [.var "base", .lit ":", b], .con "labeledArg" [.var "cof", .lit ":", c], .con "labeledArg" [.var "bdry", .lit ":", d]]] => Term.con "sub" [b, c, d]
      | _ => t

    def subInfoIsTrivial (t : Term) : Term :=
      match t with
      | .con "app" [.var "subInfoIsTrivial", .con "subInfo" [.con "labeledArg" [.var "base", .lit ":", b], .con "labeledArg" [.var "cof", .lit ":", .con "cof_top" []], .con "labeledArg" [.var "bdry", .lit ":", d]]] => Term.con "true" []
      | _ => t

    def subInfoIsTrivialOther (t : Term) : Term :=
      match t with
      | .con "app" [.var "subInfoIsTrivial", info] => Term.con "false" []
      | _ => t

    def subInfoIsImpossible (t : Term) : Term :=
      match t with
      | .con "app" [.var "subInfoIsImpossible", .con "subInfo" [.con "labeledArg" [.var "base", .lit ":", b], .con "labeledArg" [.var "cof", .lit ":", .con "cof_bot" []], .con "labeledArg" [.var "bdry", .lit ":", d]]] => Term.con "true" []
      | _ => t

    def subInfoIsImpossibleOther (t : Term) : Term :=
      match t with
      | .con "app" [.var "subInfoIsImpossible", info] => Term.con "false" []
      | _ => t

    def subInfoGetBase (t : Term) : Term :=
      match t with
      | .con "app" [.var "subInfoGetBase", info] => Term.con "app" [Term.var "subInfoBase", info]
      | _ => t

    def subInfoEvalBoundary (t : Term) : Term :=
      match t with
      | .con "subInfoEvalBoundary" [.con "subInfo" [.con "labeledArg" [.var "base", .lit ":", b], .con "labeledArg" [.var "cof", .lit ":", c], .con "labeledArg" [.var "bdry", .lit ":", d]], prf] => Term.con "subst" [Term.con "num" [Term.con "number" [Term.lit "0"]], prf, d]
      | _ => t

  end SubInfo

  section MkSub

    def mkSub (t : Term) : Term :=
      match t with
      | .con "mkSub" [baseType, cof, boundary] => Term.con "sub" [baseType, cof, boundary]
      | _ => t

    def mkSubTrivial (t : Term) : Term :=
      match t with
      | .con "mkSubTrivial" [baseType, .con "app" [.var "lam", .con "app" [.var "ix", .con "num" [.con "number" [.lit "0"]]]]] => baseType
      | _ => t

    def mkSubTrivialOther (t : Term) : Term :=
      match t with
      | .con "mkSubTrivial" [baseType, boundary] => Term.con "sub" [baseType, Term.con "cof_top" [], boundary]
      | _ => t

  end MkSub

  section MkSubIn

    def mkSubIn (t : Term) : Term :=
      match t with
      | .con "app" [.var "mkSubIn", e] => Term.con "app" [Term.var "subIn", e]
      | _ => t

    def mkSubInOut (t : Term) : Term :=
      match t with
      | .con "app" [.var "mkSubInOut", .con "app" [.var "subOut", e]] => e
      | _ => t

    def mkSubInOutOther (t : Term) : Term :=
      match t with
      | .con "app" [.var "mkSubInOutOther", e] => Term.con "app" [Term.var "subIn", e]
      | _ => t

  end MkSubIn

  section MkSubOut

    def mkSubOut (t : Term) : Term :=
      match t with
      | .con "app" [.var "mkSubOut", .con "app" [.var "subIn", inner]] => inner
      | _ => t

    def mkSubOutOther (t : Term) : Term :=
      match t with
      | .con "app" [.var "mkSubOut", e] => Term.con "app" [Term.var "subOut", e]
      | _ => t

  end MkSubOut

  section ReduceSub

    def reduceSubOut (t : Term) : Term :=
      match t with
      | .con "app" [.var "reduceSubOut", .con "app" [.var "subOut", .con "app" [.var "subIn", e]]] => Term.con "app" [Term.var "some", e]
      | _ => t

    def reduceSubOutOther (t : Term) : Term :=
      match t with
      | .con "app" [.var "reduceSubOut", e] => Term.con "none" []
      | _ => t

    def reduceSubExpr (t : Term) : Term :=
      match t with
      | .con "app" [.var "reduceSubExpr", .con "app" [.var "subOut", e]] => Term.con "caseExpr" [Term.lit "(", Term.lit "case", e, Term.con "arm" [Term.lit "(", Term.var "subIn", Term.var "inner", Term.lit ")", Term.lit "=>", Term.con "app" [Term.var "some", Term.var "inner"]], Term.con "arm" [Term.var "_", Term.lit "=>", Term.con "none" []], Term.lit ")"]
      | _ => t

    def reduceSubExprOther (t : Term) : Term :=
      match t with
      | .con "app" [.var "reduceSubExpr", e] => Term.con "none" []
      | _ => t

  end ReduceSub

  section NormalizeSub

    def normalizeSub (t : Term) : Term :=
      match t with
      | .con "normalizeSub" [.con "num" [.con "number" [.lit "0"]], e] => e
      | _ => t

    def normalizeSubStep (t : Term) : Term :=
      match t with
      | .con "normalizeSub" [.con "app" [.var "succ", fuel], e] => Term.con "caseExpr" [Term.lit "(", Term.lit "case", Term.con "app" [Term.var "reduceSubExpr", e], Term.con "arm" [Term.lit "(", Term.var "some", Term.var "e'", Term.lit ")", Term.lit "=>", Term.con "normalizeSub" [fuel, Term.var "e'"]], Term.con "arm" [Term.var "none", Term.lit "=>", Term.con "normalizeSubRec" [fuel, e]], Term.lit ")"]
      | _ => t

    def normalizeSubRec (t : Term) : Term :=
      match t with
      | .con "normalizeSubRec" [fuel, .con "sub" [ty, cof, bdry]] => Term.con "sub" [Term.con "normalizeSub" [fuel, ty], Term.con "normalizeSub" [fuel, cof], Term.con "normalizeSub" [fuel, bdry]]
      | _ => t

    def normalizeSubRecIn (t : Term) : Term :=
      match t with
      | .con "normalizeSubRec" [fuel, .con "app" [.var "subIn", inner]] => Term.con "app" [Term.var "subIn", Term.con "normalizeSub" [fuel, inner]]
      | _ => t

    def normalizeSubRecOut (t : Term) : Term :=
      match t with
      | .con "normalizeSubRec" [fuel, .con "app" [.var "subOut", inner]] => Term.con "letIn" [Term.lit "(", Term.lit "let", Term.lit "$", Term.var "inner'", Term.lit "=", Term.con "normalizeSub" [fuel, inner], Term.lit "in", Term.con "caseExpr" [Term.lit "(", Term.lit "case", Term.var "inner'", Term.con "arm" [Term.lit "(", Term.var "subIn", Term.var "x", Term.lit ")", Term.lit "=>", Term.var "x"], Term.con "arm" [Term.var "_", Term.lit "=>", Term.con "app" [Term.var "subOut", Term.var "inner'"]], Term.lit ")"], Term.lit ")"]
      | _ => t

    def normalizeSubRecOther (t : Term) : Term :=
      match t with
      | .con "normalizeSubRec" [fuel, e] => e
      | _ => t

  end NormalizeSub

  section TrivialSub

    def trivialSubEquiv (t : Term) : Term :=
      match t with
      | .con "app" [.var "trivialSubEquiv", ty] => Term.con "mkSub" [ty, Term.con "cof_top" [Term.con "paren" [Term.lit "(", Term.con "lam" [Term.con "app" [Term.var "ix", Term.con "num" [Term.con "number" [Term.lit "0"]]]], Term.lit ")"]]]
      | _ => t

  end TrivialSub

  section ImpossibleSub

    def impossibleSub (t : Term) : Term :=
      match t with
      | .con "app" [.var "impossibleSub", ty] => Term.con "mkSub" [ty, Term.con "cof_bot" [Term.con "paren" [Term.lit "(", Term.con "lam" [Term.con "app" [Term.var "lit", Term.con "terminal" [Term.lit "⊥-elim"]]], Term.lit ")"]]]
      | _ => t

  end ImpossibleSub

  section SubTypeEquiv

    def subTypeEquiv (t : Term) : Term :=
      match t with
      | .con "subTypeEquiv" [s1, s2] => Term.con "and" [Term.con "conv" [Term.con "app" [Term.var "subInfoBase", s1], Term.con "app" [Term.var "subInfoBase", s2]], Term.con "and" [Term.con "conv" [Term.con "app" [Term.var "subInfoCof", s1], Term.con "app" [Term.var "subInfoCof", s2]], Term.con "conv" [Term.con "app" [Term.var "subInfoBdry", s1], Term.con "app" [Term.var "subInfoBdry", s2]]]]
      | _ => t

  end SubTypeEquiv

  section SubKan

    def coeSub (t : Term) : Term :=
      match t with
      | .con "coeSub" [r, r', .con "app" [.var "lam", .con "sub" [A, φ, t]], .con "app" [.var "subIn", v]] => Term.con "app" [Term.var "subIn", Term.con "coe" [r, r', Term.con "app" [Term.var "lam", A], v]]
      | _ => t

    def coeSubStuck (t : Term) : Term :=
      match t with
      | .con "coeSub" [r, r', line, v] => Term.con "coe" [r, r', line, v]
      | _ => t

    def hcomSub (t : Term) : Term :=
      match t with
      | .con "hcomSub" [.con "sub" [A, φ, t], r, r', ψ, tubes, .con "app" [.var "subIn", cap]] => Term.con "app" [Term.var "subIn", Term.con "hcom" [A, r, r', ψ, Term.con "app" [Term.var "mapSubOut", tubes], cap]]
      | _ => t

    def hcomSubStuck (t : Term) : Term :=
      match t with
      | .con "hcomSub" [subTy, r, r', ψ, tubes, cap] => Term.con "hcom" [subTy, r, r', ψ, tubes, cap]
      | _ => t

    def mapSubOut (t : Term) : Term :=
      match t with
      | .con "app" [.var "mapSubOut", .con "app" [.var "lam", .con "app" [.var "lam", body]]] => Term.con "app" [Term.var "lam", Term.con "app" [Term.var "lam", Term.con "app" [Term.var "subOut", body]]]
      | _ => t

  end SubKan

  section SubBoundaryCheck

    def checkSubBoundary (t : Term) : Term :=
      match t with
      | .con "checkSubBoundary" [e, .con "subInfo" [.con "labeledArg" [.var "base", .lit ":", A], .con "labeledArg" [.var "cof", .lit ":", φ], .con "labeledArg" [.var "bdry", .lit ":", t]]] => Term.con "caseExpr" [Term.lit "(", Term.lit "case", φ, Term.con "arm" [Term.var "cof_bot", Term.lit "=>", Term.con "true" []], Term.con "arm" [Term.var "cof_top", Term.lit "=>", Term.con "conv" [e, Term.con "subst" [Term.con "num" [Term.con "number" [Term.lit "0"]], Term.con "app" [Term.var "lit", Term.con "terminal" [Term.lit "trivial"]], t]]], Term.con "arm" [Term.var "_", Term.lit "=>", Term.con "checkSubBoundaryGeneral" [e, φ, t]], Term.lit ")"]
      | _ => t

    def checkSubBoundaryGeneral (t : Term) : Term :=
      match t with
      | .con "checkSubBoundaryGeneral" [e, φ, t] => Term.con "true" []
      | _ => t

  end SubBoundaryCheck

  section SubPartial

    def partialToSub (t : Term) : Term :=
      match t with
      | .con "partialToSub" [A, φ, partial_] => Term.con "sub" [A, φ, partial_]
      | _ => t

    def subToPartial (t : Term) : Term :=
      match t with
      | .con "app" [.var "subToPartial", .con "sub" [A, φ, bdry]] => bdry
      | _ => t

  end SubPartial

  section ExtIntegration

    def extAsSub (t : Term) : Term :=
      match t with
      | .con "extAsSub" [dim, A, φ, bdry] => Term.con "pi" [dim, Term.con "sub" [Term.con "app" [Term.con "shift" [Term.con "num" [Term.con "number" [Term.lit "0"]], Term.con "num" [Term.con "number" [Term.lit "1"]], A], Term.con "app" [Term.var "ix", Term.con "num" [Term.con "number" [Term.lit "0"]]]], Term.con "app" [Term.con "shift" [Term.con "num" [Term.con "number" [Term.lit "0"]], Term.con "num" [Term.con "number" [Term.lit "1"]], φ], Term.con "app" [Term.var "ix", Term.con "num" [Term.con "number" [Term.lit "0"]]]], Term.con "app" [Term.con "shift" [Term.con "num" [Term.con "number" [Term.lit "0"]], Term.con "num" [Term.con "number" [Term.lit "1"]], bdry], Term.con "app" [Term.var "ix", Term.con "num" [Term.con "number" [Term.lit "0"]]]]]]
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

  end ExtIntegration

end SubType