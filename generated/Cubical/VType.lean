/-
  AUTO-GENERATED from .lego files
  Do not edit directly.
-/

import Lego.Algebra

open Lego

namespace VType

  section VTypeInfo

    def vtypeInfoDim (t : Term) : Term :=
      match t with
      | .con "app" [.var "vtypeInfoDim", .con "vtypeInfo" [.con "labeledArg" [.var "dim", .lit ":", d], .con "labeledArg" [.var "ty0", .lit ":", a], .con "labeledArg" [.var "ty1", .lit ":", b], .con "labeledArg" [.var "equiv", .lit ":", e]]] => d
      | _ => t

    def vtypeInfoTy0 (t : Term) : Term :=
      match t with
      | .con "app" [.var "vtypeInfoTy0", .con "vtypeInfo" [.con "labeledArg" [.var "dim", .lit ":", d], .con "labeledArg" [.var "ty0", .lit ":", a], .con "labeledArg" [.var "ty1", .lit ":", b], .con "labeledArg" [.var "equiv", .lit ":", e]]] => a
      | _ => t

    def vtypeInfoTy1 (t : Term) : Term :=
      match t with
      | .con "app" [.var "vtypeInfoTy1", .con "vtypeInfo" [.con "labeledArg" [.var "dim", .lit ":", d], .con "labeledArg" [.var "ty0", .lit ":", a], .con "labeledArg" [.var "ty1", .lit ":", b], .con "labeledArg" [.var "equiv", .lit ":", e]]] => b
      | _ => t

    def vtypeInfoEquiv (t : Term) : Term :=
      match t with
      | .con "app" [.var "vtypeInfoEquiv", .con "vtypeInfo" [.con "labeledArg" [.var "dim", .lit ":", d], .con "labeledArg" [.var "ty0", .lit ":", a], .con "labeledArg" [.var "ty1", .lit ":", b], .con "labeledArg" [.var "equiv", .lit ":", e]]] => e
      | _ => t

    def vtypeInfoAtDim0 (t : Term) : Term :=
      match t with
      | .con "app" [.var "vtypeInfoAtDim0", .con "vtypeInfo" [.con "labeledArg" [.var "dim", .lit ":", .con "dim0" []], .con "labeledArg" [.var "ty0", .lit ":", a], .con "labeledArg" [.var "ty1", .lit ":", b], .con "labeledArg" [.var "equiv", .lit ":", e]]] => Term.con "true" []
      | _ => t

    def vtypeInfoAtDim0Other (t : Term) : Term :=
      match t with
      | .con "app" [.var "vtypeInfoAtDim0", info] => Term.con "false" []
      | _ => t

    def vtypeInfoAtDim1 (t : Term) : Term :=
      match t with
      | .con "app" [.var "vtypeInfoAtDim1", .con "vtypeInfo" [.con "labeledArg" [.var "dim", .lit ":", .con "dim1" []], .con "labeledArg" [.var "ty0", .lit ":", a], .con "labeledArg" [.var "ty1", .lit ":", b], .con "labeledArg" [.var "equiv", .lit ":", e]]] => Term.con "true" []
      | _ => t

    def vtypeInfoAtDim1Other (t : Term) : Term :=
      match t with
      | .con "app" [.var "vtypeInfoAtDim1", info] => Term.con "false" []
      | _ => t

    def vtypeInfoReduce (t : Term) : Term :=
      match t with
      | .con "app" [.var "vtypeInfoReduce", .con "vtypeInfo" [.con "labeledArg" [.var "dim", .lit ":", .con "dim0" []], .con "labeledArg" [.var "ty0", .lit ":", a], .con "labeledArg" [.var "ty1", .lit ":", b], .con "labeledArg" [.var "equiv", .lit ":", e]]] => Term.con "app" [Term.var "some", a]
      | _ => t

    def vtypeInfoReduce1 (t : Term) : Term :=
      match t with
      | .con "app" [.var "vtypeInfoReduce", .con "vtypeInfo" [.con "labeledArg" [.var "dim", .lit ":", .con "dim1" []], .con "labeledArg" [.var "ty0", .lit ":", a], .con "labeledArg" [.var "ty1", .lit ":", b], .con "labeledArg" [.var "equiv", .lit ":", e]]] => Term.con "app" [Term.var "some", b]
      | _ => t

    def vtypeInfoReduceOther (t : Term) : Term :=
      match t with
      | .con "app" [.var "vtypeInfoReduce", info] => Term.con "none" []
      | _ => t

  end VTypeInfo

  section VInInfo

    def vinInfoDim (t : Term) : Term :=
      match t with
      | .con "app" [.var "vinInfoDim", .con "vinInfo" [.con "labeledArg" [.var "dim", .lit ":", d], .con "labeledArg" [.var "tm0", .lit ":", a], .con "labeledArg" [.var "tm1", .lit ":", b]]] => d
      | _ => t

    def vinInfoTm0 (t : Term) : Term :=
      match t with
      | .con "app" [.var "vinInfoTm0", .con "vinInfo" [.con "labeledArg" [.var "dim", .lit ":", d], .con "labeledArg" [.var "tm0", .lit ":", a], .con "labeledArg" [.var "tm1", .lit ":", b]]] => a
      | _ => t

    def vinInfoTm1 (t : Term) : Term :=
      match t with
      | .con "app" [.var "vinInfoTm1", .con "vinInfo" [.con "labeledArg" [.var "dim", .lit ":", d], .con "labeledArg" [.var "tm0", .lit ":", a], .con "labeledArg" [.var "tm1", .lit ":", b]]] => b
      | _ => t

    def vinInfoAtDim0 (t : Term) : Term :=
      match t with
      | .con "app" [.var "vinInfoAtDim0", .con "vinInfo" [.con "labeledArg" [.var "dim", .lit ":", .con "dim0" []], .con "labeledArg" [.var "tm0", .lit ":", a], .con "labeledArg" [.var "tm1", .lit ":", b]]] => Term.con "true" []
      | _ => t

    def vinInfoAtDim0Other (t : Term) : Term :=
      match t with
      | .con "app" [.var "vinInfoAtDim0", info] => Term.con "false" []
      | _ => t

    def vinInfoAtDim1 (t : Term) : Term :=
      match t with
      | .con "app" [.var "vinInfoAtDim1", .con "vinInfo" [.con "labeledArg" [.var "dim", .lit ":", .con "dim1" []], .con "labeledArg" [.var "tm0", .lit ":", a], .con "labeledArg" [.var "tm1", .lit ":", b]]] => Term.con "true" []
      | _ => t

    def vinInfoAtDim1Other (t : Term) : Term :=
      match t with
      | .con "app" [.var "vinInfoAtDim1", info] => Term.con "false" []
      | _ => t

    def vinInfoReduce (t : Term) : Term :=
      match t with
      | .con "app" [.var "vinInfoReduce", .con "vinInfo" [.con "labeledArg" [.var "dim", .lit ":", .con "dim0" []], .con "labeledArg" [.var "tm0", .lit ":", a], .con "labeledArg" [.var "tm1", .lit ":", b]]] => Term.con "app" [Term.var "some", a]
      | _ => t

    def vinInfoReduce1 (t : Term) : Term :=
      match t with
      | .con "app" [.var "vinInfoReduce", .con "vinInfo" [.con "labeledArg" [.var "dim", .lit ":", .con "dim1" []], .con "labeledArg" [.var "tm0", .lit ":", a], .con "labeledArg" [.var "tm1", .lit ":", b]]] => Term.con "app" [Term.var "some", b]
      | _ => t

    def vinInfoReduceOther (t : Term) : Term :=
      match t with
      | .con "app" [.var "vinInfoReduce", info] => Term.con "none" []
      | _ => t

  end VInInfo

  section Equivalence

    def equivFunc (t : Term) : Term :=
      match t with
      | .con "app" [.var "equivFunc", e] => Term.con "app" [Term.var "fst", e]
      | _ => t

    def equivInv (t : Term) : Term :=
      match t with
      | .con "app" [.var "equivInv", e] => Term.con "app" [Term.var "fst", Term.con "app" [Term.var "snd", e]]
      | _ => t

    def isEquiv (t : Term) : Term :=
      match t with
      | .con "app" [.var "isEquiv", .con "pair" [f, .con "pair" [g, proofs]]] => Term.con "true" []
      | _ => t

    def isEquivOther (t : Term) : Term :=
      match t with
      | .con "app" [.var "isEquiv", e] => Term.con "false" []
      | _ => t

  end Equivalence

  section MkVType

    def mkVType (t : Term) : Term :=
      match t with
      | .con "mkVType" [.con "dim0" [], A, B, e] => A
      | _ => t

    def mkVType1 (t : Term) : Term :=
      match t with
      | .con "mkVType" [.con "dim1" [], A, B, e] => B
      | _ => t

    def mkVTypeOther (t : Term) : Term :=
      match t with
      | .con "mkVType" [r, A, B, e] => Term.con "vtype" [r, A, B, e]
      | _ => t

  end MkVType

  section MkVIn

    def mkVIn (t : Term) : Term :=
      match t with
      | .con "mkVIn" [.con "dim0" [], a, b] => a
      | _ => t

    def mkVIn1 (t : Term) : Term :=
      match t with
      | .con "mkVIn" [.con "dim1" [], a, b] => b
      | _ => t

    def mkVInOther (t : Term) : Term :=
      match t with
      | .con "mkVIn" [r, a, b] => Term.con "vin" [r, a, b]
      | _ => t

  end MkVIn

  section ReduceVProj

    def reduceVProj0 (t : Term) : Term :=
      match t with
      | .con "reduceVProj" [.con "dim0" [], ty0, ty1, equiv, el] => Term.con "app" [Term.con "app" [Term.var "equivFunc", equiv], el]
      | _ => t

    def reduceVProj1 (t : Term) : Term :=
      match t with
      | .con "reduceVProj" [.con "dim1" [], ty0, ty1, equiv, el] => el
      | _ => t

    def reduceVProjVin (t : Term) : Term :=
      match t with
      | .con "reduceVProj" [r, ty0, ty1, equiv, .con "vin" [r', a, b]] => Term.con "caseExpr" [Term.lit "(", Term.lit "case", Term.con "eq" [r, r'], Term.con "arm" [Term.var "true", Term.lit "=>", b], Term.con "arm" [Term.var "false", Term.lit "=>", Term.con "vproj" [r, ty0, ty1, equiv, Term.con "vin" [r', a, b]]], Term.lit ")"]
      | _ => t

    def reduceVProjOther (t : Term) : Term :=
      match t with
      | .con "reduceVProj" [r, ty0, ty1, equiv, el] => Term.con "vproj" [r, ty0, ty1, equiv, el]
      | _ => t

  end ReduceVProj

  section CoeV

    def coeV (t : Term) : Term :=
      match t with
      | .con "coeV" [dir, .con "vtypeInfo" [.con "labeledArg" [.var "dim", .lit ":", d], .con "labeledArg" [.var "ty0", .lit ":", A], .con "labeledArg" [.var "ty1", .lit ":", B], .con "labeledArg" [.var "equiv", .lit ":", e]], el] => Term.con "caseExpr" [Term.lit "(", Term.lit "case", Term.con "app" [Term.var "dirIsDegenerate", dir], Term.con "arm" [Term.var "true", Term.lit "=>", el], Term.con "arm" [Term.var "false", Term.lit "=>", Term.con "coeVBody" [dir, d, A, B, e, el]], Term.lit ")"]
      | _ => t

    def dirIsDegenerate (t : Term) : Term :=
      match t with
      | .con "app" [.var "dirIsDegenerate", .con "dir" [r, r_dup]] => Term.con "true" []
      | _ => t

    def dirIsDegenerateOther (t : Term) : Term :=
      match t with
      | .con "app" [.var "dirIsDegenerate", dir] => Term.con "false" []
      | _ => t

    def coeVBody (t : Term) : Term :=
      match t with
      | .con "coeVBody" [.con "dir" [r, r'], d, A, B, e, el] => Term.con "mkVIn" [r', Term.con "coe" [r, r', Term.con "app" [Term.var "lam", A], Term.con "caseExpr" [Term.lit "(", Term.lit "case", el, Term.con "arm" [Term.lit "(", Term.var "vin", Term.var "_", Term.var "a", Term.var "_", Term.lit ")", Term.lit "=>", Term.var "a"], Term.con "arm" [Term.var "_", Term.lit "=>", el], Term.lit ")"]], Term.con "coe" [r, r', Term.con "app" [Term.var "lam", B], Term.con "caseExpr" [Term.lit "(", Term.lit "case", el, Term.con "arm" [Term.lit "(", Term.var "vin", Term.var "_", Term.var "_", Term.var "b", Term.lit ")", Term.lit "=>", Term.var "b"], Term.con "arm" [Term.var "_", Term.lit "=>", Term.con "app" [Term.con "app" [Term.var "equivFunc", e], el]], Term.lit ")"]]]
      | _ => t

  end CoeV

  section HComV

    def hcomV (t : Term) : Term :=
      match t with
      | .con "hcomV" [.con "vtype" [d, A, B, e], r, r', φ, tubes, cap] => Term.con "mkVIn" [d, Term.con "hcom" [A, r, r', φ, Term.con "app" [Term.var "lam", Term.con "app" [Term.var "lam", Term.con "app" [Term.var "vinProj0", Term.con "app" [Term.con "app" [Term.con "shift" [Term.con "num" [Term.con "number" [Term.lit "0"]], Term.con "num" [Term.con "number" [Term.lit "2"]], tubes], Term.con "app" [Term.var "ix", Term.con "num" [Term.con "number" [Term.lit "1"]]]], Term.con "app" [Term.var "ix", Term.con "num" [Term.con "number" [Term.lit "0"]]]]]]], Term.con "app" [Term.var "vinProj0", cap]], Term.con "hcom" [B, r, r', Term.con "cof_disj" [φ, Term.con "cof_eq" [d, Term.con "dim0" []]], Term.con "app" [Term.var "lam", Term.con "app" [Term.var "lam", Term.con "caseCof" [Term.con "app" [Term.var "ix", Term.con "num" [Term.con "number" [Term.lit "1"]]], Term.con "tuple" [φ, Term.lit "=>", Term.con "app" [Term.var "vinProj1", Term.con "app" [Term.con "app" [Term.con "shift" [Term.con "num" [Term.con "number" [Term.lit "0"]], Term.con "num" [Term.con "number" [Term.lit "2"]], tubes], Term.con "app" [Term.var "ix", Term.con "num" [Term.con "number" [Term.lit "1"]]]], Term.con "app" [Term.var "ix", Term.con "num" [Term.con "number" [Term.lit "0"]]]]]], Term.con "tuple" [Term.con "app" [Term.lit "(", Term.con "cof_eq" [], d, Term.con "dim0" [], Term.lit ")"], Term.lit "=>", Term.con "app" [Term.con "app" [Term.var "equivFunc", e], Term.con "app" [Term.var "vinProj0", Term.con "app" [Term.con "app" [Term.con "shift" [Term.con "num" [Term.con "number" [Term.lit "0"]], Term.con "num" [Term.con "number" [Term.lit "2"]], tubes], Term.con "app" [Term.var "ix", Term.con "num" [Term.con "number" [Term.lit "1"]]]], Term.con "app" [Term.var "ix", Term.con "num" [Term.con "number" [Term.lit "0"]]]]]]]]]], Term.con "app" [Term.var "vinProj1", cap]]]
      | _ => t

    def vinProj0 (t : Term) : Term :=
      match t with
      | .con "app" [.var "vinProj0", .con "vin" [d, a, b]] => a
      | _ => t

    def vinProj0Other (t : Term) : Term :=
      match t with
      | .con "app" [.var "vinProj0", e] => e
      | _ => t

    def vinProj1 (t : Term) : Term :=
      match t with
      | .con "app" [.var "vinProj1", .con "vin" [d, a, b]] => b
      | _ => t

    def vinProj1Other (t : Term) : Term :=
      match t with
      | .con "app" [.var "vinProj1", e] => e
      | _ => t

  end HComV

  section Univalence

    def ua (t : Term) : Term :=
      match t with
      | .con "ua" [A, B, e] => Term.con "plam" [Term.con "app" [Term.var "lit", Term.con "terminal" [Term.lit "i"]], Term.con "vtype" [Term.con "app" [Term.var "ix", Term.con "num" [Term.con "number" [Term.lit "0"]]], Term.con "shift" [Term.con "num" [Term.con "number" [Term.lit "0"]], Term.con "num" [Term.con "number" [Term.lit "1"]], A], Term.con "shift" [Term.con "num" [Term.con "number" [Term.lit "0"]], Term.con "num" [Term.con "number" [Term.lit "1"]], B], Term.con "shift" [Term.con "num" [Term.con "number" [Term.lit "0"]], Term.con "num" [Term.con "number" [Term.lit "1"]], e]]]
      | _ => t

    def idEquiv (t : Term) : Term :=
      match t with
      | .con "app" [.var "idEquiv", A] => Term.con "pair" [Term.con "app" [Term.var "lam", Term.con "app" [Term.var "ix", Term.con "num" [Term.con "number" [Term.lit "0"]]]], Term.con "pair" [Term.con "app" [Term.var "lam", Term.con "app" [Term.var "ix", Term.con "num" [Term.con "number" [Term.lit "0"]]]], Term.con "pair" [Term.con "app" [Term.var "lam", Term.con "refl" []], Term.con "pair" [Term.con "app" [Term.var "lam", Term.con "refl" []], Term.con "app" [Term.var "lit", Term.con "terminal" [Term.lit "contractible-fibers"]]]]]]
      | _ => t

    def uaβ (t : Term) : Term :=
      match t with
      | .con "uaβ" [e, a] => Term.con "coe" [Term.con "dim0" [], Term.con "dim1" [Term.con "ua" [Term.con "app" [Term.var "typeOf", a], Term.con "app" [Term.var "codomain", e], e]], a]
      | _ => t

    def uaη (t : Term) : Term :=
      match t with
      | .con "app" [.var "uaη", A] => Term.con "plam" [Term.con "app" [Term.var "lit", Term.con "terminal" [Term.lit "_"]], A]
      | _ => t

  end Univalence

  section VTypeQuote

    def quoteVType (t : Term) : Term :=
      match t with
      | .con "app" [.var "quoteVType", .con "vtype" [r, A, B, e]] => Term.con "app" [Term.var "surface", Term.con "tuple" [Term.con "string" [Term.lit "V"], Term.con "app" [Term.var "quoteDim", r], Term.con "app" [Term.var "quote", A], Term.con "app" [Term.var "quote", B], Term.con "app" [Term.var "quote", e]]]
      | _ => t

    def quoteVIn (t : Term) : Term :=
      match t with
      | .con "app" [.var "quoteVIn", .con "vin" [r, a, b]] => Term.con "app" [Term.var "surface", Term.con "tuple" [Term.con "string" [Term.lit "vin"], Term.con "app" [Term.var "quoteDim", r], Term.con "app" [Term.var "quote", a], Term.con "app" [Term.var "quote", b]]]
      | _ => t

    def quoteVProj (t : Term) : Term :=
      match t with
      | .con "app" [.var "quoteVProj", .con "vproj" [r, A, B, e, v]] => Term.con "app" [Term.var "surface", Term.con "tuple" [Term.con "string" [Term.lit "vproj"], Term.con "app" [Term.var "quoteDim", r], Term.con "app" [Term.var "quote", v]]]
      | _ => t

  end VTypeQuote

  section VTypeNormalize

    def normalizeVType (t : Term) : Term :=
      match t with
      | .con "app" [.var "normalizeVType", .con "vtype" [.con "dim0" [], A, B, e]] => A
      | _ => t

    def normalizeVType1 (t : Term) : Term :=
      match t with
      | .con "app" [.var "normalizeVType", .con "vtype" [.con "dim1" [], A, B, e]] => B
      | _ => t

    def normalizeVTypeOther (t : Term) : Term :=
      match t with
      | .con "app" [.var "normalizeVType", .con "vtype" [r, A, B, e]] => Term.con "vtype" [Term.con "app" [Term.var "normalizeDim", r], Term.con "app" [Term.var "normalize", A], Term.con "app" [Term.var "normalize", B], Term.con "app" [Term.var "normalize", e]]
      | _ => t

    def normalizeVIn (t : Term) : Term :=
      match t with
      | .con "app" [.var "normalizeVIn", .con "vin" [.con "dim0" [], a, b]] => a
      | _ => t

    def normalizeVIn1 (t : Term) : Term :=
      match t with
      | .con "app" [.var "normalizeVIn", .con "vin" [.con "dim1" [], a, b]] => b
      | _ => t

    def normalizeVInOther (t : Term) : Term :=
      match t with
      | .con "app" [.var "normalizeVIn", .con "vin" [r, a, b]] => Term.con "vin" [Term.con "app" [Term.var "normalizeDim", r], Term.con "app" [Term.var "normalize", a], Term.con "app" [Term.var "normalize", b]]
      | _ => t

    def normalizeVProj (t : Term) : Term :=
      match t with
      | .con "app" [.var "normalizeVProj", .con "vproj" [.con "dim0" [], A, B, e, v]] => Term.con "app" [Term.con "app" [Term.var "equivFunc", e], v]
      | _ => t

    def normalizeVProj1 (t : Term) : Term :=
      match t with
      | .con "app" [.var "normalizeVProj", .con "vproj" [.con "dim1" [], A, B, e, v]] => v
      | _ => t

    def normalizeVProjVin (t : Term) : Term :=
      match t with
      | .con "app" [.var "normalizeVProj", .con "vproj" [r, A, B, e, .con "vin" [r_dup, a, b]]] => b
      | _ => t

    def normalizeVProjOther (t : Term) : Term :=
      match t with
      | .con "app" [.var "normalizeVProj", .con "vproj" [r, A, B, e, v]] => Term.con "vproj" [Term.con "app" [Term.var "normalizeDim", r], Term.con "app" [Term.var "normalize", A], Term.con "app" [Term.var "normalize", B], Term.con "app" [Term.var "normalize", e], Term.con "app" [Term.var "normalize", v]]
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

  end VTypeNormalize

end VType