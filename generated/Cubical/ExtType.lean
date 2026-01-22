/-
  AUTO-GENERATED from .lego files
  Do not edit directly.
-/

import Lego.Algebra

open Lego

namespace ExtType

  section ExtInfo

    def extInfoArity (t : Term) : Term :=
      match t with
      | .con "app" [.var "extInfoArity", .con "extInfo" [.con "labeledArg" [.var "arity", .lit ":", n], .con "labeledArg" [.var "family", .lit ":", f], .con "labeledArg" [.var "cof", .lit ":", c], .con "labeledArg" [.var "boundary", .lit ":", b]]] => n
      | _ => t

    def extInfoFamily (t : Term) : Term :=
      match t with
      | .con "app" [.var "extInfoFamily", .con "extInfo" [.con "labeledArg" [.var "arity", .lit ":", n], .con "labeledArg" [.var "family", .lit ":", f], .con "labeledArg" [.var "cof", .lit ":", c], .con "labeledArg" [.var "boundary", .lit ":", b]]] => f
      | _ => t

    def extInfoCof (t : Term) : Term :=
      match t with
      | .con "app" [.var "extInfoCof", .con "extInfo" [.con "labeledArg" [.var "arity", .lit ":", n], .con "labeledArg" [.var "family", .lit ":", f], .con "labeledArg" [.var "cof", .lit ":", c], .con "labeledArg" [.var "boundary", .lit ":", b]]] => c
      | _ => t

    def extInfoBoundary (t : Term) : Term :=
      match t with
      | .con "app" [.var "extInfoBoundary", .con "extInfo" [.con "labeledArg" [.var "arity", .lit ":", n], .con "labeledArg" [.var "family", .lit ":", f], .con "labeledArg" [.var "cof", .lit ":", c], .con "labeledArg" [.var "boundary", .lit ":", b]]] => b
      | _ => t

    def extInfoFromExpr (t : Term) : Term :=
      match t with
      | .con "app" [.var "extInfoFromExpr", .con "ext" [n, fam, cof, bdry]] => Term.con "app" [Term.var "some", Term.con "extInfo" [Term.con "labeledArg" [Term.var "arity", Term.lit ":", n], Term.con "labeledArg" [Term.var "family", Term.lit ":", fam], Term.con "labeledArg" [Term.var "cof", Term.lit ":", cof], Term.con "labeledArg" [Term.var "boundary", Term.lit ":", bdry]]]
      | _ => t

    def extInfoFromExprOther (t : Term) : Term :=
      match t with
      | .con "app" [.var "extInfoFromExpr", e] => Term.con "none" []
      | _ => t

    def extInfoToExpr (t : Term) : Term :=
      match t with
      | .con "app" [.var "extInfoToExpr", .con "extInfo" [.con "labeledArg" [.var "arity", .lit ":", n], .con "labeledArg" [.var "family", .lit ":", f], .con "labeledArg" [.var "cof", .lit ":", c], .con "labeledArg" [.var "boundary", .lit ":", b]]] => Term.con "ext" [n, f, c, b]
      | _ => t

    def extInfoIsNullary (t : Term) : Term :=
      match t with
      | .con "app" [.var "extInfoIsNullary", .con "extInfo" [.con "labeledArg" [.var "arity", .lit ":", .con "num" [.con "number" [.lit "0"]]], .con "labeledArg" [.var "family", .lit ":", f], .con "labeledArg" [.var "cof", .lit ":", c], .con "labeledArg" [.var "boundary", .lit ":", b]]] => Term.con "true" []
      | _ => t

    def extInfoIsNullaryN (t : Term) : Term :=
      match t with
      | .con "app" [.var "extInfoIsNullary", .con "extInfo" [.con "labeledArg" [.var "arity", .lit ":", n], .con "labeledArg" [.var "family", .lit ":", f], .con "labeledArg" [.var "cof", .lit ":", c], .con "labeledArg" [.var "boundary", .lit ":", b]]] => Term.con "false" []
      | _ => t

    def extInfoHasTrivialBoundary (t : Term) : Term :=
      match t with
      | .con "app" [.var "extInfoHasTrivialBoundary", .con "extInfo" [.con "labeledArg" [.var "arity", .lit ":", n], .con "labeledArg" [.var "family", .lit ":", f], .con "labeledArg" [.var "cof", .lit ":", .con "cof_bot" []], .con "labeledArg" [.var "boundary", .lit ":", b]]] => Term.con "true" []
      | _ => t

    def extInfoHasTrivialBoundaryOther (t : Term) : Term :=
      match t with
      | .con "app" [.var "extInfoHasTrivialBoundary", .con "extInfo" [.con "labeledArg" [.var "arity", .lit ":", n], .con "labeledArg" [.var "family", .lit ":", f], .con "labeledArg" [.var "cof", .lit ":", c], .con "labeledArg" [.var "boundary", .lit ":", b]]] => Term.con "false" []
      | _ => t

  end ExtInfo

  section ApplyDims

    def applyFamily (t : Term) : Term :=
      match t with
      | .con "applyFamily" [.con "extInfo" [.con "labeledArg" [.var "arity", .lit ":", n], .con "labeledArg" [.var "family", .lit ":", f], .con "labeledArg" [.var "cof", .lit ":", c], .con "labeledArg" [.var "boundary", .lit ":", b]], dims] => Term.con "caseExpr" [Term.lit "(", Term.lit "case", Term.con "eq" [Term.con "app" [Term.var "length", dims], n], Term.con "arm" [Term.var "true", Term.lit "=>", Term.con "foldr" [Term.con "fun" [Term.con "dim" [], Term.con "acc" [], Term.lit "=>", Term.con "subst" [Term.con "num" [Term.con "number" [Term.lit "0"]], Term.con "dim" [], Term.con "acc" []]], f, dims]], Term.con "arm" [Term.var "false", Term.lit "=>", f], Term.lit ")"]
      | _ => t

    def applyCof (t : Term) : Term :=
      match t with
      | .con "applyCof" [.con "extInfo" [.con "labeledArg" [.var "arity", .lit ":", n], .con "labeledArg" [.var "family", .lit ":", f], .con "labeledArg" [.var "cof", .lit ":", c], .con "labeledArg" [.var "boundary", .lit ":", b]], dims] => Term.con "caseExpr" [Term.lit "(", Term.lit "case", Term.con "eq" [Term.con "app" [Term.var "length", dims], n], Term.con "arm" [Term.var "true", Term.lit "=>", Term.con "foldr" [Term.con "fun" [Term.con "dim" [], Term.con "acc" [], Term.lit "=>", Term.con "subst" [Term.con "num" [Term.con "number" [Term.lit "0"]], Term.con "dim" [], Term.con "acc" []]], c, dims]], Term.con "arm" [Term.var "false", Term.lit "=>", c], Term.lit ")"]
      | _ => t

    def applyBoundary (t : Term) : Term :=
      match t with
      | .con "applyBoundary" [.con "extInfo" [.con "labeledArg" [.var "arity", .lit ":", n], .con "labeledArg" [.var "family", .lit ":", f], .con "labeledArg" [.var "cof", .lit ":", c], .con "labeledArg" [.var "boundary", .lit ":", b]], dims] => Term.con "caseExpr" [Term.lit "(", Term.lit "case", Term.con "eq" [Term.con "app" [Term.var "length", dims], n], Term.con "arm" [Term.var "true", Term.lit "=>", Term.con "foldr" [Term.con "fun" [Term.con "dim" [], Term.con "acc" [], Term.lit "=>", Term.con "subst" [Term.con "num" [Term.con "number" [Term.lit "0"]], Term.con "dim" [], Term.con "acc" []]], b, dims]], Term.con "arm" [Term.var "false", Term.lit "=>", b], Term.lit ")"]
      | _ => t

  end ApplyDims

  section MkExt

    def mkExt (t : Term) : Term :=
      match t with
      | .con "mkExt" [arity, fam, cof, bdry] => Term.con "caseExpr" [Term.lit "(", Term.lit "case", cof, Term.con "arm" [Term.var "cof_bot", Term.lit "=>", Term.con "ext" [arity, fam, Term.con "cof_bot" [], bdry]], Term.con "arm" [Term.var "cof_top", Term.lit "=>", Term.con "ext" [arity, fam, Term.con "cof_top" [], bdry]], Term.con "arm" [Term.var "_", Term.lit "=>", Term.con "ext" [arity, fam, cof, bdry]], Term.lit ")"]
      | _ => t

  end MkExt

  section MkExtLam

    def mkExtLam (t : Term) : Term :=
      match t with
      | .con "mkExtLam" [arity, body] => Term.con "extLam" [arity, body]
      | _ => t

  end MkExtLam

  section MkExtApp

    def mkExtApp (t : Term) : Term :=
      match t with
      | .con "mkExtApp" [.con "extLam" [n, body], dims] => Term.con "caseExpr" [Term.lit "(", Term.lit "case", Term.con "eq" [Term.con "app" [Term.var "length", dims], n], Term.con "arm" [Term.var "true", Term.lit "=>", Term.con "foldr" [Term.con "fun" [Term.con "dim" [], Term.con "acc" [], Term.lit "=>", Term.con "subst" [Term.con "num" [Term.con "number" [Term.lit "0"]], Term.con "dim" [], Term.con "acc" []]], body, dims]], Term.con "arm" [Term.var "false", Term.lit "=>", Term.con "extApp" [Term.con "extLam" [n, body], dims]], Term.lit ")"]
      | _ => t

    def mkExtAppOther (t : Term) : Term :=
      match t with
      | .con "mkExtApp" [e, dims] => Term.con "extApp" [e, dims]
      | _ => t

  end MkExtApp

  section ReduceExt

    def reduceExtExpr (t : Term) : Term :=
      match t with
      | .con "app" [.var "reduceExtExpr", .con "extApp" [.con "extLam" [n, body], dims]] => Term.con "caseExpr" [Term.lit "(", Term.lit "case", Term.con "eq" [Term.con "app" [Term.var "length", dims], n], Term.con "arm" [Term.var "true", Term.lit "=>", Term.con "app" [Term.var "some", Term.con "foldr" [Term.con "fun" [Term.con "dim" [], Term.con "acc" [], Term.lit "=>", Term.con "subst" [Term.con "num" [Term.con "number" [Term.lit "0"]], Term.con "dim" [], Term.con "acc" []]], body, dims]]], Term.con "arm" [Term.var "false", Term.lit "=>", Term.con "none" []], Term.lit ")"]
      | _ => t

    def reduceExtExprOther (t : Term) : Term :=
      match t with
      | .con "app" [.var "reduceExtExpr", e] => Term.con "none" []
      | _ => t

    def normalizeExt (t : Term) : Term :=
      match t with
      | .con "normalizeExt" [fuel, e] => Term.con "normalizeExt'" [fuel, e]
      | _ => t

    def normalizeExt'0 (t : Term) : Term :=
      match t with
      | .con "normalizeExt'" [.con "num" [.con "number" [.lit "0"]], e] => e
      | _ => t

    def normalizeExt' (t : Term) : Term :=
      match t with
      | .con "normalizeExt'" [.con "app" [.var "suc", fuel], e] => Term.con "caseExpr" [Term.lit "(", Term.lit "case", Term.con "app" [Term.var "reduceExtExpr", e], Term.con "arm" [Term.lit "(", Term.var "some", Term.var "e'", Term.lit ")", Term.lit "=>", Term.con "normalizeExt'" [fuel, Term.var "e'"]], Term.con "arm" [Term.var "none", Term.lit "=>", e], Term.lit ")"]
      | _ => t

  end ReduceExt

  section PathAsExt

    def pathToExt (t : Term) : Term :=
      match t with
      | .con "app" [.var "pathToExt", .con "path" [A, a, b]] => Term.con "ext" [Term.con "num" [Term.con "number" [Term.lit "1"]], Term.con "app" [Term.var "lam", A], Term.con "cof_or" [Term.con "cof_eq" [Term.con "app" [Term.var "ix", Term.con "num" [Term.con "number" [Term.lit "0"]]], Term.con "dim0" []], Term.con "cof_eq" [Term.con "app" [Term.var "ix", Term.con "num" [Term.con "number" [Term.lit "0"]]], Term.con "dim1" []]], Term.con "app" [Term.var "lam", Term.con "caseExpr" [Term.lit "(", Term.lit "case", Term.con "app" [Term.var "ix", Term.con "num" [Term.con "number" [Term.lit "0"]]], Term.con "arm" [Term.var "dim0", Term.lit "=>", Term.con "shift" [Term.con "num" [Term.con "number" [Term.lit "0"]], Term.con "num" [Term.con "number" [Term.lit "1"]], a]], Term.con "arm" [Term.var "dim1", Term.lit "=>", Term.con "shift" [Term.con "num" [Term.con "number" [Term.lit "0"]], Term.con "num" [Term.con "number" [Term.lit "1"]], b]], Term.lit ")"]]]
      | _ => t

    def extToPath (t : Term) : Term :=
      match t with
      | .con "app" [.var "extToPath", .con "ext" [.con "num" [.con "number" [.lit "1"]], .con "app" [.var "lam", A], cof, bdry]] => Term.con "app" [Term.var "some", Term.con "path" [A, Term.con "app" [Term.var "evalAtDim0", bdry], Term.con "app" [Term.var "evalAtDim1", bdry]]]
      | _ => t

    def extToPathOther (t : Term) : Term :=
      match t with
      | .con "app" [.var "extToPath", e] => Term.con "none" []
      | _ => t

    def evalAtDim0 (t : Term) : Term :=
      match t with
      | .con "app" [.var "evalAtDim0", .con "app" [.var "lam", body]] => Term.con "subst" [Term.con "num" [Term.con "number" [Term.lit "0"]], Term.con "dim0" [], body]
      | _ => t

    def evalAtDim1 (t : Term) : Term :=
      match t with
      | .con "app" [.var "evalAtDim1", .con "app" [.var "lam", body]] => Term.con "subst" [Term.con "num" [Term.con "number" [Term.lit "0"]], Term.con "dim1" [], body]
      | _ => t

  end PathAsExt

  section HComExt

    def hcomExt (t : Term) : Term :=
      match t with
      | .con "hcomExt" [r, r', .con "ext" [n, fam, cof, bdry], φ, tubes, cap] => Term.con "extLam" [n, Term.con "hcom" [Term.con "mkExtApp" [fam, Term.con "app" [Term.var "dimVarsN", n]], r, r', Term.con "cof_or" [φ, Term.con "mkExtApp" [cof, Term.con "app" [Term.var "dimVarsN", n]]], Term.con "app" [Term.var "lam", Term.con "app" [Term.var "lam", Term.con "caseExpr" [Term.lit "(", Term.lit "case", Term.con "meetsCof" [Term.con "app" [Term.var "ix", Term.con "num" [Term.con "number" [Term.lit "1"]]], φ], Term.con "arm" [Term.var "true", Term.lit "=>", Term.con "mkExtApp" [Term.con "app" [Term.con "app" [Term.con "shift" [Term.con "num" [Term.con "number" [Term.lit "0"]], Term.con "num" [Term.con "number" [Term.lit "2"]], tubes], Term.con "app" [Term.var "ix", Term.con "num" [Term.con "number" [Term.lit "1"]]]], Term.con "app" [Term.var "ix", Term.con "num" [Term.con "number" [Term.lit "0"]]]], Term.con "app" [Term.var "dimVarsN", n]]], Term.con "arm" [Term.var "false", Term.lit "=>", Term.con "mkExtApp" [Term.con "shift" [Term.con "num" [Term.con "number" [Term.lit "0"]], Term.con "num" [Term.con "number" [Term.lit "2"]], bdry], Term.con "app" [Term.var "dimVarsN", n]]], Term.lit ")"]]], Term.con "mkExtApp" [cap, Term.con "app" [Term.var "dimVarsN", n]]]]
      | _ => t

    def dimVarsN (t : Term) : Term :=
      match t with
      | .con "app" [.var "dimVarsN", n] => Term.con "dimVarsN'" [n, Term.con "unit" [Term.lit "(", Term.lit ")"]]
      | _ => t

    def dimVarsN'0 (t : Term) : Term :=
      match t with
      | .con "dimVarsN'" [.con "num" [.con "number" [.lit "0"]], acc] => acc
      | _ => t

    def dimVarsN' (t : Term) : Term :=
      match t with
      | .con "dimVarsN'" [.con "app" [.var "suc", n], acc] => Term.con "dimVarsN'" [n, Term.con "tuple" [Term.con "app" [Term.lit "(", Term.con "ix" [], n, Term.lit ")"], acc]]
      | _ => t

  end HComExt

  section CoeExt

    def coeExt (t : Term) : Term :=
      match t with
      | .con "coeExt" [r, r', .con "app" [.var "lam", .con "ext" [n, fam, cof, bdry]], e] => Term.con "extLam" [n, Term.con "com" [Term.con "app" [Term.var "lam", Term.con "mkExtApp" [fam, Term.con "app" [Term.var "dimVarsN", n]]], r, r', Term.con "mkExtApp" [cof, Term.con "app" [Term.var "dimVarsN", n]], Term.con "app" [Term.var "lam", Term.con "app" [Term.var "lam", Term.con "mkExtApp" [Term.con "shift" [Term.con "num" [Term.con "number" [Term.lit "0"]], Term.con "num" [Term.con "number" [Term.lit "2"]], bdry], Term.con "app" [Term.var "dimVarsN", n]]]], Term.con "mkExtApp" [e, Term.con "app" [Term.var "dimVarsN", n]]]]
      | _ => t

  end CoeExt

  section ExtCurry

    def extCurry (t : Term) : Term :=
      match t with
      | .con "extCurry" [n, m, e] => Term.con "extLam" [n, Term.con "extLam" [m, Term.con "mkExtApp" [e, Term.con "append" [Term.con "app" [Term.var "dimVarsN", n], Term.con "app" [Term.var "dimVarsN", m]]]]]
      | _ => t

    def extUncurry (t : Term) : Term :=
      match t with
      | .con "extUncurry" [n, m, e] => Term.con "extLam" [Term.con "plus" [n, m], Term.con "mkExtApp" [Term.con "mkExtApp" [e, Term.con "takeN" [n, Term.con "app" [Term.var "dimVarsN", Term.con "plus" [n, m]]]], Term.con "dropN" [n, Term.con "app" [Term.var "dimVarsN", Term.con "plus" [n, m]]]]]
      | _ => t

  end ExtCurry

  section ExtRestrict

    def extRestrict (t : Term) : Term :=
      match t with
      | .con "extRestrict" [.con "ext" [n, fam, cof, bdry], dim, val] => Term.con "ext" [Term.con "minus" [n, Term.con "num" [Term.con "number" [Term.lit "1"]]], Term.con "app" [Term.var "lam", Term.con "subst" [dim, val, fam]], Term.con "subst" [dim, val, cof], Term.con "app" [Term.var "lam", Term.con "subst" [dim, val, bdry]]]
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

  end ExtRestrict

end ExtType