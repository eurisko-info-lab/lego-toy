/-
  AUTO-GENERATED from .lego files
  Do not edit directly.
-/

import Lego.Algebra

open Lego

namespace CubicalTT

  section Dimension

    def join0L (t : Term) : Term :=
      match t with
      | .con "join" [.con "num" [.con "number" [.lit "0"]], r] => r
      | _ => t

    def join0R (t : Term) : Term :=
      match t with
      | .con "join" [r, .con "num" [.con "number" [.lit "0"]]] => r
      | _ => t

    def join1L (t : Term) : Term :=
      match t with
      | .con "join" [.con "num" [.con "number" [.lit "1"]], r] => Term.con "num" [Term.con "number" [Term.lit "1"]]
      | _ => t

    def join1R (t : Term) : Term :=
      match t with
      | .con "join" [r, .con "num" [.con "number" [.lit "1"]]] => Term.con "num" [Term.con "number" [Term.lit "1"]]
      | _ => t

    def joinIdem (t : Term) : Term :=
      match t with
      | .con "join" [r, r_dup] => r
      | _ => t

    def meet0L (t : Term) : Term :=
      match t with
      | .con "meet" [.con "num" [.con "number" [.lit "0"]], r] => Term.con "num" [Term.con "number" [Term.lit "0"]]
      | _ => t

    def meet0R (t : Term) : Term :=
      match t with
      | .con "meet" [r, .con "num" [.con "number" [.lit "0"]]] => Term.con "num" [Term.con "number" [Term.lit "0"]]
      | _ => t

    def meet1L (t : Term) : Term :=
      match t with
      | .con "meet" [.con "num" [.con "number" [.lit "1"]], r] => r
      | _ => t

    def meet1R (t : Term) : Term :=
      match t with
      | .con "meet" [r, .con "num" [.con "number" [.lit "1"]]] => r
      | _ => t

    def meetIdem (t : Term) : Term :=
      match t with
      | .con "meet" [r, r_dup] => r
      | _ => t

    def inv0 (t : Term) : Term :=
      match t with
      | .con "app" [.var "inv", .con "num" [.con "number" [.lit "0"]]] => Term.con "num" [Term.con "number" [Term.lit "1"]]
      | _ => t

    def inv1 (t : Term) : Term :=
      match t with
      | .con "app" [.var "inv", .con "num" [.con "number" [.lit "1"]]] => Term.con "num" [Term.con "number" [Term.lit "0"]]
      | _ => t

    def invInv (t : Term) : Term :=
      match t with
      | .con "app" [.var "inv", .con "app" [.var "inv", r]] => r
      | _ => t

    def deMorganOr (t : Term) : Term :=
      match t with
      | .con "app" [.var "inv", .con "join" [r, s]] => Term.con "meet" [Term.con "app" [Term.var "inv", r], Term.con "app" [Term.var "inv", s]]
      | _ => t

    def deMorganAnd (t : Term) : Term :=
      match t with
      | .con "app" [.var "inv", .con "meet" [r, s]] => Term.con "join" [Term.con "app" [Term.var "inv", r], Term.con "app" [Term.var "inv", s]]
      | _ => t

    -- Test: test
    -- (join (num (number 0)) $(i))

    -- Test: test
    -- (meet (num (number 0)) $(i))

    -- Test: test
    -- ()

  end Dimension

  section Cofibration

    def cof0Or (t : Term) : Term :=
      match t with
      | .con "cofOr" [.con "cof0" [], φ] => φ
      | _ => t

    def cof1Or (t : Term) : Term :=
      match t with
      | .con "cofOr" [.con "cof1" [], φ] => Term.con "cof1" []
      | _ => t

    def cofOrIdem (t : Term) : Term :=
      match t with
      | .con "cofOr" [φ, φ_dup] => φ
      | _ => t

    def cof0And (t : Term) : Term :=
      match t with
      | .con "cofAnd" [.con "cof0" [], φ] => Term.con "cof0" []
      | _ => t

    def cof1And (t : Term) : Term :=
      match t with
      | .con "cofAnd" [.con "cof1" [], φ] => φ
      | _ => t

    def cofAndIdem (t : Term) : Term :=
      match t with
      | .con "cofAnd" [φ, φ_dup] => φ
      | _ => t

    def eqRefl (t : Term) : Term :=
      match t with
      | .con "eq" [r, r_dup] => Term.con "cof1" []
      | _ => t

    def eq01 (t : Term) : Term :=
      match t with
      | .con "eq" [.con "num" [.con "number" [.lit "0"]], .con "num" [.con "number" [.lit "1"]]] => Term.con "cof0" []
      | _ => t

    def eq10 (t : Term) : Term :=
      match t with
      | .con "eq" [.con "num" [.con "number" [.lit "1"]], .con "num" [.con "number" [.lit "0"]]] => Term.con "cof0" []
      | _ => t

  end Cofibration

  section Core

    def fstPair (t : Term) : Term :=
      match t with
      | .con "app" [.var "fst", .con "pair" [a, b]] => a
      | _ => t

    def sndPair (t : Term) : Term :=
      match t with
      | .con "app" [.var "snd", .con "pair" [a, b]] => b
      | _ => t

    -- Test: test
    -- ()

    -- Test: test
    -- ()

  end Core

  section Lambda

    def beta (t : Term) : Term :=
      match t with
      | .con "app" [.con "app" [.var "lam", .con "binder" [.lit "$", .var "x", .lit ".", body]], arg] => Term.con "subst" [Term.lit "[", Term.var "x", Term.lit ":=", arg, Term.lit "]", body]
      | _ => t

    def dbeta (t : Term) : Term :=
      match t with
      | .con "dapp" [.con "app" [.var "dlam", .con "binder" [.lit "$", .var "i", .lit ".", body]], r] => Term.con "subst" [Term.lit "[", Term.var "i", Term.lit ":=", r, Term.lit "]", body]
      | _ => t

    -- Test: test
    -- (app (lam (objBinder x . $(x))) $(y))

    -- Test: test
    -- (dapp (dlam (objBinder i . (dapp $(f) $(i)))) (num (number 0)))

    -- Derived substitution for term
    -- Binders: [lam]
    mutual
    partial def substterm (k : Nat) (v : Term) (t : Term) : Term :=
      match t with
      | Term.con "ix" [Term.con "number" [Term.lit n]] =>
        let idx := n.toNat!
        if idx == k then v
        else if idx > k then Term.con "ix" [Term.con "number" [Term.lit (toString (idx - 1))]]
        else t
      | Term.con tag args =>
        let isBinder := ["lam"].contains tag
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
        let isBinder := ["lam"].contains tag
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

    -- Derived catamorphism for term
    partial def cataterm [Inhabited α] (alg : String → List α → α) (varF : String → α) (t : Term) : α :=
      match t with
      | Term.var n => varF n
      | Term.lit s => alg "lit" []
      | Term.con tag args => alg tag (args.map (cataterm alg varF))

  end Lambda

  section Pi

    def arrSugar (t : Term) : Term :=
      match t with
      | .con "tuple" [A, .lit "→", B] => Term.con "app" [Term.var "Pi", Term.con "labeledArg" [Term.var "_", Term.lit ":", Term.con "binder" [Term.lit "$", Term.var "A", Term.lit ".", B]]]
      | _ => t

  end Pi

  section Sigma

    def prodSugar (t : Term) : Term :=
      match t with
      | .con "tuple" [A, .lit "×", B] => Term.con "app" [Term.var "Sigma", Term.con "labeledArg" [Term.var "_", Term.lit ":", Term.con "binder" [Term.lit "$", Term.var "A", Term.lit ".", B]]]
      | _ => t

  end Sigma

  section Path

    def pathSugar (t : Term) : Term :=
      match t with
      | .con "Path" [A, a, b] => Term.con "introExpr" [Term.lit "(", Term.var "PathP", Term.var "_", Term.lit ".", A, Term.lit ".", Term.con "binder" [Term.lit "$", Term.var "a", Term.lit ".", b], Term.lit ")"]
      | _ => t

    -- Test: test
    -- ()

  end Path

  section System



  end System

  section Coe

    def coeRefl (t : Term) : Term :=
      match t with
      | .con "coe" [r, .lit "~>", r_dup, .con "binderParen" [.lit "(", .lit "$", .var "i", .lit ".", A, .lit ")"], a] => a
      | _ => t

    def coeConst (t : Term) : Term :=
      match t with
      | .con "coe" [r, .lit "~>", s, .con "binderParen" [.lit "(", .lit "$", .var "i", .lit ".", A, .lit ")"], a] => a
      | _ => t

    -- Test: test
    -- (coe (num (number 0)) (~>) (num (number 0)) (objBinderParen ( i . $(A) )) $(a))

  end Coe

  section Hcom

    def hcomRefl (t : Term) : Term :=
      match t with
      | .con "hcom" [r, .lit "~>", r_dup, A, sys, a] => a
      | _ => t

    def hcomTotal (t : Term) : Term :=
      match t with
      | .con "hcom" [r, .lit "~>", s, A, .con "app" [.var "sys", .con "bracket" [.lit "[", .con "cof1" [.lit "↦", u], .lit "]"]], a] => Term.con "subst" [Term.lit "[", Term.var "j", Term.lit ":=", s, Term.lit "]", u]
      | _ => t

  end Hcom

  section Com

    def comRefl (t : Term) : Term :=
      match t with
      | .con "com" [r, .lit "~>", r_dup, .con "binderParen" [.lit "(", .lit "$", .var "i", .lit ".", A, .lit ")"], sys, a] => a
      | _ => t

  end Com

  section VType

    def V0 (t : Term) : Term :=
      match t with
      | .con "V" [.con "num" [.con "number" [.lit "0"]], A, B, e] => A
      | _ => t

    def V1 (t : Term) : Term :=
      match t with
      | .con "V" [.con "num" [.con "number" [.lit "1"]], A, B, e] => B
      | _ => t

    def Vin0 (t : Term) : Term :=
      match t with
      | .con "Vin" [.con "num" [.con "number" [.lit "0"]], a] => Term.con "app" [Term.var "fst", a]
      | _ => t

    def Vin1 (t : Term) : Term :=
      match t with
      | .con "Vin" [.con "num" [.con "number" [.lit "1"]], a] => a
      | _ => t

    def Vproj0 (t : Term) : Term :=
      match t with
      | .con "Vproj" [.con "num" [.con "number" [.lit "0"]], v, e] => Term.con "app" [e, Term.con "app" [Term.var "snd", v]]
      | _ => t

    def Vproj1 (t : Term) : Term :=
      match t with
      | .con "Vproj" [.con "num" [.con "number" [.lit "1"]], v, e] => v
      | _ => t

  end VType

  section Sub

    def outInS (t : Term) : Term :=
      match t with
      | .con "app" [.var "outS", .con "app" [.var "inS", a]] => a
      | _ => t

  end Sub

  section Glue

    def unglueGlue (t : Term) : Term :=
      match t with
      | .con "unglue" [φ, .con "glue" [sys, a]] => a
      | _ => t

  end Glue

  section Conversion

    def convRefl (t : Term) : Term :=
      match t with
      | .con "conv" [A, A_dup] => Term.con "true" []
      | _ => t

    def convSym (t : Term) : Term :=
      match t with
      | .con "conv" [A, B] => Term.con "conv" [B, A]
      | _ => t

    def convU (t : Term) : Term :=
      match t with
      | .con "conv" [.con "U" [], .con "U" []] => Term.con "true" []
      | _ => t

    def convPi (t : Term) : Term :=
      match t with
      | .con "conv" [.con "app" [.var "Pi", .con "typedVar" [.lit "$", .var "x", .lit ":", .con "binder" [.lit "$", .var "A1", .lit ".", B1]]], .con "app" [.var "Pi", .con "typedVar" [.lit "$", .var "x", .lit ":", .con "binder" [.lit "$", .var "A2", .lit ".", B2]]]] => Term.con "and" [Term.con "conv" [Term.var "A2", Term.var "A1"], Term.con "conv" [B1, B2]]
      | _ => t

    def convSigma (t : Term) : Term :=
      match t with
      | .con "conv" [.con "app" [.var "Σ", .con "typedVar" [.lit "$", .var "x", .lit ":", .con "binder" [.lit "$", .var "A1", .lit ".", B1]]], .con "app" [.var "Σ", .con "typedVar" [.lit "$", .var "x", .lit ":", .con "binder" [.lit "$", .var "A2", .lit ".", B2]]]] => Term.con "and" [Term.con "conv" [Term.var "A1", Term.var "A2"], Term.con "conv" [B1, B2]]
      | _ => t

    def convPath (t : Term) : Term :=
      match t with
      | .con "conv" [.con "app" [.var "PathP", .con "binder" [.lit "$", .var "i", .lit ".", .con "binder" [.lit "$", .var "A1", .lit ".", .con "binder" [.lit "$", .var "a01", .lit ".", a11]]]], .con "app" [.var "PathP", .con "binder" [.lit "$", .var "i", .lit ".", .con "binder" [.lit "$", .var "A2", .lit ".", .con "binder" [.lit "$", .var "a02", .lit ".", a12]]]]] => Term.con "and" [Term.con "conv" [Term.var "A1", Term.var "A2"], Term.con "and" [Term.con "conv" [Term.var "a01", Term.var "a02"], Term.con "conv" [a11, a12]]]
      | _ => t

  end Conversion

  section Neutral

    def isNeutralVar (t : Term) : Term :=
      match t with
      | .con "app" [.var "neutral", .con "app" [.var "var", x]] => Term.con "true" []
      | _ => t

    def isNeutralApp (t : Term) : Term :=
      match t with
      | .con "app" [.var "neutral", .con "app" [f, a]] => Term.con "app" [Term.var "neutral", f]
      | _ => t

    def isNeutralFst (t : Term) : Term :=
      match t with
      | .con "app" [.var "neutral", .con "app" [.var "fst", p]] => Term.con "app" [Term.var "neutral", p]
      | _ => t

    def isNeutralSnd (t : Term) : Term :=
      match t with
      | .con "app" [.var "neutral", .con "app" [.var "snd", p]] => Term.con "app" [Term.var "neutral", p]
      | _ => t

    def isNeutralDApp (t : Term) : Term :=
      match t with
      | .con "app" [.var "neutral", .con "dapp" [p, r]] => Term.con "app" [Term.var "neutral", p]
      | _ => t

    def isNeutralCoe (t : Term) : Term :=
      match t with
      | .con "app" [.var "neutral", .con "coe" [r, .lit "~>", s, .con "binderParen" [.lit "(", .lit "$", .var "i", .lit ".", A, .lit ")"], a]] => Term.con "or" [Term.con "app" [Term.var "neutral", A], Term.con "app" [Term.var "neutral", a]]
      | _ => t

    def isNeutralHcom (t : Term) : Term :=
      match t with
      | .con "app" [.var "neutral", .con "hcom" [r, .lit "~>", s, A, sys, a]] => Term.con "or" [Term.con "app" [Term.var "neutral", A], Term.con "app" [Term.var "neutral", a]]
      | _ => t

  end Neutral

  section Equiv

    def equivFunId (t : Term) : Term :=
      match t with
      | .con "app" [.var "equivFun", .con "app" [.var "idEquiv", A]] => Term.con "introExpr" [Term.lit "(", Term.var "lam", Term.var "x", Term.lit ".", Term.var "x", Term.lit ")"]
      | _ => t

  end Equiv

  section Fiber

    -- Derived structural equality for term
    partial def eqterm (t1 t2 : Term) : Bool :=
      match t1, t2 with
      | Term.var n1, Term.var n2 => n1 == n2
      | Term.lit s1, Term.lit s2 => s1 == s2
      | Term.con tag1 args1, Term.con tag2 args2 =>
        tag1 == tag2 && args1.length == args2.length && (args1.zip args2).all fun (a, b) => eqterm a b
      | _, _ => false

  end Fiber

end CubicalTT