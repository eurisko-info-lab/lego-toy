/-
  AUTO-GENERATED from .lego files
  Do not edit directly.
-/

import Lego.Algebra

set_option linter.unusedVariables false

open Lego

namespace Core

  section Level

    def maxIdempotent (t : Term) : Term :=
      match t with
      | .con "lmax" [l, l_dup] => l
      | _ => t

    def maxZeroL (t : Term) : Term :=
      match t with
      | .con "lmax" [.con "lzero" [], l] => l
      | _ => t

    def maxZeroR (t : Term) : Term :=
      match t with
      | .con "lmax" [l, .con "lzero" []] => l
      | _ => t

    def maxSucSuc (t : Term) : Term :=
      match t with
      | .con "lmax" [.con "app" [.var "lsuc", l1], .con "app" [.var "lsuc", l2]] => Term.con "app" [Term.var "lsuc", Term.con "lmax" [l1, l2]]
      | _ => t

    -- Test: test
    -- (lmax (lsuc $(lzero)) (lsuc $(lzero)))

    -- Test: test
    -- (lmax $(lzero) (lsuc $(lzero)))

  end Level

  section Expr

    def beta (t : Term) : Term :=
      match t with
      | .con "app" [.con "app" [.var "lam", body], arg] => Term.con "subst" [Term.con "num" [Term.con "number" [Term.lit "0"]], arg, body]
      | _ => t

    def fstPair (t : Term) : Term :=
      match t with
      | .con "app" [.var "fst", .con "pair" [a, b]] => a
      | _ => t

    def sndPair (t : Term) : Term :=
      match t with
      | .con "app" [.var "snd", .con "pair" [a, b]] => b
      | _ => t

    def letBeta (t : Term) : Term :=
      match t with
      | .con "letE" [ty, val, body] => Term.con "subst" [Term.con "num" [Term.con "number" [Term.lit "0"]], val, body]
      | _ => t

    -- Test: test
    -- (app (lam (ix (num (number 0)))) (lit str "x"))

    -- Test: test
    -- ()

    -- Test: test
    -- ()

  end Expr

  section Dimension



  end Dimension

  section Cofibration

    def eqRefl (t : Term) : Term :=
      match t with
      | .con "cof_eq" [r, r_dup] => Term.con "cof_top" []
      | _ => t

    def eq01 (t : Term) : Term :=
      match t with
      | .con "cof_eq" [.con "dim0" [], .con "dim1" []] => Term.con "cof_bot" []
      | _ => t

    def eq10 (t : Term) : Term :=
      match t with
      | .con "cof_eq" [.con "dim1" [], .con "dim0" []] => Term.con "cof_bot" []
      | _ => t

    def andTop (t : Term) : Term :=
      match t with
      | .con "cof_and" [.con "cof_top" [], φ] => φ
      | _ => t

    def andBot (t : Term) : Term :=
      match t with
      | .con "cof_and" [.con "cof_bot" [], φ] => Term.con "cof_bot" []
      | _ => t

    def orTop (t : Term) : Term :=
      match t with
      | .con "cof_or" [.con "cof_top" [], φ] => Term.con "cof_top" []
      | _ => t

    def orBot (t : Term) : Term :=
      match t with
      | .con "cof_or" [.con "cof_bot" [], φ] => φ
      | _ => t

    -- Test: test
    -- (cof_eq $(dim0) $(dim0))

    -- Test: test
    -- (cof_eq $(dim0) $(dim1))

  end Cofibration

  section Path

    def plamApp0 (t : Term) : Term :=
      match t with
      | .con "papp" [.con "app" [.var "plam", body], .con "dim0" []] => Term.con "substDim" [Term.con "num" [Term.con "number" [Term.lit "0"]], Term.con "dim0" [], body]
      | _ => t

    def plamApp1 (t : Term) : Term :=
      match t with
      | .con "papp" [.con "app" [.var "plam", body], .con "dim1" []] => Term.con "substDim" [Term.con "num" [Term.con "number" [Term.lit "0"]], Term.con "dim1" [], body]
      | _ => t

    def reflApp (t : Term) : Term :=
      match t with
      | .con "papp" [.con "app" [.var "refl", a], r] => a
      | _ => t

    -- Test: test
    -- (papp (refl (lit str "a")) $(dim0))

  end Path

  section Kan

    def coeRefl (t : Term) : Term :=
      match t with
      | .con "coe" [r, r_dup, A, a] => a
      | _ => t

    def hcomRefl (t : Term) : Term :=
      match t with
      | .con "hcom" [r, r_dup, A, φ, cap] => cap
      | _ => t

    -- Test: test
    -- (coe $(dim0) $(dim0) (univ $(lzero)) (lit str "A"))

  end Kan

  section FHCom



  end FHCom

  section Sys



  end Sys

  section VType

    def vin0 (t : Term) : Term :=
      match t with
      | .con "vin" [.con "dim0" [], a, b] => a
      | _ => t

    def vin1 (t : Term) : Term :=
      match t with
      | .con "vin" [.con "dim1" [], a, b] => b
      | _ => t

    -- Test: test
    -- (vin $(dim0) (lit str "a") (lit str "b"))

    -- Test: test
    -- (vin $(dim1) (lit str "a") (lit str "b"))

  end VType

  section Nat

    def natElimZero (t : Term) : Term :=
      match t with
      | .con "natElim" [P, z, s, .con "zero" []] => z
      | _ => t

    def natElimSuc (t : Term) : Term :=
      match t with
      | .con "natElim" [P, z, s, .con "app" [.var "suc", n]] => Term.con "app" [Term.con "app" [s, n], Term.con "natElim" [P, z, s, n]]
      | _ => t

    -- Test: test
    -- (natElim $(P) $(z) $(s) $(zero))

  end Nat

  section Circle

    def loop0 (t : Term) : Term :=
      match t with
      | .con "app" [.var "loop", .con "dim0" []] => Term.con "base" []
      | _ => t

    def loop1 (t : Term) : Term :=
      match t with
      | .con "app" [.var "loop", .con "dim1" []] => Term.con "base" []
      | _ => t

    def circleElimBase (t : Term) : Term :=
      match t with
      | .con "circleElim" [P, b, l, .con "base" []] => b
      | _ => t

    -- Test: test
    -- ()

    -- Test: test
    -- ()

  end Circle

  section Extension



  end Extension

  section Sub

    def subBeta (t : Term) : Term :=
      match t with
      | .con "app" [.var "subOut", .con "app" [.var "subIn", e]] => e
      | _ => t

    -- Test: test
    -- ()

  end Sub

  section Shift

    def shiftIx (t : Term) : Term :=
      match t with
      | .con "shift" [k, n, .con "app" [.var "ix", m]] => Term.con "app" [Term.var "ix", Term.con "if" [Term.con "geq" [m, k], Term.con "add" [m, n], m]]
      | _ => t

    def shiftLam (t : Term) : Term :=
      match t with
      | .con "shift" [k, n, .con "app" [.var "lam", body]] => Term.con "app" [Term.var "lam", Term.con "shift" [Term.con "add" [k, Term.con "num" [Term.con "number" [Term.lit "1"]]], n, body]]
      | _ => t

    def shiftApp (t : Term) : Term :=
      match t with
      | .con "shift" [k, n, .con "app" [f, a]] => Term.con "app" [Term.con "shift" [k, n, f], Term.con "shift" [k, n, a]]
      | _ => t

    def shiftPi (t : Term) : Term :=
      match t with
      | .con "shift" [k, n, .con "pi" [A, B]] => Term.con "pi" [Term.con "shift" [k, n, A], Term.con "shift" [Term.con "add" [k, Term.con "num" [Term.con "number" [Term.lit "1"]]], n, B]]
      | _ => t

  end Shift

  section Subst

    def substIxHit (t : Term) : Term :=
      match t with
      | .con "subst" [k, v, .con "app" [.var "ix", k_dup]] => v
      | _ => t

    def substIxMiss (t : Term) : Term :=
      match t with
      | .con "subst" [k, v, .con "app" [.var "ix", m]] => Term.con "app" [Term.var "ix", Term.con "if" [Term.con "gt" [m, k], Term.con "sub" [m, Term.con "num" [Term.con "number" [Term.lit "1"]]], m]]
      | _ => t

    def substLam (t : Term) : Term :=
      match t with
      | .con "subst" [k, v, .con "app" [.var "lam", body]] => Term.con "app" [Term.var "lam", Term.con "subst" [Term.con "add" [k, Term.con "num" [Term.con "number" [Term.lit "1"]]], Term.con "shift" [Term.con "num" [Term.con "number" [Term.lit "0"]], Term.con "num" [Term.con "number" [Term.lit "1"]], v], body]]
      | _ => t

    def substApp (t : Term) : Term :=
      match t with
      | .con "subst" [k, v, .con "app" [f, a]] => Term.con "app" [Term.con "subst" [k, v, f], Term.con "subst" [k, v, a]]
      | _ => t

  end Subst

  section Normalize

    def normalize (t : Term) : Term :=
      match t with
      | .con "normalize" [fuel, t] => Term.con "normalizeStep" [Term.con "sub" [fuel, Term.con "num" [Term.con "number" [Term.lit "1"]]], Term.con "app" [Term.var "step", t]]
      | _ => t

    def normalizeZero (t : Term) : Term :=
      match t with
      | .con "normalize" [.con "num" [.con "number" [.lit "0"]], t] => t
      | _ => t

    def normalizeStep (t : Term) : Term :=
      match t with
      | .con "normalizeStep" [fuel, .con "app" [.var "some", t]] => Term.con "normalize" [fuel, t]
      | _ => t

    def normalizeStepNone (t : Term) : Term :=
      match t with
      | .con "normalizeStep" [fuel, .con "none" []] => Term.var "t"
      | _ => t

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

    -- Derived shift for term (included with subst)

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

    -- Derived conversion check for term
    def convterm (t1 t2 : Term) : Bool :=
      normalizeterm 1000 t1 == normalizeterm 1000 t2

  end Normalize

end Core