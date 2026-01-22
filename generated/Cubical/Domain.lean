/-
  AUTO-GENERATED from .lego files
  Do not edit directly.
-/

import Lego.Algebra

open Lego

namespace Domain

  section DLevel

    def dlevZero (t : Term) : Term :=
      match t with
      | .con "dzero" [] => Term.con "app" [Term.var "dconst", Term.con "num" [Term.con "number" [Term.lit "0"]]]
      | _ => t

    def dlevOne (t : Term) : Term :=
      match t with
      | .con "done" [] => Term.con "app" [Term.var "dconst", Term.con "num" [Term.con "number" [Term.lit "1"]]]
      | _ => t

    def ofLevelZero (t : Term) : Term :=
      match t with
      | .con "app" [.var "ofLevel", .con "lzero" []] => Term.con "dzero" []
      | _ => t

    def ofLevelSuc (t : Term) : Term :=
      match t with
      | .con "app" [.var "ofLevel", .con "app" [.var "lsuc", l]] => Term.con "app" [Term.var "dsuc", Term.con "app" [Term.var "ofLevel", l]]
      | _ => t

    def ofLevelMax (t : Term) : Term :=
      match t with
      | .con "app" [.var "ofLevel", .con "lmax" [l1, l2]] => Term.con "dmax" [Term.con "app" [Term.var "ofLevel", l1], Term.con "app" [Term.var "ofLevel", l2]]
      | _ => t

    def ofLevelVar (t : Term) : Term :=
      match t with
      | .con "app" [.var "ofLevel", .con "app" [.var "lvar", n]] => Term.con "app" [Term.var "dlvar", n]
      | _ => t

  end DLevel

  section Dim

    def dimOfExprD0 (t : Term) : Term :=
      match t with
      | .con "app" [.var "dimOfExpr", .con "dim0" []] => Term.con "app" [Term.var "some", Term.con "ddim0" []]
      | _ => t

    def dimOfExprD1 (t : Term) : Term :=
      match t with
      | .con "app" [.var "dimOfExpr", .con "dim1" []] => Term.con "app" [Term.var "some", Term.con "ddim1" []]
      | _ => t

    def dimOfExprVar (t : Term) : Term :=
      match t with
      | .con "app" [.var "dimOfExpr", .con "app" [.var "dimVar", n]] => Term.con "app" [Term.var "some", Term.con "app" [Term.var "dvar", n]]
      | _ => t

    def dimOfExprOther (t : Term) : Term :=
      match t with
      | .con "app" [.var "dimOfExpr", e] => Term.con "none" []
      | _ => t

    def dimToExprD0 (t : Term) : Term :=
      match t with
      | .con "app" [.var "dimToExpr", .con "ddim0" []] => Term.con "dim0" []
      | _ => t

    def dimToExprD1 (t : Term) : Term :=
      match t with
      | .con "app" [.var "dimToExpr", .con "ddim1" []] => Term.con "dim1" []
      | _ => t

    def dimToExprVar (t : Term) : Term :=
      match t with
      | .con "app" [.var "dimToExpr", .con "app" [.var "dvar", n]] => Term.con "app" [Term.var "dimVar", n]
      | _ => t

    def dimEqD0 (t : Term) : Term :=
      match t with
      | .con "dimEqD" [.con "ddim0" [], .con "ddim0" []] => Term.con "true" []
      | _ => t

    def dimEqD1 (t : Term) : Term :=
      match t with
      | .con "dimEqD" [.con "ddim1" [], .con "ddim1" []] => Term.con "true" []
      | _ => t

    def dimEqVar (t : Term) : Term :=
      match t with
      | .con "dimEqD" [.con "app" [.var "dvar", n], .con "app" [.var "dvar", m]] => Term.con "eq" [n, m]
      | _ => t

    def dimEqMixed (t : Term) : Term :=
      match t with
      | .con "dimEqD" [d1, d2] => Term.con "false" []
      | _ => t

    -- Test: test
    -- (dimEqD $(ddim0) $(ddim0))

    -- Test: test
    -- (dimEqD $(ddim0) $(ddim1))

  end Dim

  section DCof

    def isTrueTop (t : Term) : Term :=
      match t with
      | .con "app" [.var "dCofIsTrue", .con "dcof_top" []] => Term.con "true" []
      | _ => t

    def isTrueBot (t : Term) : Term :=
      match t with
      | .con "app" [.var "dCofIsTrue", .con "dcof_bot" []] => Term.con "false" []
      | _ => t

    def isTrueEq (t : Term) : Term :=
      match t with
      | .con "app" [.var "dCofIsTrue", .con "dcof_eq" [d1, d2]] => Term.con "dimEqD" [d1, d2]
      | _ => t

    def isTrueJoin (t : Term) : Term :=
      match t with
      | .con "app" [.var "dCofIsTrue", .con "dcof_join" [φ, ψ]] => Term.con "or" [Term.con "app" [Term.var "dCofIsTrue", φ], Term.con "app" [Term.var "dCofIsTrue", ψ]]
      | _ => t

    def isTrueMeet (t : Term) : Term :=
      match t with
      | .con "app" [.var "dCofIsTrue", .con "dcof_meet" [φ, ψ]] => Term.con "and" [Term.con "app" [Term.var "dCofIsTrue", φ], Term.con "app" [Term.var "dCofIsTrue", ψ]]
      | _ => t

    def isFalse (t : Term) : Term :=
      match t with
      | .con "app" [.var "dCofIsFalse", φ] => Term.con "app" [Term.var "not", Term.con "app" [Term.var "dCofIsTrue", φ]]
      | _ => t

    -- Test: test
    -- ()

    -- Test: test
    -- ()

  end DCof

  section DEnv

    def envLookup0 (t : Term) : Term :=
      match t with
      | .con "denvLookup" [.con "num" [.con "number" [.lit "0"]], .con "denvCons" [v, rest]] => Term.con "app" [Term.var "some", v]
      | _ => t

    def envLookupS (t : Term) : Term :=
      match t with
      | .con "denvLookup" [.con "app" [.var "suc", n], .con "denvCons" [v, rest]] => Term.con "denvLookup" [n, rest]
      | _ => t

    def envLookupNil (t : Term) : Term :=
      match t with
      | .con "denvLookup" [n, .con "denvNil" []] => Term.con "none" []
      | _ => t

    def envExtend (t : Term) : Term :=
      match t with
      | .con "denvExtend" [v, env] => Term.con "denvCons" [v, env]
      | _ => t

    -- Test: test
    -- (denvLookup (num (number 0)) (denvCons (dlit str "x") $(denvNil)))

  end DEnv

  section DClo

    def cloApply (t : Term) : Term :=
      match t with
      | .con "dCloApply" [.con "dclo" [body, env], arg] => Term.con "deval" [Term.con "denvCons" [arg, env], body]
      | _ => t

  end DClo

  section DCon



  end DCon

  section DTp



  end DTp

  section DCut



  end DCut

  section Eval

    def evalIx (t : Term) : Term :=
      match t with
      | .con "deval" [env, .con "app" [.var "ix", n]] => Term.con "fromOption" [Term.con "denvLookup" [n, env], Term.con "app" [Term.var "dneu", Term.con "dcut" [Term.con "app" [Term.var "dneuVar", n], Term.con "dtpUnknown" []]]]
      | _ => t

    def evalLit (t : Term) : Term :=
      match t with
      | .con "deval" [env, .con "app" [.var "lit", s]] => Term.con "app" [Term.var "dlit", s]
      | _ => t

    def evalLam (t : Term) : Term :=
      match t with
      | .con "deval" [env, .con "app" [.var "lam", body]] => Term.con "app" [Term.var "dlam", Term.con "dclo" [body, env]]
      | _ => t

    def evalApp (t : Term) : Term :=
      match t with
      | .con "deval" [env, .con "app" [f, a]] => Term.con "dApply" [Term.con "deval" [env, f], Term.con "deval" [env, a]]
      | _ => t

    def evalPi (t : Term) : Term :=
      match t with
      | .con "deval" [env, .con "pi" [A, B]] => Term.con "dpi" [Term.con "app" [Term.var "dtpOf", Term.con "deval" [env, A]], Term.con "dclo" [B, env]]
      | _ => t

    def evalSigma (t : Term) : Term :=
      match t with
      | .con "deval" [env, .con "sigma" [A, B]] => Term.con "dsigma" [Term.con "app" [Term.var "dtpOf", Term.con "deval" [env, A]], Term.con "dclo" [B, env]]
      | _ => t

    def evalPair (t : Term) : Term :=
      match t with
      | .con "deval" [env, .con "pair" [a, b]] => Term.con "dpair" [Term.con "deval" [env, a], Term.con "deval" [env, b]]
      | _ => t

    def evalFst (t : Term) : Term :=
      match t with
      | .con "deval" [env, .con "app" [.var "fst", p]] => Term.con "app" [Term.var "dFst", Term.con "deval" [env, p]]
      | _ => t

    def evalSnd (t : Term) : Term :=
      match t with
      | .con "deval" [env, .con "app" [.var "snd", p]] => Term.con "app" [Term.var "dSnd", Term.con "deval" [env, p]]
      | _ => t

    def evalUniv (t : Term) : Term :=
      match t with
      | .con "deval" [env, .con "app" [.var "univ", l]] => Term.con "app" [Term.var "duniv", Term.con "app" [Term.var "ofLevel", l]]
      | _ => t

    def evalPath (t : Term) : Term :=
      match t with
      | .con "deval" [env, .con "path" [A, a, b]] => Term.con "dpath" [Term.con "app" [Term.var "dtpOf", Term.con "deval" [env, A]], Term.con "deval" [env, a], Term.con "deval" [env, b]]
      | _ => t

    def evalPlam (t : Term) : Term :=
      match t with
      | .con "deval" [env, .con "app" [.var "plam", body]] => Term.con "app" [Term.var "dplam", Term.con "dclo" [body, env]]
      | _ => t

    def evalPapp (t : Term) : Term :=
      match t with
      | .con "deval" [env, .con "papp" [p, r]] => Term.con "dPApp" [Term.con "deval" [env, p], Term.con "app" [Term.var "dimOfExprForce", r]]
      | _ => t

    def evalRefl (t : Term) : Term :=
      match t with
      | .con "deval" [env, .con "app" [.var "refl", a]] => Term.con "app" [Term.var "drefl", Term.con "deval" [env, a]]
      | _ => t

    def evalNat (t : Term) : Term :=
      match t with
      | .con "deval" [env, .con "nat" []] => Term.con "dnat" []
      | _ => t

    def evalZero (t : Term) : Term :=
      match t with
      | .con "deval" [env, .con "zero" []] => Term.con "dzeroN" []
      | _ => t

    def evalSuc (t : Term) : Term :=
      match t with
      | .con "deval" [env, .con "app" [.var "suc", n]] => Term.con "app" [Term.var "dsucN", Term.con "deval" [env, n]]
      | _ => t

    def evalCircle (t : Term) : Term :=
      match t with
      | .con "deval" [env, .con "circle" []] => Term.con "dcircle" []
      | _ => t

    def evalBase (t : Term) : Term :=
      match t with
      | .con "deval" [env, .con "base" []] => Term.con "dbase" []
      | _ => t

    def evalLoop (t : Term) : Term :=
      match t with
      | .con "deval" [env, .con "app" [.var "loop", r]] => Term.con "app" [Term.var "dloop", Term.con "app" [Term.var "dimOfExprForce", r]]
      | _ => t

  end Eval

  section Operations

    def applyLam (t : Term) : Term :=
      match t with
      | .con "dApply" [.con "app" [.var "dlam", clo], arg] => Term.con "dCloApply" [clo, arg]
      | _ => t

    def applyNeu (t : Term) : Term :=
      match t with
      | .con "dApply" [.con "app" [.var "dneu", .con "dcut" [neu, tp]], arg] => Term.con "app" [Term.var "dneu", Term.con "dcut" [Term.con "dneuApp" [neu, arg], Term.con "dtpApply" [tp, arg]]]
      | _ => t

    def fstPair (t : Term) : Term :=
      match t with
      | .con "app" [.var "dFst", .con "dpair" [a, b]] => a
      | _ => t

    def fstNeu (t : Term) : Term :=
      match t with
      | .con "app" [.var "dFst", .con "app" [.var "dneu", .con "dcut" [neu, tp]]] => Term.con "app" [Term.var "dneu", Term.con "dcut" [Term.con "app" [Term.var "dneuFst", neu], Term.con "app" [Term.var "dtpFst", tp]]]
      | _ => t

    def sndPair (t : Term) : Term :=
      match t with
      | .con "app" [.var "dSnd", .con "dpair" [a, b]] => b
      | _ => t

    def sndNeu (t : Term) : Term :=
      match t with
      | .con "app" [.var "dSnd", .con "app" [.var "dneu", .con "dcut" [neu, tp]]] => Term.con "app" [Term.var "dneu", Term.con "dcut" [Term.con "app" [Term.var "dneuSnd", neu], Term.con "app" [Term.var "dtpSnd", tp]]]
      | _ => t

    def pappPlam (t : Term) : Term :=
      match t with
      | .con "dPApp" [.con "app" [.var "dplam", clo], d] => Term.con "dCloApplyDim" [clo, d]
      | _ => t

    def pappRefl (t : Term) : Term :=
      match t with
      | .con "dPApp" [.con "app" [.var "drefl", a], d] => a
      | _ => t

    def pappNeu (t : Term) : Term :=
      match t with
      | .con "dPApp" [.con "app" [.var "dneu", .con "dcut" [neu, tp]], d] => Term.con "app" [Term.var "dneu", Term.con "dcut" [Term.con "dneuPApp" [neu, d], Term.con "dtpPApp" [tp, d]]]
      | _ => t

    -- Test: test
    -- (dApply (dlam (dclo (ix (num (number 0))) $(denvNil))) (dlit str "x"))

    -- Test: test
    -- ()

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

  end Operations

end Domain