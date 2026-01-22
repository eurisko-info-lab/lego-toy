/-
  AUTO-GENERATED from .lego files
  Do not edit directly.
-/

import Lego.Algebra

open Lego

namespace Quote

  section QuoteEnv

    def qenvEmpty (t : Term) : Term :=
      match t with
      | .con "qenvEmpty" [] => Term.con "qenv" [Term.con "num" [Term.con "number" [Term.lit "0"]], Term.con "num" [Term.con "number" [Term.lit "0"]]]
      | _ => t

    def qenvSucc (t : Term) : Term :=
      match t with
      | .con "app" [.var "qenvSucc", .con "qenv" [l, dl]] => Term.con "qenv" [Term.con "app" [Term.var "suc", l], dl]
      | _ => t

    def qenvSuccDim (t : Term) : Term :=
      match t with
      | .con "app" [.var "qenvSuccDim", .con "qenv" [l, dl]] => Term.con "qenv" [l, Term.con "app" [Term.var "suc", dl]]
      | _ => t

    def levelToIndex (t : Term) : Term :=
      match t with
      | .con "levelToIndex" [.con "qenv" [l, dl], lvl] => Term.con "sub" [Term.con "sub" [l, lvl], Term.con "num" [Term.con "number" [Term.lit "1"]]]
      | _ => t

    def dimLevelToIndex (t : Term) : Term :=
      match t with
      | .con "dimLevelToIndex" [.con "qenv" [l, dl], lvl] => Term.con "sub" [Term.con "sub" [dl, lvl], Term.con "num" [Term.con "number" [Term.lit "1"]]]
      | _ => t

    -- Test: test
    -- (levelToIndex (qenv (num (number 3)) (num (number 0))) (num (number 0)))

  end QuoteEnv

  section Generic

    def generic (t : Term) : Term :=
      match t with
      | .con "app" [.var "generic", .con "qenv" [l, dl]] => Term.con "app" [Term.var "ix", l]
      | _ => t

    def genericDim (t : Term) : Term :=
      match t with
      | .con "app" [.var "genericDim", .con "qenv" [l, dl]] => Term.con "app" [Term.var "dimVar", dl]
      | _ => t

  end Generic

  section Shift

    def shiftFromIx (t : Term) : Term :=
      match t with
      | .con "shiftFrom" [.con "app" [.var "ix", k], n, cutoff] => Term.con "if" [Term.con "geq" [k, cutoff], Term.con "app" [Term.var "ix", Term.con "add" [k, n]], Term.con "app" [Term.var "ix", k]]
      | _ => t

    def shiftFromLam (t : Term) : Term :=
      match t with
      | .con "shiftFrom" [.con "app" [.var "lam", body], n, cutoff] => Term.con "app" [Term.var "lam", Term.con "shiftFrom" [body, n, Term.con "app" [Term.var "suc", cutoff]]]
      | _ => t

    def shiftFromApp (t : Term) : Term :=
      match t with
      | .con "shiftFrom" [.con "app" [f, a], n, cutoff] => Term.con "app" [Term.con "shiftFrom" [f, n, cutoff], Term.con "shiftFrom" [a, n, cutoff]]
      | _ => t

    def shiftFromPi (t : Term) : Term :=
      match t with
      | .con "shiftFrom" [.con "pi" [A, B], n, cutoff] => Term.con "pi" [Term.con "shiftFrom" [A, n, cutoff], Term.con "shiftFrom" [B, n, Term.con "app" [Term.var "suc", cutoff]]]
      | _ => t

    def shiftFromSigma (t : Term) : Term :=
      match t with
      | .con "shiftFrom" [.con "sigma" [A, B], n, cutoff] => Term.con "sigma" [Term.con "shiftFrom" [A, n, cutoff], Term.con "shiftFrom" [B, n, Term.con "app" [Term.var "suc", cutoff]]]
      | _ => t

    def shiftFromPair (t : Term) : Term :=
      match t with
      | .con "shiftFrom" [.con "pair" [a, b], n, cutoff] => Term.con "pair" [Term.con "shiftFrom" [a, n, cutoff], Term.con "shiftFrom" [b, n, cutoff]]
      | _ => t

    def shiftFromFst (t : Term) : Term :=
      match t with
      | .con "shiftFrom" [.con "app" [.var "fst", p], n, cutoff] => Term.con "app" [Term.var "fst", Term.con "shiftFrom" [p, n, cutoff]]
      | _ => t

    def shiftFromSnd (t : Term) : Term :=
      match t with
      | .con "shiftFrom" [.con "app" [.var "snd", p], n, cutoff] => Term.con "app" [Term.var "snd", Term.con "shiftFrom" [p, n, cutoff]]
      | _ => t

    def shiftFromPlam (t : Term) : Term :=
      match t with
      | .con "shiftFrom" [.con "app" [.var "plam", body], n, cutoff] => Term.con "app" [Term.var "plam", Term.con "shiftFrom" [body, n, cutoff]]
      | _ => t

    def shiftFromPapp (t : Term) : Term :=
      match t with
      | .con "shiftFrom" [.con "papp" [p, r], n, cutoff] => Term.con "papp" [Term.con "shiftFrom" [p, n, cutoff], r]
      | _ => t

    def shiftFromLit (t : Term) : Term :=
      match t with
      | .con "shiftFrom" [.con "app" [.var "lit", s], n, cutoff] => Term.con "app" [Term.var "lit", s]
      | _ => t

    def shiftFromUniv (t : Term) : Term :=
      match t with
      | .con "shiftFrom" [.con "app" [.var "univ", l], n, cutoff] => Term.con "app" [Term.var "univ", l]
      | _ => t

    def shiftFromDim (t : Term) : Term :=
      match t with
      | .con "shiftFrom" [d, n, cutoff] => d
      | _ => t

  end Shift

  section QuoteCon

    def quoteLit (t : Term) : Term :=
      match t with
      | .con "quoteCon" [env, .con "app" [.var "dlit", s]] => Term.con "app" [Term.var "lit", s]
      | _ => t

    def quoteLam (t : Term) : Term :=
      match t with
      | .con "quoteCon" [env, .con "app" [.var "dlam", .con "dclo" [body, cloEnv]]] => Term.con "app" [Term.var "lam", Term.con "quoteCon" [Term.con "app" [Term.var "qenvSucc", env], Term.con "deval" [Term.con "denvCons" [Term.con "app" [Term.var "dneu", Term.con "dcut" [Term.con "app" [Term.var "dneuVar", Term.con "app" [Term.var "qenvLevel", env]], Term.con "dtpUnknown" []]], cloEnv], body]]]
      | _ => t

    def quotePair (t : Term) : Term :=
      match t with
      | .con "quoteCon" [env, .con "dpair" [a, b]] => Term.con "pair" [Term.con "quoteCon" [env, a], Term.con "quoteCon" [env, b]]
      | _ => t

    def quoteUniv (t : Term) : Term :=
      match t with
      | .con "quoteCon" [env, .con "app" [.var "duniv", l]] => Term.con "app" [Term.var "univ", Term.con "app" [Term.var "quoteLevel", l]]
      | _ => t

    def quotePi (t : Term) : Term :=
      match t with
      | .con "quoteCon" [env, .con "dpi" [A, .con "dclo" [B, cloEnv]]] => Term.con "pi" [Term.con "quoteTp" [env, A], Term.con "quoteCon" [Term.con "app" [Term.var "qenvSucc", env], Term.con "deval" [Term.con "denvCons" [Term.con "app" [Term.var "dneu", Term.con "dcut" [Term.con "app" [Term.var "dneuVar", Term.con "app" [Term.var "qenvLevel", env]], A]], cloEnv], B]]]
      | _ => t

    def quoteSigma (t : Term) : Term :=
      match t with
      | .con "quoteCon" [env, .con "dsigma" [A, .con "dclo" [B, cloEnv]]] => Term.con "sigma" [Term.con "quoteTp" [env, A], Term.con "quoteCon" [Term.con "app" [Term.var "qenvSucc", env], Term.con "deval" [Term.con "denvCons" [Term.con "app" [Term.var "dneu", Term.con "dcut" [Term.con "app" [Term.var "dneuVar", Term.con "app" [Term.var "qenvLevel", env]], A]], cloEnv], B]]]
      | _ => t

    def quotePath (t : Term) : Term :=
      match t with
      | .con "quoteCon" [env, .con "dpath" [A, a, b]] => Term.con "path" [Term.con "quoteTp" [env, A], Term.con "quoteCon" [env, a], Term.con "quoteCon" [env, b]]
      | _ => t

    def quotePlam (t : Term) : Term :=
      match t with
      | .con "quoteCon" [env, .con "app" [.var "dplam", .con "dclo" [body, cloEnv]]] => Term.con "app" [Term.var "plam", Term.con "quoteCon" [Term.con "app" [Term.var "qenvSuccDim", env], Term.con "deval" [Term.con "denvCons" [Term.con "app" [Term.var "dneu", Term.con "dcut" [Term.con "app" [Term.var "dneuVar", Term.con "app" [Term.var "qenvDimLevel", env]], Term.con "dtpI" []]], cloEnv], body]]]
      | _ => t

    def quoteRefl (t : Term) : Term :=
      match t with
      | .con "quoteCon" [env, .con "app" [.var "drefl", a]] => Term.con "app" [Term.var "refl", Term.con "quoteCon" [env, a]]
      | _ => t

    def quoteNat (t : Term) : Term :=
      match t with
      | .con "quoteCon" [env, .con "dnat" []] => Term.con "nat" []
      | _ => t

    def quoteZero (t : Term) : Term :=
      match t with
      | .con "quoteCon" [env, .con "dzeroN" []] => Term.con "zero" []
      | _ => t

    def quoteSuc (t : Term) : Term :=
      match t with
      | .con "quoteCon" [env, .con "app" [.var "dsucN", n]] => Term.con "app" [Term.var "suc", Term.con "quoteCon" [env, n]]
      | _ => t

    def quoteCircle (t : Term) : Term :=
      match t with
      | .con "quoteCon" [env, .con "dcircle" []] => Term.con "circle" []
      | _ => t

    def quoteBase (t : Term) : Term :=
      match t with
      | .con "quoteCon" [env, .con "dbase" []] => Term.con "base" []
      | _ => t

    def quoteLoop (t : Term) : Term :=
      match t with
      | .con "quoteCon" [env, .con "app" [.var "dloop", d]] => Term.con "app" [Term.var "loop", Term.con "app" [Term.var "quoteDim", d]]
      | _ => t

    def quoteNeu (t : Term) : Term :=
      match t with
      | .con "quoteCon" [env, .con "app" [.var "dneu", cut]] => Term.con "quoteNeutral" [env, cut]
      | _ => t

  end QuoteCon

  section QuoteTp

    def quoteTpUniv (t : Term) : Term :=
      match t with
      | .con "quoteTp" [env, .con "app" [.var "dtpUniv", l]] => Term.con "app" [Term.var "univ", Term.con "app" [Term.var "quoteLevel", l]]
      | _ => t

    def quoteTpPi (t : Term) : Term :=
      match t with
      | .con "quoteTp" [env, .con "dtpPi" [A, clo]] => Term.con "pi" [Term.con "quoteTp" [env, A], Term.con "quoteTpClo" [Term.con "app" [Term.var "qenvSucc", env], clo]]
      | _ => t

    def quoteTpSigma (t : Term) : Term :=
      match t with
      | .con "quoteTp" [env, .con "dtpSigma" [A, clo]] => Term.con "sigma" [Term.con "quoteTp" [env, A], Term.con "quoteTpClo" [Term.con "app" [Term.var "qenvSucc", env], clo]]
      | _ => t

    def quoteTpPath (t : Term) : Term :=
      match t with
      | .con "quoteTp" [env, .con "dtpPath" [A, a, b]] => Term.con "path" [Term.con "quoteTp" [env, A], Term.con "quoteCon" [env, a], Term.con "quoteCon" [env, b]]
      | _ => t

    def quoteTpNat (t : Term) : Term :=
      match t with
      | .con "quoteTp" [env, .con "dtpNat" []] => Term.con "nat" []
      | _ => t

    def quoteTpCircle (t : Term) : Term :=
      match t with
      | .con "quoteTp" [env, .con "dtpCircle" []] => Term.con "circle" []
      | _ => t

    def quoteTpNeu (t : Term) : Term :=
      match t with
      | .con "quoteTp" [env, .con "app" [.var "dtpNeu", cut]] => Term.con "quoteNeutral" [env, cut]
      | _ => t

  end QuoteTp

  section QuoteNeutral

    def quoteNeuVar (t : Term) : Term :=
      match t with
      | .con "quoteNeutral" [env, .con "dcut" [.con "app" [.var "dneuVar", l], tp]] => Term.con "app" [Term.var "ix", Term.con "levelToIndex" [env, l]]
      | _ => t

    def quoteNeuApp (t : Term) : Term :=
      match t with
      | .con "quoteNeutral" [env, .con "dcut" [.con "dneuApp" [neu, arg], tp]] => Term.con "app" [Term.con "quoteNeutral" [env, Term.con "dcut" [neu, Term.con "dtpUnknown" []]], Term.con "quoteCon" [env, arg]]
      | _ => t

    def quoteNeuFst (t : Term) : Term :=
      match t with
      | .con "quoteNeutral" [env, .con "dcut" [.con "app" [.var "dneuFst", neu], tp]] => Term.con "app" [Term.var "fst", Term.con "quoteNeutral" [env, Term.con "dcut" [neu, Term.con "dtpUnknown" []]]]
      | _ => t

    def quoteNeuSnd (t : Term) : Term :=
      match t with
      | .con "quoteNeutral" [env, .con "dcut" [.con "app" [.var "dneuSnd", neu], tp]] => Term.con "app" [Term.var "snd", Term.con "quoteNeutral" [env, Term.con "dcut" [neu, Term.con "dtpUnknown" []]]]
      | _ => t

    def quoteNeuPApp (t : Term) : Term :=
      match t with
      | .con "quoteNeutral" [env, .con "dcut" [.con "dneuPApp" [neu, d], tp]] => Term.con "papp" [Term.con "quoteNeutral" [env, Term.con "dcut" [neu, Term.con "dtpUnknown" []]], Term.con "app" [Term.var "quoteDim", d]]
      | _ => t

    def quoteNeuNatElim (t : Term) : Term :=
      match t with
      | .con "quoteNeutral" [env, .con "dcut" [.con "dneuNatElim" [P, z, s, neu], tp]] => Term.con "natElim" [Term.con "quoteCon" [env, P], Term.con "quoteCon" [env, z], Term.con "quoteCon" [env, s], Term.con "quoteNeutral" [env, Term.con "dcut" [neu, Term.con "dtpNat" []]]]
      | _ => t

    def quoteNeuCircleElim (t : Term) : Term :=
      match t with
      | .con "quoteNeutral" [env, .con "dcut" [.con "dneuCircleElim" [P, b, l, neu], tp]] => Term.con "circleElim" [Term.con "quoteCon" [env, P], Term.con "quoteCon" [env, b], Term.con "quoteCon" [env, l], Term.con "quoteNeutral" [env, Term.con "dcut" [neu, Term.con "dtpCircle" []]]]
      | _ => t

  end QuoteNeutral

  section QuoteLevel

    def quoteLevelConst (t : Term) : Term :=
      match t with
      | .con "app" [.var "quoteLevel", .con "app" [.var "dconst", n]] => Term.con "app" [Term.var "ofNat", n]
      | _ => t

    def quoteLevelVar (t : Term) : Term :=
      match t with
      | .con "app" [.var "quoteLevel", .con "app" [.var "dlvar", n]] => Term.con "app" [Term.var "lvar", n]
      | _ => t

    def quoteLevelMax (t : Term) : Term :=
      match t with
      | .con "app" [.var "quoteLevel", .con "dmax" [l1, l2]] => Term.con "lmax" [Term.con "app" [Term.var "quoteLevel", l1], Term.con "app" [Term.var "quoteLevel", l2]]
      | _ => t

    def quoteLevelSuc (t : Term) : Term :=
      match t with
      | .con "app" [.var "quoteLevel", .con "app" [.var "dsuc", l]] => Term.con "app" [Term.var "lsuc", Term.con "app" [Term.var "quoteLevel", l]]
      | _ => t

    def ofNat0 (t : Term) : Term :=
      match t with
      | .con "app" [.var "ofNat", .con "num" [.con "number" [.lit "0"]]] => Term.con "lzero" []
      | _ => t

    def ofNatS (t : Term) : Term :=
      match t with
      | .con "app" [.var "ofNat", .con "app" [.var "suc", n]] => Term.con "app" [Term.var "lsuc", Term.con "app" [Term.var "ofNat", n]]
      | _ => t

  end QuoteLevel

  section QuoteDim

    def quoteDim0 (t : Term) : Term :=
      match t with
      | .con "app" [.var "quoteDim", .con "ddim0" []] => Term.con "dim0" []
      | _ => t

    def quoteDim1 (t : Term) : Term :=
      match t with
      | .con "app" [.var "quoteDim", .con "ddim1" []] => Term.con "dim1" []
      | _ => t

    def quoteDimVar (t : Term) : Term :=
      match t with
      | .con "app" [.var "quoteDim", .con "app" [.var "dvar", n]] => Term.con "app" [Term.var "dimVar", n]
      | _ => t

  end QuoteDim

  section NbE

    def nbe (t : Term) : Term :=
      match t with
      | .con "app" [.var "nbe", t] => Term.con "app" [Term.var "quoteCon", Term.con "qenvEmpty" [Term.con "deval" [Term.con "denvNil" [], t]]]
      | _ => t

    def nbeEnv (t : Term) : Term :=
      match t with
      | .con "nbeWithEnv" [env, t] => Term.con "app" [Term.var "quoteCon", Term.con "qenvEmpty" [Term.con "deval" [env, t]]]
      | _ => t

    -- Test: test
    -- ()

    -- Test: test
    -- ()

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

  end NbE

end Quote