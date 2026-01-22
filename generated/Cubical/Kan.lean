/-
  AUTO-GENERATED from .lego files
  Do not edit directly.
-/

import Lego.Algebra

open Lego

namespace Kan

  section Dir

    def isDegenerate (t : Term) : Term :=
      match t with
      | .con "app" [.var "dirIsDegenerate", .con "dir" [src, tgt]] => Term.con "dimEqD" [src, tgt]
      | _ => t

    def dirOfExpr (t : Term) : Term :=
      match t with
      | .con "dirOfExpr" [r, r'] => Term.con "dir" [Term.con "app" [Term.var "dimOfExprForce", r], Term.con "app" [Term.var "dimOfExprForce", r']]
      | _ => t

    -- Test: test
    -- ()

    -- Test: test
    -- ()

  end Dir

  section EvalCof

    def evalCofTop (t : Term) : Term :=
      match t with
      | .con "evalCof" [subst, .con "cof_top" []] => Term.con "true" []
      | _ => t

    def evalCofBot (t : Term) : Term :=
      match t with
      | .con "evalCof" [subst, .con "cof_bot" []] => Term.con "false" []
      | _ => t

    def evalCofEq (t : Term) : Term :=
      match t with
      | .con "evalCof" [subst, .con "cof_eq" [r, s]] => Term.con "dimEqSubst" [subst, r, s]
      | _ => t

    def evalCofAnd (t : Term) : Term :=
      match t with
      | .con "evalCof" [subst, .con "cof_and" [φ, ψ]] => Term.con "and" [Term.con "evalCof" [subst, φ], Term.con "evalCof" [subst, ψ]]
      | _ => t

    def evalCofOr (t : Term) : Term :=
      match t with
      | .con "evalCof" [subst, .con "cof_or" [φ, ψ]] => Term.con "or" [Term.con "evalCof" [subst, φ], Term.con "evalCof" [subst, ψ]]
      | _ => t

  end EvalCof

  section SubstDim0

    def substDim0Ix (t : Term) : Term :=
      match t with
      | .con "substDim0'" [d, .con "app" [.var "ix", n]] => Term.con "app" [Term.var "ix", n]
      | _ => t

    def substDim0Dim0 (t : Term) : Term :=
      match t with
      | .con "substDim0'" [d, .con "dim0" []] => Term.con "dim0" []
      | _ => t

    def substDim0Dim1 (t : Term) : Term :=
      match t with
      | .con "substDim0'" [d, .con "dim1" []] => Term.con "dim1" []
      | _ => t

    def substDim0DimVar0 (t : Term) : Term :=
      match t with
      | .con "substDim0'" [d, .con "app" [.var "dimVar", .con "num" [.con "number" [.lit "0"]]]] => d
      | _ => t

    def substDim0DimVarS (t : Term) : Term :=
      match t with
      | .con "substDim0'" [d, .con "app" [.var "dimVar", .con "app" [.var "suc", n]]] => Term.con "app" [Term.var "dimVar", n]
      | _ => t

    def substDim0Lam (t : Term) : Term :=
      match t with
      | .con "substDim0'" [d, .con "app" [.var "lam", body]] => Term.con "app" [Term.var "lam", Term.con "substDim0'" [d, body]]
      | _ => t

    def substDim0Plam (t : Term) : Term :=
      match t with
      | .con "substDim0'" [d, .con "app" [.var "plam", body]] => Term.con "app" [Term.var "plam", Term.con "substDim0'" [Term.con "shift" [Term.con "num" [Term.con "number" [Term.lit "0"]], Term.con "num" [Term.con "number" [Term.lit "1"]], d], body]]
      | _ => t

    def substDim0App (t : Term) : Term :=
      match t with
      | .con "substDim0'" [d, .con "app" [f, a]] => Term.con "app" [Term.con "substDim0'" [d, f], Term.con "substDim0'" [d, a]]
      | _ => t

    def substDim0Pi (t : Term) : Term :=
      match t with
      | .con "substDim0'" [d, .con "pi" [A, B]] => Term.con "pi" [Term.con "substDim0'" [d, A], Term.con "substDim0'" [d, B]]
      | _ => t

  end SubstDim0

  section Coe

    def coeRefl (t : Term) : Term :=
      match t with
      | .con "coe" [r, r_dup, ty, a] => a
      | _ => t

    def coeUniv (t : Term) : Term :=
      match t with
      | .con "coe" [r, r', .con "app" [.var "plam", .con "app" [.var "univ", l]], a] => a
      | _ => t

    def coePi (t : Term) : Term :=
      match t with
      | .con "coe" [r, r', .con "app" [.var "plam", .con "pi" [dom, cod]], f] => Term.con "app" [Term.var "lam", Term.con "coe" [r, r', Term.con "plamSubst" [Term.con "num" [Term.con "number" [Term.lit "0"]], Term.con "coe" [r', r, Term.con "app" [Term.var "plamInv", dom], Term.con "app" [Term.var "ix", Term.con "num" [Term.con "number" [Term.lit "0"]]]], cod], Term.con "app" [f, Term.con "coe" [r', r, dom, Term.con "app" [Term.var "ix", Term.con "num" [Term.con "number" [Term.lit "0"]]]]]]]
      | _ => t

    def coeSigma (t : Term) : Term :=
      match t with
      | .con "coe" [r, r', .con "app" [.var "plam", .con "sigma" [dom, cod]], p] => Term.con "pair" [Term.con "coe" [r, r', dom, Term.con "app" [Term.var "fst", p]], Term.con "coe" [r, r', Term.con "plamSubst" [Term.con "num" [Term.con "number" [Term.lit "0"]], Term.con "coe" [r, r', dom, Term.con "app" [Term.var "fst", p]], cod], Term.con "app" [Term.var "snd", p]]]
      | _ => t

    def coePath (t : Term) : Term :=
      match t with
      | .con "coe" [r, r', .con "app" [.var "plam", .con "path" [A, a, b]], p] => Term.con "app" [Term.var "plam", Term.con "coe" [r, r', A, Term.con "papp" [p, Term.con "app" [Term.var "dimVar", Term.con "num" [Term.con "number" [Term.lit "0"]]]]]]
      | _ => t

    -- Test: test
    -- (coe $(dim0) $(dim0) (plam (univ $(lzero))) (lit str "A"))

    -- Test: test
    -- (coe $(dim0) $(dim1) (plam (univ $(lzero))) (lit str "A"))

  end Coe

  section HCom

    def hcomRefl (t : Term) : Term :=
      match t with
      | .con "hcom" [r, r_dup, ty, phi, cap] => cap
      | _ => t

    def hcomTrue (t : Term) : Term :=
      match t with
      | .con "hcom" [r, r', ty, .con "cof_top" [], tube, cap] => Term.con "app" [Term.con "app" [tube, r'], Term.con "app" [Term.var "lit", Term.con "terminal" [Term.lit "prf"]]]
      | _ => t

    def hcomFalse (t : Term) : Term :=
      match t with
      | .con "hcom" [r, r', ty, .con "cof_bot" [], tube, cap] => cap
      | _ => t

    def hcomPi (t : Term) : Term :=
      match t with
      | .con "hcom" [r, r', .con "pi" [A, B], phi, tube, cap] => Term.con "app" [Term.var "lam", Term.con "hcom" [r, r', Term.con "substBody" [Term.con "num" [Term.con "number" [Term.lit "0"]], Term.con "app" [Term.var "ix", Term.con "num" [Term.con "number" [Term.lit "0"]]], B], phi, Term.con "app" [Term.var "lam", Term.con "app" [Term.var "lam", Term.con "app" [Term.con "app" [Term.con "app" [tube, Term.con "app" [Term.var "ix", Term.con "num" [Term.con "number" [Term.lit "1"]]]], Term.con "app" [Term.var "ix", Term.con "num" [Term.con "number" [Term.lit "0"]]]], Term.con "app" [Term.var "ix", Term.con "num" [Term.con "number" [Term.lit "2"]]]]]], Term.con "app" [cap, Term.con "app" [Term.var "ix", Term.con "num" [Term.con "number" [Term.lit "0"]]]]]]
      | _ => t

    def hcomSigma (t : Term) : Term :=
      match t with
      | .con "hcom" [r, r', .con "sigma" [A, B], phi, tube, cap] => Term.con "pair" [Term.con "hcom" [r, r', A, phi, Term.con "app" [Term.var "lam", Term.con "app" [Term.var "lam", Term.con "app" [Term.var "fst", Term.con "app" [Term.con "app" [tube, Term.con "app" [Term.var "ix", Term.con "num" [Term.con "number" [Term.lit "1"]]]], Term.con "app" [Term.var "ix", Term.con "num" [Term.con "number" [Term.lit "0"]]]]]]], Term.con "app" [Term.var "fst", cap]], Term.con "com" [r, r', Term.con "app" [Term.var "plam", Term.con "substBody" [Term.con "num" [Term.con "number" [Term.lit "0"]], Term.con "hcom" [r, Term.con "app" [Term.var "dimVar", Term.con "num" [Term.con "number" [Term.lit "0"]]], A, phi, Term.con "app" [Term.var "lam", Term.con "app" [Term.var "lam", Term.con "app" [Term.var "fst", Term.con "app" [Term.con "app" [tube, Term.con "app" [Term.var "ix", Term.con "num" [Term.con "number" [Term.lit "1"]]]], Term.con "app" [Term.var "ix", Term.con "num" [Term.con "number" [Term.lit "0"]]]]]]], Term.con "app" [Term.var "fst", cap]], B]], phi, Term.con "app" [Term.var "lam", Term.con "app" [Term.var "lam", Term.con "app" [Term.var "snd", Term.con "app" [Term.con "app" [tube, Term.con "app" [Term.var "ix", Term.con "num" [Term.con "number" [Term.lit "1"]]]], Term.con "app" [Term.var "ix", Term.con "num" [Term.con "number" [Term.lit "0"]]]]]]], Term.con "app" [Term.var "snd", cap]]]
      | _ => t

    def hcomPath (t : Term) : Term :=
      match t with
      | .con "hcom" [r, r', .con "path" [A, a, b], phi, tube, cap] => Term.con "app" [Term.var "plam", Term.con "hcom" [r, r', A, Term.con "cof_or" [phi, Term.con "cof_or" [Term.con "cof_eq" [Term.con "app" [Term.var "dimVar", Term.con "num" [Term.con "number" [Term.lit "0"]]], Term.con "dim0" []], Term.con "cof_eq" [Term.con "app" [Term.var "dimVar", Term.con "num" [Term.con "number" [Term.lit "0"]]], Term.con "dim1" []]]], Term.con "mkTube" [tube, Term.con "app" [Term.var "dimVar", Term.con "num" [Term.con "number" [Term.lit "0"]]], a, b], Term.con "papp" [cap, Term.con "app" [Term.var "dimVar", Term.con "num" [Term.con "number" [Term.lit "0"]]]]]]
      | _ => t

    -- Test: test
    -- (hcom $(dim0) $(dim0) (univ $(lzero)) $(cof_bot) (lit str "tube") (lit str "cap"))

    -- Test: test
    -- (hcom $(dim0) $(dim1) (univ $(lzero)) $(cof_bot) (lit str "tube") (lit str "cap"))

  end HCom

  section Com

    def comRefl (t : Term) : Term :=
      match t with
      | .con "com" [r, r_dup, line, phi, tube, cap] => cap
      | _ => t

    def comGen (t : Term) : Term :=
      match t with
      | .con "com" [r, r', line, phi, tube, cap] => Term.con "hcom" [r, r', Term.con "substDim0'" [r', Term.con "app" [Term.var "plamBody", line]], phi, Term.con "app" [Term.var "lam", Term.con "app" [Term.var "lam", Term.con "coe" [Term.con "app" [Term.var "ix", Term.con "num" [Term.con "number" [Term.lit "1"]]], r', line, Term.con "app" [Term.con "app" [tube, Term.con "app" [Term.var "ix", Term.con "num" [Term.con "number" [Term.lit "1"]]]], Term.con "app" [Term.var "ix", Term.con "num" [Term.con "number" [Term.lit "0"]]]]]]], Term.con "coe" [r, r', line, cap]]
      | _ => t

    -- Test: test
    -- (com $(dim0) $(dim0) (plam (univ $(lzero))) $(cof_bot) (lit str "tube") (lit str "cap"))

  end Com

  section GHCom

    def ghcomRefl (t : Term) : Term :=
      match t with
      | .con "ghcom" [r, r_dup, A, sys, cap] => cap
      | _ => t

    def ghcomBdy (t : Term) : Term :=
      match t with
      | .con "ghcom" [r, r', A, .con "sysCons" [.con "tuple" [.lit "(", phi, .lit ",", tube, .lit ")"], rest], cap] => Term.con "substDim0'" [r', tube]
      | _ => t

  end GHCom

  section GCom

    def gcomRefl (t : Term) : Term :=
      match t with
      | .con "gcom" [r, r_dup, line, sys, cap] => cap
      | _ => t

    def gcomBdy (t : Term) : Term :=
      match t with
      | .con "gcom" [r, r', line, .con "sysCons" [.con "tuple" [.lit "(", phi, .lit ",", tube, .lit ")"], rest], cap] => Term.con "substDim0'" [r', tube]
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

  end GCom

end Kan