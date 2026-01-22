/-
  AUTO-GENERATED from .lego files
  Do not edit directly.
-/

import Lego.Algebra

open Lego

namespace Cofibration

  section DimOps

    def isDim0_0 (t : Term) : Term :=
      match t with
      | .con "app" [.var "isDim0", .con "dim0" []] => Term.con "true" []
      | _ => t

    def isDim0_1 (t : Term) : Term :=
      match t with
      | .con "app" [.var "isDim0", .con "dim1" []] => Term.con "false" []
      | _ => t

    def isDim0_var (t : Term) : Term :=
      match t with
      | .con "app" [.var "isDim0", .con "app" [.var "dimVar", n]] => Term.con "false" []
      | _ => t

    def isDim1_0 (t : Term) : Term :=
      match t with
      | .con "app" [.var "isDim1", .con "dim0" []] => Term.con "false" []
      | _ => t

    def isDim1_1 (t : Term) : Term :=
      match t with
      | .con "app" [.var "isDim1", .con "dim1" []] => Term.con "true" []
      | _ => t

    def isDim1_var (t : Term) : Term :=
      match t with
      | .con "app" [.var "isDim1", .con "app" [.var "dimVar", n]] => Term.con "false" []
      | _ => t

    def dimEq00 (t : Term) : Term :=
      match t with
      | .con "dimEq" [.con "dim0" [], .con "dim0" []] => Term.con "true" []
      | _ => t

    def dimEq11 (t : Term) : Term :=
      match t with
      | .con "dimEq" [.con "dim1" [], .con "dim1" []] => Term.con "true" []
      | _ => t

    def dimEqVar (t : Term) : Term :=
      match t with
      | .con "dimEq" [.con "app" [.var "dimVar", n], .con "app" [.var "dimVar", m]] => Term.con "eq" [n, m]
      | _ => t

    def dimEqMixed (t : Term) : Term :=
      match t with
      | .con "dimEq" [r, s] => Term.con "false" []
      | _ => t

    -- Test: test
    -- ()

    -- Test: test
    -- ()

    -- Test: test
    -- (dimEq $(dim0) $(dim0))

  end DimOps

  section CofConstructors

    def top (t : Term) : Term :=
      match t with
      | .con "top" [] => Term.con "cof_top" []
      | _ => t

    def bot (t : Term) : Term :=
      match t with
      | .con "bot" [] => Term.con "cof_bot" []
      | _ => t

    def eqSame (t : Term) : Term :=
      match t with
      | .con "cofEq" [r, r_dup] => Term.con "cof_top" []
      | _ => t

    def eq01 (t : Term) : Term :=
      match t with
      | .con "cofEq" [.con "dim0" [], .con "dim1" []] => Term.con "cof_bot" []
      | _ => t

    def eq10 (t : Term) : Term :=
      match t with
      | .con "cofEq" [.con "dim1" [], .con "dim0" []] => Term.con "cof_bot" []
      | _ => t

    def eqGen (t : Term) : Term :=
      match t with
      | .con "cofEq" [r, s] => Term.con "cof_eq" [r, s]
      | _ => t

    def le (t : Term) : Term :=
      match t with
      | .con "cofLe" [r, s] => Term.con "cof_or" [Term.con "cof_eq" [r, Term.con "dim0" []], Term.con "cof_eq" [s, Term.con "dim1" []]]
      | _ => t

    def boundary (t : Term) : Term :=
      match t with
      | .con "app" [.var "boundary", r] => Term.con "cof_or" [Term.con "cof_eq" [r, Term.con "dim0" []], Term.con "cof_eq" [r, Term.con "dim1" []]]
      | _ => t

    -- Test: test
    -- (cofEq $(dim0) $(dim0))

    -- Test: test
    -- (cofEq $(dim0) $(dim1))

    -- Test: test
    -- (cof_or (cof_eq (dimVar (num (number 0))) $(dim0)) (cof_eq (dimVar (num (number 0))) $(dim1)))

  end CofConstructors

  section Meet

    def meetTopL (t : Term) : Term :=
      match t with
      | .con "cof_and" [.con "cof_top" [], φ] => φ
      | _ => t

    def meetTopR (t : Term) : Term :=
      match t with
      | .con "cof_and" [φ, .con "cof_top" []] => φ
      | _ => t

    def meetBotL (t : Term) : Term :=
      match t with
      | .con "cof_and" [.con "cof_bot" [], φ] => Term.con "cof_bot" []
      | _ => t

    def meetBotR (t : Term) : Term :=
      match t with
      | .con "cof_and" [φ, .con "cof_bot" []] => Term.con "cof_bot" []
      | _ => t

    def meetIdem (t : Term) : Term :=
      match t with
      | .con "cof_and" [φ, φ_dup] => φ
      | _ => t

    -- Test: test
    -- (cof_and $(cof_top) (cof_eq $(dim0) $(dim0)))

    -- Test: test
    -- (cof_and $(cof_bot) $(cof_top))

    -- Test: test
    -- (cof_and (cof_eq $(dim0) $(dim1)) (cof_eq $(dim0) $(dim1)))

  end Meet

  section Join

    def joinBotL (t : Term) : Term :=
      match t with
      | .con "cof_or" [.con "cof_bot" [], φ] => φ
      | _ => t

    def joinBotR (t : Term) : Term :=
      match t with
      | .con "cof_or" [φ, .con "cof_bot" []] => φ
      | _ => t

    def joinTopL (t : Term) : Term :=
      match t with
      | .con "cof_or" [.con "cof_top" [], φ] => Term.con "cof_top" []
      | _ => t

    def joinTopR (t : Term) : Term :=
      match t with
      | .con "cof_or" [φ, .con "cof_top" []] => Term.con "cof_top" []
      | _ => t

    def joinIdem (t : Term) : Term :=
      match t with
      | .con "cof_or" [φ, φ_dup] => φ
      | _ => t

    -- Test: test
    -- (cof_or $(cof_bot) (cof_eq $(dim0) $(dim0)))

    -- Test: test
    -- (cof_or $(cof_top) (cof_eq $(dim0) $(dim1)))

    -- Test: test
    -- (cof_or (cof_eq $(dim0) $(dim1)) (cof_eq $(dim0) $(dim1)))

  end Join

  section Normalize

    def normTop (t : Term) : Term :=
      match t with
      | .con "app" [.var "normCof", .con "cof_top" []] => Term.con "cof_top" []
      | _ => t

    def normBot (t : Term) : Term :=
      match t with
      | .con "app" [.var "normCof", .con "cof_bot" []] => Term.con "cof_bot" []
      | _ => t

    def normEq (t : Term) : Term :=
      match t with
      | .con "app" [.var "normCof", .con "cof_eq" [r, s]] => Term.con "cofEq" [r, s]
      | _ => t

    def normAnd (t : Term) : Term :=
      match t with
      | .con "app" [.var "normCof", .con "cof_and" [φ, ψ]] => Term.con "cof_and" [Term.con "app" [Term.var "normCof", φ], Term.con "app" [Term.var "normCof", ψ]]
      | _ => t

    def normOr (t : Term) : Term :=
      match t with
      | .con "app" [.var "normCof", .con "cof_or" [φ, ψ]] => Term.con "cof_or" [Term.con "app" [Term.var "normCof", φ], Term.con "app" [Term.var "normCof", ψ]]
      | _ => t

  end Normalize

  section Decide

    def cofTrueTop (t : Term) : Term :=
      match t with
      | .con "app" [.var "cofTrue", .con "cof_top" []] => Term.con "true" []
      | _ => t

    def cofTrueBot (t : Term) : Term :=
      match t with
      | .con "app" [.var "cofTrue", .con "cof_bot" []] => Term.con "false" []
      | _ => t

    def cofTrueEq (t : Term) : Term :=
      match t with
      | .con "app" [.var "cofTrue", .con "cof_eq" [r, s]] => Term.con "dimEq" [r, s]
      | _ => t

    def cofTrueAnd (t : Term) : Term :=
      match t with
      | .con "app" [.var "cofTrue", .con "cof_and" [φ, ψ]] => Term.con "and" [Term.con "app" [Term.var "cofTrue", φ], Term.con "app" [Term.var "cofTrue", ψ]]
      | _ => t

    def cofTrueOr (t : Term) : Term :=
      match t with
      | .con "app" [.var "cofTrue", .con "cof_or" [φ, ψ]] => Term.con "or" [Term.con "app" [Term.var "cofTrue", φ], Term.con "app" [Term.var "cofTrue", ψ]]
      | _ => t

    def cofFalse (t : Term) : Term :=
      match t with
      | .con "app" [.var "cofFalse", φ] => Term.con "app" [Term.var "not", Term.con "app" [Term.var "cofTrue", φ]]
      | _ => t

    -- Test: test
    -- ()

    -- Test: test
    -- ()

    -- Test: test
    -- ()

  end Decide

  section Sequent

    def entails (t : Term) : Term :=
      match t with
      | .con "entails" [φ, ψ] => Term.con "app" [Term.var "cofTrue", Term.con "cof_or" [Term.con "app" [Term.var "cof_not", φ], ψ]]
      | _ => t

    def notTop (t : Term) : Term :=
      match t with
      | .con "app" [.var "cof_not", .con "cof_top" []] => Term.con "cof_bot" []
      | _ => t

    def notBot (t : Term) : Term :=
      match t with
      | .con "app" [.var "cof_not", .con "cof_bot" []] => Term.con "cof_top" []
      | _ => t

  end Sequent

  section DimSubst

    def substCofTop (t : Term) : Term :=
      match t with
      | .con "substCof" [n, r, .con "cof_top" []] => Term.con "cof_top" []
      | _ => t

    def substCofBot (t : Term) : Term :=
      match t with
      | .con "substCof" [n, r, .con "cof_bot" []] => Term.con "cof_bot" []
      | _ => t

    def substCofEq (t : Term) : Term :=
      match t with
      | .con "substCof" [n, r, .con "cof_eq" [s, t]] => Term.con "cof_eq" [Term.con "substDimInDim" [n, r, s], Term.con "substDimInDim" [n, r, t]]
      | _ => t

    def substCofAnd (t : Term) : Term :=
      match t with
      | .con "substCof" [n, r, .con "cof_and" [φ, ψ]] => Term.con "cof_and" [Term.con "substCof" [n, r, φ], Term.con "substCof" [n, r, ψ]]
      | _ => t

    def substCofOr (t : Term) : Term :=
      match t with
      | .con "substCof" [n, r, .con "cof_or" [φ, ψ]] => Term.con "cof_or" [Term.con "substCof" [n, r, φ], Term.con "substCof" [n, r, ψ]]
      | _ => t

    def substDimVar (t : Term) : Term :=
      match t with
      | .con "substDimInDim" [n, r, .con "app" [.var "dimVar", n_dup]] => r
      | _ => t

    def substDimVarOther (t : Term) : Term :=
      match t with
      | .con "substDimInDim" [n, r, .con "app" [.var "dimVar", m]] => Term.con "app" [Term.var "dimVar", m]
      | _ => t

    def substDim0 (t : Term) : Term :=
      match t with
      | .con "substDimInDim" [n, r, .con "dim0" []] => Term.con "dim0" []
      | _ => t

    def substDim1 (t : Term) : Term :=
      match t with
      | .con "substDimInDim" [n, r, .con "dim1" []] => Term.con "dim1" []
      | _ => t

  end DimSubst

  section Forall

    def forallCof (t : Term) : Term :=
      match t with
      | .con "forallDim" [i, φ] => Term.con "cof_and" [Term.con "substCof" [i, Term.con "dim0" [], φ], Term.con "substCof" [i, Term.con "dim1" [], φ]]
      | _ => t

    def existsCof (t : Term) : Term :=
      match t with
      | .con "existsDim" [i, φ] => Term.con "cof_or" [Term.con "substCof" [i, Term.con "dim0" [], φ], Term.con "substCof" [i, Term.con "dim1" [], φ]]
      | _ => t

    -- Derived substitution for cof
    -- Binders: [lam, pi, sigma, plam, pathLam, extLam, let, glue]
    mutual
    partial def substcof (k : Nat) (v : Term) (t : Term) : Term :=
      match t with
      | Term.con "ix" [Term.con "number" [Term.lit n]] =>
        let idx := n.toNat!
        if idx == k then v
        else if idx > k then Term.con "ix" [Term.con "number" [Term.lit (toString (idx - 1))]]
        else t
      | Term.con tag args =>
        let isBinder := ["lam", "pi", "sigma", "plam", "pathLam", "extLam", "let", "glue"].contains tag
        if isBinder && args.length > 0 then
          Term.con tag (args.dropLast.map (substcof k v) ++ [substcof (k + 1) (shiftcof 0 1 v) args.getLast!])
        else
          Term.con tag (args.map (substcof k v))
      | _ => t
    
    partial def shiftcof (c : Nat) (n : Int) (t : Term) : Term :=
      match t with
      | Term.con "ix" [Term.con "number" [Term.lit m]] =>
        let idx := m.toNat!
        if idx >= c then Term.con "ix" [Term.con "number" [Term.lit (toString (Int.toNat (idx + n)))]]
        else t
      | Term.con tag args =>
        let isBinder := ["lam", "pi", "sigma", "plam", "pathLam", "extLam", "let", "glue"].contains tag
        if isBinder && args.length > 0 then
          Term.con tag (args.dropLast.map (shiftcof c n) ++ [shiftcof (c + 1) n args.getLast!])
        else
          Term.con tag (args.map (shiftcof c n))
      | _ => t
    end

    -- Derived normalizer for cof with fuel=1000
    mutual
    partial def normalizecof (fuel : Nat) (t : Term) : Term :=
      if fuel == 0 then t else
      let t' := stepcof t
      if t' == t then t else normalizecof (fuel - 1) t'
    
    partial def stepcof (t : Term) : Term :=
      match t with
      | Term.con "app" [Term.con "lam" [body], arg] => substcof 0 arg body
      | Term.con "fst" [Term.con "pair" [a, _]] => a
      | Term.con "snd" [Term.con "pair" [_, b]] => b
      | Term.con tag args => Term.con tag (args.map stepcof)
      | _ => t
    end

    -- Derived catamorphism for cof
    partial def catacof [Inhabited α] (alg : String → List α → α) (varF : String → α) (t : Term) : α :=
      match t with
      | Term.var n => varF n
      | Term.lit s => alg "lit" []
      | Term.con tag args => alg tag (args.map (catacof alg varF))

  end Forall

end Cofibration