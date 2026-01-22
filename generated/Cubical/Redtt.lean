/-
  AUTO-GENERATED from .lego files
  Do not edit directly.
-/

import Lego.Algebra

open Lego

namespace Redtt

  -- Token definitions for: Token (commented out)

  section File



  end File

  section Imports



  end Imports

  section Definitions



  end Definitions

  section Meta



  end Meta

  section DataTypes



  end DataTypes

  section Expr



  end Expr

  section Lambda



  end Lambda

  section Let



  end Let

  section Types



  end Types

  section Application



  end Application

  section Atoms



  end Atoms

  section PathTypes



  end PathTypes

  section Cubical



  end Cubical

  section Universe



  end Universe

  section VTypes



  end VTypes

  section EquivTypes



  end EquivTypes

  section FunExtApd



  end FunExtApd

  section Connections



  end Connections

  section SquareTypes



  end SquareTypes

  section Eliminators



  end Eliminators

  section BoxCap



  end BoxCap

  section RawTerms



  end RawTerms

  section RunML

    -- Derived substitution for expr
    -- Binders: [lam]
    mutual
    partial def substexpr (k : Nat) (v : Term) (t : Term) : Term :=
      match t with
      | Term.con "ix" [Term.con "number" [Term.lit n]] =>
        let idx := n.toNat!
        if idx == k then v
        else if idx > k then Term.con "ix" [Term.con "number" [Term.lit (toString (idx - 1))]]
        else t
      | Term.con tag args =>
        let isBinder := ["lam"].contains tag
        if isBinder && args.length > 0 then
          Term.con tag (args.dropLast.map (substexpr k v) ++ [substexpr (k + 1) (shiftexpr 0 1 v) args.getLast!])
        else
          Term.con tag (args.map (substexpr k v))
      | _ => t
    
    partial def shiftexpr (c : Nat) (n : Int) (t : Term) : Term :=
      match t with
      | Term.con "ix" [Term.con "number" [Term.lit m]] =>
        let idx := m.toNat!
        if idx >= c then Term.con "ix" [Term.con "number" [Term.lit (toString (Int.toNat (idx + n)))]]
        else t
      | Term.con tag args =>
        let isBinder := ["lam"].contains tag
        if isBinder && args.length > 0 then
          Term.con tag (args.dropLast.map (shiftexpr c n) ++ [shiftexpr (c + 1) n args.getLast!])
        else
          Term.con tag (args.map (shiftexpr c n))
      | _ => t
    end

    -- Derived normalizer for expr with fuel=1000
    mutual
    partial def normalizeexpr (fuel : Nat) (t : Term) : Term :=
      if fuel == 0 then t else
      let t' := stepexpr t
      if t' == t then t else normalizeexpr (fuel - 1) t'
    
    partial def stepexpr (t : Term) : Term :=
      match t with
      | Term.con "app" [Term.con "lam" [body], arg] => substexpr 0 arg body
      | Term.con "fst" [Term.con "pair" [a, _]] => a
      | Term.con "snd" [Term.con "pair" [_, b]] => b
      | Term.con tag args => Term.con tag (args.map stepexpr)
      | _ => t
    end

    -- Derived catamorphism for expr
    partial def cataexpr [Inhabited α] (alg : String → List α → α) (varF : String → α) (t : Term) : α :=
      match t with
      | Term.var n => varF n
      | Term.lit s => alg "lit" []
      | Term.con tag args => alg tag (args.map (cataexpr alg varF))

    def beta_lam (t : Term) : Term :=
      match t with
      | .con "App" [.con "Lam" [x, body], arg] => Term.con "subst" [body, x, arg]
      | _ => t

    def beta_fst (t : Term) : Term :=
      match t with
      | .con "app" [.var "Fst", .con "Cons" [a, b]] => a
      | _ => t

    def beta_snd (t : Term) : Term :=
      match t with
      | .con "app" [.var "Snd", .con "Cons" [a, b]] => b
      | _ => t

    def beta_let (t : Term) : Term :=
      match t with
      | .con "Let" [x, val, body] => Term.con "subst" [body, x, val]
      | _ => t

    def beta_extapp_0 (t : Term) : Term :=
      match t with
      | .con "ExtApp" [.con "ExtLam" [i, body], .con "Dim0" []] => Term.con "subst" [body, i, Term.con "Dim0" []]
      | _ => t

    def beta_extapp_1 (t : Term) : Term :=
      match t with
      | .con "ExtApp" [.con "ExtLam" [i, body], .con "Dim1" []] => Term.con "subst" [body, i, Term.con "Dim1" []]
      | _ => t

    def coe_refl (t : Term) : Term :=
      match t with
      | .con "Coe" [r, r_dup, ty, tm] => tm
      | _ => t

    def hcom_refl (t : Term) : Term :=
      match t with
      | .con "HCom" [r, r_dup, ty, cap, sys] => cap
      | _ => t

    def coe_const (t : Term) : Term :=
      match t with
      | .con "Coe" [r, r', .con "app" [.var "const", A], tm] => tm
      | _ => t

    def path_app_refl (t : Term) : Term :=
      match t with
      | .con "ExtApp" [.con "app" [.var "Refl", a], r] => a
      | _ => t

    def path_0 (t : Term) : Term :=
      match t with
      | .con "ExtApp" [.con "ExtLam" [i, body], .con "Dim0" []] => Term.con "subst" [body, i, Term.con "Dim0" []]
      | _ => t

    def path_1 (t : Term) : Term :=
      match t with
      | .con "ExtApp" [.con "ExtLam" [i, body], .con "Dim1" []] => Term.con "subst" [body, i, Term.con "Dim1" []]
      | _ => t

    def v_0 (t : Term) : Term :=
      match t with
      | .con "V" [.con "Dim0" [], ty0, ty1, equiv] => ty0
      | _ => t

    def v_1 (t : Term) : Term :=
      match t with
      | .con "V" [.con "Dim1" [], ty0, ty1, equiv] => ty1
      | _ => t

    def vin_0 (t : Term) : Term :=
      match t with
      | .con "VIn" [.con "Dim0" [], tm0, tm1] => tm0
      | _ => t

    def vin_1 (t : Term) : Term :=
      match t with
      | .con "VIn" [.con "Dim1" [], tm0, tm1] => tm1
      | _ => t

    def elim_intro (t : Term) : Term :=
      match t with
      | .con "Elim" [.con "Intro" [dlbl, clbl, args], mot, clauses] => Term.con "apply-clause" [Term.con "lookup" [clbl, clauses], args]
      | _ => t

    -- Test: test
    -- ()

    -- Test: test
    -- (import $(prelude) $(path))

    -- Test: test
    -- (def $(id) $(x) $(x))

    -- Test: test
    -- (def $(id) (x $(COLON) $(A)) $(COLON) $(A) $(x))

    -- Derived structural equality for expr
    partial def eqexpr (t1 t2 : Term) : Bool :=
      match t1, t2 with
      | Term.var n1, Term.var n2 => n1 == n2
      | Term.lit s1, Term.lit s2 => s1 == s2
      | Term.con tag1 args1, Term.con tag2 args2 =>
        tag1 == tag2 && args1.length == args2.length && (args1.zip args2).all fun (a, b) => eqexpr a b
      | _, _ => false

  end RunML

end Redtt