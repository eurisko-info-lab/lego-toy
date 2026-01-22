/-
  AUTO-GENERATED from .lego files
  Do not edit directly.
-/

import Lego.Algebra

open Lego

namespace Red

  section ExtType

    def extBeta (t : Term) : Term :=
      match t with
      | .con "extApp" [.con "app" [.var "extLam", .con "binder" [.lit "$", .var "x", .lit ".", body]], r] => Term.con "subst" [Term.lit "[", Term.var "x", Term.lit ":=", r, Term.lit "]", body]
      | _ => t

    def extApp0 (t : Term) : Term :=
      match t with
      | .con "extApp" [.con "app" [.var "extLam", .con "binder" [.lit "$", .var "x", .lit ".", body]], .con "num" [.con "number" [.lit "0"]]] => Term.con "subst" [Term.lit "[", Term.var "x", Term.lit ":=", Term.con "num" [Term.con "number" [Term.lit "0"]], Term.lit "]", body]
      | _ => t

    def extApp1 (t : Term) : Term :=
      match t with
      | .con "extApp" [.con "app" [.var "extLam", .con "binder" [.lit "$", .var "x", .lit ".", body]], .con "num" [.con "number" [.lit "1"]]] => Term.con "subst" [Term.lit "[", Term.var "x", Term.lit ":=", Term.con "num" [Term.con "number" [Term.lit "1"]], Term.lit "]", body]
      | _ => t

    -- Test: test
    -- (extApp (extLam (objBinder i . (f $(i)))) (num (number 0)))

  end ExtType

  section GCom

    def ghcomRefl (t : Term) : Term :=
      match t with
      | .con "ghcom" [r, .lit "~>", r_dup, A, sys, a] => a
      | _ => t

    def gcomRefl (t : Term) : Term :=
      match t with
      | .con "gcom" [r, .lit "~>", r_dup, .con "binderParen" [.lit "(", .lit "$", .var "i", .lit ".", A, .lit ")"], sys, a] => a
      | _ => t

    def ghcomBdy (t : Term) : Term :=
      match t with
      | .con "ghcom" [r, .lit "~>", s, A, .con "bracket" [.lit "[", φ, .lit "↦", .con "binder" [.lit "$", .var "i", .lit ".", u], .lit "]"], a] => Term.con "subst" [Term.lit "[", Term.var "i", Term.lit ":=", s, Term.lit "]", u]
      | _ => t

    def gcomBdy (t : Term) : Term :=
      match t with
      | .con "gcom" [r, .lit "~>", s, .con "binderParen" [.lit "(", .lit "$", .var "i", .lit ".", A, .lit ")"], .con "bracket" [.lit "[", φ, .lit "↦", .con "binder" [.lit "$", .var "j", .lit ".", u], .lit "]"], a] => Term.con "subst" [Term.lit "[", Term.var "j", Term.lit ":=", s, Term.lit "]", u]
      | _ => t

  end GCom

  section Data

    def introElim (t : Term) : Term :=
      match t with
      | .con "elim" [e, .con "tuple" [C, ms], .con "intro" [c, as]] => Term.con "tuple" [Term.con "app" [Term.lit "(", ms, c, Term.lit ")"], as]
      | _ => t

    def introBdy (t : Term) : Term :=
      match t with
      | .con "intro" [c, as] => Term.var "bdy"
      | _ => t

  end Data

  section Twin

    def twin0 (t : Term) : Term :=
      match t with
      | .con "twin" [x, y, .con "num" [.con "number" [.lit "0"]], a] => Term.con "subst" [Term.lit "[", y, Term.lit ":=", x, Term.lit "]", a]
      | _ => t

    def twin1 (t : Term) : Term :=
      match t with
      | .con "twin" [x, y, .con "num" [.con "number" [.lit "1"]], a] => a
      | _ => t

    def twinSym (t : Term) : Term :=
      match t with
      | .con "twin" [x, y, i, .con "twin" [y_dup, x_dup, .con "tuple" [.con "num" [.con "number" [.lit "1"]], .lit "-", i_dup], a]] => a
      | _ => t

  end Twin

  section Restrict



  end Restrict

  section FHcom

    def fhcomRefl (t : Term) : Term :=
      match t with
      | .con "fhcom" [r, .lit "~>", r_dup, A, sys, a] => a
      | _ => t

    def fhcomBdy (t : Term) : Term :=
      match t with
      | .con "fhcom" [r, .lit "~>", s, A, .con "bracket" [.lit "[", φ, .lit "↦", .con "binder" [.lit "$", .var "i", .lit ".", u], .lit "]"], a] => Term.con "subst" [Term.lit "[", Term.var "i", Term.lit ":=", s, Term.lit "]", u]
      | _ => t

  end FHcom

  section BoxCap

    def capBox (t : Term) : Term :=
      match t with
      | .con "cap" [r, .lit "~>", s, sys, .con "box" [r_dup, .lit "~>", s_dup, sys', a]] => a
      | _ => t

    def boxBdy (t : Term) : Term :=
      match t with
      | .con "box" [r, .lit "~>", s, .con "bracket" [.lit "[", φ, .lit "↦", u, .lit "]"], a] => u
      | _ => t

  end BoxCap

  section Coeq

    def coeqGlue0 (t : Term) : Term :=
      match t with
      | .con "coeqGlue" [a, .con "num" [.con "number" [.lit "0"]]] => Term.con "app" [Term.var "coeqIn", Term.con "tuple" [Term.var "f", a]]
      | _ => t

    def coeqGlue1 (t : Term) : Term :=
      match t with
      | .con "coeqGlue" [a, .con "num" [.con "number" [.lit "1"]]] => Term.con "app" [Term.var "coeqIn", Term.con "tuple" [Term.var "g", a]]
      | _ => t

    def coeqElimIn (t : Term) : Term :=
      match t with
      | .con "coeqElim" [P, h, p, .con "app" [.var "coeqIn", b]] => Term.con "tuple" [h, b]
      | _ => t

  end Coeq

  section Pushout

    def push0 (t : Term) : Term :=
      match t with
      | .con "push" [a, .con "num" [.con "number" [.lit "0"]]] => Term.con "app" [Term.var "inl", Term.con "tuple" [Term.var "f", a]]
      | _ => t

    def push1 (t : Term) : Term :=
      match t with
      | .con "push" [a, .con "num" [.con "number" [.lit "1"]]] => Term.con "app" [Term.var "inr", Term.con "tuple" [Term.var "g", a]]
      | _ => t

    def pushElimInl (t : Term) : Term :=
      match t with
      | .con "pushElim" [P, l, r, p, .con "app" [.var "inl", a]] => Term.con "tuple" [l, a]
      | _ => t

    def pushElimInr (t : Term) : Term :=
      match t with
      | .con "pushElim" [P, l, r, p, .con "app" [.var "inr", b]] => Term.con "tuple" [r, b]
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

    -- Derived structural equality for term
    partial def eqterm (t1 t2 : Term) : Bool :=
      match t1, t2 with
      | Term.var n1, Term.var n2 => n1 == n2
      | Term.lit s1, Term.lit s2 => s1 == s2
      | Term.con tag1 args1, Term.con tag2 args2 =>
        tag1 == tag2 && args1.length == args2.length && (args1.zip args2).all fun (a, b) => eqterm a b
      | _, _ => false

  end Pushout

end Red