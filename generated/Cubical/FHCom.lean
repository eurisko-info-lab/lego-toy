/-
  AUTO-GENERATED from .lego files
  Do not edit directly.
-/

import Lego.Algebra

open Lego

namespace FHCom

  section FHComInfo

    def fhcomInfoR (t : Term) : Term :=
      match t with
      | .con "app" [.var "fhcomInfoR", .con "fhcomInfo" [.con "labeledArg" [.var "r", .lit ":", r], .con "labeledArg" [.var "r'", .lit ":", r'], .con "labeledArg" [.var "cap", .lit ":", c], .con "labeledArg" [.var "sys", .lit ":", s]]] => r
      | _ => t

    def fhcomInfoR' (t : Term) : Term :=
      match t with
      | .con "app" [.var "fhcomInfoR'", .con "fhcomInfo" [.con "labeledArg" [.var "r", .lit ":", r], .con "labeledArg" [.var "r'", .lit ":", r'], .con "labeledArg" [.var "cap", .lit ":", c], .con "labeledArg" [.var "sys", .lit ":", s]]] => r'
      | _ => t

    def fhcomInfoCap (t : Term) : Term :=
      match t with
      | .con "app" [.var "fhcomInfoCap", .con "fhcomInfo" [.con "labeledArg" [.var "r", .lit ":", r], .con "labeledArg" [.var "r'", .lit ":", r'], .con "labeledArg" [.var "cap", .lit ":", c], .con "labeledArg" [.var "sys", .lit ":", s]]] => c
      | _ => t

    def fhcomInfoSys (t : Term) : Term :=
      match t with
      | .con "app" [.var "fhcomInfoSys", .con "fhcomInfo" [.con "labeledArg" [.var "r", .lit ":", r], .con "labeledArg" [.var "r'", .lit ":", r'], .con "labeledArg" [.var "cap", .lit ":", c], .con "labeledArg" [.var "sys", .lit ":", s]]] => s
      | _ => t

    def fhcomInfoIsDegenerate (t : Term) : Term :=
      match t with
      | .con "app" [.var "fhcomInfoIsDegenerate", .con "fhcomInfo" [.con "labeledArg" [.var "r", .lit ":", r], .con "labeledArg" [.var "r'", .lit ":", r'], .con "labeledArg" [.var "cap", .lit ":", c], .con "labeledArg" [.var "sys", .lit ":", s]]] => Term.con "eq" [r, r']
      | _ => t

    def fhcomInfoAtR (t : Term) : Term :=
      match t with
      | .con "app" [.var "fhcomInfoAtR", .con "fhcomInfo" [.con "labeledArg" [.var "r", .lit ":", r], .con "labeledArg" [.var "r'", .lit ":", r'], .con "labeledArg" [.var "cap", .lit ":", c], .con "labeledArg" [.var "sys", .lit ":", s]]] => c
      | _ => t

    def fhcomInfoAtR' (t : Term) : Term :=
      match t with
      | .con "app" [.var "fhcomInfoAtR'", .con "fhcomInfo" [.con "labeledArg" [.var "r", .lit ":", r], .con "labeledArg" [.var "r'", .lit ":", r'], .con "labeledArg" [.var "cap", .lit ":", c], .con "labeledArg" [.var "sys", .lit ":", s]]] => Term.con "caseExpr" [Term.lit "(", Term.lit "case", Term.con "eq" [r, r'], Term.con "arm" [Term.var "true", Term.lit "=>", c], Term.con "arm" [Term.var "false", Term.lit "=>", c], Term.lit ")"]
      | _ => t

    def fhcomInfoReduce (t : Term) : Term :=
      match t with
      | .con "app" [.var "fhcomInfoReduce", .con "fhcomInfo" [.con "labeledArg" [.var "r", .lit ":", r], .con "labeledArg" [.var "r'", .lit ":", r'], .con "labeledArg" [.var "cap", .lit ":", c], .con "labeledArg" [.var "sys", .lit ":", s]]] => Term.con "caseExpr" [Term.lit "(", Term.lit "case", Term.con "eq" [r, r'], Term.con "arm" [Term.var "true", Term.lit "=>", Term.con "app" [Term.var "some", c]], Term.con "arm" [Term.var "false", Term.lit "=>", Term.con "none" []], Term.lit ")"]
      | _ => t

  end FHComInfo

  section MkFHCom

    def mkFHCom (t : Term) : Term :=
      match t with
      | .con "mkFHCom" [r, r', cap, sys] => Term.con "caseExpr" [Term.lit "(", Term.lit "case", Term.con "eq" [r, r'], Term.con "arm" [Term.var "true", Term.lit "=>", cap], Term.con "arm" [Term.var "false", Term.lit "=>", Term.con "fhcom" [r, r', cap, sys]], Term.lit ")"]
      | _ => t

  end MkFHCom

  section BoxInfo

    def boxInfoR (t : Term) : Term :=
      match t with
      | .con "app" [.var "boxInfoR", .con "boxInfo" [.con "labeledArg" [.var "r", .lit ":", r], .con "labeledArg" [.var "r'", .lit ":", r'], .con "labeledArg" [.var "cap", .lit ":", c], .con "labeledArg" [.var "sys", .lit ":", s]]] => r
      | _ => t

    def boxInfoR' (t : Term) : Term :=
      match t with
      | .con "app" [.var "boxInfoR'", .con "boxInfo" [.con "labeledArg" [.var "r", .lit ":", r], .con "labeledArg" [.var "r'", .lit ":", r'], .con "labeledArg" [.var "cap", .lit ":", c], .con "labeledArg" [.var "sys", .lit ":", s]]] => r'
      | _ => t

    def boxInfoCap (t : Term) : Term :=
      match t with
      | .con "app" [.var "boxInfoCap", .con "boxInfo" [.con "labeledArg" [.var "r", .lit ":", r], .con "labeledArg" [.var "r'", .lit ":", r'], .con "labeledArg" [.var "cap", .lit ":", c], .con "labeledArg" [.var "sys", .lit ":", s]]] => c
      | _ => t

    def boxInfoSys (t : Term) : Term :=
      match t with
      | .con "app" [.var "boxInfoSys", .con "boxInfo" [.con "labeledArg" [.var "r", .lit ":", r], .con "labeledArg" [.var "r'", .lit ":", r'], .con "labeledArg" [.var "cap", .lit ":", c], .con "labeledArg" [.var "sys", .lit ":", s]]] => s
      | _ => t

    def boxInfoIsDegenerate (t : Term) : Term :=
      match t with
      | .con "app" [.var "boxInfoIsDegenerate", .con "boxInfo" [.con "labeledArg" [.var "r", .lit ":", r], .con "labeledArg" [.var "r'", .lit ":", r'], .con "labeledArg" [.var "cap", .lit ":", c], .con "labeledArg" [.var "sys", .lit ":", s]]] => Term.con "eq" [r, r']
      | _ => t

    def boxInfoGetCap (t : Term) : Term :=
      match t with
      | .con "app" [.var "boxInfoGetCap", .con "boxInfo" [.con "labeledArg" [.var "r", .lit ":", r], .con "labeledArg" [.var "r'", .lit ":", r'], .con "labeledArg" [.var "cap", .lit ":", c], .con "labeledArg" [.var "sys", .lit ":", s]]] => c
      | _ => t

    def boxInfoReduce (t : Term) : Term :=
      match t with
      | .con "app" [.var "boxInfoReduce", .con "boxInfo" [.con "labeledArg" [.var "r", .lit ":", r], .con "labeledArg" [.var "r'", .lit ":", r'], .con "labeledArg" [.var "cap", .lit ":", c], .con "labeledArg" [.var "sys", .lit ":", s]]] => Term.con "caseExpr" [Term.lit "(", Term.lit "case", Term.con "eq" [r, r'], Term.con "arm" [Term.var "true", Term.lit "=>", Term.con "app" [Term.var "some", c]], Term.con "arm" [Term.var "false", Term.lit "=>", Term.con "none" []], Term.lit ")"]
      | _ => t

  end BoxInfo

  section MkBox

    def mkBox (t : Term) : Term :=
      match t with
      | .con "mkBox" [r, r', cap, sys] => Term.con "caseExpr" [Term.lit "(", Term.lit "case", Term.con "eq" [r, r'], Term.con "arm" [Term.var "true", Term.lit "=>", cap], Term.con "arm" [Term.var "false", Term.lit "=>", Term.con "box" [r, r', cap, sys]], Term.lit ")"]
      | _ => t

  end MkBox

  section CapInfo

    def capInfoR (t : Term) : Term :=
      match t with
      | .con "app" [.var "capInfoR", .con "capInfo" [.con "labeledArg" [.var "r", .lit ":", r], .con "labeledArg" [.var "r'", .lit ":", r'], .con "labeledArg" [.var "ty", .lit ":", t], .con "labeledArg" [.var "sys", .lit ":", s], .con "labeledArg" [.var "el", .lit ":", e]]] => r
      | _ => t

    def capInfoR' (t : Term) : Term :=
      match t with
      | .con "app" [.var "capInfoR'", .con "capInfo" [.con "labeledArg" [.var "r", .lit ":", r], .con "labeledArg" [.var "r'", .lit ":", r'], .con "labeledArg" [.var "ty", .lit ":", t], .con "labeledArg" [.var "sys", .lit ":", s], .con "labeledArg" [.var "el", .lit ":", e]]] => r'
      | _ => t

    def capInfoTy (t : Term) : Term :=
      match t with
      | .con "app" [.var "capInfoTy", .con "capInfo" [.con "labeledArg" [.var "r", .lit ":", r], .con "labeledArg" [.var "r'", .lit ":", r'], .con "labeledArg" [.var "ty", .lit ":", t], .con "labeledArg" [.var "sys", .lit ":", s], .con "labeledArg" [.var "el", .lit ":", e]]] => t
      | _ => t

    def capInfoSys (t : Term) : Term :=
      match t with
      | .con "app" [.var "capInfoSys", .con "capInfo" [.con "labeledArg" [.var "r", .lit ":", r], .con "labeledArg" [.var "r'", .lit ":", r'], .con "labeledArg" [.var "ty", .lit ":", t], .con "labeledArg" [.var "sys", .lit ":", s], .con "labeledArg" [.var "el", .lit ":", e]]] => s
      | _ => t

    def capInfoEl (t : Term) : Term :=
      match t with
      | .con "app" [.var "capInfoEl", .con "capInfo" [.con "labeledArg" [.var "r", .lit ":", r], .con "labeledArg" [.var "r'", .lit ":", r'], .con "labeledArg" [.var "ty", .lit ":", t], .con "labeledArg" [.var "sys", .lit ":", s], .con "labeledArg" [.var "el", .lit ":", e]]] => e
      | _ => t

  end CapInfo

  section MkCap

    def mkCapBox (t : Term) : Term :=
      match t with
      | .con "mkCap" [r, r', ty, sys, .con "box" [r_dup, r'_dup, cap, sysBx]] => cap
      | _ => t

    def mkCapDegenerate (t : Term) : Term :=
      match t with
      | .con "mkCap" [r, r_dup, ty, sys, v] => v
      | _ => t

    def mkCapOther (t : Term) : Term :=
      match t with
      | .con "mkCap" [r, r', ty, sys, v] => Term.con "cap" [r, r', ty, sys, v]
      | _ => t

  end MkCap

  section ReduceFHCom

    def reduceFHComDegenerate (t : Term) : Term :=
      match t with
      | .con "app" [.var "reduceFHCom", .con "fhcom" [r, r_dup, cap, sys]] => Term.con "app" [Term.var "some", cap]
      | _ => t

    def reduceFHComOther (t : Term) : Term :=
      match t with
      | .con "app" [.var "reduceFHCom", e] => Term.con "none" []
      | _ => t

    def reduceBoxDegenerate (t : Term) : Term :=
      match t with
      | .con "app" [.var "reduceBox", .con "box" [r, r_dup, cap, sys]] => Term.con "app" [Term.var "some", cap]
      | _ => t

    def reduceBoxOther (t : Term) : Term :=
      match t with
      | .con "app" [.var "reduceBox", e] => Term.con "none" []
      | _ => t

    def reduceCapBeta (t : Term) : Term :=
      match t with
      | .con "app" [.var "reduceCap", .con "cap" [r, r', ty, sys, .con "box" [r_dup, r'_dup, cap, sysBx]]] => Term.con "app" [Term.var "some", cap]
      | _ => t

    def reduceCapDegenerate (t : Term) : Term :=
      match t with
      | .con "app" [.var "reduceCap", .con "cap" [r, r_dup, ty, sys, v]] => Term.con "app" [Term.var "some", v]
      | _ => t

    def reduceCapOther (t : Term) : Term :=
      match t with
      | .con "app" [.var "reduceCap", e] => Term.con "none" []
      | _ => t

  end ReduceFHCom

  section HComFHCom

    def hcomFHCom (t : Term) : Term :=
      match t with
      | .con "hcomFHCom" [r, r', .con "fhcom" [rTy, r'Ty, capTy, sysTy], φ, tubes, cap] => Term.con "mkBox" [r, r', Term.con "hcom" [capTy, r, r', φ, Term.con "app" [Term.var "lam", Term.con "app" [Term.var "lam", Term.con "mkCap" [rTy, r'Ty, capTy, sysTy, Term.con "app" [Term.con "app" [Term.con "shift" [Term.con "num" [Term.con "number" [Term.lit "0"]], Term.con "num" [Term.con "number" [Term.lit "2"]], tubes], Term.con "app" [Term.var "ix", Term.con "num" [Term.con "number" [Term.lit "1"]]]], Term.con "app" [Term.var "ix", Term.con "num" [Term.con "number" [Term.lit "0"]]]]]]], Term.con "mkCap" [rTy, r'Ty, capTy, sysTy, cap]], Term.con "hcomSys" [sysTy, φ, tubes, cap, r, r']]
      | _ => t

    def hcomSys (t : Term) : Term :=
      match t with
      | .con "hcomSys" [.con "unit" [.lit "(", .lit ")"], φ, tubes, cap, r, r'] => Term.con "unit" [Term.lit "(", Term.lit ")"]
      | _ => t

    def hcomSysCons (t : Term) : Term :=
      match t with
      | .con "hcomSys" [.con "app" [.lit "(", .lit "(", .lit "[", φSys, .lit "↦", tube, .lit "]", .lit ")", rest, .lit ")"], φ, tubes, cap, r, r'] => Term.con "tuple" [Term.con "app" [Term.lit "(", Term.con "bracket" [Term.lit "[", φSys, Term.lit "↦", Term.con "app" [Term.var "lam", Term.con "app" [Term.var "lam", Term.con "getSide" [Term.con "app" [Term.con "app" [Term.con "shift" [Term.con "num" [Term.con "number" [Term.lit "0"]], Term.con "num" [Term.con "number" [Term.lit "2"]], tubes], Term.con "app" [Term.var "ix", Term.con "num" [Term.con "number" [Term.lit "1"]]]], Term.con "app" [Term.var "ix", Term.con "num" [Term.con "number" [Term.lit "0"]]]], φSys]]], Term.lit "]"], Term.lit ")"], Term.con "hcomSys" [rest, φ, tubes, cap, r, r']]
      | _ => t

    def getSide (t : Term) : Term :=
      match t with
      | .con "getSide" [.con "box" [r, r', cap, sys], φ] => Term.con "lookupSys" [sys, φ]
      | _ => t

    def getSideOther (t : Term) : Term :=
      match t with
      | .con "getSide" [e, φ] => e
      | _ => t

    def lookupSysNil (t : Term) : Term :=
      match t with
      | .con "lookupSys" [.con "unit" [.lit "(", .lit ")"], φ] => Term.con "app" [Term.var "lit", Term.con "terminal" [Term.lit "side-not-found"]]
      | _ => t

    def lookupSysMatch (t : Term) : Term :=
      match t with
      | .con "lookupSys" [.con "app" [.lit "(", .lit "(", .lit "[", φ, .lit "↦", side, .lit "]", .lit ")", rest, .lit ")"], φ_dup] => side
      | _ => t

    def lookupSysMiss (t : Term) : Term :=
      match t with
      | .con "lookupSys" [.con "app" [.lit "(", .lit "(", entry, .lit ")", rest, .lit ")"], φ] => Term.con "lookupSys" [rest, φ]
      | _ => t

  end HComFHCom

  section CoeFHCom

    def coeFHCom (t : Term) : Term :=
      match t with
      | .con "coeFHCom" [r, r', .con "app" [.var "lam", .con "fhcom" [rTy, r'Ty, capTy, sysTy]], v] => Term.con "mkBox" [r, r', Term.con "com" [Term.con "app" [Term.var "lam", capTy], r, r', Term.con "cof_bot" [Term.con "paren" [Term.lit "(", Term.con "lam" [Term.con "paren" [Term.lit "(", Term.con "lam" [Term.con "app" [Term.var "lit", Term.con "terminal" [Term.lit "no-tube"]]], Term.lit ")"]], Term.lit ")"], Term.con "mkCap" [rTy, r'Ty, Term.con "subst" [Term.con "num" [Term.con "number" [Term.lit "0"]], r, capTy], sysTy, v]]], Term.con "unit" [Term.lit "(", Term.lit ")"]]
      | _ => t

  end CoeFHCom

  section VProjFHCom

    def vprojFHCom (t : Term) : Term :=
      match t with
      | .con "vprojFHCom" [r, .con "fhcom" [rTy, r'Ty, A, sys], B, equiv, v] => Term.con "mkCap" [rTy, r'Ty, A, sys, Term.con "vproj" [r, A, B, equiv, v]]
      | _ => t

  end VProjFHCom

  section UnfoldFHCom

    def unfoldFHComAt0 (t : Term) : Term :=
      match t with
      | .con "unfoldFHComAt" [.con "fhcom" [.con "dim0" [], r', cap, sys], .con "dim0" []] => cap
      | _ => t

    def unfoldFHComAt1 (t : Term) : Term :=
      match t with
      | .con "unfoldFHComAt" [.con "fhcom" [.con "dim1" [], r', cap, sys], .con "dim1" []] => cap
      | _ => t

    def unfoldFHComAtOther (t : Term) : Term :=
      match t with
      | .con "unfoldFHComAt" [fh, r] => fh
      | _ => t

    def unfoldBoxAt0 (t : Term) : Term :=
      match t with
      | .con "unfoldBoxAt" [.con "box" [.con "dim0" [], r', cap, sys], .con "dim0" []] => cap
      | _ => t

    def unfoldBoxAt1 (t : Term) : Term :=
      match t with
      | .con "unfoldBoxAt" [.con "box" [.con "dim1" [], r', cap, sys], .con "dim1" []] => cap
      | _ => t

    def unfoldBoxAtOther (t : Term) : Term :=
      match t with
      | .con "unfoldBoxAt" [bx, r] => bx
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

  end UnfoldFHCom

end FHCom