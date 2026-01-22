/-
  AUTO-GENERATED from .lego files
  Do not edit directly.
-/

import Lego.Algebra

open Lego

namespace Signature

  section Label

    def labelToString (t : Term) : Term :=
      match t with
      | .con "app" [.var "labelToString", .con "app" [.var "userLabel", s]] => s
      | _ => t

    def labelToStringAnon (t : Term) : Term :=
      match t with
      | .con "app" [.var "labelToString", .con "app" [.var "anonLabel", n]] => Term.con "strConcat" [Term.con "terminal" [Term.lit "_"], Term.con "app" [Term.var "natToString", n]]
      | _ => t

    def isAnonLabel (t : Term) : Term :=
      match t with
      | .con "app" [.var "isAnonLabel", .con "app" [.var "anonLabel", n]] => Term.con "true" []
      | _ => t

    def isAnonLabelUser (t : Term) : Term :=
      match t with
      | .con "app" [.var "isAnonLabel", .con "app" [.var "userLabel", s]] => Term.con "false" []
      | _ => t

    def labelEq (t : Term) : Term :=
      match t with
      | .con "labelEq" [.con "app" [.var "userLabel", s1], .con "app" [.var "userLabel", s2]] => Term.con "eq" [s1, s2]
      | _ => t

    def labelEqAnon (t : Term) : Term :=
      match t with
      | .con "labelEq" [.con "app" [.var "anonLabel", n1], .con "app" [.var "anonLabel", n2]] => Term.con "eq" [n1, n2]
      | _ => t

    def labelEqMix (t : Term) : Term :=
      match t with
      | .con "labelEq" [l1, l2] => Term.con "false" []
      | _ => t

  end Label

  section Cell

    def cellLabel (t : Term) : Term :=
      match t with
      | .con "app" [.var "cellLabel", .con "teleCell" [.con "labeledArg" [.var "label", .lit ":", l], .con "labeledArg" [.var "ty", .lit ":", t]]] => l
      | _ => t

    def cellTy (t : Term) : Term :=
      match t with
      | .con "app" [.var "cellTy", .con "teleCell" [.con "labeledArg" [.var "label", .lit ":", l], .con "labeledArg" [.var "ty", .lit ":", t]]] => t
      | _ => t

  end Cell

  section Telescope

    def telescopeEmpty (t : Term) : Term :=
      match t with
      | .con "telescopeEmpty" [] => Term.con "telescope" []
      | _ => t

    def telescopeExtend (t : Term) : Term :=
      match t with
      | .con "telescopeExtend" [.con "app" [.var "telescope", cells], lbl, ty] => Term.con "telescope" [cells, Term.con "teleCell" [Term.con "labeledArg" [Term.var "label", Term.lit ":", lbl], Term.con "labeledArg" [Term.var "ty", Term.lit ":", ty]]]
      | _ => t

    def telescopeLength (t : Term) : Term :=
      match t with
      | .con "app" [.var "telescopeLength", .con "telescope" []] => Term.con "num" [Term.con "number" [Term.lit "0"]]
      | _ => t

    def telescopeLengthCons (t : Term) : Term :=
      match t with
      | .con "app" [.var "telescopeLength", .con "telescope" [cells, c]] => Term.con "app" [Term.var "succ", Term.con "app" [Term.var "telescopeLength", Term.con "app" [Term.var "telescope", cells]]]
      | _ => t

    def telescopeLabels (t : Term) : Term :=
      match t with
      | .con "app" [.var "telescopeLabels", .con "telescope" []] => Term.con "unit" [Term.lit "(", Term.lit ")"]
      | _ => t

    def telescopeLabelsCons (t : Term) : Term :=
      match t with
      | .con "app" [.var "telescopeLabels", .con "telescope" [cells, c]] => Term.con "tuple" [Term.con "app" [Term.lit "(", Term.con "telescopeLabels" [Term.con "app" [Term.var "telescope", cells]], Term.lit ")"], Term.con "app" [Term.var "cellLabel", c]]
      | _ => t

    def telescopeFindByLabel (t : Term) : Term :=
      match t with
      | .con "telescopeFindByLabel" [.con "telescope" [], lbl] => Term.con "none" []
      | _ => t

    def telescopeFindByLabelMatch (t : Term) : Term :=
      match t with
      | .con "telescopeFindByLabel" [.con "telescope" [cells, .con "teleCell" [.con "labeledArg" [.var "label", .lit ":", lbl], .con "labeledArg" [.var "ty", .lit ":", t]]], lbl_dup] => Term.con "app" [Term.var "some", Term.con "tuple" [Term.lit "(", Term.con "app" [Term.var "telescopeLength", Term.con "app" [Term.var "telescope", cells]], Term.lit ",", Term.con "teleCell" [Term.con "labeledArg" [Term.var "label", Term.lit ":", lbl], Term.con "labeledArg" [Term.var "ty", Term.lit ":", t]], Term.lit ")"]]
      | _ => t

    def telescopeFindByLabelMiss (t : Term) : Term :=
      match t with
      | .con "telescopeFindByLabel" [.con "telescope" [cells, c], lbl] => Term.con "telescopeFindByLabel" [Term.con "app" [Term.var "telescope", cells], lbl]
      | _ => t

    def telescopeTypeAt (t : Term) : Term :=
      match t with
      | .con "telescopeTypeAt" [.con "telescope" [], idx] => Term.con "none" []
      | _ => t

    def telescopeTypeAtHit (t : Term) : Term :=
      match t with
      | .con "telescopeTypeAt" [.con "telescope" [cells, c], .con "num" [.con "number" [.lit "0"]]] => Term.con "app" [Term.var "some", Term.con "app" [Term.var "cellTy", c]]
      | _ => t

    def telescopeTypeAtMiss (t : Term) : Term :=
      match t with
      | .con "telescopeTypeAt" [.con "telescope" [cells, c], .con "app" [.var "succ", n]] => Term.con "telescopeTypeAt" [Term.con "app" [Term.var "telescope", cells], n]
      | _ => t

    def telescopeShiftAll (t : Term) : Term :=
      match t with
      | .con "telescopeShiftAll" [delta, .con "telescope" []] => Term.con "telescope" []
      | _ => t

    def telescopeShiftAllCons (t : Term) : Term :=
      match t with
      | .con "telescopeShiftAll" [delta, .con "telescope" [cells, c]] => Term.con "telescope" [Term.con "telescopeShiftAll" [delta, Term.con "app" [Term.var "telescope", cells]], Term.con "teleCell" [Term.con "labeledArg" [Term.var "label", Term.lit ":", Term.con "app" [Term.var "cellLabel", c]], Term.con "labeledArg" [Term.var "ty", Term.lit ":", Term.con "shift" [Term.con "num" [Term.con "number" [Term.lit "0"]], delta, Term.con "app" [Term.var "cellTy", c]]]]]
      | _ => t

  end Telescope

  section KCell

    def kCellLabel (t : Term) : Term :=
      match t with
      | .con "app" [.var "kCellLabel", .con "kCell" [.con "labeledArg" [.var "label", .lit ":", l], .con "labeledArg" [.var "code", .lit ":", c]]] => l
      | _ => t

    def kCellCode (t : Term) : Term :=
      match t with
      | .con "app" [.var "kCellCode", .con "kCell" [.con "labeledArg" [.var "label", .lit ":", l], .con "labeledArg" [.var "code", .lit ":", c]]] => c
      | _ => t

  end KCell

  section KTelescope

    def kTelescopeEmpty (t : Term) : Term :=
      match t with
      | .con "kTelescopeEmpty" [] => Term.con "kTelescope" []
      | _ => t

    def kTelescopeExtend (t : Term) : Term :=
      match t with
      | .con "kTelescopeExtend" [.con "app" [.var "kTelescope", cells], lbl, code] => Term.con "kTelescope" [cells, Term.con "kCell" [Term.con "labeledArg" [Term.var "label", Term.lit ":", lbl], Term.con "labeledArg" [Term.var "code", Term.lit ":", code]]]
      | _ => t

    def kTelescopeLength (t : Term) : Term :=
      match t with
      | .con "app" [.var "kTelescopeLength", .con "kTelescope" []] => Term.con "num" [Term.con "number" [Term.lit "0"]]
      | _ => t

    def kTelescopeLengthCons (t : Term) : Term :=
      match t with
      | .con "app" [.var "kTelescopeLength", .con "kTelescope" [cells, c]] => Term.con "app" [Term.var "succ", Term.con "app" [Term.var "kTelescopeLength", Term.con "app" [Term.var "kTelescope", cells]]]
      | _ => t

    def kTelescopeToTelescope (t : Term) : Term :=
      match t with
      | .con "app" [.var "kTelescopeToTelescope", .con "kTelescope" []] => Term.con "telescope" []
      | _ => t

    def kTelescopeToTelescopeCons (t : Term) : Term :=
      match t with
      | .con "app" [.var "kTelescopeToTelescope", .con "kTelescope" [cells, c]] => Term.con "telescope" [Term.con "app" [Term.var "kTelescopeToTelescope", Term.con "app" [Term.var "kTelescope", cells]], Term.con "teleCell" [Term.con "labeledArg" [Term.var "label", Term.lit ":", Term.con "app" [Term.var "kCellLabel", c]], Term.con "labeledArg" [Term.var "ty", Term.lit ":", Term.con "app" [Term.var "kCellCode", c]]]]
      | _ => t

  end KTelescope

  section SignatureType

    def sigTypeEmpty (t : Term) : Term :=
      match t with
      | .con "sigTypeEmpty" [] => Term.con "app" [Term.var "sigType", Term.con "telescopeEmpty" []]
      | _ => t

    def sigTypeSingle (t : Term) : Term :=
      match t with
      | .con "sigTypeSingle" [lbl, ty] => Term.con "app" [Term.var "sigType", Term.con "telescopeExtend" [Term.con "telescopeEmpty" [], lbl, ty]]
      | _ => t

    def sigTypeExtend (t : Term) : Term :=
      match t with
      | .con "sigTypeExtend" [.con "app" [.var "sigType", tele], lbl, ty] => Term.con "app" [Term.var "sigType", Term.con "telescopeExtend" [tele, lbl, ty]]
      | _ => t

    def sigTypeNumFields (t : Term) : Term :=
      match t with
      | .con "app" [.var "sigTypeNumFields", .con "app" [.var "sigType", tele]] => Term.con "app" [Term.var "telescopeLength", tele]
      | _ => t

    def sigTypeLabels (t : Term) : Term :=
      match t with
      | .con "app" [.var "sigTypeLabels", .con "app" [.var "sigType", tele]] => Term.con "app" [Term.var "telescopeLabels", tele]
      | _ => t

    def sigTypeFindField (t : Term) : Term :=
      match t with
      | .con "sigTypeFindField" [.con "app" [.var "sigType", tele], lbl] => Term.con "caseExpr" [Term.lit "(", Term.lit "case", Term.con "telescopeFindByLabel" [tele, lbl], Term.con "arm" [Term.lit "(", Term.var "some", Term.con "tuple" [Term.lit "(", Term.var "idx", Term.lit ",", Term.var "cell", Term.lit ")"], Term.lit ")", Term.lit "=>", Term.con "app" [Term.var "some", Term.var "idx"]], Term.con "arm" [Term.var "none", Term.lit "=>", Term.con "none" []], Term.lit ")"]
      | _ => t

    def sigTypeFieldType (t : Term) : Term :=
      match t with
      | .con "sigTypeFieldType" [.con "app" [.var "sigType", tele], idx] => Term.con "telescopeTypeAt" [tele, idx]
      | _ => t

    def sigTypeToSigma (t : Term) : Term :=
      match t with
      | .con "app" [.var "sigTypeToSigma", .con "app" [.var "sigType", .con "telescope" []]] => Term.con "app" [Term.var "univ", Term.con "num" [Term.con "number" [Term.lit "0"]]]
      | _ => t

    def sigTypeToSigmaSingle (t : Term) : Term :=
      match t with
      | .con "app" [.var "sigTypeToSigma", .con "app" [.var "sigType", .con "app" [.var "telescope", c]]] => Term.con "app" [Term.var "cellTy", c]
      | _ => t

    def sigTypeToSigmaMulti (t : Term) : Term :=
      match t with
      | .con "app" [.var "sigTypeToSigma", .con "app" [.var "sigType", .con "telescope" [cells, c]]] => Term.con "sigma" [Term.con "app" [Term.var "cellTy", Term.con "app" [Term.var "head", cells]], Term.con "app" [Term.var "sigTypeToSigma", Term.con "app" [Term.var "sigType", Term.con "telescope" [Term.con "app" [Term.var "tail", cells], c]]]]
      | _ => t

    def head (t : Term) : Term :=
      match t with
      | .con "app" [.var "head", .con "tuple" [x, rest]] => x
      | _ => t

    def tail (t : Term) : Term :=
      match t with
      | .con "app" [.var "tail", .con "tuple" [x, rest]] => rest
      | _ => t

  end SignatureType

  section Field

    def fieldLabel (t : Term) : Term :=
      match t with
      | .con "app" [.var "fieldLabel", .con "field" [.con "labeledArg" [.var "label", .lit ":", l], .con "labeledArg" [.var "value", .lit ":", v]]] => l
      | _ => t

    def fieldValue (t : Term) : Term :=
      match t with
      | .con "app" [.var "fieldValue", .con "field" [.con "labeledArg" [.var "label", .lit ":", l], .con "labeledArg" [.var "value", .lit ":", v]]] => v
      | _ => t

  end Field

  section Struct

    def structEmpty (t : Term) : Term :=
      match t with
      | .con "structEmpty" [] => Term.con "struct" []
      | _ => t

    def structSingle (t : Term) : Term :=
      match t with
      | .con "structSingle" [lbl, val] => Term.con "app" [Term.var "struct", Term.con "field" [Term.con "labeledArg" [Term.var "label", Term.lit ":", lbl], Term.con "labeledArg" [Term.var "value", Term.lit ":", val]]]
      | _ => t

    def structExtend (t : Term) : Term :=
      match t with
      | .con "structExtend" [.con "app" [.var "struct", fields], lbl, val] => Term.con "struct" [fields, Term.con "field" [Term.con "labeledArg" [Term.var "label", Term.lit ":", lbl], Term.con "labeledArg" [Term.var "value", Term.lit ":", val]]]
      | _ => t

    def structNumFields (t : Term) : Term :=
      match t with
      | .con "app" [.var "structNumFields", .con "struct" []] => Term.con "num" [Term.con "number" [Term.lit "0"]]
      | _ => t

    def structNumFieldsCons (t : Term) : Term :=
      match t with
      | .con "app" [.var "structNumFields", .con "struct" [fields, f]] => Term.con "app" [Term.var "succ", Term.con "app" [Term.var "structNumFields", Term.con "app" [Term.var "struct", fields]]]
      | _ => t

    def structLabels (t : Term) : Term :=
      match t with
      | .con "app" [.var "structLabels", .con "struct" []] => Term.con "unit" [Term.lit "(", Term.lit ")"]
      | _ => t

    def structLabelsCons (t : Term) : Term :=
      match t with
      | .con "app" [.var "structLabels", .con "struct" [fields, f]] => Term.con "tuple" [Term.con "app" [Term.lit "(", Term.con "structLabels" [Term.con "app" [Term.var "struct", fields]], Term.lit ")"], Term.con "app" [Term.var "fieldLabel", f]]
      | _ => t

    def structValues (t : Term) : Term :=
      match t with
      | .con "app" [.var "structValues", .con "struct" []] => Term.con "unit" [Term.lit "(", Term.lit ")"]
      | _ => t

    def structValuesCons (t : Term) : Term :=
      match t with
      | .con "app" [.var "structValues", .con "struct" [fields, f]] => Term.con "tuple" [Term.con "app" [Term.lit "(", Term.con "structValues" [Term.con "app" [Term.var "struct", fields]], Term.lit ")"], Term.con "app" [Term.var "fieldValue", f]]
      | _ => t

    def structFindField (t : Term) : Term :=
      match t with
      | .con "structFindField" [.con "struct" [], lbl] => Term.con "none" []
      | _ => t

    def structFindFieldMatch (t : Term) : Term :=
      match t with
      | .con "structFindField" [.con "struct" [fields, .con "field" [.con "labeledArg" [.var "label", .lit ":", lbl], .con "labeledArg" [.var "value", .lit ":", v]]], lbl_dup] => Term.con "app" [Term.var "some", Term.con "field" [Term.con "labeledArg" [Term.var "label", Term.lit ":", lbl], Term.con "labeledArg" [Term.var "value", Term.lit ":", v]]]
      | _ => t

    def structFindFieldMiss (t : Term) : Term :=
      match t with
      | .con "structFindField" [.con "struct" [fields, f], lbl] => Term.con "structFindField" [Term.con "app" [Term.var "struct", fields], lbl]
      | _ => t

    def structGetField (t : Term) : Term :=
      match t with
      | .con "structGetField" [s, lbl] => Term.con "caseExpr" [Term.lit "(", Term.lit "case", Term.con "structFindField" [s, lbl], Term.con "arm" [Term.lit "(", Term.var "some", Term.var "f", Term.lit ")", Term.lit "=>", Term.con "app" [Term.var "some", Term.con "app" [Term.var "fieldValue", Term.var "f"]]], Term.con "arm" [Term.var "none", Term.lit "=>", Term.con "none" []], Term.lit ")"]
      | _ => t

    def structGetAt (t : Term) : Term :=
      match t with
      | .con "structGetAt" [.con "struct" [], idx] => Term.con "none" []
      | _ => t

    def structGetAtHit (t : Term) : Term :=
      match t with
      | .con "structGetAt" [.con "struct" [fields, f], .con "num" [.con "number" [.lit "0"]]] => Term.con "app" [Term.var "some", Term.con "app" [Term.var "fieldValue", f]]
      | _ => t

    def structGetAtMiss (t : Term) : Term :=
      match t with
      | .con "structGetAt" [.con "struct" [fields, f], .con "app" [.var "succ", n]] => Term.con "structGetAt" [Term.con "app" [Term.var "struct", fields], n]
      | _ => t

    def structToPair (t : Term) : Term :=
      match t with
      | .con "app" [.var "structToPair", .con "struct" []] => Term.con "app" [Term.var "lit", Term.con "terminal" [Term.lit "unit"]]
      | _ => t

    def structToPairSingle (t : Term) : Term :=
      match t with
      | .con "app" [.var "structToPair", .con "app" [.var "struct", f]] => Term.con "app" [Term.var "fieldValue", f]
      | _ => t

    def structToPairMulti (t : Term) : Term :=
      match t with
      | .con "app" [.var "structToPair", .con "struct" [fields, f]] => Term.con "pair" [Term.con "app" [Term.var "fieldValue", Term.con "app" [Term.var "head", fields]], Term.con "app" [Term.var "structToPair", Term.con "struct" [Term.con "app" [Term.var "tail", fields], f]]]
      | _ => t

    def structFromList (t : Term) : Term :=
      match t with
      | .con "app" [.var "structFromList", .con "unit" [.lit "(", .lit ")"]] => Term.con "structEmpty" []
      | _ => t

    def structFromListCons (t : Term) : Term :=
      match t with
      | .con "app" [.var "structFromList", .con "app" [.lit "(", .lit "(", lbl, .lit ",", val, .lit ")", rest, .lit ")"]] => Term.con "structExtend" [Term.con "app" [Term.var "structFromList", rest], lbl, val]
      | _ => t

  end Struct

  section Projection

    def projAt (t : Term) : Term :=
      match t with
      | .con "projAt" [e, .con "num" [.con "number" [.lit "0"]]] => Term.con "app" [Term.var "fst", e]
      | _ => t

    def projAtSucc (t : Term) : Term :=
      match t with
      | .con "projAt" [e, .con "app" [.var "succ", n]] => Term.con "projAt" [Term.con "app" [Term.var "snd", e], n]
      | _ => t

    def mkProj (t : Term) : Term :=
      match t with
      | .con "mkProj" [struct, lbl, idx] => Term.con "projAt" [struct, idx]
      | _ => t

  end Projection

  section Unpack

    def unpack (t : Term) : Term :=
      match t with
      | .con "app" [.var "unpack", s] => Term.con "app" [Term.var "structValues", s]
      | _ => t

  end Unpack

  section SignatureKan

    def mcoeTele (t : Term) : Term :=
      match t with
      | .con "mcoeTele" [r, r', .con "kTelescope" [], struct] => struct
      | _ => t

    def mcoeTeleCons (t : Term) : Term :=
      match t with
      | .con "mcoeTele" [r, r', .con "kTelescope" [cells, c], struct] => Term.con "letIn" [Term.lit "(", Term.lit "let", Term.lit "$", Term.var "coedFirst", Term.lit "=", Term.con "coe" [r, r', Term.con "app" [Term.var "kCellCode", c], Term.con "structGetAt" [struct, Term.con "num" [Term.con "number" [Term.lit "0"]]]], Term.lit "in", Term.con "structExtend" [Term.con "mcoeTele" [r, r', Term.con "app" [Term.var "kTelescope", cells], Term.con "app" [Term.var "structTail", struct]], Term.con "app" [Term.var "kCellLabel", c], Term.var "coedFirst"], Term.lit ")"]
      | _ => t

    def structTail (t : Term) : Term :=
      match t with
      | .con "app" [.var "structTail", .con "struct" [f, rest]] => Term.con "app" [Term.var "struct", rest]
      | _ => t

    def mcomTele (t : Term) : Term :=
      match t with
      | .con "mcomTele" [r, r', .con "kTelescope" [], φ, tubes, cap] => cap
      | _ => t

    def mcomTeleCons (t : Term) : Term :=
      match t with
      | .con "mcomTele" [r, r', .con "kTelescope" [cells, c], φ, tubes, cap] => Term.con "letIn" [Term.lit "(", Term.lit "let", Term.lit "$", Term.var "comFirst", Term.lit "=", Term.con "com" [Term.con "app" [Term.var "kCellCode", c], r, r', φ, Term.con "app" [Term.var "lam", Term.con "app" [Term.var "lam", Term.con "structGetAt" [Term.con "app" [Term.con "app" [Term.con "shift" [Term.con "num" [Term.con "number" [Term.lit "0"]], Term.con "num" [Term.con "number" [Term.lit "2"]], tubes], Term.con "app" [Term.var "ix", Term.con "num" [Term.con "number" [Term.lit "1"]]]], Term.con "app" [Term.var "ix", Term.con "num" [Term.con "number" [Term.lit "0"]]]], Term.con "num" [Term.con "number" [Term.lit "0"]]]]], Term.con "structGetAt" [cap, Term.con "num" [Term.con "number" [Term.lit "0"]]]], Term.lit "in", Term.con "structExtend" [Term.con "mcomTele" [r, r', Term.con "app" [Term.var "kTelescope", cells], φ, Term.con "app" [Term.var "lam", Term.con "app" [Term.var "lam", Term.con "app" [Term.var "structTail", Term.con "app" [Term.con "app" [Term.con "shift" [Term.con "num" [Term.con "number" [Term.lit "0"]], Term.con "num" [Term.con "number" [Term.lit "2"]], tubes], Term.con "app" [Term.var "ix", Term.con "num" [Term.con "number" [Term.lit "1"]]]], Term.con "app" [Term.var "ix", Term.con "num" [Term.con "number" [Term.lit "0"]]]]]]], Term.con "app" [Term.var "structTail", cap]], Term.con "app" [Term.var "kCellLabel", c], Term.var "comFirst"], Term.lit ")"]
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

  end SignatureKan

end Signature