/-
  AUTO-GENERATED from .lego files
  Do not edit directly.
-/

import Lego.Algebra

set_option linter.unusedVariables false

open Lego

namespace GlobalEnv

  section GName

    def gnameNamed (t : Term) : Term :=
      match t with
      | .con "app" [.var "gnameNamed", s] => Term.con "gname" [s, Term.con "labeledArg" [Term.var "source", Term.lit ":", Term.con "none" []]]
      | _ => t

    def gnameFresh (t : Term) : Term :=
      match t with
      | .con "gnameFresh" [base, counter] => Term.con "gname" [Term.con "concat" [base, Term.con "terminal" [Term.lit "_"], counter], Term.con "labeledArg" [Term.var "source", Term.lit ":", Term.con "none" []]]
      | _ => t

    def gnameAnonymous (t : Term) : Term :=
      match t with
      | .con "gnameAnonymous" [] => Term.con "gname" [Term.con "terminal" [Term.lit "_"], Term.con "labeledArg" [Term.var "source", Term.lit ":", Term.con "none" []]]
      | _ => t

    def gnameName (t : Term) : Term :=
      match t with
      | .con "app" [.var "gnameName", .con "gname" [n, .con "labeledArg" [.var "source", .lit ":", s]]] => n
      | _ => t

    def gnameSource (t : Term) : Term :=
      match t with
      | .con "app" [.var "gnameSource", .con "gname" [n, .con "labeledArg" [.var "source", .lit ":", s]]] => s
      | _ => t

    def gnameEq (t : Term) : Term :=
      match t with
      | .con "gnameEq" [.con "gname" [n1, .con "labeledArg" [.var "source", .lit ":", s1]], .con "gname" [n2, .con "labeledArg" [.var "source", .lit ":", s2]]] => Term.con "eq" [n1, n2]
      | _ => t

  end GName

  section GArgSpec



  end GArgSpec

  section GConstructor

    def gconstructorName (t : Term) : Term :=
      match t with
      | .con "app" [.var "gconstructorName", .con "constructor" [.con "labeledArg" [.var "name", .lit ":", n], .con "labeledArg" [.var "args", .lit ":", a], .con "labeledArg" [.var "boundary", .lit ":", b]]] => n
      | _ => t

    def gconstructorArgs (t : Term) : Term :=
      match t with
      | .con "app" [.var "gconstructorArgs", .con "constructor" [.con "labeledArg" [.var "name", .lit ":", n], .con "labeledArg" [.var "args", .lit ":", a], .con "labeledArg" [.var "boundary", .lit ":", b]]] => a
      | _ => t

    def gconstructorBoundary (t : Term) : Term :=
      match t with
      | .con "app" [.var "gconstructorBoundary", .con "constructor" [.con "labeledArg" [.var "name", .lit ":", n], .con "labeledArg" [.var "args", .lit ":", a], .con "labeledArg" [.var "boundary", .lit ":", b]]] => b
      | _ => t

  end GConstructor

  section GDataDesc

    def gdataDescName (t : Term) : Term :=
      match t with
      | .con "app" [.var "gdataDescName", .con "dataDesc" [.con "labeledArg" [.var "name", .lit ":", n], .con "labeledArg" [.var "params", .lit ":", p], .con "labeledArg" [.var "level", .lit ":", l], .con "labeledArg" [.var "constrs", .lit ":", c]]] => n
      | _ => t

    def gdataDescParams (t : Term) : Term :=
      match t with
      | .con "app" [.var "gdataDescParams", .con "dataDesc" [.con "labeledArg" [.var "name", .lit ":", n], .con "labeledArg" [.var "params", .lit ":", p], .con "labeledArg" [.var "level", .lit ":", l], .con "labeledArg" [.var "constrs", .lit ":", c]]] => p
      | _ => t

    def gdataDescLevel (t : Term) : Term :=
      match t with
      | .con "app" [.var "gdataDescLevel", .con "dataDesc" [.con "labeledArg" [.var "name", .lit ":", n], .con "labeledArg" [.var "params", .lit ":", p], .con "labeledArg" [.var "level", .lit ":", l], .con "labeledArg" [.var "constrs", .lit ":", c]]] => l
      | _ => t

    def gdataDescConstrs (t : Term) : Term :=
      match t with
      | .con "app" [.var "gdataDescConstrs", .con "dataDesc" [.con "labeledArg" [.var "name", .lit ":", n], .con "labeledArg" [.var "params", .lit ":", p], .con "labeledArg" [.var "level", .lit ":", l], .con "labeledArg" [.var "constrs", .lit ":", c]]] => c
      | _ => t

  end GDataDesc

  section GEntry

    def gEntryGetType (t : Term) : Term :=
      match t with
      | .con "app" [.var "gEntryGetType", .con "app" [.var "param", ty]] => Term.con "app" [Term.var "some", ty]
      | _ => t

    def gEntryGetTypeDefn (t : Term) : Term :=
      match t with
      | .con "app" [.var "gEntryGetType", .con "defn" [.con "labeledArg" [.var "type", .lit ":", ty], .con "labeledArg" [.var "value", .lit ":", v]]] => Term.con "app" [Term.var "some", ty]
      | _ => t

    def gEntryGetTypeDatatype (t : Term) : Term :=
      match t with
      | .con "app" [.var "gEntryGetType", .con "app" [.var "datatype", desc]] => Term.con "app" [Term.var "some", Term.con "app" [Term.var "univ", Term.con "app" [Term.var "gdataDescLevel", desc]]]
      | _ => t

    def gEntryGetTypeDimVar (t : Term) : Term :=
      match t with
      | .con "app" [.var "gEntryGetType", .con "dimVar" []] => Term.con "app" [Term.var "some", Term.con "app" [Term.var "lit", Term.con "terminal" [Term.lit "𝕀"]]]
      | _ => t

    def gEntryGetTypeMeta (t : Term) : Term :=
      match t with
      | .con "app" [.var "gEntryGetType", .con "metaVar" [.con "labeledArg" [.var "type", .lit ":", ty], .con "labeledArg" [.var "solution", .lit ":", sol]]] => Term.con "app" [Term.var "some", ty]
      | _ => t

  end GEntry

  section GlobalEnv

    def globalEnvEmpty (t : Term) : Term :=
      match t with
      | .con "globalEnvEmpty" [] => Term.con "globalEnv" [Term.con "labeledArg" [Term.var "entries", Term.lit ":", Term.con "unit" [Term.lit "(", Term.lit ")"]], Term.con "labeledArg" [Term.var "order", Term.lit ":", Term.con "unit" [Term.lit "(", Term.lit ")"]]]
      | _ => t

    def globalEnvExtend (t : Term) : Term :=
      match t with
      | .con "globalEnvExtend" [.con "globalEnv" [.con "labeledArg" [.var "entries", .lit ":", entries], .con "labeledArg" [.var "order", .lit ":", order]], nm, entry] => Term.con "globalEnv" [Term.con "labeledArg" [Term.var "entries", Term.lit ":", Term.con "tuple" [entries, Term.con "app" [Term.lit "(", nm, Term.lit "↦", entry, Term.lit ")"]]], Term.con "labeledArg" [Term.var "order", Term.lit ":", Term.con "tuple" [nm, order]]]
      | _ => t

    def globalEnvDefine (t : Term) : Term :=
      match t with
      | .con "globalEnvDefine" [env, nm, ty, tm] => Term.con "globalEnvExtend" [env, nm, Term.con "defn" [Term.con "labeledArg" [Term.var "type", Term.lit ":", ty], Term.con "labeledArg" [Term.var "value", Term.lit ":", tm]]]
      | _ => t

    def globalEnvDeclareParam (t : Term) : Term :=
      match t with
      | .con "globalEnvDeclareParam" [env, nm, ty] => Term.con "globalEnvExtend" [env, nm, Term.con "app" [Term.var "param", ty]]
      | _ => t

    def globalEnvDeclareDim (t : Term) : Term :=
      match t with
      | .con "globalEnvDeclareDim" [env, nm] => Term.con "globalEnvExtend" [env, nm, Term.con "dimVar" []]
      | _ => t

    def globalEnvDeclareDatatype (t : Term) : Term :=
      match t with
      | .con "globalEnvDeclareDatatype" [env, desc] => Term.con "globalEnvExtend" [env, Term.con "app" [Term.var "gdataDescName", desc], Term.con "app" [Term.var "datatype", desc]]
      | _ => t

    def globalEnvCreateMeta (t : Term) : Term :=
      match t with
      | .con "globalEnvCreateMeta" [env, nm, ty] => Term.con "globalEnvExtend" [env, nm, Term.con "metaVar" [Term.con "labeledArg" [Term.var "type", Term.lit ":", ty], Term.con "labeledArg" [Term.var "solution", Term.lit ":", Term.con "none" []]]]
      | _ => t

    def globalEnvSolveMeta (t : Term) : Term :=
      match t with
      | .con "globalEnvSolveMeta" [.con "globalEnv" [.con "labeledArg" [.var "entries", .lit ":", entries], .con "labeledArg" [.var "order", .lit ":", order]], nm, solution] => Term.con "globalEnv" [Term.con "labeledArg" [Term.var "entries", Term.lit ":", Term.con "solveMeta'" [entries, nm, solution]], Term.con "labeledArg" [Term.var "order", Term.lit ":", order]]
      | _ => t

    def solveMeta'Nil (t : Term) : Term :=
      match t with
      | .con "solveMeta'" [.con "unit" [.lit "(", .lit ")"], nm, sol] => Term.con "unit" [Term.lit "(", Term.lit ")"]
      | _ => t

    def solveMeta'Match (t : Term) : Term :=
      match t with
      | .con "solveMeta'" [.con "app" [.lit "(", .lit "(", .lit "(", nm, .lit "↦", .con "metaVar" [.con "labeledArg" [.var "type", .lit ":", ty], .con "labeledArg" [.var "solution", .lit ":", old]], .lit ")", .lit ")", rest, .lit ")"], nm_dup, sol] => Term.con "tuple" [Term.con "app" [Term.lit "(", Term.con "tuple" [nm, Term.lit "↦", Term.con "metaVar" [Term.con "labeledArg" [Term.var "type", Term.lit ":", ty], Term.con "labeledArg" [Term.var "solution", Term.lit ":", Term.con "app" [Term.var "some", sol]]]], Term.lit ")"], rest]
      | _ => t

    def solveMeta'Miss (t : Term) : Term :=
      match t with
      | .con "solveMeta'" [.con "app" [.lit "(", .lit "(", entry, .lit ")", rest, .lit ")"], nm, sol] => Term.con "tuple" [Term.con "app" [Term.lit "(", entry, Term.lit ")"], Term.con "solveMeta'" [rest, nm, sol]]
      | _ => t

  end GlobalEnv

  section Lookup

    def globalEnvLookup (t : Term) : Term :=
      match t with
      | .con "globalEnvLookup" [.con "globalEnv" [.con "labeledArg" [.var "entries", .lit ":", entries], .con "labeledArg" [.var "order", .lit ":", order]], nm] => Term.con "lookupEntry" [entries, nm]
      | _ => t

    def lookupEntryNil (t : Term) : Term :=
      match t with
      | .con "lookupEntry" [.con "unit" [.lit "(", .lit ")"], nm] => Term.con "none" []
      | _ => t

    def lookupEntryMatch (t : Term) : Term :=
      match t with
      | .con "lookupEntry" [.con "app" [.lit "(", .lit "(", .lit "(", nm, .lit "↦", entry, .lit ")", .lit ")", rest, .lit ")"], nm_dup] => Term.con "app" [Term.var "some", entry]
      | _ => t

    def lookupEntryMiss (t : Term) : Term :=
      match t with
      | .con "lookupEntry" [.con "app" [.lit "(", .lit "(", .lit "(", nm', .lit "↦", entry, .lit ")", .lit ")", rest, .lit ")"], nm] => Term.con "lookupEntry" [rest, nm]
      | _ => t

    def globalEnvLookupType (t : Term) : Term :=
      match t with
      | .con "globalEnvLookupType" [env, nm] => Term.con "caseExpr" [Term.lit "(", Term.lit "case", Term.con "globalEnvLookup" [env, nm], Term.con "arm" [Term.lit "(", Term.var "some", Term.var "entry", Term.lit ")", Term.lit "=>", Term.con "app" [Term.var "gEntryGetType", Term.var "entry"]], Term.con "arm" [Term.var "none", Term.lit "=>", Term.con "none" []], Term.lit ")"]
      | _ => t

    def globalEnvLookupValue (t : Term) : Term :=
      match t with
      | .con "globalEnvLookupValue" [.con "globalEnv" [.con "labeledArg" [.var "entries", .lit ":", entries], .con "labeledArg" [.var "order", .lit ":", order]], nm] => Term.con "caseExpr" [Term.lit "(", Term.lit "case", Term.con "lookupEntry" [entries, nm], Term.con "arm" [Term.lit "(", Term.var "some", Term.con "defn" [Term.con "labeledArg" [Term.var "type", Term.lit ":", Term.var "ty"], Term.con "labeledArg" [Term.var "value", Term.lit ":", Term.var "v"]], Term.lit ")", Term.lit "=>", Term.con "app" [Term.var "some", Term.var "v"]], Term.con "arm" [Term.var "_", Term.lit "=>", Term.con "none" []], Term.lit ")"]
      | _ => t

    def globalEnvLookupDatatype (t : Term) : Term :=
      match t with
      | .con "globalEnvLookupDatatype" [.con "globalEnv" [.con "labeledArg" [.var "entries", .lit ":", entries], .con "labeledArg" [.var "order", .lit ":", order]], nm] => Term.con "caseExpr" [Term.lit "(", Term.lit "case", Term.con "lookupEntry" [entries, nm], Term.con "arm" [Term.lit "(", Term.var "some", Term.con "app" [Term.var "datatype", Term.var "desc"], Term.lit ")", Term.lit "=>", Term.con "app" [Term.var "some", Term.var "desc"]], Term.con "arm" [Term.var "_", Term.lit "=>", Term.con "none" []], Term.lit ")"]
      | _ => t

    def globalEnvLookupMeta (t : Term) : Term :=
      match t with
      | .con "globalEnvLookupMeta" [.con "globalEnv" [.con "labeledArg" [.var "entries", .lit ":", entries], .con "labeledArg" [.var "order", .lit ":", order]], nm] => Term.con "caseExpr" [Term.lit "(", Term.lit "case", Term.con "lookupEntry" [entries, nm], Term.con "arm" [Term.lit "(", Term.var "some", Term.con "metaVar" [Term.con "labeledArg" [Term.var "type", Term.lit ":", Term.var "ty"], Term.con "labeledArg" [Term.var "solution", Term.lit ":", Term.var "sol"]], Term.lit ")", Term.lit "=>", Term.con "app" [Term.var "some", Term.con "record" [Term.lit "(", Term.var "type", Term.lit ":", Term.var "ty", Term.con "labeledArg" [Term.var "solution", Term.lit ":", Term.var "sol"], Term.lit ")"]]], Term.con "arm" [Term.var "_", Term.lit "=>", Term.con "none" []], Term.lit ")"]
      | _ => t

  end Lookup

  section Query

    def globalEnvIsDefined (t : Term) : Term :=
      match t with
      | .con "globalEnvIsDefined" [env, nm] => Term.con "caseExpr" [Term.lit "(", Term.lit "case", Term.con "globalEnvLookup" [env, nm], Term.con "arm" [Term.lit "(", Term.var "some", Term.con "_" [], Term.lit ")", Term.lit "=>", Term.con "true" []], Term.con "arm" [Term.var "none", Term.lit "=>", Term.con "false" []], Term.lit ")"]
      | _ => t

    def globalEnvIsMetaSolved (t : Term) : Term :=
      match t with
      | .con "globalEnvIsMetaSolved" [env, nm] => Term.con "caseExpr" [Term.lit "(", Term.lit "case", Term.con "globalEnvLookupMeta" [env, nm], Term.con "arm" [Term.lit "(", Term.var "some", Term.con "type" [Term.lit ":", Term.var "ty", Term.con "labeledArg" [Term.var "solution", Term.lit ":", Term.con "app" [Term.var "some", Term.var "sol"]]], Term.lit ")", Term.lit "=>", Term.con "true" []], Term.con "arm" [Term.var "_", Term.lit "=>", Term.con "false" []], Term.lit ")"]
      | _ => t

    def globalEnvAllNames (t : Term) : Term :=
      match t with
      | .con "app" [.var "globalEnvAllNames", .con "globalEnv" [.con "labeledArg" [.var "entries", .lit ":", entries], .con "labeledArg" [.var "order", .lit ":", order]]] => order
      | _ => t

    def globalEnvFilterByKind (t : Term) : Term :=
      match t with
      | .con "globalEnvFilterByKind" [.con "globalEnv" [.con "labeledArg" [.var "entries", .lit ":", entries], .con "labeledArg" [.var "order", .lit ":", order]], kind] => Term.con "filter" [Term.con "fun" [Term.con "nm" [], Term.lit "=>", Term.con "matchKind" [Term.con "lookupEntry" [entries, Term.con "nm" []], kind]], order]
      | _ => t

    def matchKindDefn (t : Term) : Term :=
      match t with
      | .con "matchKind" [.con "app" [.var "some", .con "defn" [.con "labeledArg" [.var "type", .lit ":", t], .con "labeledArg" [.var "value", .lit ":", v]]], .con "defn" []] => Term.con "true" []
      | _ => t

    def matchKindParam (t : Term) : Term :=
      match t with
      | .con "matchKind" [.con "app" [.var "some", .con "app" [.var "param", t]], .con "param" []] => Term.con "true" []
      | _ => t

    def matchKindDatatype (t : Term) : Term :=
      match t with
      | .con "matchKind" [.con "app" [.var "some", .con "app" [.var "datatype", d]], .con "datatype" []] => Term.con "true" []
      | _ => t

    def matchKindDimVar (t : Term) : Term :=
      match t with
      | .con "matchKind" [.con "app" [.var "some", .con "dimVar" []], .con "dimVar" []] => Term.con "true" []
      | _ => t

    def matchKindMetaVar (t : Term) : Term :=
      match t with
      | .con "matchKind" [.con "app" [.var "some", .con "metaVar" [.con "labeledArg" [.var "type", .lit ":", t], .con "labeledArg" [.var "solution", .lit ":", s]]], .con "metaVar" []] => Term.con "true" []
      | _ => t

    def matchKindOther (t : Term) : Term :=
      match t with
      | .con "matchKind" [entry, kind] => Term.con "false" []
      | _ => t

  end Query

  section Unfold

    def unfoldOne (t : Term) : Term :=
      match t with
      | .con "unfoldOne" [env, .con "app" [.var "lit", name]] => Term.con "caseExpr" [Term.lit "(", Term.lit "case", Term.con "globalEnvLookupValue" [env, Term.con "app" [Term.var "gnameNamed", name]], Term.con "arm" [Term.lit "(", Term.var "some", Term.var "val", Term.lit ")", Term.lit "=>", Term.var "val"], Term.con "arm" [Term.var "none", Term.lit "=>", Term.con "app" [Term.var "lit", name]], Term.lit ")"]
      | _ => t

    def unfoldOneOther (t : Term) : Term :=
      match t with
      | .con "unfoldOne" [env, e] => e
      | _ => t

    def unfoldAll (t : Term) : Term :=
      match t with
      | .con "unfoldAll" [env, e] => Term.con "unfoldAll'" [env, e, Term.con "num" [Term.con "number" [Term.lit "100"]]]
      | _ => t

    def unfoldAll'0 (t : Term) : Term :=
      match t with
      | .con "unfoldAll'" [env, e, .con "num" [.con "number" [.lit "0"]]] => e
      | _ => t

    def unfoldAll' (t : Term) : Term :=
      match t with
      | .con "unfoldAll'" [env, e, .con "app" [.var "suc", fuel]] => Term.con "letIn" [Term.lit "(", Term.lit "let", Term.var "e'", Term.lit "=", Term.con "unfoldStep" [env, e], Term.lit "in", Term.con "caseExpr" [Term.lit "case", Term.con "eq" [Term.con "e'" [], e], Term.con "arm" [Term.var "true", Term.lit "=>", Term.con "e'" []], Term.con "arm" [Term.var "false", Term.lit "=>", Term.con "unfoldAll'" [env, Term.con "e'" [], fuel]]], Term.lit ")"]
      | _ => t

    def unfoldStepLit (t : Term) : Term :=
      match t with
      | .con "unfoldStep" [env, .con "app" [.var "lit", name]] => Term.con "caseExpr" [Term.lit "(", Term.lit "case", Term.con "globalEnvLookupValue" [env, Term.con "app" [Term.var "gnameNamed", name]], Term.con "arm" [Term.lit "(", Term.var "some", Term.var "val", Term.lit ")", Term.lit "=>", Term.var "val"], Term.con "arm" [Term.var "none", Term.lit "=>", Term.con "app" [Term.var "lit", name]], Term.lit ")"]
      | _ => t

    def unfoldStepApp (t : Term) : Term :=
      match t with
      | .con "unfoldStep" [env, .con "app" [f, a]] => Term.con "app" [Term.con "unfoldStep" [env, f], Term.con "unfoldStep" [env, a]]
      | _ => t

    def unfoldStepLam (t : Term) : Term :=
      match t with
      | .con "unfoldStep" [env, .con "app" [.var "lam", body]] => Term.con "app" [Term.var "lam", Term.con "unfoldStep" [env, body]]
      | _ => t

    def unfoldStepPi (t : Term) : Term :=
      match t with
      | .con "unfoldStep" [env, .con "pi" [dom, cod]] => Term.con "pi" [Term.con "unfoldStep" [env, dom], Term.con "unfoldStep" [env, cod]]
      | _ => t

    def unfoldStepOther (t : Term) : Term :=
      match t with
      | .con "unfoldStep" [env, e] => e
      | _ => t

  end Unfold

  section Print

    def globalEnvPrint (t : Term) : Term :=
      match t with
      | .con "app" [.var "globalEnvPrint", .con "globalEnv" [.con "labeledArg" [.var "entries", .lit ":", entries], .con "labeledArg" [.var "order", .lit ":", order]]] => Term.con "mapReverse" [Term.con "fun" [Term.con "nm" [], Term.lit "=>", Term.con "app" [Term.var "printEntry", Term.con "nm" [Term.con "lookupEntry" [entries, Term.con "nm" []]]]], order]
      | _ => t

    def printEntry (t : Term) : Term :=
      match t with
      | .con "printEntry" [nm, .con "app" [.var "some", .con "defn" [.con "labeledArg" [.var "type", .lit ":", ty], .con "labeledArg" [.var "value", .lit ":", v]]]] => Term.con "concat" [Term.con "terminal" [Term.lit "def "], Term.con "app" [Term.var "gnameName", nm], Term.con "terminal" [Term.lit " : "], Term.con "app" [Term.var "show", ty], Term.con "terminal" [Term.lit " := "], Term.con "app" [Term.var "show", v]]
      | _ => t

    def printEntryParam (t : Term) : Term :=
      match t with
      | .con "printEntry" [nm, .con "app" [.var "some", .con "app" [.var "param", ty]]] => Term.con "concat" [Term.con "terminal" [Term.lit "param "], Term.con "app" [Term.var "gnameName", nm], Term.con "terminal" [Term.lit " : "], Term.con "app" [Term.var "show", ty]]
      | _ => t

    def printEntryDatatype (t : Term) : Term :=
      match t with
      | .con "printEntry" [nm, .con "app" [.var "some", .con "app" [.var "datatype", desc]]] => Term.con "concat" [Term.con "terminal" [Term.lit "data "], Term.con "app" [Term.var "gnameName", nm], Term.con "terminal" [Term.lit " ..."]]
      | _ => t

    def printEntryDimVar (t : Term) : Term :=
      match t with
      | .con "printEntry" [nm, .con "app" [.var "some", .con "dimVar" []]] => Term.con "concat" [Term.con "terminal" [Term.lit "dim "], Term.con "app" [Term.var "gnameName", nm]]
      | _ => t

    def printEntryMetaVar (t : Term) : Term :=
      match t with
      | .con "printEntry" [nm, .con "app" [.var "some", .con "metaVar" [.con "labeledArg" [.var "type", .lit ":", ty], .con "labeledArg" [.var "solution", .lit ":", sol]]]] => Term.con "concat" [Term.con "terminal" [Term.lit "meta "], Term.con "app" [Term.var "gnameName", nm], Term.con "terminal" [Term.lit " : "], Term.con "app" [Term.var "show", ty]]
      | _ => t

    def printEntryNone (t : Term) : Term :=
      match t with
      | .con "printEntry" [nm, .con "none" []] => Term.con "concat" [Term.con "terminal" [Term.lit "unknown "], Term.con "app" [Term.var "gnameName", nm]]
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

  end Print

end GlobalEnv