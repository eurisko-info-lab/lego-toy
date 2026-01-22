/-
  AUTO-GENERATED from .lego files
  Do not edit directly.
-/

import Lego.Algebra

set_option linter.unusedVariables false

open Lego

namespace Module

  section Selector

    def selectorToPath (t : Term) : Term :=
      match t with
      | .con "app" [.var "selectorToPath", .con "selector" []] => Term.con "terminal" [Term.lit ""]
      | _ => t

    def selectorToPathCons (t : Term) : Term :=
      match t with
      | .con "app" [.var "selectorToPath", .con "selector" [n, rest]] => Term.con "strConcat" [n, Term.con "terminal" [Term.lit "."], Term.con "app" [Term.var "selectorToPath", Term.con "app" [Term.var "selector", rest]]]
      | _ => t

    def selectorFromPath (t : Term) : Term :=
      match t with
      | .con "app" [.var "selectorFromPath", path] => Term.con "app" [Term.var "selector", Term.con "strSplit" [path, Term.con "terminal" [Term.lit "."]]]
      | _ => t

    def selectorToFilePath (t : Term) : Term :=
      match t with
      | .con "selectorToFilePath" [base, .con "app" [.var "selector", parts], ext] => Term.con "strConcat" [base, Term.con "terminal" [Term.lit "/"], Term.con "strJoin" [Term.con "terminal" [Term.lit "/"], parts], ext]
      | _ => t

  end Selector

  section Visibility

    def isPublic (t : Term) : Term :=
      match t with
      | .con "app" [.var "isPublic", .con "pub" []] => Term.con "true" []
      | _ => t

    def isPublicPriv (t : Term) : Term :=
      match t with
      | .con "app" [.var "isPublic", .con "priv" []] => Term.con "false" []
      | _ => t

    def visibilityToString (t : Term) : Term :=
      match t with
      | .con "app" [.var "visibilityToString", .con "pub" []] => Term.con "terminal" [Term.lit "public"]
      | _ => t

    def visibilityToStringPriv (t : Term) : Term :=
      match t with
      | .con "app" [.var "visibilityToString", .con "priv" []] => Term.con "terminal" [Term.lit "private"]
      | _ => t

  end Visibility

  section ModDecl

    def modDeclVisibility (t : Term) : Term :=
      match t with
      | .con "app" [.var "modDeclVisibility", .con "importMod" [v, s]] => v
      | _ => t

    def modDeclVisibilityDef (t : Term) : Term :=
      match t with
      | .con "app" [.var "modDeclVisibility", .con "define" [v, .con "typedVar" [.lit "$", .var "n", .lit ":", t], .lit ":=", b]] => v
      | _ => t

    def modDeclVisibilityData (t : Term) : Term :=
      match t with
      | .con "app" [.var "modDeclVisibility", .con "dataDecl" [v, d]] => v
      | _ => t

    def modDeclVisibilityAxiom (t : Term) : Term :=
      match t with
      | .con "app" [.var "modDeclVisibility", .con "axiomDecl" [v, .con "typedVar" [.lit "$", .var "n", .lit ":", t]]] => v
      | _ => t

    def modDeclName (t : Term) : Term :=
      match t with
      | .con "app" [.var "modDeclName", .con "define" [v, .con "typedVar" [.lit "$", .var "n", .lit ":", t], .lit ":=", b]] => Term.con "app" [Term.var "some", Term.var "n"]
      | _ => t

    def modDeclNameData (t : Term) : Term :=
      match t with
      | .con "app" [.var "modDeclName", .con "dataDecl" [v, d]] => Term.con "app" [Term.var "some", Term.con "app" [Term.var "dataDescName", d]]
      | _ => t

    def modDeclNameAxiom (t : Term) : Term :=
      match t with
      | .con "app" [.var "modDeclName", .con "axiomDecl" [v, .con "typedVar" [.lit "$", .var "n", .lit ":", t]]] => Term.con "app" [Term.var "some", Term.var "n"]
      | _ => t

    def modDeclNameImport (t : Term) : Term :=
      match t with
      | .con "app" [.var "modDeclName", .con "importMod" [v, s]] => Term.con "none" []
      | _ => t

  end ModDecl

  section ModuleStruct

    def moduleName (t : Term) : Term :=
      match t with
      | .con "app" [.var "moduleName", .con "module" [sel, .con "brace" [.lit "{", decls, .lit "}"]]] => sel
      | _ => t

    def moduleDecls (t : Term) : Term :=
      match t with
      | .con "app" [.var "moduleDecls", .con "module" [sel, .con "brace" [.lit "{", decls, .lit "}"]]] => decls
      | _ => t

  end ModuleStruct

  section Resolution

    def isLocalResolution (t : Term) : Term :=
      match t with
      | .con "app" [.var "isLocalResolution", .con "app" [.var "localIx", n]] => Term.con "true" []
      | _ => t

    def isLocalResolutionGlobal (t : Term) : Term :=
      match t with
      | .con "app" [.var "isLocalResolution", .con "app" [.var "globalRes", g]] => Term.con "false" []
      | _ => t

    def isGlobalResolution (t : Term) : Term :=
      match t with
      | .con "app" [.var "isGlobalResolution", .con "app" [.var "globalRes", g]] => Term.con "true" []
      | _ => t

    def isGlobalResolutionLocal (t : Term) : Term :=
      match t with
      | .con "app" [.var "isGlobalResolution", .con "app" [.var "localIx", n]] => Term.con "false" []
      | _ => t

    def resolutionIndex (t : Term) : Term :=
      match t with
      | .con "app" [.var "resolutionIndex", .con "app" [.var "localIx", n]] => n
      | _ => t

    def resolutionGName (t : Term) : Term :=
      match t with
      | .con "app" [.var "resolutionGName", .con "app" [.var "globalRes", g]] => g
      | _ => t

  end Resolution

  section ImportInfo

    def importInfoName (t : Term) : Term :=
      match t with
      | .con "app" [.var "importInfoName", .con "importInfo" [.con "labeledArg" [.var "name", .lit ":", n], .con "labeledArg" [.var "vis", .lit ":", v], .con "labeledArg" [.var "from", .lit ":", s]]] => n
      | _ => t

    def importInfoVis (t : Term) : Term :=
      match t with
      | .con "app" [.var "importInfoVis", .con "importInfo" [.con "labeledArg" [.var "name", .lit ":", n], .con "labeledArg" [.var "vis", .lit ":", v], .con "labeledArg" [.var "from", .lit ":", s]]] => v
      | _ => t

    def importInfoFrom (t : Term) : Term :=
      match t with
      | .con "app" [.var "importInfoFrom", .con "importInfo" [.con "labeledArg" [.var "name", .lit ":", n], .con "labeledArg" [.var "vis", .lit ":", v], .con "labeledArg" [.var "from", .lit ":", s]]] => s
      | _ => t

  end ImportInfo

  section ResEnv

    def resEnvEmpty (t : Term) : Term :=
      match t with
      | .con "resEnvEmpty" [] => Term.con "resEnv" [Term.con "labeledArg" [Term.var "locals", Term.lit ":", Term.con "unit" [Term.lit "(", Term.lit ")"]], Term.con "labeledArg" [Term.var "globals", Term.lit ":", Term.con "unit" [Term.lit "(", Term.lit ")"]], Term.con "labeledArg" [Term.var "natives", Term.lit ":", Term.con "unit" [Term.lit "(", Term.lit ")"]]]
      | _ => t

    def resEnvBind (t : Term) : Term :=
      match t with
      | .con "resEnvBind" [x, .con "resEnv" [.con "labeledArg" [.var "locals", .lit ":", ls], .con "labeledArg" [.var "globals", .lit ":", gs], .con "labeledArg" [.var "natives", .lit ":", ns]]] => Term.con "resEnv" [Term.con "labeledArg" [Term.var "locals", Term.lit ":", Term.con "tuple" [x, ls]], Term.con "labeledArg" [Term.var "globals", Term.lit ":", gs], Term.con "labeledArg" [Term.var "natives", Term.lit ":", ns]]
      | _ => t

    def resEnvBindN (t : Term) : Term :=
      match t with
      | .con "resEnvBindN" [.con "unit" [.lit "(", .lit ")"], env] => env
      | _ => t

    def resEnvBindNCons (t : Term) : Term :=
      match t with
      | .con "resEnvBindN" [.con "tuple" [x, xs], env] => Term.con "resEnvBindN" [xs, Term.con "resEnvBind" [x, env]]
      | _ => t

    def resEnvGet (t : Term) : Term :=
      match t with
      | .con "resEnvGet" [x, .con "resEnv" [.con "labeledArg" [.var "locals", .lit ":", ls], .con "labeledArg" [.var "globals", .lit ":", gs], .con "labeledArg" [.var "natives", .lit ":", ns]]] => Term.con "resEnvLookup" [x, ls, gs, Term.con "num" [Term.con "number" [Term.lit "0"]]]
      | _ => t

    def resEnvLookup (t : Term) : Term :=
      match t with
      | .con "resEnvLookup" [x, .con "unit" [.lit "(", .lit ")"], gs, idx] => Term.con "resEnvLookupGlobal" [x, gs]
      | _ => t

    def resEnvLookupMatch (t : Term) : Term :=
      match t with
      | .con "resEnvLookup" [x, .con "tuple" [x_dup, rest], gs, idx] => Term.con "app" [Term.var "some", Term.con "app" [Term.var "localIx", idx]]
      | _ => t

    def resEnvLookupMiss (t : Term) : Term :=
      match t with
      | .con "resEnvLookup" [x, .con "tuple" [y, rest], gs, idx] => Term.con "resEnvLookup" [x, rest, gs, Term.con "app" [Term.var "succ", idx]]
      | _ => t

    def resEnvLookupGlobal (t : Term) : Term :=
      match t with
      | .con "resEnvLookupGlobal" [x, .con "unit" [.lit "(", .lit ")"]] => Term.con "none" []
      | _ => t

    def resEnvLookupGlobalMatch (t : Term) : Term :=
      match t with
      | .con "resEnvLookupGlobal" [x, .con "app" [.lit "(", .lit "(", .lit "[", x_dup, .lit "↦", info, .lit "]", .lit ")", rest, .lit ")"]] => Term.con "app" [Term.var "some", Term.con "app" [Term.var "globalRes", Term.con "app" [Term.var "importInfoName", info]]]
      | _ => t

    def resEnvLookupGlobalMiss (t : Term) : Term :=
      match t with
      | .con "resEnvLookupGlobal" [x, .con "app" [.lit "(", .lit "(", entry, .lit ")", rest, .lit ")"]] => Term.con "resEnvLookupGlobal" [x, rest]
      | _ => t

    def resEnvAddNative (t : Term) : Term :=
      match t with
      | .con "resEnvAddNative" [vis, gname, .con "resEnv" [.con "labeledArg" [.var "locals", .lit ":", ls], .con "labeledArg" [.var "globals", .lit ":", gs], .con "labeledArg" [.var "natives", .lit ":", ns]]] => Term.con "resEnv" [Term.con "labeledArg" [Term.var "locals", Term.lit ":", ls], Term.con "labeledArg" [Term.var "globals", Term.lit ":", Term.con "tuple" [Term.con "app" [Term.lit "(", Term.con "bracket" [Term.lit "[", Term.con "app" [Term.var "gnameName", gname], Term.lit "↦", Term.con "importInfo" [Term.con "labeledArg" [Term.var "name", Term.lit ":", gname], Term.con "labeledArg" [Term.var "vis", Term.lit ":", vis], Term.con "labeledArg" [Term.var "from", Term.lit ":", Term.con "selector" []]], Term.lit "]"], Term.lit ")"], gs]], Term.con "labeledArg" [Term.var "natives", Term.lit ":", Term.con "tuple" [gname, ns]]]
      | _ => t

    def resEnvImportGlobal (t : Term) : Term :=
      match t with
      | .con "resEnvImportGlobal" [vis, gname, fromMod, .con "resEnv" [.con "labeledArg" [.var "locals", .lit ":", ls], .con "labeledArg" [.var "globals", .lit ":", gs], .con "labeledArg" [.var "natives", .lit ":", ns]]] => Term.con "resEnv" [Term.con "labeledArg" [Term.var "locals", Term.lit ":", ls], Term.con "labeledArg" [Term.var "globals", Term.lit ":", Term.con "tuple" [Term.con "app" [Term.lit "(", Term.con "bracket" [Term.lit "[", Term.con "app" [Term.var "gnameName", gname], Term.lit "↦", Term.con "importInfo" [Term.con "labeledArg" [Term.var "name", Term.lit ":", gname], Term.con "labeledArg" [Term.var "vis", Term.lit ":", vis], Term.con "labeledArg" [Term.var "from", Term.lit ":", fromMod]], Term.lit "]"], Term.lit ")"], gs]], Term.con "labeledArg" [Term.var "natives", Term.lit ":", ns]]
      | _ => t

    def resEnvExports (t : Term) : Term :=
      match t with
      | .con "app" [.var "resEnvExports", .con "resEnv" [.con "labeledArg" [.var "locals", .lit ":", ls], .con "labeledArg" [.var "globals", .lit ":", gs], .con "labeledArg" [.var "natives", .lit ":", ns]]] => Term.con "resEnvCollectExports" [gs, Term.con "unit" [Term.lit "(", Term.lit ")"]]
      | _ => t

    def resEnvCollectExports (t : Term) : Term :=
      match t with
      | .con "resEnvCollectExports" [.con "unit" [.lit "(", .lit ")"], acc] => acc
      | _ => t

    def resEnvCollectExportsPub (t : Term) : Term :=
      match t with
      | .con "resEnvCollectExports" [.con "app" [.lit "(", .lit "(", .lit "[", n, .lit "↦", .con "importInfo" [.con "labeledArg" [.var "name", .lit ":", g], .con "labeledArg" [.var "vis", .lit ":", .con "pub" []], .con "labeledArg" [.var "from", .lit ":", f]], .lit "]", .lit ")", rest, .lit ")"], acc] => Term.con "resEnvCollectExports" [rest, Term.con "tuple" [g, acc]]
      | _ => t

    def resEnvCollectExportsPriv (t : Term) : Term :=
      match t with
      | .con "resEnvCollectExports" [.con "app" [.lit "(", .lit "(", .lit "[", n, .lit "↦", .con "importInfo" [.con "labeledArg" [.var "name", .lit ":", g], .con "labeledArg" [.var "vis", .lit ":", .con "priv" []], .con "labeledArg" [.var "from", .lit ":", f]], .lit "]", .lit ")", rest, .lit ")"], acc] => Term.con "resEnvCollectExports" [rest, acc]
      | _ => t

  end ResEnv

  section ModuleCache

    def moduleCacheEmpty (t : Term) : Term :=
      match t with
      | .con "moduleCacheEmpty" [] => Term.con "moduleCache" [Term.con "labeledArg" [Term.var "loaded", Term.lit ":", Term.con "unit" [Term.lit "(", Term.lit ")"]], Term.con "labeledArg" [Term.var "loading", Term.lit ":", Term.con "unit" [Term.lit "(", Term.lit ")"]]]
      | _ => t

    def moduleCacheIsLoaded (t : Term) : Term :=
      match t with
      | .con "moduleCacheIsLoaded" [sel, .con "moduleCache" [.con "labeledArg" [.var "loaded", .lit ":", ls], .con "labeledArg" [.var "loading", .lit ":", ing]]] => Term.con "cacheContains" [sel, ls]
      | _ => t

    def cacheContains (t : Term) : Term :=
      match t with
      | .con "cacheContains" [sel, .con "unit" [.lit "(", .lit ")"]] => Term.con "false" []
      | _ => t

    def cacheContainsMatch (t : Term) : Term :=
      match t with
      | .con "cacheContains" [sel, .con "app" [.lit "(", .lit "(", .lit "[", sel_dup, .lit "↦", r, .lit ",", e, .lit "]", .lit ")", rest, .lit ")"]] => Term.con "true" []
      | _ => t

    def cacheContainsMiss (t : Term) : Term :=
      match t with
      | .con "cacheContains" [sel, .con "app" [.lit "(", .lit "(", entry, .lit ")", rest, .lit ")"]] => Term.con "cacheContains" [sel, rest]
      | _ => t

    def moduleCacheIsCyclic (t : Term) : Term :=
      match t with
      | .con "moduleCacheIsCyclic" [sel, .con "moduleCache" [.con "labeledArg" [.var "loaded", .lit ":", ls], .con "labeledArg" [.var "loading", .lit ":", ing]]] => Term.con "listContains" [sel, ing]
      | _ => t

    def moduleCacheStartLoading (t : Term) : Term :=
      match t with
      | .con "moduleCacheStartLoading" [sel, .con "moduleCache" [.con "labeledArg" [.var "loaded", .lit ":", ls], .con "labeledArg" [.var "loading", .lit ":", ing]]] => Term.con "moduleCache" [Term.con "labeledArg" [Term.var "loaded", Term.lit ":", ls], Term.con "labeledArg" [Term.var "loading", Term.lit ":", Term.con "tuple" [sel, ing]]]
      | _ => t

    def moduleCacheStore (t : Term) : Term :=
      match t with
      | .con "moduleCacheStore" [sel, res, env, .con "moduleCache" [.con "labeledArg" [.var "loaded", .lit ":", ls], .con "labeledArg" [.var "loading", .lit ":", ing]]] => Term.con "moduleCache" [Term.con "labeledArg" [Term.var "loaded", Term.lit ":", Term.con "tuple" [Term.con "app" [Term.lit "(", Term.con "bracket" [Term.lit "[", sel, Term.lit "↦", res, Term.lit ",", env, Term.lit "]"], Term.lit ")"], ls]], Term.con "labeledArg" [Term.var "loading", Term.lit ":", Term.con "listRemove" [sel, ing]]]
      | _ => t

    def moduleCacheGetModule (t : Term) : Term :=
      match t with
      | .con "moduleCacheGetModule" [sel, .con "moduleCache" [.con "labeledArg" [.var "loaded", .lit ":", ls], .con "labeledArg" [.var "loading", .lit ":", ing]]] => Term.con "cacheLookup" [sel, ls]
      | _ => t

    def cacheLookup (t : Term) : Term :=
      match t with
      | .con "cacheLookup" [sel, .con "unit" [.lit "(", .lit ")"]] => Term.con "none" []
      | _ => t

    def cacheLookupMatch (t : Term) : Term :=
      match t with
      | .con "cacheLookup" [sel, .con "app" [.lit "(", .lit "(", .lit "[", sel_dup, .lit "↦", r, .lit ",", e, .lit "]", .lit ")", rest, .lit ")"]] => Term.con "app" [Term.var "some", Term.con "tuple" [Term.lit "(", r, Term.lit ",", e, Term.lit ")"]]
      | _ => t

    def cacheLookupMiss (t : Term) : Term :=
      match t with
      | .con "cacheLookup" [sel, .con "app" [.lit "(", .lit "(", entry, .lit ")", rest, .lit ")"]] => Term.con "cacheLookup" [sel, rest]
      | _ => t

  end ModuleCache

  section ProcessDecl

    def processImport (t : Term) : Term :=
      match t with
      | .con "processDecl" [.con "importMod" [vis, sel], resEnv, globEnv, loadImport] => Term.con "letIn" [Term.lit "(", Term.lit "let", Term.lit "$", Term.var "importedRes", Term.lit "=", Term.con "apply" [loadImport, sel], Term.lit "in", Term.con "tuple" [Term.lit "(", resEnv, Term.lit ",", globEnv, Term.lit ")"], Term.lit ")"]
      | _ => t

    def processDefine (t : Term) : Term :=
      match t with
      | .con "processDecl" [.con "define" [vis, .con "typedVar" [.lit "$", .var "name", .lit ":", ty], .lit ":=", tm], resEnv, globEnv, loadImport] => Term.con "letIn" [Term.lit "(", Term.lit "let", Term.lit "$", Term.var "gname", Term.lit "=", Term.con "app" [Term.var "gname", Term.var "name"], Term.lit "in", Term.con "letIn" [Term.lit "(", Term.lit "let", Term.lit "$", Term.var "globEnv'", Term.lit "=", Term.con "globalEnvDefine" [Term.var "gname", ty, tm, globEnv], Term.lit "in", Term.con "letIn" [Term.lit "(", Term.lit "let", Term.lit "$", Term.var "resEnv'", Term.lit "=", Term.con "resEnvAddNative" [vis, Term.var "gname", resEnv], Term.lit "in", Term.con "tuple" [Term.lit "(", Term.var "resEnv'", Term.lit ",", Term.var "globEnv'", Term.lit ")"], Term.lit ")"], Term.lit ")"], Term.lit ")"]
      | _ => t

    def processDataDecl (t : Term) : Term :=
      match t with
      | .con "processDecl" [.con "dataDecl" [vis, desc], resEnv, globEnv, loadImport] => Term.con "letIn" [Term.lit "(", Term.lit "let", Term.lit "$", Term.var "globEnv'", Term.lit "=", Term.con "globalEnvDeclareDatatype" [desc, globEnv], Term.lit "in", Term.con "letIn" [Term.lit "(", Term.lit "let", Term.lit "$", Term.var "resEnv'", Term.lit "=", Term.con "resEnvAddNative" [vis, Term.con "app" [Term.var "dataDescName", desc], resEnv], Term.lit "in", Term.con "tuple" [Term.lit "(", Term.var "resEnv'", Term.lit ",", Term.var "globEnv'", Term.lit ")"], Term.lit ")"], Term.lit ")"]
      | _ => t

    def processAxiom (t : Term) : Term :=
      match t with
      | .con "processDecl" [.con "axiomDecl" [vis, .con "typedVar" [.lit "$", .var "name", .lit ":", ty]], resEnv, globEnv, loadImport] => Term.con "letIn" [Term.lit "(", Term.lit "let", Term.lit "$", Term.var "gname", Term.lit "=", Term.con "app" [Term.var "gname", Term.var "name"], Term.lit "in", Term.con "letIn" [Term.lit "(", Term.lit "let", Term.lit "$", Term.var "globEnv'", Term.lit "=", Term.con "globalEnvDeclareParam" [Term.var "gname", ty, globEnv], Term.lit "in", Term.con "letIn" [Term.lit "(", Term.lit "let", Term.lit "$", Term.var "resEnv'", Term.lit "=", Term.con "resEnvAddNative" [vis, Term.var "gname", resEnv], Term.lit "in", Term.con "tuple" [Term.lit "(", Term.var "resEnv'", Term.lit ",", Term.var "globEnv'", Term.lit ")"], Term.lit ")"], Term.lit ")"], Term.lit ")"]
      | _ => t

  end ProcessDecl

  section QualifiedName

    def resolveQualified (t : Term) : Term :=
      match t with
      | .con "resolveQualified" [name, env, cache] => Term.con "resEnvGet" [name, env]
      | _ => t

    def resolveQualifiedMulti (t : Term) : Term :=
      match t with
      | .con "resolveQualified" [.con "tuple" [modPart, rest], env, cache] => Term.con "caseExpr" [Term.lit "(", Term.lit "case", Term.con "moduleCacheGetModule" [Term.con "app" [Term.var "selector", Term.con "tuple" [modPart, rest]], cache], Term.con "arm" [Term.lit "(", Term.var "some", Term.con "tuple" [Term.lit "(", Term.var "res", Term.lit ",", Term.var "genv", Term.lit ")"], Term.lit ")", Term.lit "=>", Term.con "resEnvGet" [Term.con "app" [Term.var "last", Term.con "tuple" [modPart, rest]], Term.var "res"]], Term.con "arm" [Term.var "none", Term.lit "=>", Term.con "none" []], Term.lit ")"]
      | _ => t

    def last (t : Term) : Term :=
      match t with
      | .con "app" [.var "last", x] => x
      | _ => t

    def lastCons (t : Term) : Term :=
      match t with
      | .con "app" [.var "last", .con "tuple" [x, y, rest]] => Term.con "app" [Term.var "last", Term.con "tuple" [y, rest]]
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

  end QualifiedName

end Module