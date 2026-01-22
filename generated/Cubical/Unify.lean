/-
  AUTO-GENERATED from .lego files
  Do not edit directly.
-/

import Lego.Algebra

set_option linter.unusedVariables false

open Lego

namespace Unify

  section MetaInfo

    def metaInfoName (t : Term) : Term :=
      match t with
      | .con "app" [.var "metaInfoName", .con "metaInfo" [.con "labeledArg" [.var "name", .lit ":", n], .con "labeledArg" [.var "ctx", .lit ":", c], .con "labeledArg" [.var "ty", .lit ":", t], .con "labeledArg" [.var "solution", .lit ":", s]]] => n
      | _ => t

    def metaInfoCtx (t : Term) : Term :=
      match t with
      | .con "app" [.var "metaInfoCtx", .con "metaInfo" [.con "labeledArg" [.var "name", .lit ":", n], .con "labeledArg" [.var "ctx", .lit ":", c], .con "labeledArg" [.var "ty", .lit ":", t], .con "labeledArg" [.var "solution", .lit ":", s]]] => c
      | _ => t

    def metaInfoTy (t : Term) : Term :=
      match t with
      | .con "app" [.var "metaInfoTy", .con "metaInfo" [.con "labeledArg" [.var "name", .lit ":", n], .con "labeledArg" [.var "ctx", .lit ":", c], .con "labeledArg" [.var "ty", .lit ":", t], .con "labeledArg" [.var "solution", .lit ":", s]]] => t
      | _ => t

    def metaInfoSolution (t : Term) : Term :=
      match t with
      | .con "app" [.var "metaInfoSolution", .con "metaInfo" [.con "labeledArg" [.var "name", .lit ":", n], .con "labeledArg" [.var "ctx", .lit ":", c], .con "labeledArg" [.var "ty", .lit ":", t], .con "labeledArg" [.var "solution", .lit ":", s]]] => s
      | _ => t

  end MetaInfo

  section UnifyState

    def unifyStateEmpty (t : Term) : Term :=
      match t with
      | .con "unifyStateEmpty" [] => Term.con "unifyState" [Term.con "labeledArg" [Term.var "metas", Term.lit ":", Term.con "unit" [Term.lit "(", Term.lit ")"]], Term.con "labeledArg" [Term.var "nextId", Term.lit ":", Term.con "num" [Term.con "number" [Term.lit "0"]]], Term.con "labeledArg" [Term.var "postponed", Term.lit ":", Term.con "unit" [Term.lit "(", Term.lit ")"]]]
      | _ => t

    def unifyStateFreshMeta (t : Term) : Term :=
      match t with
      | .con "unifyStateFreshMeta" [.con "unifyState" [.con "labeledArg" [.var "metas", .lit ":", metas], .con "labeledArg" [.var "nextId", .lit ":", n], .con "labeledArg" [.var "postponed", .lit ":", p]], ctx, ty] => Term.con "letIn" [Term.lit "(", Term.lit "let", Term.var "name", Term.lit "=", Term.con "gnameFresh" [Term.con "terminal" [Term.lit "?"], n], Term.lit "in", Term.con "letIn" [Term.lit "let", Term.var "info", Term.lit "=", Term.con "metaInfo" [Term.con "labeledArg" [Term.var "name", Term.lit ":", Term.con "name" []], Term.con "labeledArg" [Term.var "ctx", Term.lit ":", ctx], Term.con "labeledArg" [Term.var "ty", Term.lit ":", ty], Term.con "labeledArg" [Term.var "solution", Term.lit ":", Term.con "none" []]], Term.lit "in", Term.con "record" [Term.lit "(", Term.var "result", Term.lit ":", Term.con "unifyState" [Term.con "labeledArg" [Term.var "metas", Term.lit ":", Term.con "app" [Term.var "info", metas]], Term.con "labeledArg" [Term.var "nextId", Term.lit ":", Term.con "app" [Term.var "suc", n]], Term.con "labeledArg" [Term.var "postponed", Term.lit ":", p]], Term.con "labeledArg" [Term.var "name", Term.lit ":", Term.con "name" []], Term.lit ")"]], Term.lit ")"]
      | _ => t

    def unifyStateLookupMeta (t : Term) : Term :=
      match t with
      | .con "unifyStateLookupMeta" [.con "unifyState" [.con "labeledArg" [.var "metas", .lit ":", metas], .con "labeledArg" [.var "nextId", .lit ":", n], .con "labeledArg" [.var "postponed", .lit ":", p]], name] => Term.con "findMeta" [metas, name]
      | _ => t

    def findMetaNil (t : Term) : Term :=
      match t with
      | .con "findMeta" [.con "unit" [.lit "(", .lit ")"], name] => Term.con "none" []
      | _ => t

    def findMetaMatch (t : Term) : Term :=
      match t with
      | .con "findMeta" [.con "app" [.lit "(", .lit "(", .var "metaInfo", .con "labeledArg" [.var "name", .lit ":", name], .con "labeledArg" [.var "ctx", .lit ":", c], .con "labeledArg" [.var "ty", .lit ":", t], .con "labeledArg" [.var "solution", .lit ":", s], .lit ")", rest, .lit ")"], name_dup] => Term.con "app" [Term.var "some", Term.con "metaInfo" [Term.con "labeledArg" [Term.var "name", Term.lit ":", name], Term.con "labeledArg" [Term.var "ctx", Term.lit ":", c], Term.con "labeledArg" [Term.var "ty", Term.lit ":", t], Term.con "labeledArg" [Term.var "solution", Term.lit ":", s]]]
      | _ => t

    def findMetaMiss (t : Term) : Term :=
      match t with
      | .con "findMeta" [.con "tuple" [m, rest], name] => Term.con "findMeta" [rest, name]
      | _ => t

    def unifyStateSolveMeta (t : Term) : Term :=
      match t with
      | .con "unifyStateSolveMeta" [.con "unifyState" [.con "labeledArg" [.var "metas", .lit ":", metas], .con "labeledArg" [.var "nextId", .lit ":", n], .con "labeledArg" [.var "postponed", .lit ":", p]], name, sol] => Term.con "unifyState" [Term.con "labeledArg" [Term.var "metas", Term.lit ":", Term.con "solveMeta" [metas, name, sol]], Term.con "labeledArg" [Term.var "nextId", Term.lit ":", n], Term.con "labeledArg" [Term.var "postponed", Term.lit ":", p]]
      | _ => t

    def solveMetaNil (t : Term) : Term :=
      match t with
      | .con "solveMeta" [.con "unit" [.lit "(", .lit ")"], name, sol] => Term.con "unit" [Term.lit "(", Term.lit ")"]
      | _ => t

    def solveMetaMatch (t : Term) : Term :=
      match t with
      | .con "solveMeta" [.con "app" [.lit "(", .lit "(", .var "metaInfo", .con "labeledArg" [.var "name", .lit ":", name], .con "labeledArg" [.var "ctx", .lit ":", c], .con "labeledArg" [.var "ty", .lit ":", t], .con "labeledArg" [.var "solution", .lit ":", old], .lit ")", rest, .lit ")"], name_dup, sol] => Term.con "tuple" [Term.con "app" [Term.lit "(", Term.con "metaInfo" [], Term.con "labeledArg" [Term.var "name", Term.lit ":", name], Term.con "labeledArg" [Term.var "ctx", Term.lit ":", c], Term.con "labeledArg" [Term.var "ty", Term.lit ":", t], Term.con "labeledArg" [Term.var "solution", Term.lit ":", Term.con "app" [Term.var "some", sol]], Term.lit ")"], rest]
      | _ => t

    def solveMetaMiss (t : Term) : Term :=
      match t with
      | .con "solveMeta" [.con "tuple" [m, rest], name, sol] => Term.con "tuple" [m, Term.con "solveMeta" [rest, name, sol]]
      | _ => t

    def unifyStateIsSolved (t : Term) : Term :=
      match t with
      | .con "unifyStateIsSolved" [st, name] => Term.con "caseExpr" [Term.lit "(", Term.lit "case", Term.con "unifyStateLookupMeta" [st, name], Term.con "arm" [Term.lit "(", Term.var "some", Term.con "metaInfo" [Term.con "labeledArg" [Term.var "name", Term.lit ":", Term.con "_" []], Term.con "labeledArg" [Term.var "ctx", Term.lit ":", Term.con "_" []], Term.con "labeledArg" [Term.var "ty", Term.lit ":", Term.con "_" []], Term.con "labeledArg" [Term.var "solution", Term.lit ":", Term.con "app" [Term.var "some", Term.con "_" []]]], Term.lit ")", Term.lit "=>", Term.con "true" []], Term.con "arm" [Term.var "_", Term.lit "=>", Term.con "false" []], Term.lit ")"]
      | _ => t

    def unifyStateUnsolved (t : Term) : Term :=
      match t with
      | .con "app" [.var "unifyStateUnsolved", .con "unifyState" [.con "labeledArg" [.var "metas", .lit ":", metas], .con "labeledArg" [.var "nextId", .lit ":", n], .con "labeledArg" [.var "postponed", .lit ":", p]]] => Term.con "filter" [Term.con "fun" [Term.con "m" [], Term.lit "=>", Term.con "app" [Term.var "isNone", Term.con "app" [Term.var "metaInfoSolution", Term.con "m" []]]], metas]
      | _ => t

    def unifyStatePostpone (t : Term) : Term :=
      match t with
      | .con "unifyStatePostpone" [.con "unifyState" [.con "labeledArg" [.var "metas", .lit ":", metas], .con "labeledArg" [.var "nextId", .lit ":", n], .con "labeledArg" [.var "postponed", .lit ":", p]], t1, t2] => Term.con "unifyState" [Term.con "labeledArg" [Term.var "metas", Term.lit ":", metas], Term.con "labeledArg" [Term.var "nextId", Term.lit ":", n], Term.con "labeledArg" [Term.var "postponed", Term.lit ":", Term.con "tuple" [Term.con "app" [Term.lit "(", t1, Term.con "≡" [], t2, Term.lit ")"], p]]]
      | _ => t

    def unifyStateTakePostponed (t : Term) : Term :=
      match t with
      | .con "app" [.var "unifyStateTakePostponed", .con "unifyState" [.con "labeledArg" [.var "metas", .lit ":", metas], .con "labeledArg" [.var "nextId", .lit ":", n], .con "labeledArg" [.var "postponed", .lit ":", p]]] => Term.con "record" [Term.lit "(", Term.var "result", Term.lit ":", Term.con "unifyState" [Term.con "labeledArg" [Term.var "metas", Term.lit ":", metas], Term.con "labeledArg" [Term.var "nextId", Term.lit ":", n], Term.con "labeledArg" [Term.var "postponed", Term.lit ":", Term.con "unit" [Term.lit "(", Term.lit ")"]]], Term.con "labeledArg" [Term.var "constraints", Term.lit ":", p], Term.lit ")"]
      | _ => t

  end UnifyState

  section UnifyResult



  end UnifyResult

  section SpineElem

    def classifySpineArg (t : Term) : Term :=
      match t with
      | .con "app" [.var "classifySpineArg", .con "app" [.var "ix", n]] => Term.con "app" [Term.var "termVar", n]
      | _ => t

    def classifySpineArgDim (t : Term) : Term :=
      match t with
      | .con "app" [.var "classifySpineArg", .con "app" [.var "dimVar", n]] => Term.con "app" [Term.var "dimVar", n]
      | _ => t

    def classifySpineArgOther (t : Term) : Term :=
      match t with
      | .con "app" [.var "classifySpineArg", e] => Term.con "app" [Term.var "other", e]
      | _ => t

  end SpineElem

  section Spine

    def collectSpine (t : Term) : Term :=
      match t with
      | .con "app" [.var "collectSpine", e] => Term.con "collectSpine'" [e, Term.con "unit" [Term.lit "(", Term.lit ")"]]
      | _ => t

    def collectSpine'App (t : Term) : Term :=
      match t with
      | .con "collectSpine'" [.con "app" [f, a], acc] => Term.con "collectSpine'" [f, Term.con "tuple" [acc, a]]
      | _ => t

    def collectSpine'Papp (t : Term) : Term :=
      match t with
      | .con "collectSpine'" [.con "papp" [f, a], acc] => Term.con "collectSpine'" [f, Term.con "tuple" [acc, a]]
      | _ => t

    def collectSpine'Other (t : Term) : Term :=
      match t with
      | .con "collectSpine'" [e, acc] => Term.con "tuple" [Term.lit "(", e, Term.lit ",", acc, Term.lit ")"]
      | _ => t

    def isPatternSpine (t : Term) : Term :=
      match t with
      | .con "app" [.var "isPatternSpine", args] => Term.con "letIn" [Term.lit "(", Term.lit "let", Term.var "elems", Term.lit "=", Term.con "map" [Term.con "classifySpineArg" [], args], Term.lit "in", Term.con "letIn" [Term.lit "let", Term.var "allVars", Term.lit "=", Term.con "all" [Term.con "isSpineVar" [], Term.con "elems" []], Term.lit "in", Term.con "letIn" [Term.lit "let", Term.var "distinct", Term.lit "=", Term.con "eq" [Term.con "app" [Term.var "length", Term.con "app" [Term.var "eraseDups", Term.con "elems" []]], Term.con "app" [Term.var "length", Term.con "elems" []]], Term.lit "in", Term.con "and" [Term.con "allVars" [], Term.con "distinct" []]]], Term.lit ")"]
      | _ => t

    def isSpineVar (t : Term) : Term :=
      match t with
      | .con "app" [.var "isSpineVar", .con "app" [.var "termVar", n]] => Term.con "true" []
      | _ => t

    def isSpineVarDim (t : Term) : Term :=
      match t with
      | .con "app" [.var "isSpineVar", .con "app" [.var "dimVar", n]] => Term.con "true" []
      | _ => t

    def isSpineVarOther (t : Term) : Term :=
      match t with
      | .con "app" [.var "isSpineVar", .con "app" [.var "other", e]] => Term.con "false" []
      | _ => t

    def spineToVars (t : Term) : Term :=
      match t with
      | .con "app" [.var "spineToVars", args] => Term.con "app" [Term.var "filterMap", Term.con "extractVarIndex" [Term.con "map" [Term.con "classifySpineArg" [], args]]]
      | _ => t

    def extractVarIndex (t : Term) : Term :=
      match t with
      | .con "app" [.var "extractVarIndex", .con "app" [.var "termVar", n]] => Term.con "app" [Term.var "some", n]
      | _ => t

    def extractVarIndexDim (t : Term) : Term :=
      match t with
      | .con "app" [.var "extractVarIndex", .con "app" [.var "dimVar", n]] => Term.con "app" [Term.var "some", n]
      | _ => t

    def extractVarIndexOther (t : Term) : Term :=
      match t with
      | .con "app" [.var "extractVarIndex", .con "app" [.var "other", e]] => Term.con "none" []
      | _ => t

    def isMeta (t : Term) : Term :=
      match t with
      | .con "app" [.var "isMeta", .con "app" [.var "lit", name]] => Term.con "caseExpr" [Term.lit "(", Term.lit "case", Term.con "startsWith" [name, Term.con "terminal" [Term.lit "?"]], Term.con "arm" [Term.var "true", Term.lit "=>", Term.con "app" [Term.var "some", name]], Term.con "arm" [Term.var "false", Term.lit "=>", Term.con "none" []], Term.lit ")"]
      | _ => t

    def isMetaOther (t : Term) : Term :=
      match t with
      | .con "app" [.var "isMeta", e] => Term.con "none" []
      | _ => t

  end Spine

  section Invert

    def invertTerm (t : Term) : Term :=
      match t with
      | .con "invertTerm" [spineVars, term] => Term.con "invertTerm'" [spineVars, term, Term.con "num" [Term.con "number" [Term.lit "0"]], Term.con "app" [Term.var "length", spineVars]]
      | _ => t

    def invertTerm'Ix (t : Term) : Term :=
      match t with
      | .con "invertTerm'" [spineVars, .con "app" [.var "ix", n], depth, len] => Term.con "caseExpr" [Term.lit "(", Term.lit "case", Term.con "findIndex" [spineVars, n], Term.con "arm" [Term.lit "(", Term.var "some", Term.var "i", Term.lit ")", Term.lit "=>", Term.con "app" [Term.var "some", Term.con "app" [Term.var "ix", Term.con "plus" [depth, Term.con "minus" [Term.con "minus" [len, Term.var "i"], Term.con "num" [Term.con "number" [Term.lit "1"]]]]]]], Term.con "arm" [Term.var "none", Term.lit "=>", Term.con "caseExpr" [Term.lit "(", Term.lit "case", Term.con "gte" [n, len], Term.con "arm" [Term.var "true", Term.lit "=>", Term.con "app" [Term.var "some", Term.con "app" [Term.var "ix", Term.con "plus" [depth, Term.con "minus" [n, len]]]]], Term.con "arm" [Term.var "false", Term.lit "=>", Term.con "none" []], Term.lit ")"]], Term.lit ")"]
      | _ => t

    def invertTerm'Lam (t : Term) : Term :=
      match t with
      | .con "invertTerm'" [spineVars, .con "app" [.var "lam", body], depth, len] => Term.con "caseExpr" [Term.lit "(", Term.lit "case", Term.con "invertTerm'" [spineVars, body, Term.con "app" [Term.var "suc", depth], len], Term.con "arm" [Term.lit "(", Term.var "some", Term.var "body'", Term.lit ")", Term.lit "=>", Term.con "app" [Term.var "some", Term.con "app" [Term.var "lam", Term.var "body'"]]], Term.con "arm" [Term.var "none", Term.lit "=>", Term.con "none" []], Term.lit ")"]
      | _ => t

    def invertTerm'App (t : Term) : Term :=
      match t with
      | .con "invertTerm'" [spineVars, .con "app" [f, a], depth, len] => Term.con "caseExpr" [Term.lit "(", Term.lit "case", Term.con "invertTerm'" [spineVars, f, depth, len], Term.con "arm" [Term.lit "(", Term.var "some", Term.var "f'", Term.lit ")", Term.lit "=>", Term.con "caseExpr" [Term.lit "(", Term.lit "case", Term.con "invertTerm'" [spineVars, a, depth, len], Term.con "arm" [Term.lit "(", Term.var "some", Term.var "a'", Term.lit ")", Term.lit "=>", Term.con "app" [Term.var "some", Term.con "app" [Term.var "f'", Term.var "a'"]]], Term.con "arm" [Term.var "none", Term.lit "=>", Term.con "none" []], Term.lit ")"]], Term.con "arm" [Term.var "none", Term.lit "=>", Term.con "none" []], Term.lit ")"]
      | _ => t

    def invertTerm'Pi (t : Term) : Term :=
      match t with
      | .con "invertTerm'" [spineVars, .con "pi" [dom, cod], depth, len] => Term.con "caseExpr" [Term.lit "(", Term.lit "case", Term.con "invertTerm'" [spineVars, dom, depth, len], Term.con "arm" [Term.lit "(", Term.var "some", Term.var "dom'", Term.lit ")", Term.lit "=>", Term.con "caseExpr" [Term.lit "(", Term.lit "case", Term.con "invertTerm'" [spineVars, cod, Term.con "app" [Term.var "suc", depth], len], Term.con "arm" [Term.lit "(", Term.var "some", Term.var "cod'", Term.lit ")", Term.lit "=>", Term.con "app" [Term.var "some", Term.con "pi" [Term.var "dom'", Term.var "cod'"]]], Term.con "arm" [Term.var "none", Term.lit "=>", Term.con "none" []], Term.lit ")"]], Term.con "arm" [Term.var "none", Term.lit "=>", Term.con "none" []], Term.lit ")"]
      | _ => t

    def invertTerm'Lit (t : Term) : Term :=
      match t with
      | .con "invertTerm'" [spineVars, .con "app" [.var "lit", s], depth, len] => Term.con "app" [Term.var "some", Term.con "app" [Term.var "lit", s]]
      | _ => t

    def invertTerm'Dim0 (t : Term) : Term :=
      match t with
      | .con "invertTerm'" [spineVars, .con "dim0" [], depth, len] => Term.con "app" [Term.var "some", Term.con "dim0" []]
      | _ => t

    def invertTerm'Dim1 (t : Term) : Term :=
      match t with
      | .con "invertTerm'" [spineVars, .con "dim1" [], depth, len] => Term.con "app" [Term.var "some", Term.con "dim1" []]
      | _ => t

    def invertTerm'Default (t : Term) : Term :=
      match t with
      | .con "invertTerm'" [spineVars, e, depth, len] => Term.con "app" [Term.var "some", e]
      | _ => t

  end Invert

  section FlexRigid

    def solveFlexRigid (t : Term) : Term :=
      match t with
      | .con "solveFlexRigid" [st, metaName, args, term] => Term.con "letIn" [Term.lit "(", Term.lit "let", Term.var "gname", Term.lit "=", Term.con "app" [Term.var "gnameNamed", metaName], Term.lit "in", Term.con "caseExpr" [Term.lit "case", Term.con "occurs" [Term.con "gname" [], term], Term.con "arm" [Term.var "true", Term.lit "=>", Term.con "app" [Term.var "failure", Term.con "concat" [Term.con "terminal" [Term.lit "occurs check failed: "], metaName, Term.con "terminal" [Term.lit " occurs in solution"]]]], Term.con "arm" [Term.var "false", Term.lit "=>", Term.con "solveFlexRigid'" [st, metaName, args, term, Term.con "gname" []]]], Term.lit ")"]
      | _ => t

    def solveFlexRigid' (t : Term) : Term :=
      match t with
      | .con "solveFlexRigid'" [st, metaName, args, term, gname] => Term.con "caseExpr" [Term.lit "(", Term.lit "case", Term.con "app" [Term.var "isPatternSpine", args], Term.con "arm" [Term.var "false", Term.lit "=>", Term.con "app" [Term.var "stuck", Term.con "unifyStatePostpone" [st, Term.con "app" [Term.var "lit", metaName], term]]], Term.con "arm" [Term.var "true", Term.lit "=>", Term.con "letIn" [Term.lit "(", Term.lit "let", Term.var "spineVars", Term.lit "=", Term.con "app" [Term.var "spineToVars", args], Term.lit "in", Term.con "caseExpr" [Term.lit "case", Term.con "invertTerm" [Term.con "spineVars" [], term], Term.con "arm" [Term.var "none", Term.lit "=>", Term.con "app" [Term.var "stuck", Term.con "unifyStatePostpone" [st, Term.con "app" [Term.var "lit", metaName], term]]], Term.con "arm" [Term.lit "(", Term.var "some", Term.var "invertedTerm", Term.lit ")", Term.lit "=>", Term.con "letIn" [Term.lit "(", Term.lit "let", Term.var "solution", Term.lit "=", Term.con "buildSolution" [args, Term.var "invertedTerm"], Term.lit "in", Term.con "app" [Term.var "success", Term.con "unifyStateSolveMeta" [st, gname, Term.con "solution" []]], Term.lit ")"]]], Term.lit ")"]], Term.lit ")"]
      | _ => t

    def buildSolution (t : Term) : Term :=
      match t with
      | .con "buildSolution" [.con "unit" [.lit "(", .lit ")"], body] => body
      | _ => t

    def buildSolutionCons (t : Term) : Term :=
      match t with
      | .con "buildSolution" [.con "tuple" [a, rest], body] => Term.con "app" [Term.var "lam", Term.con "buildSolution" [rest, body]]
      | _ => t

  end FlexRigid

  section Unify

    def unify (t : Term) : Term :=
      match t with
      | .con "unify" [st, t1, t2] => Term.con "caseExpr" [Term.lit "(", Term.lit "case", Term.con "conv" [t1, t2], Term.con "arm" [Term.var "true", Term.lit "=>", Term.con "app" [Term.var "success", st]], Term.con "arm" [Term.var "false", Term.lit "=>", Term.con "letIn" [Term.lit "(", Term.lit "let", Term.var "h1Args1", Term.lit "=", Term.con "app" [Term.var "collectSpine", t1], Term.lit "in", Term.con "letIn" [Term.lit "let", Term.var "h2Args2", Term.lit "=", Term.con "app" [Term.var "collectSpine", t2], Term.lit "in", Term.con "unifyHeads" [st, Term.con "app" [Term.var "fst", Term.con "h1Args1" []], Term.con "app" [Term.var "snd", Term.con "h1Args1" []], Term.con "app" [Term.var "fst", Term.con "h2Args2" []], Term.con "app" [Term.var "snd", Term.con "h2Args2" []]]], Term.lit ")"]], Term.lit ")"]
      | _ => t

    def unifyHeads (t : Term) : Term :=
      match t with
      | .con "unifyHeads" [st, h1, args1, h2, args2] => Term.con "case" [Term.con "app" [Term.var "isMeta", h1], Term.con "app" [Term.var "isMeta", h2], Term.con "app" [Term.var "some", Term.var "m"], Term.con "none" [], Term.lit "=>", Term.con "solveFlexRigid" [st, Term.var "m", args1, Term.con "foldl" [Term.con "app" [], h2, args2]], Term.con "none" [Term.con "app" [Term.var "some", Term.var "m"]], Term.lit "=>", Term.con "solveFlexRigid" [st, Term.var "m", args2, Term.con "foldl" [Term.con "app" [], h1, args1]], Term.con "app" [Term.var "some", Term.var "m1"], Term.con "app" [Term.var "some", Term.var "m2"], Term.lit "=>", Term.con "caseExpr" [Term.lit "(", Term.lit "case", Term.con "eq" [Term.var "m1", Term.var "m2"], Term.con "arm" [Term.var "true", Term.lit "=>", Term.con "flexFlexSame" [st, Term.var "m1", args1, args2]], Term.con "arm" [Term.var "false", Term.lit "=>", Term.con "flexFlexDiff" [st, Term.var "m1", args1, Term.var "m2", args2]], Term.lit ")"], Term.con "none" [], Term.con "none" [], Term.lit "=>", Term.con "unifyRigid" [st, Term.con "foldl" [Term.con "app" [], h1, args1], Term.con "foldl" [Term.con "app" [], h2, args2]]]
      | _ => t

  end Unify

  section FlexFlexSame

    def flexFlexSame (t : Term) : Term :=
      match t with
      | .con "flexFlexSame" [st, metaName, args1, args2] => Term.con "caseExpr" [Term.lit "(", Term.lit "case", Term.con "eq" [Term.con "app" [Term.var "length", args1], Term.con "app" [Term.var "length", args2]], Term.con "arm" [Term.var "false", Term.lit "=>", Term.con "app" [Term.var "failure", Term.con "terminal" [Term.lit "flex-flex: spine length mismatch"]]], Term.con "arm" [Term.var "true", Term.lit "=>", Term.con "caseExpr" [Term.lit "(", Term.lit "case", Term.con "and" [Term.con "app" [Term.var "isPatternSpine", args1], Term.con "app" [Term.var "isPatternSpine", args2]], Term.con "arm" [Term.var "false", Term.lit "=>", Term.con "app" [Term.var "stuck", Term.con "unifyStatePostpone" [st, Term.con "app" [Term.var "lit", metaName], Term.con "app" [Term.var "lit", metaName]]]], Term.con "arm" [Term.var "true", Term.lit "=>", Term.con "flexFlexSamePattern" [st, metaName, Term.con "app" [Term.var "spineToVars", args1], Term.con "app" [Term.var "spineToVars", args2]]], Term.lit ")"]], Term.lit ")"]
      | _ => t

    def flexFlexSamePattern (t : Term) : Term :=
      match t with
      | .con "flexFlexSamePattern" [st, metaName, vars1, vars2] => Term.con "letIn" [Term.lit "(", Term.lit "let", Term.var "pairs", Term.lit "=", Term.con "zip" [vars1, vars2], Term.lit "in", Term.con "letIn" [Term.lit "let", Term.var "commonCount", Term.lit "=", Term.con "app" [Term.var "length", Term.con "filter" [Term.con "fun" [Term.con "p" [], Term.lit "=>", Term.con "eq" [Term.con "app" [Term.var "fst", Term.con "p" []], Term.con "app" [Term.var "snd", Term.con "p" []]]], Term.con "pairs" []]], Term.lit "in", Term.con "caseExpr" [Term.lit "case", Term.con "app" [Term.var "eq", Term.con "commonCount" [Term.con "app" [Term.var "length", vars1]]], Term.con "arm" [Term.var "true", Term.lit "=>", Term.con "app" [Term.var "success", st]], Term.con "arm" [Term.var "false", Term.lit "=>", Term.con "app" [Term.var "stuck", Term.con "unifyStatePostpone" [st, Term.con "app" [Term.var "lit", metaName], Term.con "app" [Term.var "lit", metaName]]]]]], Term.lit ")"]
      | _ => t

  end FlexFlexSame

  section FlexFlexDiff

    def flexFlexDiff (t : Term) : Term :=
      match t with
      | .con "flexFlexDiff" [st, m1, args1, m2, args2] => Term.con "caseExpr" [Term.lit "(", Term.lit "case", Term.con "and" [Term.con "app" [Term.var "isPatternSpine", args1], Term.con "app" [Term.var "isPatternSpine", args2]], Term.con "arm" [Term.var "false", Term.lit "=>", Term.con "app" [Term.var "stuck", Term.con "unifyStatePostpone" [st, Term.con "app" [Term.var "lit", m1], Term.con "app" [Term.var "lit", m2]]]], Term.con "arm" [Term.var "true", Term.lit "=>", Term.con "letIn" [Term.lit "(", Term.lit "let", Term.var "vars1", Term.lit "=", Term.con "app" [Term.var "spineToVars", args1], Term.lit "in", Term.con "letIn" [Term.lit "let", Term.var "vars2", Term.lit "=", Term.con "app" [Term.var "spineToVars", args2], Term.lit "in", Term.con "flexFlexDiff'" [st, m1, args1, Term.con "vars1" [], m2, args2, Term.con "vars2" []]], Term.lit ")"]], Term.lit ")"]
      | _ => t

    def flexFlexDiff' (t : Term) : Term :=
      match t with
      | .con "flexFlexDiff'" [st, m1, args1, vars1, m2, args2, vars2] => Term.con "letIn" [Term.lit "(", Term.lit "let", Term.var "subset21", Term.lit "=", Term.con "all" [Term.con "fun" [Term.con "v" [], Term.lit "=>", Term.con "contains" [vars1, Term.con "v" []]], vars2], Term.lit "in", Term.con "letIn" [Term.lit "let", Term.var "subset12", Term.lit "=", Term.con "all" [Term.con "fun" [Term.con "v" [], Term.lit "=>", Term.con "contains" [vars2, Term.con "v" []]], vars1], Term.lit "in", Term.con "caseExpr" [Term.lit "case", Term.con "subset21" [], Term.con "arm" [Term.var "true", Term.lit "=>", Term.con "letIn" [Term.lit "(", Term.lit "let", Term.var "body", Term.lit "=", Term.con "buildMetaApp" [m1, vars1, vars2], Term.lit "in", Term.con "letIn" [Term.lit "let", Term.var "solution", Term.lit "=", Term.con "buildSolution" [args2, Term.con "body" []], Term.lit "in", Term.con "app" [Term.var "success", Term.con "unifyStateSolveMeta" [st, Term.con "app" [Term.var "gnameNamed", m2], Term.con "solution" []]]], Term.lit ")"]], Term.con "arm" [Term.var "false", Term.lit "=>", Term.con "caseExpr" [Term.lit "(", Term.lit "case", Term.con "subset12" [], Term.con "arm" [Term.var "true", Term.lit "=>", Term.con "letIn" [Term.lit "(", Term.lit "let", Term.var "body", Term.lit "=", Term.con "buildMetaApp" [m2, vars2, vars1], Term.lit "in", Term.con "letIn" [Term.lit "let", Term.var "solution", Term.lit "=", Term.con "buildSolution" [args1, Term.con "body" []], Term.lit "in", Term.con "app" [Term.var "success", Term.con "unifyStateSolveMeta" [st, Term.con "app" [Term.var "gnameNamed", m1], Term.con "solution" []]]], Term.lit ")"]], Term.con "arm" [Term.var "false", Term.lit "=>", Term.con "app" [Term.var "stuck", Term.con "unifyStatePostpone" [st, Term.con "app" [Term.var "lit", m1], Term.con "app" [Term.var "lit", m2]]]], Term.lit ")"]]]], Term.lit ")"]
      | _ => t

    def buildMetaApp (t : Term) : Term :=
      match t with
      | .con "buildMetaApp" [m, sourceVars, targetVars] => Term.con "letIn" [Term.lit "(", Term.lit "let", Term.var "reindexed", Term.lit "=", Term.con "map" [Term.con "fun" [Term.con "v" [], Term.lit "=>", Term.con "findIndexOr0" [sourceVars, Term.con "v" []]], targetVars], Term.lit "in", Term.con "app" [Term.var "foldl", Term.con "app" [Term.con "app" [Term.var "lit", m], Term.con "map" [Term.con "ix" [], Term.con "reindexed" []]]], Term.lit ")"]
      | _ => t

    def findIndexOr0 (t : Term) : Term :=
      match t with
      | .con "findIndexOr0" [xs, v] => Term.con "caseExpr" [Term.lit "(", Term.lit "case", Term.con "findIndex" [xs, v], Term.con "arm" [Term.lit "(", Term.var "some", Term.var "i", Term.lit ")", Term.lit "=>", Term.var "i"], Term.con "arm" [Term.var "none", Term.lit "=>", Term.con "num" [Term.con "number" [Term.lit "0"]]], Term.lit ")"]
      | _ => t

  end FlexFlexDiff

  section UnifyRigid

    def unifyRigidIx (t : Term) : Term :=
      match t with
      | .con "unifyRigid" [st, .con "app" [.var "ix", n1], .con "app" [.var "ix", n2]] => Term.con "caseExpr" [Term.lit "(", Term.lit "case", Term.con "eq" [n1, n2], Term.con "arm" [Term.var "true", Term.lit "=>", Term.con "app" [Term.var "success", st]], Term.con "arm" [Term.var "false", Term.lit "=>", Term.con "app" [Term.var "failure", Term.con "terminal" [Term.lit "variable mismatch"]]], Term.lit ")"]
      | _ => t

    def unifyRigidLit (t : Term) : Term :=
      match t with
      | .con "unifyRigid" [st, .con "app" [.var "lit", l1], .con "app" [.var "lit", l2]] => Term.con "caseExpr" [Term.lit "(", Term.lit "case", Term.con "eq" [l1, l2], Term.con "arm" [Term.var "true", Term.lit "=>", Term.con "app" [Term.var "success", st]], Term.con "arm" [Term.var "false", Term.lit "=>", Term.con "app" [Term.var "failure", Term.con "concat" [Term.con "terminal" [Term.lit "literal mismatch: "], l1, Term.con "terminal" [Term.lit " ≠ "], l2]]], Term.lit ")"]
      | _ => t

    def unifyRigidUniv (t : Term) : Term :=
      match t with
      | .con "unifyRigid" [st, .con "app" [.var "univ", l1], .con "app" [.var "univ", l2]] => Term.con "caseExpr" [Term.lit "(", Term.lit "case", Term.con "levelEq" [l1, l2], Term.con "arm" [Term.var "true", Term.lit "=>", Term.con "app" [Term.var "success", st]], Term.con "arm" [Term.var "false", Term.lit "=>", Term.con "app" [Term.var "failure", Term.con "terminal" [Term.lit "universe level mismatch"]]], Term.lit ")"]
      | _ => t

    def unifyRigidLam (t : Term) : Term :=
      match t with
      | .con "unifyRigid" [st, .con "app" [.var "lam", b1], .con "app" [.var "lam", b2]] => Term.con "unify" [st, b1, b2]
      | _ => t

    def unifyRigidApp (t : Term) : Term :=
      match t with
      | .con "unifyRigid" [st, .con "app" [f1, a1], .con "app" [f2, a2]] => Term.con "caseExpr" [Term.lit "(", Term.lit "case", Term.con "unify" [st, f1, f2], Term.con "arm" [Term.lit "(", Term.var "success", Term.var "st'", Term.lit ")", Term.lit "=>", Term.con "unify" [Term.var "st'", a1, a2]], Term.con "varArm" [Term.lit "$", Term.var "other", Term.lit "=>", Term.var "other"], Term.lit ")"]
      | _ => t

    def unifyRigidPi (t : Term) : Term :=
      match t with
      | .con "unifyRigid" [st, .con "pi" [d1, c1], .con "pi" [d2, c2]] => Term.con "caseExpr" [Term.lit "(", Term.lit "case", Term.con "unify" [st, d1, d2], Term.con "arm" [Term.lit "(", Term.var "success", Term.var "st'", Term.lit ")", Term.lit "=>", Term.con "unify" [Term.var "st'", c1, c2]], Term.con "varArm" [Term.lit "$", Term.var "other", Term.lit "=>", Term.var "other"], Term.lit ")"]
      | _ => t

    def unifyRigidSigma (t : Term) : Term :=
      match t with
      | .con "unifyRigid" [st, .con "sigma" [d1, c1], .con "sigma" [d2, c2]] => Term.con "caseExpr" [Term.lit "(", Term.lit "case", Term.con "unify" [st, d1, d2], Term.con "arm" [Term.lit "(", Term.var "success", Term.var "st'", Term.lit ")", Term.lit "=>", Term.con "unify" [Term.var "st'", c1, c2]], Term.con "varArm" [Term.lit "$", Term.var "other", Term.lit "=>", Term.var "other"], Term.lit ")"]
      | _ => t

    def unifyRigidPair (t : Term) : Term :=
      match t with
      | .con "unifyRigid" [st, .con "pair" [a1, b1], .con "pair" [a2, b2]] => Term.con "caseExpr" [Term.lit "(", Term.lit "case", Term.con "unify" [st, a1, a2], Term.con "arm" [Term.lit "(", Term.var "success", Term.var "st'", Term.lit ")", Term.lit "=>", Term.con "unify" [Term.var "st'", b1, b2]], Term.con "varArm" [Term.lit "$", Term.var "other", Term.lit "=>", Term.var "other"], Term.lit ")"]
      | _ => t

    def unifyRigidFst (t : Term) : Term :=
      match t with
      | .con "unifyRigid" [st, .con "app" [.var "fst", p1], .con "app" [.var "fst", p2]] => Term.con "unify" [st, p1, p2]
      | _ => t

    def unifyRigidSnd (t : Term) : Term :=
      match t with
      | .con "unifyRigid" [st, .con "app" [.var "snd", p1], .con "app" [.var "snd", p2]] => Term.con "unify" [st, p1, p2]
      | _ => t

    def unifyRigidPath (t : Term) : Term :=
      match t with
      | .con "unifyRigid" [st, .con "path" [t1, a1, b1], .con "path" [t2, a2, b2]] => Term.con "caseExpr" [Term.lit "(", Term.lit "case", Term.con "unify" [st, t1, t2], Term.con "arm" [Term.lit "(", Term.var "success", Term.var "st'", Term.lit ")", Term.lit "=>", Term.con "caseExpr" [Term.lit "(", Term.lit "case", Term.con "unify" [Term.var "st'", a1, a2], Term.con "arm" [Term.lit "(", Term.var "success", Term.var "st''", Term.lit ")", Term.lit "=>", Term.con "unify" [Term.var "st''", b1, b2]], Term.con "varArm" [Term.lit "$", Term.var "other", Term.lit "=>", Term.var "other"], Term.lit ")"]], Term.con "varArm" [Term.lit "$", Term.var "other", Term.lit "=>", Term.var "other"], Term.lit ")"]
      | _ => t

    def unifyRigidPlam (t : Term) : Term :=
      match t with
      | .con "unifyRigid" [st, .con "app" [.var "plam", b1], .con "app" [.var "plam", b2]] => Term.con "unify" [st, b1, b2]
      | _ => t

    def unifyRigidPapp (t : Term) : Term :=
      match t with
      | .con "unifyRigid" [st, .con "papp" [p1, r1], .con "papp" [p2, r2]] => Term.con "caseExpr" [Term.lit "(", Term.lit "case", Term.con "unify" [st, p1, p2], Term.con "arm" [Term.lit "(", Term.var "success", Term.var "st'", Term.lit ")", Term.lit "=>", Term.con "unify" [Term.var "st'", r1, r2]], Term.con "varArm" [Term.lit "$", Term.var "other", Term.lit "=>", Term.var "other"], Term.lit ")"]
      | _ => t

    def unifyRigidDim0 (t : Term) : Term :=
      match t with
      | .con "unifyRigid" [st, .con "dim0" [], .con "dim0" []] => Term.con "app" [Term.var "success", st]
      | _ => t

    def unifyRigidDim1 (t : Term) : Term :=
      match t with
      | .con "unifyRigid" [st, .con "dim1" [], .con "dim1" []] => Term.con "app" [Term.var "success", st]
      | _ => t

    def unifyRigidNat (t : Term) : Term :=
      match t with
      | .con "unifyRigid" [st, .con "nat" [], .con "nat" []] => Term.con "app" [Term.var "success", st]
      | _ => t

    def unifyRigidZero (t : Term) : Term :=
      match t with
      | .con "unifyRigid" [st, .con "zero" [], .con "zero" []] => Term.con "app" [Term.var "success", st]
      | _ => t

    def unifyRigidSuc (t : Term) : Term :=
      match t with
      | .con "unifyRigid" [st, .con "app" [.var "suc", n1], .con "app" [.var "suc", n2]] => Term.con "unify" [st, n1, n2]
      | _ => t

    def unifyRigidCircle (t : Term) : Term :=
      match t with
      | .con "unifyRigid" [st, .con "circle" [], .con "circle" []] => Term.con "app" [Term.var "success", st]
      | _ => t

    def unifyRigidBase (t : Term) : Term :=
      match t with
      | .con "unifyRigid" [st, .con "base" [], .con "base" []] => Term.con "app" [Term.var "success", st]
      | _ => t

    def unifyRigidLoop (t : Term) : Term :=
      match t with
      | .con "unifyRigid" [st, .con "app" [.var "loop", r1], .con "app" [.var "loop", r2]] => Term.con "unify" [st, r1, r2]
      | _ => t

    def unifyRigidCofTop (t : Term) : Term :=
      match t with
      | .con "unifyRigid" [st, .con "cof_top" [], .con "cof_top" []] => Term.con "app" [Term.var "success", st]
      | _ => t

    def unifyRigidCofBot (t : Term) : Term :=
      match t with
      | .con "unifyRigid" [st, .con "cof_bot" [], .con "cof_bot" []] => Term.con "app" [Term.var "success", st]
      | _ => t

    def unifyRigidDefault (t : Term) : Term :=
      match t with
      | .con "unifyRigid" [st, t1, t2] => Term.con "app" [Term.var "failure", Term.con "terminal" [Term.lit "structural mismatch"]]
      | _ => t

  end UnifyRigid

  section ApplyMetas

    def applyMetas (t : Term) : Term :=
      match t with
      | .con "applyMetas" [st, e] => Term.con "applyMetas'" [st, e]
      | _ => t

    def applyMetas'Lit (t : Term) : Term :=
      match t with
      | .con "applyMetas'" [st, .con "app" [.var "lit", name]] => Term.con "caseExpr" [Term.lit "(", Term.lit "case", Term.con "startsWith" [name, Term.con "terminal" [Term.lit "?"]], Term.con "arm" [Term.var "true", Term.lit "=>", Term.con "caseExpr" [Term.lit "(", Term.lit "case", Term.con "unifyStateLookupMeta" [st, Term.con "app" [Term.var "gnameNamed", name]], Term.con "arm" [Term.lit "(", Term.var "some", Term.con "metaInfo" [Term.con "labeledArg" [Term.var "name", Term.lit ":", Term.con "_" []], Term.con "labeledArg" [Term.var "ctx", Term.lit ":", Term.con "_" []], Term.con "labeledArg" [Term.var "ty", Term.lit ":", Term.con "_" []], Term.con "labeledArg" [Term.var "solution", Term.lit ":", Term.con "app" [Term.var "some", Term.var "sol"]]], Term.lit ")", Term.lit "=>", Term.var "sol"], Term.con "arm" [Term.var "_", Term.lit "=>", Term.con "app" [Term.var "lit", name]], Term.lit ")"]], Term.con "arm" [Term.var "false", Term.lit "=>", Term.con "app" [Term.var "lit", name]], Term.lit ")"]
      | _ => t

    def applyMetas'Lam (t : Term) : Term :=
      match t with
      | .con "applyMetas'" [st, .con "app" [.var "lam", b]] => Term.con "app" [Term.var "lam", Term.con "applyMetas'" [st, b]]
      | _ => t

    def applyMetas'App (t : Term) : Term :=
      match t with
      | .con "applyMetas'" [st, .con "app" [f, a]] => Term.con "app" [Term.con "applyMetas'" [st, f], Term.con "applyMetas'" [st, a]]
      | _ => t

    def applyMetas'Pi (t : Term) : Term :=
      match t with
      | .con "applyMetas'" [st, .con "pi" [d, c]] => Term.con "pi" [Term.con "applyMetas'" [st, d], Term.con "applyMetas'" [st, c]]
      | _ => t

    def applyMetas'Default (t : Term) : Term :=
      match t with
      | .con "applyMetas'" [st, e] => e
      | _ => t

  end ApplyMetas

  section SolveAll

    def processPostponed (t : Term) : Term :=
      match t with
      | .con "app" [.var "processPostponed", st] => Term.con "caseExpr" [Term.lit "(", Term.lit "case", Term.con "app" [Term.var "unifyStateTakePostponed", st], Term.con "arm" [Term.lit "(", Term.var "result", Term.lit ":", Term.var "st'", Term.con "labeledArg" [Term.var "constraints", Term.lit ":", Term.con "unit" [Term.lit "(", Term.lit ")"]], Term.lit ")", Term.lit "=>", Term.con "record" [Term.lit "(", Term.var "result", Term.lit ":", Term.var "st'", Term.con "labeledArg" [Term.var "progress", Term.lit ":", Term.con "false" []], Term.lit ")"]], Term.con "arm" [Term.lit "(", Term.var "result", Term.lit ":", Term.var "st'", Term.con "labeledArg" [Term.var "constraints", Term.lit ":", Term.var "constraints"], Term.lit ")", Term.lit "=>", Term.con "processConstraints" [Term.var "st'", Term.var "constraints", Term.con "false" []]], Term.lit ")"]
      | _ => t

    def processConstraints (t : Term) : Term :=
      match t with
      | .con "processConstraints" [st, .con "unit" [.lit "(", .lit ")"], progress] => Term.con "record" [Term.lit "(", Term.var "result", Term.lit ":", st, Term.con "labeledArg" [Term.var "progress", Term.lit ":", progress], Term.lit ")"]
      | _ => t

    def processConstraintsCons (t : Term) : Term :=
      match t with
      | .con "processConstraints" [st, .con "app" [.lit "(", .lit "(", .lit "(", t1, .con "≡" [], t2, .lit ")", .lit ")", rest, .lit ")"], progress] => Term.con "letIn" [Term.lit "(", Term.lit "let", Term.var "t1'", Term.lit "=", Term.con "applyMetas" [st, t1], Term.lit "in", Term.con "letIn" [Term.lit "let", Term.var "t2'", Term.lit "=", Term.con "applyMetas" [st, t2], Term.lit "in", Term.con "caseExpr" [Term.lit "case", Term.con "unify" [st, Term.con "t1'" [], Term.con "t2'" []], Term.con "arm" [Term.lit "(", Term.var "success", Term.var "newSt", Term.lit ")", Term.lit "=>", Term.con "processConstraints" [Term.var "newSt", rest, Term.con "true" []]], Term.con "arm" [Term.lit "(", Term.var "stuck", Term.var "newSt", Term.lit ")", Term.lit "=>", Term.con "processConstraints" [Term.var "newSt", rest, progress]], Term.con "arm" [Term.lit "(", Term.var "failure", Term.con "_" [], Term.lit ")", Term.lit "=>", Term.con "processConstraints" [Term.con "unifyStatePostpone" [st, Term.con "t1'" [], Term.con "t2'" []], rest, progress]]]], Term.lit ")"]
      | _ => t

    def solveAll (t : Term) : Term :=
      match t with
      | .con "solveAll" [st, fuel] => Term.con "solveAll'" [st, fuel]
      | _ => t

    def solveAll'0 (t : Term) : Term :=
      match t with
      | .con "solveAll'" [st, .con "num" [.con "number" [.lit "0"]]] => st
      | _ => t

    def solveAll' (t : Term) : Term :=
      match t with
      | .con "solveAll'" [st, .con "app" [.var "suc", fuel]] => Term.con "caseExpr" [Term.lit "(", Term.lit "case", Term.con "app" [Term.var "processPostponed", st], Term.con "arm" [Term.lit "(", Term.var "result", Term.lit ":", Term.var "st'", Term.con "labeledArg" [Term.var "progress", Term.lit ":", Term.con "true" []], Term.lit ")", Term.lit "=>", Term.con "solveAll'" [Term.var "st'", fuel]], Term.con "arm" [Term.lit "(", Term.var "result", Term.lit ":", Term.var "st'", Term.con "labeledArg" [Term.var "progress", Term.lit ":", Term.con "false" []], Term.lit ")", Term.lit "=>", Term.var "st'"], Term.lit ")"]
      | _ => t

  end SolveAll

  section TopLevel

    def tryUnify (t : Term) : Term :=
      match t with
      | .con "tryUnify" [st, t1, t2] => Term.con "caseExpr" [Term.lit "(", Term.lit "case", Term.con "unify" [st, t1, t2], Term.con "arm" [Term.lit "(", Term.var "success", Term.var "st'", Term.lit ")", Term.lit "=>", Term.con "app" [Term.var "some", Term.var "st'"]], Term.con "arm" [Term.lit "(", Term.var "stuck", Term.var "st'", Term.lit ")", Term.lit "=>", Term.con "app" [Term.var "some", Term.var "st'"]], Term.con "arm" [Term.lit "(", Term.var "failure", Term.con "_" [], Term.lit ")", Term.lit "=>", Term.con "none" []], Term.lit ")"]
      | _ => t

    def unifyAndSolve (t : Term) : Term :=
      match t with
      | .con "unifyAndSolve" [st, t1, t2] => Term.con "caseExpr" [Term.lit "(", Term.lit "case", Term.con "unify" [st, t1, t2], Term.con "arm" [Term.lit "(", Term.var "success", Term.var "st'", Term.lit ")", Term.lit "=>", Term.con "app" [Term.var "some", Term.con "solveAll" [Term.var "st'", Term.con "num" [Term.con "number" [Term.lit "100"]]]]], Term.con "arm" [Term.lit "(", Term.var "stuck", Term.var "st'", Term.lit ")", Term.lit "=>", Term.con "app" [Term.var "some", Term.con "solveAll" [Term.var "st'", Term.con "num" [Term.con "number" [Term.lit "100"]]]]], Term.con "arm" [Term.lit "(", Term.var "failure", Term.con "_" [], Term.lit ")", Term.lit "=>", Term.con "none" []], Term.lit ")"]
      | _ => t

    def hole (t : Term) : Term :=
      match t with
      | .con "hole" [st, ctx, ty] => Term.con "caseExpr" [Term.lit "(", Term.lit "case", Term.con "unifyStateFreshMeta" [st, ctx, ty], Term.con "arm" [Term.lit "(", Term.var "result", Term.lit ":", Term.var "st'", Term.con "labeledArg" [Term.var "name", Term.lit ":", Term.var "name"], Term.lit ")", Term.lit "=>", Term.con "record" [Term.lit "(", Term.var "result", Term.lit ":", Term.var "st'", Term.con "labeledArg" [Term.var "expr", Term.lit ":", Term.con "app" [Term.var "lit", Term.con "app" [Term.var "gnameName", Term.var "name"]]], Term.lit ")"]], Term.lit ")"]
      | _ => t

    def allSolved (t : Term) : Term :=
      match t with
      | .con "app" [.var "allSolved", st] => Term.con "app" [Term.var "isEmpty", Term.con "app" [Term.var "unifyStateUnsolved", st]]
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

  end TopLevel

end Unify