/-
  AUTO-GENERATED from .lego files
  Do not edit directly.
-/

import Lego.Algebra

set_option linter.unusedVariables false

open Lego

namespace Elaborate

  section Surface



  end Surface

  section MetaEntry

    def metaEntryTy (t : Term) : Term :=
      match t with
      | .con "app" [.var "metaEntryTy", .con "meta" [.con "labeledArg" [.var "ty", .lit ":", ty], .con "labeledArg" [.var "solution", .lit ":", sol]]] => ty
      | _ => t

    def metaEntrySol (t : Term) : Term :=
      match t with
      | .con "app" [.var "metaEntrySol", .con "meta" [.con "labeledArg" [.var "ty", .lit ":", ty], .con "labeledArg" [.var "solution", .lit ":", sol]]] => sol
      | _ => t

  end MetaEntry

  section MetaCtx

    def metaCtxEmpty (t : Term) : Term :=
      match t with
      | .con "metaCtxEmpty" [] => Term.con "app" [Term.var "metaCtx", Term.con "unit" [Term.lit "(", Term.lit ")"]]
      | _ => t

    def metaCtxLookup (t : Term) : Term :=
      match t with
      | .con "metaCtxLookup" [.con "app" [.var "metaCtx", bindings], id] => Term.con "lookupMeta" [bindings, id]
      | _ => t

    def metaCtxInsert (t : Term) : Term :=
      match t with
      | .con "metaCtxInsert" [.con "app" [.var "metaCtx", bindings], id, entry] => Term.con "app" [Term.var "metaCtx", Term.con "tuple" [bindings, Term.con "tuple" [id, Term.lit "↦", entry]]]
      | _ => t

  end MetaCtx

  section LocalBinding

    def localBindingName (t : Term) : Term :=
      match t with
      | .con "app" [.var "localBindingName", .con "local" [.con "labeledArg" [.var "name", .lit ":", n], .con "labeledArg" [.var "ty", .lit ":", ty], .con "labeledArg" [.var "isDim", .lit ":", d]]] => n
      | _ => t

    def localBindingTy (t : Term) : Term :=
      match t with
      | .con "app" [.var "localBindingTy", .con "local" [.con "labeledArg" [.var "name", .lit ":", n], .con "labeledArg" [.var "ty", .lit ":", ty], .con "labeledArg" [.var "isDim", .lit ":", d]]] => ty
      | _ => t

    def localBindingIsDim (t : Term) : Term :=
      match t with
      | .con "app" [.var "localBindingIsDim", .con "local" [.con "labeledArg" [.var "name", .lit ":", n], .con "labeledArg" [.var "ty", .lit ":", ty], .con "labeledArg" [.var "isDim", .lit ":", d]]] => d
      | _ => t

  end LocalBinding

  section ElabCtx

    def elabCtxEmpty (t : Term) : Term :=
      match t with
      | .con "elabCtxEmpty" [] => Term.con "elabCtx" [Term.con "labeledArg" [Term.var "locals", Term.lit ":", Term.con "unit" [Term.lit "(", Term.lit ")"]], Term.con "labeledArg" [Term.var "global", Term.lit ":", Term.con "globalEnvEmpty" []], Term.con "labeledArg" [Term.var "meta", Term.lit ":", Term.con "metaCtxEmpty" []], Term.con "labeledArg" [Term.var "nextMeta", Term.lit ":", Term.con "num" [Term.con "number" [Term.lit "0"]]]]
      | _ => t

    def elabCtxWithGlobals (t : Term) : Term :=
      match t with
      | .con "app" [.var "elabCtxWithGlobals", env] => Term.con "elabCtx" [Term.con "labeledArg" [Term.var "locals", Term.lit ":", Term.con "unit" [Term.lit "(", Term.lit ")"]], Term.con "labeledArg" [Term.var "global", Term.lit ":", env], Term.con "labeledArg" [Term.var "meta", Term.lit ":", Term.con "metaCtxEmpty" []], Term.con "labeledArg" [Term.var "nextMeta", Term.lit ":", Term.con "num" [Term.con "number" [Term.lit "0"]]]]
      | _ => t

    def elabCtxExtend (t : Term) : Term :=
      match t with
      | .con "elabCtxExtend" [.con "elabCtx" [.con "labeledArg" [.var "locals", .lit ":", locals], .con "labeledArg" [.var "global", .lit ":", g], .con "labeledArg" [.var "meta", .lit ":", m], .con "labeledArg" [.var "nextMeta", .lit ":", n]], name, ty] => Term.con "elabCtx" [Term.con "labeledArg" [Term.var "locals", Term.lit ":", Term.con "tuple" [Term.con "app" [Term.lit "(", Term.con "local" [], Term.con "labeledArg" [Term.var "name", Term.lit ":", name], Term.con "labeledArg" [Term.var "ty", Term.lit ":", ty], Term.con "labeledArg" [Term.var "isDim", Term.lit ":", Term.con "false" []], Term.lit ")"], locals]], Term.con "labeledArg" [Term.var "global", Term.lit ":", g], Term.con "labeledArg" [Term.var "meta", Term.lit ":", m], Term.con "labeledArg" [Term.var "nextMeta", Term.lit ":", n]]
      | _ => t

    def elabCtxExtendDim (t : Term) : Term :=
      match t with
      | .con "elabCtxExtendDim" [.con "elabCtx" [.con "labeledArg" [.var "locals", .lit ":", locals], .con "labeledArg" [.var "global", .lit ":", g], .con "labeledArg" [.var "meta", .lit ":", m], .con "labeledArg" [.var "nextMeta", .lit ":", n]], name] => Term.con "elabCtx" [Term.con "labeledArg" [Term.var "locals", Term.lit ":", Term.con "tuple" [Term.con "app" [Term.lit "(", Term.con "local" [], Term.con "labeledArg" [Term.var "name", Term.lit ":", name], Term.con "labeledArg" [Term.var "ty", Term.lit ":", Term.con "app" [Term.var "lit", Term.con "terminal" [Term.lit "𝕀"]]], Term.con "labeledArg" [Term.var "isDim", Term.lit ":", Term.con "true" []], Term.lit ")"], locals]], Term.con "labeledArg" [Term.var "global", Term.lit ":", g], Term.con "labeledArg" [Term.var "meta", Term.lit ":", m], Term.con "labeledArg" [Term.var "nextMeta", Term.lit ":", n]]
      | _ => t

    def elabCtxLookupLocal (t : Term) : Term :=
      match t with
      | .con "elabCtxLookupLocal" [.con "elabCtx" [.con "labeledArg" [.var "locals", .lit ":", locals], .con "labeledArg" [.var "global", .lit ":", g], .con "labeledArg" [.var "meta", .lit ":", m], .con "labeledArg" [.var "nextMeta", .lit ":", n]], name] => Term.con "lookupLocal" [locals, name, Term.con "num" [Term.con "number" [Term.lit "0"]]]
      | _ => t

    def lookupLocalNil (t : Term) : Term :=
      match t with
      | .con "lookupLocal" [.con "unit" [.lit "(", .lit ")"], name, idx] => Term.con "none" []
      | _ => t

    def lookupLocalConsMatch (t : Term) : Term :=
      match t with
      | .con "lookupLocal" [.con "app" [.lit "(", .lit "(", .var "local", .con "labeledArg" [.var "name", .lit ":", name], .con "labeledArg" [.var "ty", .lit ":", ty], .con "labeledArg" [.var "isDim", .lit ":", d], .lit ")", rest, .lit ")"], name_dup, idx] => Term.con "app" [Term.var "some", Term.con "tuple" [Term.lit "(", idx, Term.lit ",", ty, Term.lit ")"]]
      | _ => t

    def lookupLocalConsMiss (t : Term) : Term :=
      match t with
      | .con "lookupLocal" [.con "app" [.lit "(", .lit "(", .var "local", .con "labeledArg" [.var "name", .lit ":", n], .con "labeledArg" [.var "ty", .lit ":", ty], .con "labeledArg" [.var "isDim", .lit ":", d], .lit ")", rest, .lit ")"], name, idx] => Term.con "lookupLocal" [rest, name, Term.con "app" [Term.var "suc", idx]]
      | _ => t

    def elabCtxDepth (t : Term) : Term :=
      match t with
      | .con "app" [.var "elabCtxDepth", .con "elabCtx" [.con "labeledArg" [.var "locals", .lit ":", locals], .con "labeledArg" [.var "global", .lit ":", g], .con "labeledArg" [.var "meta", .lit ":", m], .con "labeledArg" [.var "nextMeta", .lit ":", n]]] => Term.con "app" [Term.var "length", locals]
      | _ => t

    def elabCtxFreshMeta (t : Term) : Term :=
      match t with
      | .con "elabCtxFreshMeta" [.con "elabCtx" [.con "labeledArg" [.var "locals", .lit ":", locals], .con "labeledArg" [.var "global", .lit ":", g], .con "labeledArg" [.var "meta", .lit ":", m], .con "labeledArg" [.var "nextMeta", .lit ":", n]], ty] => Term.con "record" [Term.lit "(", Term.var "result", Term.lit ":", Term.con "elabCtx" [Term.con "labeledArg" [Term.var "locals", Term.lit ":", locals], Term.con "labeledArg" [Term.var "global", Term.lit ":", g], Term.con "labeledArg" [Term.var "meta", Term.lit ":", Term.con "metaCtxInsert" [m, n, Term.con "meta" [Term.con "labeledArg" [Term.var "ty", Term.lit ":", ty], Term.con "labeledArg" [Term.var "solution", Term.lit ":", Term.con "none" []]]]], Term.con "labeledArg" [Term.var "nextMeta", Term.lit ":", Term.con "app" [Term.var "suc", n]]], Term.con "labeledArg" [Term.var "meta", Term.lit ":", Term.con "app" [Term.var "lit", Term.con "concat" [Term.con "terminal" [Term.lit "meta."], n]]], Term.lit ")"]
      | _ => t

  end ElabCtx

  section ElabResult

    def elabResultTerm (t : Term) : Term :=
      match t with
      | .con "app" [.var "elabResultTerm", .con "ok" [.con "labeledArg" [.var "term", .lit ":", t], .con "labeledArg" [.var "type", .lit ":", ty], .con "labeledArg" [.var "ctx", .lit ":", c]]] => t
      | _ => t

    def elabResultType (t : Term) : Term :=
      match t with
      | .con "app" [.var "elabResultType", .con "ok" [.con "labeledArg" [.var "term", .lit ":", t], .con "labeledArg" [.var "type", .lit ":", ty], .con "labeledArg" [.var "ctx", .lit ":", c]]] => ty
      | _ => t

    def elabResultCtx (t : Term) : Term :=
      match t with
      | .con "app" [.var "elabResultCtx", .con "ok" [.con "labeledArg" [.var "term", .lit ":", t], .con "labeledArg" [.var "type", .lit ":", ty], .con "labeledArg" [.var "ctx", .lit ":", c]]] => c
      | _ => t

  end ElabResult

  section Infer

    def inferVar (t : Term) : Term :=
      match t with
      | .con "infer" [ctx, .con "app" [.var "var", name]] => Term.con "caseExpr" [Term.lit "(", Term.lit "case", Term.con "elabCtxLookupLocal" [ctx, name], Term.con "arm" [Term.lit "(", Term.var "some", Term.con "tuple" [Term.lit "(", Term.var "idx", Term.lit ",", Term.var "ty", Term.lit ")"], Term.lit ")", Term.lit "=>", Term.con "ok" [Term.con "labeledArg" [Term.var "term", Term.lit ":", Term.con "app" [Term.var "ix", Term.var "idx"]], Term.con "labeledArg" [Term.var "type", Term.lit ":", Term.var "ty"], Term.con "labeledArg" [Term.var "ctx", Term.lit ":", ctx]]], Term.con "arm" [Term.var "none", Term.lit "=>", Term.con "app" [Term.var "error", Term.con "concat" [Term.con "terminal" [Term.lit "Unknown variable: "], name]]], Term.lit ")"]
      | _ => t

    def inferLit (t : Term) : Term :=
      match t with
      | .con "infer" [ctx, .con "app" [.var "lit", s]] => Term.con "ok" [Term.con "labeledArg" [Term.var "term", Term.lit ":", Term.con "app" [Term.var "lit", s]], Term.con "labeledArg" [Term.var "type", Term.lit ":", Term.con "app" [Term.var "univ", Term.con "lzero" []]], Term.con "labeledArg" [Term.var "ctx", Term.lit ":", ctx]]
      | _ => t

    def inferUniv (t : Term) : Term :=
      match t with
      | .con "infer" [ctx, .con "app" [.var "Type", n]] => Term.con "ok" [Term.con "labeledArg" [Term.var "term", Term.lit ":", Term.con "app" [Term.var "univ", Term.con "app" [Term.var "levelOfNat", n]]], Term.con "labeledArg" [Term.var "type", Term.lit ":", Term.con "app" [Term.var "univ", Term.con "app" [Term.var "levelOfNat", Term.con "app" [Term.var "suc", n]]]], Term.con "labeledArg" [Term.var "ctx", Term.lit ":", ctx]]
      | _ => t

    def inferPi (t : Term) : Term :=
      match t with
      | .con "infer" [ctx, .con "Π" [.con "ann" [.lit "(", x, .lit ":", dom, .lit ")"], cod]] => Term.con "caseExpr" [Term.lit "(", Term.lit "case", Term.con "infer" [ctx, dom], Term.con "arm" [Term.lit "(", Term.var "ok", Term.con "labeledArg" [Term.var "term", Term.lit ":", Term.var "domCore"], Term.con "labeledArg" [Term.var "type", Term.lit ":", Term.var "domTy"], Term.con "labeledArg" [Term.var "ctx", Term.lit ":", Term.var "ctx'"], Term.lit ")", Term.lit "=>", Term.con "caseExpr" [Term.lit "(", Term.lit "case", Term.con "infer" [Term.con "elabCtxExtend" [Term.var "ctx'", x, Term.var "domCore"], cod], Term.con "arm" [Term.lit "(", Term.var "ok", Term.con "labeledArg" [Term.var "term", Term.lit ":", Term.var "codCore"], Term.con "labeledArg" [Term.var "type", Term.lit ":", Term.var "codTy"], Term.con "labeledArg" [Term.var "ctx", Term.lit ":", Term.var "ctx''"], Term.lit ")", Term.lit "=>", Term.con "ok" [Term.con "labeledArg" [Term.var "term", Term.lit ":", Term.con "pi" [Term.var "domCore", Term.var "codCore"]], Term.con "labeledArg" [Term.var "type", Term.lit ":", Term.con "app" [Term.var "univ", Term.con "lmax" [Term.con "app" [Term.var "levelOf", Term.var "domTy"], Term.con "app" [Term.var "levelOf", Term.var "codTy"]]]], Term.con "labeledArg" [Term.var "ctx", Term.lit ":", Term.var "ctx''"]]], Term.con "varArm" [Term.lit "$", Term.var "err", Term.lit "=>", Term.var "err"], Term.lit ")"]], Term.con "varArm" [Term.lit "$", Term.var "err", Term.lit "=>", Term.var "err"], Term.lit ")"]
      | _ => t

    def inferSigma (t : Term) : Term :=
      match t with
      | .con "infer" [ctx, .con "Σ" [.con "ann" [.lit "(", x, .lit ":", dom, .lit ")"], cod]] => Term.con "caseExpr" [Term.lit "(", Term.lit "case", Term.con "infer" [ctx, dom], Term.con "arm" [Term.lit "(", Term.var "ok", Term.con "labeledArg" [Term.var "term", Term.lit ":", Term.var "domCore"], Term.con "labeledArg" [Term.var "type", Term.lit ":", Term.var "domTy"], Term.con "labeledArg" [Term.var "ctx", Term.lit ":", Term.var "ctx'"], Term.lit ")", Term.lit "=>", Term.con "caseExpr" [Term.lit "(", Term.lit "case", Term.con "infer" [Term.con "elabCtxExtend" [Term.var "ctx'", x, Term.var "domCore"], cod], Term.con "arm" [Term.lit "(", Term.var "ok", Term.con "labeledArg" [Term.var "term", Term.lit ":", Term.var "codCore"], Term.con "labeledArg" [Term.var "type", Term.lit ":", Term.var "codTy"], Term.con "labeledArg" [Term.var "ctx", Term.lit ":", Term.var "ctx''"], Term.lit ")", Term.lit "=>", Term.con "ok" [Term.con "labeledArg" [Term.var "term", Term.lit ":", Term.con "sigma" [Term.var "domCore", Term.var "codCore"]], Term.con "labeledArg" [Term.var "type", Term.lit ":", Term.con "app" [Term.var "univ", Term.con "lmax" [Term.con "app" [Term.var "levelOf", Term.var "domTy"], Term.con "app" [Term.var "levelOf", Term.var "codTy"]]]], Term.con "labeledArg" [Term.var "ctx", Term.lit ":", Term.var "ctx''"]]], Term.con "varArm" [Term.lit "$", Term.var "err", Term.lit "=>", Term.var "err"], Term.lit ")"]], Term.con "varArm" [Term.lit "$", Term.var "err", Term.lit "=>", Term.var "err"], Term.lit ")"]
      | _ => t

    def inferApp (t : Term) : Term :=
      match t with
      | .con "infer" [ctx, .con "app" [f, x]] => Term.con "caseExpr" [Term.lit "(", Term.lit "case", Term.con "infer" [ctx, f], Term.con "arm" [Term.lit "(", Term.var "ok", Term.con "labeledArg" [Term.var "term", Term.lit ":", Term.var "fCore"], Term.con "labeledArg" [Term.var "type", Term.lit ":", Term.con "pi" [Term.var "dom", Term.var "cod"]], Term.con "labeledArg" [Term.var "ctx", Term.lit ":", Term.var "ctx'"], Term.lit ")", Term.lit "=>", Term.con "caseExpr" [Term.lit "(", Term.lit "case", Term.con "check" [Term.var "ctx'", x, Term.var "dom"], Term.con "arm" [Term.lit "(", Term.var "ok", Term.con "labeledArg" [Term.var "term", Term.lit ":", Term.var "xCore"], Term.con "labeledArg" [Term.var "type", Term.lit ":", Term.con "_" []], Term.con "labeledArg" [Term.var "ctx", Term.lit ":", Term.var "ctx''"], Term.lit ")", Term.lit "=>", Term.con "ok" [Term.con "labeledArg" [Term.var "term", Term.lit ":", Term.con "app" [Term.var "fCore", Term.var "xCore"]], Term.con "labeledArg" [Term.var "type", Term.lit ":", Term.con "subst" [Term.con "num" [Term.con "number" [Term.lit "0"]], Term.var "xCore", Term.var "cod"]], Term.con "labeledArg" [Term.var "ctx", Term.lit ":", Term.var "ctx''"]]], Term.con "varArm" [Term.lit "$", Term.var "err", Term.lit "=>", Term.var "err"], Term.lit ")"]], Term.con "arm" [Term.lit "(", Term.var "ok", Term.con "labeledArg" [Term.var "term", Term.lit ":", Term.con "_" []], Term.con "labeledArg" [Term.var "type", Term.lit ":", Term.var "ty"], Term.con "labeledArg" [Term.var "ctx", Term.lit ":", Term.con "_" []], Term.lit ")", Term.lit "=>", Term.con "app" [Term.var "error", Term.con "concat" [Term.con "terminal" [Term.lit "Expected function type, got "], Term.var "ty"]]], Term.con "varArm" [Term.lit "$", Term.var "err", Term.lit "=>", Term.var "err"], Term.lit ")"]
      | _ => t

    def inferPair (t : Term) : Term :=
      match t with
      | .con "infer" [ctx, .con "tuple" [.lit "⟨", a, .lit ",", b, .lit "⟩"]] => Term.con "caseExpr" [Term.lit "(", Term.lit "case", Term.con "infer" [ctx, a], Term.con "arm" [Term.lit "(", Term.var "ok", Term.con "labeledArg" [Term.var "term", Term.lit ":", Term.var "aCore"], Term.con "labeledArg" [Term.var "type", Term.lit ":", Term.var "aTy"], Term.con "labeledArg" [Term.var "ctx", Term.lit ":", Term.var "ctx'"], Term.lit ")", Term.lit "=>", Term.con "caseExpr" [Term.lit "(", Term.lit "case", Term.con "infer" [Term.var "ctx'", b], Term.con "arm" [Term.lit "(", Term.var "ok", Term.con "labeledArg" [Term.var "term", Term.lit ":", Term.var "bCore"], Term.con "labeledArg" [Term.var "type", Term.lit ":", Term.var "bTy"], Term.con "labeledArg" [Term.var "ctx", Term.lit ":", Term.var "ctx''"], Term.lit ")", Term.lit "=>", Term.con "ok" [Term.con "labeledArg" [Term.var "term", Term.lit ":", Term.con "pair" [Term.var "aCore", Term.var "bCore"]], Term.con "labeledArg" [Term.var "type", Term.lit ":", Term.con "sigma" [Term.var "aTy", Term.con "shift" [Term.con "num" [Term.con "number" [Term.lit "0"]], Term.con "num" [Term.con "number" [Term.lit "1"]], Term.var "bTy"]]], Term.con "labeledArg" [Term.var "ctx", Term.lit ":", Term.var "ctx''"]]], Term.con "varArm" [Term.lit "$", Term.var "err", Term.lit "=>", Term.var "err"], Term.lit ")"]], Term.con "varArm" [Term.lit "$", Term.var "err", Term.lit "=>", Term.var "err"], Term.lit ")"]
      | _ => t

    def inferFst (t : Term) : Term :=
      match t with
      | .con "infer" [ctx, .con "app" [.var "fst", p]] => Term.con "caseExpr" [Term.lit "(", Term.lit "case", Term.con "infer" [ctx, p], Term.con "arm" [Term.lit "(", Term.var "ok", Term.con "labeledArg" [Term.var "term", Term.lit ":", Term.var "pCore"], Term.con "labeledArg" [Term.var "type", Term.lit ":", Term.con "sigma" [Term.var "dom", Term.var "cod"]], Term.con "labeledArg" [Term.var "ctx", Term.lit ":", Term.var "ctx'"], Term.lit ")", Term.lit "=>", Term.con "ok" [Term.con "labeledArg" [Term.var "term", Term.lit ":", Term.con "app" [Term.var "fst", Term.var "pCore"]], Term.con "labeledArg" [Term.var "type", Term.lit ":", Term.var "dom"], Term.con "labeledArg" [Term.var "ctx", Term.lit ":", Term.var "ctx'"]]], Term.con "arm" [Term.lit "(", Term.var "ok", Term.con "labeledArg" [Term.var "term", Term.lit ":", Term.con "_" []], Term.con "labeledArg" [Term.var "type", Term.lit ":", Term.var "ty"], Term.con "labeledArg" [Term.var "ctx", Term.lit ":", Term.con "_" []], Term.lit ")", Term.lit "=>", Term.con "app" [Term.var "error", Term.con "terminal" [Term.lit "Expected sigma type for fst"]]], Term.con "varArm" [Term.lit "$", Term.var "err", Term.lit "=>", Term.var "err"], Term.lit ")"]
      | _ => t

    def inferSnd (t : Term) : Term :=
      match t with
      | .con "infer" [ctx, .con "app" [.var "snd", p]] => Term.con "caseExpr" [Term.lit "(", Term.lit "case", Term.con "infer" [ctx, p], Term.con "arm" [Term.lit "(", Term.var "ok", Term.con "labeledArg" [Term.var "term", Term.lit ":", Term.var "pCore"], Term.con "labeledArg" [Term.var "type", Term.lit ":", Term.con "sigma" [Term.var "dom", Term.var "cod"]], Term.con "labeledArg" [Term.var "ctx", Term.lit ":", Term.var "ctx'"], Term.lit ")", Term.lit "=>", Term.con "ok" [Term.con "labeledArg" [Term.var "term", Term.lit ":", Term.con "app" [Term.var "snd", Term.var "pCore"]], Term.con "labeledArg" [Term.var "type", Term.lit ":", Term.con "subst" [Term.con "num" [Term.con "number" [Term.lit "0"]], Term.con "app" [Term.var "fst", Term.var "pCore"], Term.var "cod"]], Term.con "labeledArg" [Term.var "ctx", Term.lit ":", Term.var "ctx'"]]], Term.con "arm" [Term.lit "(", Term.var "ok", Term.con "labeledArg" [Term.var "term", Term.lit ":", Term.con "_" []], Term.con "labeledArg" [Term.var "type", Term.lit ":", Term.var "ty"], Term.con "labeledArg" [Term.var "ctx", Term.lit ":", Term.con "_" []], Term.lit ")", Term.lit "=>", Term.con "app" [Term.var "error", Term.con "terminal" [Term.lit "Expected sigma type for snd"]]], Term.con "varArm" [Term.lit "$", Term.var "err", Term.lit "=>", Term.var "err"], Term.lit ")"]
      | _ => t

    def inferAnn (t : Term) : Term :=
      match t with
      | .con "infer" [ctx, .con "ann" [.lit "(", .lit "(", tm, .lit ":", ty, .lit ")", .lit ")"]] => Term.con "caseExpr" [Term.lit "(", Term.lit "case", Term.con "infer" [ctx, ty], Term.con "arm" [Term.lit "(", Term.var "ok", Term.con "labeledArg" [Term.var "term", Term.lit ":", Term.var "tyCore"], Term.con "labeledArg" [Term.var "type", Term.lit ":", Term.con "_" []], Term.con "labeledArg" [Term.var "ctx", Term.lit ":", Term.var "ctx'"], Term.lit ")", Term.lit "=>", Term.con "caseExpr" [Term.lit "(", Term.lit "case", Term.con "check" [Term.var "ctx'", tm, Term.var "tyCore"], Term.con "arm" [Term.lit "(", Term.var "ok", Term.con "labeledArg" [Term.var "term", Term.lit ":", Term.var "tmCore"], Term.con "labeledArg" [Term.var "type", Term.lit ":", Term.con "_" []], Term.con "labeledArg" [Term.var "ctx", Term.lit ":", Term.var "ctx''"], Term.lit ")", Term.lit "=>", Term.con "ok" [Term.con "labeledArg" [Term.var "term", Term.lit ":", Term.var "tmCore"], Term.con "labeledArg" [Term.var "type", Term.lit ":", Term.var "tyCore"], Term.con "labeledArg" [Term.var "ctx", Term.lit ":", Term.var "ctx''"]]], Term.con "varArm" [Term.lit "$", Term.var "err", Term.lit "=>", Term.var "err"], Term.lit ")"]], Term.con "varArm" [Term.lit "$", Term.var "err", Term.lit "=>", Term.var "err"], Term.lit ")"]
      | _ => t

    def inferHole (t : Term) : Term :=
      match t with
      | .con "infer" [ctx, .con "?" [name]] => Term.con "caseExpr" [Term.lit "(", Term.lit "case", Term.con "elabCtxFreshMeta" [ctx, Term.con "app" [Term.var "univ", Term.con "lzero" []]], Term.con "arm" [Term.lit "(", Term.var "result", Term.lit ":", Term.var "ctx'", Term.con "labeledArg" [Term.var "meta", Term.lit ":", Term.var "typeMeta"], Term.lit ")", Term.lit "=>", Term.con "caseExpr" [Term.lit "(", Term.lit "case", Term.con "elabCtxFreshMeta" [Term.var "ctx'", Term.var "typeMeta"], Term.con "arm" [Term.lit "(", Term.var "result", Term.lit ":", Term.var "ctx''", Term.con "labeledArg" [Term.var "meta", Term.lit ":", Term.var "termMeta"], Term.lit ")", Term.lit "=>", Term.con "ok" [Term.con "labeledArg" [Term.var "term", Term.lit ":", Term.var "termMeta"], Term.con "labeledArg" [Term.var "type", Term.lit ":", Term.var "typeMeta"], Term.con "labeledArg" [Term.var "ctx", Term.lit ":", Term.var "ctx''"]]], Term.lit ")"]], Term.lit ")"]
      | _ => t

    def inferDim0 (t : Term) : Term :=
      match t with
      | .con "infer" [ctx, .con "num" [.con "number" [.lit "0"]]] => Term.con "ok" [Term.con "labeledArg" [Term.var "term", Term.lit ":", Term.con "dim0" []], Term.con "labeledArg" [Term.var "type", Term.lit ":", Term.con "app" [Term.var "lit", Term.con "terminal" [Term.lit "𝕀"]]], Term.con "labeledArg" [Term.var "ctx", Term.lit ":", ctx]]
      | _ => t

    def inferDim1 (t : Term) : Term :=
      match t with
      | .con "infer" [ctx, .con "num" [.con "number" [.lit "1"]]] => Term.con "ok" [Term.con "labeledArg" [Term.var "term", Term.lit ":", Term.con "dim1" []], Term.con "labeledArg" [Term.var "type", Term.lit ":", Term.con "app" [Term.var "lit", Term.con "terminal" [Term.lit "𝕀"]]], Term.con "labeledArg" [Term.var "ctx", Term.lit ":", ctx]]
      | _ => t

    def inferPath (t : Term) : Term :=
      match t with
      | .con "infer" [ctx, .con "Path" [A, a, b]] => Term.con "caseExpr" [Term.lit "(", Term.lit "case", Term.con "infer" [ctx, A], Term.con "arm" [Term.lit "(", Term.var "ok", Term.con "labeledArg" [Term.var "term", Term.lit ":", Term.var "ACore"], Term.con "labeledArg" [Term.var "type", Term.lit ":", Term.var "ATy"], Term.con "labeledArg" [Term.var "ctx", Term.lit ":", Term.var "ctx'"], Term.lit ")", Term.lit "=>", Term.con "caseExpr" [Term.lit "(", Term.lit "case", Term.con "infer" [Term.var "ctx'", a], Term.con "arm" [Term.lit "(", Term.var "ok", Term.con "labeledArg" [Term.var "term", Term.lit ":", Term.var "aCore"], Term.con "labeledArg" [Term.var "type", Term.lit ":", Term.con "_" []], Term.con "labeledArg" [Term.var "ctx", Term.lit ":", Term.var "ctx''"], Term.lit ")", Term.lit "=>", Term.con "caseExpr" [Term.lit "(", Term.lit "case", Term.con "infer" [Term.var "ctx''", b], Term.con "arm" [Term.lit "(", Term.var "ok", Term.con "labeledArg" [Term.var "term", Term.lit ":", Term.var "bCore"], Term.con "labeledArg" [Term.var "type", Term.lit ":", Term.con "_" []], Term.con "labeledArg" [Term.var "ctx", Term.lit ":", Term.var "ctx'''"], Term.lit ")", Term.lit "=>", Term.con "ok" [Term.con "labeledArg" [Term.var "term", Term.lit ":", Term.con "path" [Term.var "ACore", Term.var "aCore", Term.var "bCore"]], Term.con "labeledArg" [Term.var "type", Term.lit ":", Term.con "app" [Term.var "univ", Term.con "app" [Term.var "levelOf", Term.var "ATy"]]], Term.con "labeledArg" [Term.var "ctx", Term.lit ":", Term.var "ctx'''"]]], Term.con "varArm" [Term.lit "$", Term.var "err", Term.lit "=>", Term.var "err"], Term.lit ")"]], Term.con "varArm" [Term.lit "$", Term.var "err", Term.lit "=>", Term.var "err"], Term.lit ")"]], Term.con "varArm" [Term.lit "$", Term.var "err", Term.lit "=>", Term.var "err"], Term.lit ")"]
      | _ => t

    def inferPapp (t : Term) : Term :=
      match t with
      | .con "infer" [ctx, .con "tuple" [p, .lit "@", r]] => Term.con "caseExpr" [Term.lit "(", Term.lit "case", Term.con "infer" [ctx, p], Term.con "arm" [Term.lit "(", Term.var "ok", Term.con "labeledArg" [Term.var "term", Term.lit ":", Term.var "pCore"], Term.con "labeledArg" [Term.var "type", Term.lit ":", Term.con "path" [Term.var "A", Term.var "l", Term.var "ep"]], Term.con "labeledArg" [Term.var "ctx", Term.lit ":", Term.var "ctx'"], Term.lit ")", Term.lit "=>", Term.con "caseExpr" [Term.lit "(", Term.lit "case", Term.con "infer" [Term.var "ctx'", r], Term.con "arm" [Term.lit "(", Term.var "ok", Term.con "labeledArg" [Term.var "term", Term.lit ":", Term.var "rCore"], Term.con "labeledArg" [Term.var "type", Term.lit ":", Term.con "_" []], Term.con "labeledArg" [Term.var "ctx", Term.lit ":", Term.var "ctx''"], Term.lit ")", Term.lit "=>", Term.con "ok" [Term.con "labeledArg" [Term.var "term", Term.lit ":", Term.con "papp" [Term.var "pCore", Term.var "rCore"]], Term.con "labeledArg" [Term.var "type", Term.lit ":", Term.var "A"], Term.con "labeledArg" [Term.var "ctx", Term.lit ":", Term.var "ctx''"]]], Term.con "varArm" [Term.lit "$", Term.var "err", Term.lit "=>", Term.var "err"], Term.lit ")"]], Term.con "arm" [Term.lit "(", Term.var "ok", Term.con "labeledArg" [Term.var "term", Term.lit ":", Term.con "_" []], Term.con "labeledArg" [Term.var "type", Term.lit ":", Term.var "ty"], Term.con "labeledArg" [Term.var "ctx", Term.lit ":", Term.con "_" []], Term.lit ")", Term.lit "=>", Term.con "app" [Term.var "error", Term.con "terminal" [Term.lit "Expected path type for @"]]], Term.con "varArm" [Term.lit "$", Term.var "err", Term.lit "=>", Term.var "err"], Term.lit ")"]
      | _ => t

    def inferRefl (t : Term) : Term :=
      match t with
      | .con "infer" [ctx, .con "app" [.var "refl", a]] => Term.con "caseExpr" [Term.lit "(", Term.lit "case", Term.con "infer" [ctx, a], Term.con "arm" [Term.lit "(", Term.var "ok", Term.con "labeledArg" [Term.var "term", Term.lit ":", Term.var "aCore"], Term.con "labeledArg" [Term.var "type", Term.lit ":", Term.var "aTy"], Term.con "labeledArg" [Term.var "ctx", Term.lit ":", Term.var "ctx'"], Term.lit ")", Term.lit "=>", Term.con "ok" [Term.con "labeledArg" [Term.var "term", Term.lit ":", Term.con "app" [Term.var "refl", Term.var "aCore"]], Term.con "labeledArg" [Term.var "type", Term.lit ":", Term.con "path" [Term.var "aTy", Term.var "aCore", Term.var "aCore"]], Term.con "labeledArg" [Term.var "ctx", Term.lit ":", Term.var "ctx'"]]], Term.con "varArm" [Term.lit "$", Term.var "err", Term.lit "=>", Term.var "err"], Term.lit ")"]
      | _ => t

  end Infer

  section Check

    def checkLam (t : Term) : Term :=
      match t with
      | .con "check" [ctx, .con "app" [.var "λ", .con "binder" [.lit "$", .var "x", .lit ".", body]], .con "pi" [dom, cod]] => Term.con "caseExpr" [Term.lit "(", Term.lit "case", Term.con "check" [Term.con "elabCtxExtend" [ctx, Term.var "x", dom], body, cod], Term.con "arm" [Term.lit "(", Term.var "ok", Term.con "labeledArg" [Term.var "term", Term.lit ":", Term.var "bodyCore"], Term.con "labeledArg" [Term.var "type", Term.lit ":", Term.con "_" []], Term.con "labeledArg" [Term.var "ctx", Term.lit ":", Term.var "ctx'"], Term.lit ")", Term.lit "=>", Term.con "ok" [Term.con "labeledArg" [Term.var "term", Term.lit ":", Term.con "app" [Term.var "lam", Term.var "bodyCore"]], Term.con "labeledArg" [Term.var "type", Term.lit ":", Term.con "pi" [dom, cod]], Term.con "labeledArg" [Term.var "ctx", Term.lit ":", Term.var "ctx'"]]], Term.con "varArm" [Term.lit "$", Term.var "err", Term.lit "=>", Term.var "err"], Term.lit ")"]
      | _ => t

    def checkPlam (t : Term) : Term :=
      match t with
      | .con "check" [ctx, .con "app" [.var "λ", .con "binder" [.lit "$", .var "i", .lit ".", body]], .con "path" [A, l, r]] => Term.con "caseExpr" [Term.lit "(", Term.lit "case", Term.con "check" [Term.con "elabCtxExtendDim" [ctx, Term.var "i"], body, A], Term.con "arm" [Term.lit "(", Term.var "ok", Term.con "labeledArg" [Term.var "term", Term.lit ":", Term.var "bodyCore"], Term.con "labeledArg" [Term.var "type", Term.lit ":", Term.con "_" []], Term.con "labeledArg" [Term.var "ctx", Term.lit ":", Term.var "ctx'"], Term.lit ")", Term.lit "=>", Term.con "ok" [Term.con "labeledArg" [Term.var "term", Term.lit ":", Term.con "app" [Term.var "plam", Term.var "bodyCore"]], Term.con "labeledArg" [Term.var "type", Term.lit ":", Term.con "path" [A, l, r]], Term.con "labeledArg" [Term.var "ctx", Term.lit ":", Term.var "ctx'"]]], Term.con "varArm" [Term.lit "$", Term.var "err", Term.lit "=>", Term.var "err"], Term.lit ")"]
      | _ => t

    def checkPair (t : Term) : Term :=
      match t with
      | .con "check" [ctx, .con "tuple" [.lit "⟨", a, .lit ",", b, .lit "⟩"], .con "sigma" [dom, cod]] => Term.con "caseExpr" [Term.lit "(", Term.lit "case", Term.con "check" [ctx, a, dom], Term.con "arm" [Term.lit "(", Term.var "ok", Term.con "labeledArg" [Term.var "term", Term.lit ":", Term.var "aCore"], Term.con "labeledArg" [Term.var "type", Term.lit ":", Term.con "_" []], Term.con "labeledArg" [Term.var "ctx", Term.lit ":", Term.var "ctx'"], Term.lit ")", Term.lit "=>", Term.con "letIn" [Term.lit "(", Term.lit "let", Term.var "codSubst", Term.lit "=", Term.con "subst" [Term.con "num" [Term.con "number" [Term.lit "0"]], Term.var "aCore", cod], Term.lit "in", Term.con "caseExpr" [Term.lit "case", Term.con "check" [Term.var "ctx'", b, Term.con "codSubst" []], Term.con "arm" [Term.lit "(", Term.var "ok", Term.con "labeledArg" [Term.var "term", Term.lit ":", Term.var "bCore"], Term.con "labeledArg" [Term.var "type", Term.lit ":", Term.con "_" []], Term.con "labeledArg" [Term.var "ctx", Term.lit ":", Term.var "ctx''"], Term.lit ")", Term.lit "=>", Term.con "ok" [Term.con "labeledArg" [Term.var "term", Term.lit ":", Term.con "pair" [Term.var "aCore", Term.var "bCore"]], Term.con "labeledArg" [Term.var "type", Term.lit ":", Term.con "sigma" [dom, cod]], Term.con "labeledArg" [Term.var "ctx", Term.lit ":", Term.var "ctx''"]]], Term.con "varArm" [Term.lit "$", Term.var "err", Term.lit "=>", Term.var "err"]], Term.lit ")"]], Term.con "varArm" [Term.lit "$", Term.var "err", Term.lit "=>", Term.var "err"], Term.lit ")"]
      | _ => t

    def checkLet (t : Term) : Term :=
      match t with
      | .con "check" [ctx, .con "let" [.con "typedVar" [.lit "$", .var "x", .lit ":", ty], .lit "=", val, .lit "in", body], expected] => Term.con "caseExpr" [Term.lit "(", Term.lit "case", Term.con "infer" [ctx, ty], Term.con "arm" [Term.lit "(", Term.var "ok", Term.con "labeledArg" [Term.var "term", Term.lit ":", Term.var "tyCore"], Term.con "labeledArg" [Term.var "type", Term.lit ":", Term.con "_" []], Term.con "labeledArg" [Term.var "ctx", Term.lit ":", Term.var "ctx'"], Term.lit ")", Term.lit "=>", Term.con "caseExpr" [Term.lit "(", Term.lit "case", Term.con "check" [Term.var "ctx'", val, Term.var "tyCore"], Term.con "arm" [Term.lit "(", Term.var "ok", Term.con "labeledArg" [Term.var "term", Term.lit ":", Term.var "valCore"], Term.con "labeledArg" [Term.var "type", Term.lit ":", Term.con "_" []], Term.con "labeledArg" [Term.var "ctx", Term.lit ":", Term.var "ctx''"], Term.lit ")", Term.lit "=>", Term.con "caseExpr" [Term.lit "(", Term.lit "case", Term.con "check" [Term.con "elabCtxExtend" [Term.var "ctx''", Term.var "x", Term.var "tyCore"], body, expected], Term.con "arm" [Term.lit "(", Term.var "ok", Term.con "labeledArg" [Term.var "term", Term.lit ":", Term.var "bodyCore"], Term.con "labeledArg" [Term.var "type", Term.lit ":", Term.con "_" []], Term.con "labeledArg" [Term.var "ctx", Term.lit ":", Term.var "ctx'''"], Term.lit ")", Term.lit "=>", Term.con "ok" [Term.con "labeledArg" [Term.var "term", Term.lit ":", Term.con "letE" [Term.var "tyCore", Term.var "valCore", Term.var "bodyCore"]], Term.con "labeledArg" [Term.var "type", Term.lit ":", expected], Term.con "labeledArg" [Term.var "ctx", Term.lit ":", Term.var "ctx'''"]]], Term.con "varArm" [Term.lit "$", Term.var "err", Term.lit "=>", Term.var "err"], Term.lit ")"]], Term.con "varArm" [Term.lit "$", Term.var "err", Term.lit "=>", Term.var "err"], Term.lit ")"]], Term.con "varArm" [Term.lit "$", Term.var "err", Term.lit "=>", Term.var "err"], Term.lit ")"]
      | _ => t

    def checkHole (t : Term) : Term :=
      match t with
      | .con "check" [ctx, .con "?" [name], expected] => Term.con "caseExpr" [Term.lit "(", Term.lit "case", Term.con "elabCtxFreshMeta" [ctx, expected], Term.con "arm" [Term.lit "(", Term.var "result", Term.lit ":", Term.var "ctx'", Term.con "labeledArg" [Term.var "meta", Term.lit ":", Term.var "termMeta"], Term.lit ")", Term.lit "=>", Term.con "ok" [Term.con "labeledArg" [Term.var "term", Term.lit ":", Term.var "termMeta"], Term.con "labeledArg" [Term.var "type", Term.lit ":", expected], Term.con "labeledArg" [Term.var "ctx", Term.lit ":", Term.var "ctx'"]]], Term.lit ")"]
      | _ => t

    def checkRefl (t : Term) : Term :=
      match t with
      | .con "check" [ctx, .con "app" [.var "refl", a], .con "path" [A, l, r]] => Term.con "caseExpr" [Term.lit "(", Term.lit "case", Term.con "check" [ctx, a, l], Term.con "arm" [Term.lit "(", Term.var "ok", Term.con "labeledArg" [Term.var "term", Term.lit ":", Term.var "aCore"], Term.con "labeledArg" [Term.var "type", Term.lit ":", Term.con "_" []], Term.con "labeledArg" [Term.var "ctx", Term.lit ":", Term.var "ctx'"], Term.lit ")", Term.lit "=>", Term.con "ok" [Term.con "labeledArg" [Term.var "term", Term.lit ":", Term.con "app" [Term.var "refl", Term.var "aCore"]], Term.con "labeledArg" [Term.var "type", Term.lit ":", Term.con "path" [A, l, r]], Term.con "labeledArg" [Term.var "ctx", Term.lit ":", Term.var "ctx'"]]], Term.con "varArm" [Term.lit "$", Term.var "err", Term.lit "=>", Term.var "err"], Term.lit ")"]
      | _ => t

    def checkFallback (t : Term) : Term :=
      match t with
      | .con "check" [ctx, s, expected] => Term.con "caseExpr" [Term.lit "(", Term.lit "case", Term.con "infer" [ctx, s], Term.con "arm" [Term.lit "(", Term.var "ok", Term.con "labeledArg" [Term.var "term", Term.lit ":", Term.var "core"], Term.con "labeledArg" [Term.var "type", Term.lit ":", Term.var "inferred"], Term.con "labeledArg" [Term.var "ctx", Term.lit ":", Term.var "ctx'"], Term.lit ")", Term.lit "=>", Term.con "caseExpr" [Term.lit "(", Term.lit "case", Term.con "conv" [Term.var "inferred", expected], Term.con "arm" [Term.var "true", Term.lit "=>", Term.con "ok" [Term.con "labeledArg" [Term.var "term", Term.lit ":", Term.var "core"], Term.con "labeledArg" [Term.var "type", Term.lit ":", expected], Term.con "labeledArg" [Term.var "ctx", Term.lit ":", Term.var "ctx'"]]], Term.con "arm" [Term.var "false", Term.lit "=>", Term.con "app" [Term.var "error", Term.con "concat" [Term.con "terminal" [Term.lit "Type mismatch: expected "], expected, Term.con "terminal" [Term.lit ", got "], Term.var "inferred"]]], Term.lit ")"]], Term.con "varArm" [Term.lit "$", Term.var "err", Term.lit "=>", Term.var "err"], Term.lit ")"]
      | _ => t

  end Check

  section Conv

    def conv (t : Term) : Term :=
      match t with
      | .con "conv" [t1, t2] => Term.con "letIn" [Term.lit "(", Term.lit "let", Term.var "t1'", Term.lit "=", Term.con "normalize" [Term.con "num" [Term.con "number" [Term.lit "100"]], t1], Term.lit "in", Term.con "letIn" [Term.lit "let", Term.var "t2'", Term.lit "=", Term.con "normalize" [Term.con "num" [Term.con "number" [Term.lit "100"]], t2], Term.lit "in", Term.con "eq" [Term.con "t1'" [], Term.con "t2'" []]], Term.lit ")"]
      | _ => t

  end Conv

  section TopLevel

    def elaborate (t : Term) : Term :=
      match t with
      | .con "elaborate" [env, s, ty] => Term.con "caseExpr" [Term.lit "(", Term.lit "case", Term.con "check" [Term.con "app" [Term.var "elabCtxWithGlobals", env], s, ty], Term.con "arm" [Term.lit "(", Term.var "ok", Term.con "labeledArg" [Term.var "term", Term.lit ":", Term.var "result"], Term.con "labeledArg" [Term.var "type", Term.lit ":", Term.con "_" []], Term.con "labeledArg" [Term.var "ctx", Term.lit ":", Term.con "_" []], Term.lit ")", Term.lit "=>", Term.con "app" [Term.var "ok", Term.var "result"]], Term.con "arm" [Term.lit "(", Term.var "error", Term.var "msg", Term.lit ")", Term.lit "=>", Term.con "app" [Term.var "error", Term.var "msg"]], Term.lit ")"]
      | _ => t

    def elaborateInfer (t : Term) : Term :=
      match t with
      | .con "elaborateInfer" [env, s] => Term.con "caseExpr" [Term.lit "(", Term.lit "case", Term.con "infer" [Term.con "app" [Term.var "elabCtxWithGlobals", env], s], Term.con "arm" [Term.lit "(", Term.var "ok", Term.con "labeledArg" [Term.var "term", Term.lit ":", Term.var "t"], Term.con "labeledArg" [Term.var "type", Term.lit ":", Term.var "ty"], Term.con "labeledArg" [Term.var "ctx", Term.lit ":", Term.con "_" []], Term.lit ")", Term.lit "=>", Term.con "app" [Term.var "ok", Term.con "tuple" [Term.lit "(", Term.var "t", Term.lit ",", Term.var "ty", Term.lit ")"]]], Term.con "arm" [Term.lit "(", Term.var "error", Term.var "msg", Term.lit ")", Term.lit "=>", Term.con "app" [Term.var "error", Term.var "msg"]], Term.lit ")"]
      | _ => t

  end TopLevel

  section CheckType

    def checkType (t : Term) : Term :=
      match t with
      | .con "checkType" [ctx, s] => Term.con "caseExpr" [Term.lit "(", Term.lit "case", Term.con "infer" [ctx, s], Term.con "arm" [Term.lit "(", Term.var "ok", Term.con "labeledArg" [Term.var "term", Term.lit ":", Term.var "tyCore"], Term.con "labeledArg" [Term.var "type", Term.lit ":", Term.con "app" [Term.var "univ", Term.var "level"]], Term.con "labeledArg" [Term.var "ctx", Term.lit ":", Term.var "ctx'"], Term.lit ")", Term.lit "=>", Term.con "app" [Term.var "ok", Term.con "record" [Term.lit "(", Term.var "type", Term.lit ":", Term.var "tyCore", Term.con "labeledArg" [Term.var "level", Term.lit ":", Term.var "level"], Term.con "labeledArg" [Term.var "ctx", Term.lit ":", Term.var "ctx'"], Term.lit ")"]]], Term.con "arm" [Term.lit "(", Term.var "ok", Term.con "labeledArg" [Term.var "term", Term.lit ":", Term.con "_" []], Term.con "labeledArg" [Term.var "type", Term.lit ":", Term.var "ty"], Term.con "labeledArg" [Term.var "ctx", Term.lit ":", Term.con "_" []], Term.lit ")", Term.lit "=>", Term.con "app" [Term.var "error", Term.con "concat" [Term.con "terminal" [Term.lit "Expected a type, got "], Term.var "ty"]]], Term.con "varArm" [Term.lit "$", Term.var "err", Term.lit "=>", Term.var "err"], Term.lit ")"]
      | _ => t

    def checkTypeAtLevel (t : Term) : Term :=
      match t with
      | .con "checkTypeAtLevel" [ctx, s, expected] => Term.con "caseExpr" [Term.lit "(", Term.lit "case", Term.con "checkType" [ctx, s], Term.con "arm" [Term.lit "(", Term.var "ok", Term.con "type" [Term.lit ":", Term.var "tyCore", Term.con "labeledArg" [Term.var "level", Term.lit ":", Term.var "level"], Term.con "labeledArg" [Term.var "ctx", Term.lit ":", Term.var "ctx'"]], Term.lit ")", Term.lit "=>", Term.con "caseExpr" [Term.lit "(", Term.lit "case", Term.con "levelLeq" [Term.var "level", expected], Term.con "arm" [Term.var "true", Term.lit "=>", Term.con "ok" [Term.con "labeledArg" [Term.var "term", Term.lit ":", Term.var "tyCore"], Term.con "labeledArg" [Term.var "ctx", Term.lit ":", Term.var "ctx'"]]], Term.con "arm" [Term.var "false", Term.lit "=>", Term.con "app" [Term.var "error", Term.con "concat" [Term.con "terminal" [Term.lit "Universe level mismatch: expected ≤ "], expected, Term.con "terminal" [Term.lit ", got "], Term.var "level"]]], Term.lit ")"]], Term.con "varArm" [Term.lit "$", Term.var "err", Term.lit "=>", Term.var "err"], Term.lit ")"]
      | _ => t

  end CheckType

  section Telescope

    def checkTelescope (t : Term) : Term :=
      match t with
      | .con "checkTelescope" [ctx, .con "unit" [.lit "(", .lit ")"]] => Term.con "app" [Term.var "ok", Term.con "record" [Term.lit "(", Term.var "tele", Term.lit ":", Term.con "unit" [Term.lit "(", Term.lit ")"], Term.con "labeledArg" [Term.var "ctx", Term.lit ":", ctx], Term.lit ")"]]
      | _ => t

    def checkTelescopeCons (t : Term) : Term :=
      match t with
      | .con "checkTelescope" [ctx, .con "app" [.lit "(", .lit "(", .var "teleEntry", .con "labeledArg" [.var "name", .lit ":", name], .con "labeledArg" [.var "surface", .lit ":", s], .lit ")", rest, .lit ")"]] => Term.con "caseExpr" [Term.lit "(", Term.lit "case", Term.con "checkType" [ctx, s], Term.con "arm" [Term.lit "(", Term.var "ok", Term.con "type" [Term.lit ":", Term.var "tyCore", Term.con "labeledArg" [Term.var "level", Term.lit ":", Term.con "_" []], Term.con "labeledArg" [Term.var "ctx", Term.lit ":", Term.var "ctx'"]], Term.lit ")", Term.lit "=>", Term.con "caseExpr" [Term.lit "(", Term.lit "case", Term.con "checkTelescope" [Term.con "elabCtxExtend" [Term.var "ctx'", name, Term.var "tyCore"], rest], Term.con "arm" [Term.lit "(", Term.var "ok", Term.con "tele" [Term.lit ":", Term.var "restTele", Term.con "labeledArg" [Term.var "ctx", Term.lit ":", Term.var "ctx''"]], Term.lit ")", Term.lit "=>", Term.con "app" [Term.var "ok", Term.con "record" [Term.lit "(", Term.var "tele", Term.lit ":", Term.con "tuple" [Term.con "tuple" [Term.lit "(", name, Term.lit ",", Term.var "tyCore", Term.lit ")"], Term.var "restTele"], Term.con "labeledArg" [Term.var "ctx", Term.lit ":", Term.var "ctx''"], Term.lit ")"]]], Term.con "varArm" [Term.lit "$", Term.var "err", Term.lit "=>", Term.var "err"], Term.lit ")"]], Term.con "varArm" [Term.lit "$", Term.var "err", Term.lit "=>", Term.var "err"], Term.lit ")"]
      | _ => t

    def teleToPi (t : Term) : Term :=
      match t with
      | .con "teleToPi" [.con "unit" [.lit "(", .lit ")"], cod] => cod
      | _ => t

    def teleToPiCons (t : Term) : Term :=
      match t with
      | .con "teleToPi" [.con "app" [.lit "(", .lit "(", x, .lit ",", dom, .lit ")", rest, .lit ")"], cod] => Term.con "pi" [dom, Term.con "teleToPi" [rest, cod]]
      | _ => t

  end Telescope

  section SurfaceExt



  end SurfaceExt

  section Helpers

    def mkPiNil (t : Term) : Term :=
      match t with
      | .con "mkPi" [.con "unit" [.lit "(", .lit ")"], cod] => cod
      | _ => t

    def mkPiCons (t : Term) : Term :=
      match t with
      | .con "mkPi" [.con "app" [.lit "(", .lit "(", x, .lit ",", ty, .lit ")", rest, .lit ")"], cod] => Term.con "Π" [Term.con "typed" [Term.lit "(", x, Term.lit ":", ty, Term.lit ")"], Term.con "mkPi" [rest, cod]]
      | _ => t

    def mkLamNil (t : Term) : Term :=
      match t with
      | .con "mkLam" [.con "unit" [.lit "(", .lit ")"], body] => body
      | _ => t

    def mkLamCons (t : Term) : Term :=
      match t with
      | .con "mkLam" [.con "tuple" [x, rest], body] => Term.con "app" [Term.var "λ", Term.con "binder" [Term.lit "$", Term.var "x", Term.lit ".", Term.con "mkLam" [rest, body]]]
      | _ => t

    def mkAppsNil (t : Term) : Term :=
      match t with
      | .con "mkApps" [f, .con "unit" [.lit "(", .lit ")"]] => f
      | _ => t

    def mkAppsCons (t : Term) : Term :=
      match t with
      | .con "mkApps" [f, .con "tuple" [a, rest]] => Term.con "mkApps" [Term.con "app" [f, a], rest]
      | _ => t

  end Helpers

  section Examples

    def idSurface (t : Term) : Term :=
      match t with
      | .con "idSurface" [] => Term.con "lamParen" [Term.lit "(", Term.lit "λ", Term.var "x", Term.lit ".", Term.con "app" [Term.var "var", Term.con "x" []], Term.lit ")"]
      | _ => t

    def idTypeSurface (t : Term) : Term :=
      match t with
      | .con "idTypeSurface" [] => Term.con "Π" [Term.con "typed" [Term.lit "(", Term.con "A" [], Term.lit ":", Term.con "app" [Term.var "Type", Term.con "num" [Term.con "number" [Term.lit "0"]]], Term.lit ")"], Term.con "Π" [Term.con "typed" [Term.lit "(", Term.con "x" [], Term.lit ":", Term.con "app" [Term.var "var", Term.con "A" []], Term.lit ")"], Term.con "app" [Term.var "var", Term.con "A" []]]]
      | _ => t

    def constSurface (t : Term) : Term :=
      match t with
      | .con "constSurface" [] => Term.con "lamParen" [Term.lit "(", Term.lit "λ", Term.var "x", Term.lit ".", Term.con "lamParen" [Term.lit "(", Term.lit "λ", Term.var "y", Term.lit ".", Term.con "app" [Term.var "var", Term.con "x" []], Term.lit ")"], Term.lit ")"]
      | _ => t

    def flipSurface (t : Term) : Term :=
      match t with
      | .con "flipSurface" [] => Term.con "lamParen" [Term.lit "(", Term.lit "λ", Term.var "f", Term.lit ".", Term.con "lamParen" [Term.lit "(", Term.lit "λ", Term.var "x", Term.lit ".", Term.con "lamParen" [Term.lit "(", Term.lit "λ", Term.var "y", Term.lit ".", Term.con "app" [Term.con "app" [Term.con "app" [Term.var "var", Term.con "f" []], Term.con "app" [Term.var "var", Term.con "y" []]], Term.con "app" [Term.var "var", Term.con "x" []]], Term.lit ")"], Term.lit ")"], Term.lit ")"]
      | _ => t

    def zeroSurface (t : Term) : Term :=
      match t with
      | .con "zeroSurface" [] => Term.con "introExpr" [Term.lit "(", Term.var "intro", Term.var "Nat", Term.lit ".", Term.var "zero", Term.con "unit" [Term.lit "(", Term.lit ")"], Term.lit ")"]
      | _ => t

    def sucSurface (t : Term) : Term :=
      match t with
      | .con "app" [.var "sucSurface", n] => Term.con "introExpr" [Term.lit "(", Term.var "intro", Term.var "Nat", Term.lit ".", Term.var "suc", n, Term.lit ")"]
      | _ => t

    def twoSurface (t : Term) : Term :=
      match t with
      | .con "twoSurface" [] => Term.con "app" [Term.var "sucSurface", Term.con "app" [Term.var "sucSurface", Term.con "zeroSurface" []]]
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

  end Examples

end Elaborate