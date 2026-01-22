/-
  AUTO-GENERATED from .lego files
  Do not edit directly.
-/

import Lego.Algebra

open Lego

namespace Tactic

  section TacResult

    def isTacOk (t : Term) : Term :=
      match t with
      | .con "app" [.var "isTacOk", .con "app" [.var "tacOk", a]] => Term.con "true" []
      | _ => t

    def isTacOkErr (t : Term) : Term :=
      match t with
      | .con "app" [.var "isTacOk", .con "app" [.var "tacError", msg]] => Term.con "false" []
      | _ => t

    def tacResultMap (t : Term) : Term :=
      match t with
      | .con "tacResultMap" [f, .con "app" [.var "tacOk", a]] => Term.con "app" [Term.var "tacOk", Term.con "tuple" [f, a]]
      | _ => t

    def tacResultMapErr (t : Term) : Term :=
      match t with
      | .con "tacResultMap" [f, .con "app" [.var "tacError", msg]] => Term.con "app" [Term.var "tacError", msg]
      | _ => t

    def tacResultBind (t : Term) : Term :=
      match t with
      | .con "tacResultBind" [.con "app" [.var "tacOk", a], f] => Term.con "tuple" [f, a]
      | _ => t

    def tacResultBindErr (t : Term) : Term :=
      match t with
      | .con "tacResultBind" [.con "app" [.var "tacError", msg], f] => Term.con "app" [Term.var "tacError", msg]
      | _ => t

    def tacResultPure (t : Term) : Term :=
      match t with
      | .con "app" [.var "tacResultPure", a] => Term.con "app" [Term.var "tacOk", a]
      | _ => t

    def tacResultGetOrElse (t : Term) : Term :=
      match t with
      | .con "tacResultGetOrElse" [.con "app" [.var "tacOk", a], default] => a
      | _ => t

    def tacResultGetOrElseErr (t : Term) : Term :=
      match t with
      | .con "tacResultGetOrElse" [.con "app" [.var "tacError", msg], default] => default
      | _ => t

  end TacResult

  section TpCtx

    def tpCtxEmpty (t : Term) : Term :=
      match t with
      | .con "tpCtxEmpty" [] => Term.con "tpCtx" [Term.con "labeledArg" [Term.var "types", Term.lit ":", Term.con "unit" [Term.lit "(", Term.lit ")"]], Term.con "labeledArg" [Term.var "cofs", Term.lit ":", Term.con "unit" [Term.lit "(", Term.lit ")"]]]
      | _ => t

    def tpCtxExtend (t : Term) : Term :=
      match t with
      | .con "tpCtxExtend" [.con "tpCtx" [.con "labeledArg" [.var "types", .lit ":", ts], .con "labeledArg" [.var "cofs", .lit ":", cs]], ty] => Term.con "tpCtx" [Term.con "labeledArg" [Term.var "types", Term.lit ":", Term.con "tuple" [ty, ts]], Term.con "labeledArg" [Term.var "cofs", Term.lit ":", cs]]
      | _ => t

    def tpCtxLookup (t : Term) : Term :=
      match t with
      | .con "tpCtxLookup" [.con "tpCtx" [.con "labeledArg" [.var "types", .lit ":", ts], .con "labeledArg" [.var "cofs", .lit ":", cs]], n] => Term.con "listGet" [ts, n]
      | _ => t

    def tpCtxSize (t : Term) : Term :=
      match t with
      | .con "app" [.var "tpCtxSize", .con "tpCtx" [.con "labeledArg" [.var "types", .lit ":", ts], .con "labeledArg" [.var "cofs", .lit ":", cs]]] => Term.con "app" [Term.var "length", ts]
      | _ => t

    def tpCtxAssume (t : Term) : Term :=
      match t with
      | .con "tpCtxAssume" [.con "tpCtx" [.con "labeledArg" [.var "types", .lit ":", ts], .con "labeledArg" [.var "cofs", .lit ":", cs]], φ] => Term.con "tpCtx" [Term.con "labeledArg" [Term.var "types", Term.lit ":", ts], Term.con "labeledArg" [Term.var "cofs", Term.lit ":", Term.con "tuple" [φ, cs]]]
      | _ => t

    def tpCtxIsConsistent (t : Term) : Term :=
      match t with
      | .con "app" [.var "tpCtxIsConsistent", .con "tpCtx" [.con "labeledArg" [.var "types", .lit ":", ts], .con "labeledArg" [.var "cofs", .lit ":", cs]]] => Term.con "app" [Term.var "cofIsConsistent", Term.con "app" [Term.var "meetAll", cs]]
      | _ => t

    def meetAll (t : Term) : Term :=
      match t with
      | .con "app" [.var "meetAll", .con "unit" [.lit "(", .lit ")"]] => Term.con "cof_top" []
      | _ => t

    def meetAllCons (t : Term) : Term :=
      match t with
      | .con "app" [.var "meetAll", .con "tuple" [φ, rest]] => Term.con "cof_and" [φ, Term.con "app" [Term.var "meetAll", rest]]
      | _ => t

  end TpCtx

  section ChkGoal

    def chkGoalSimple (t : Term) : Term :=
      match t with
      | .con "app" [.var "chkGoalSimple", ty] => Term.con "chkGoal" [Term.con "labeledArg" [Term.var "tp", Term.lit ":", ty], Term.con "labeledArg" [Term.var "cof", Term.lit ":", Term.con "cof_top" []], Term.con "labeledArg" [Term.var "bdry", Term.lit ":", Term.con "app" [Term.var "lit", Term.con "terminal" [Term.lit "unit"]]]]
      | _ => t

    def chkGoalWithBoundary (t : Term) : Term :=
      match t with
      | .con "chkGoalWithBoundary" [ty, φ, bdry] => Term.con "chkGoal" [Term.con "labeledArg" [Term.var "tp", Term.lit ":", ty], Term.con "labeledArg" [Term.var "cof", Term.lit ":", φ], Term.con "labeledArg" [Term.var "bdry", Term.lit ":", bdry]]
      | _ => t

    def chkGoalTp (t : Term) : Term :=
      match t with
      | .con "app" [.var "chkGoalTp", .con "chkGoal" [.con "labeledArg" [.var "tp", .lit ":", t], .con "labeledArg" [.var "cof", .lit ":", c], .con "labeledArg" [.var "bdry", .lit ":", b]]] => t
      | _ => t

    def chkGoalCof (t : Term) : Term :=
      match t with
      | .con "app" [.var "chkGoalCof", .con "chkGoal" [.con "labeledArg" [.var "tp", .lit ":", t], .con "labeledArg" [.var "cof", .lit ":", c], .con "labeledArg" [.var "bdry", .lit ":", b]]] => c
      | _ => t

    def chkGoalBdry (t : Term) : Term :=
      match t with
      | .con "app" [.var "chkGoalBdry", .con "chkGoal" [.con "labeledArg" [.var "tp", .lit ":", t], .con "labeledArg" [.var "cof", .lit ":", c], .con "labeledArg" [.var "bdry", .lit ":", b]]] => b
      | _ => t

  end ChkGoal

  section TpTac

    def tpTacRun (t : Term) : Term :=
      match t with
      | .con "tpTacRun" [tac, ctx] => Term.con "tuple" [tac, ctx]
      | _ => t

    def tpTacPure (t : Term) : Term :=
      match t with
      | .con "tpTacPure" [e, ctx] => Term.con "app" [Term.var "tacOk", e]
      | _ => t

    def tpTacNat (t : Term) : Term :=
      match t with
      | .con "app" [.var "tpTacNat", ctx] => Term.con "app" [Term.var "tacOk", Term.con "nat" []]
      | _ => t

    def tpTacCircle (t : Term) : Term :=
      match t with
      | .con "app" [.var "tpTacCircle", ctx] => Term.con "app" [Term.var "tacOk", Term.con "S1" []]
      | _ => t

    def tpTacUniv (t : Term) : Term :=
      match t with
      | .con "app" [.var "tpTacUniv", ctx] => Term.con "app" [Term.var "tacOk", Term.con "app" [Term.var "univ", Term.con "num" [Term.con "number" [Term.lit "0"]]]]
      | _ => t

    def tpTacDim (t : Term) : Term :=
      match t with
      | .con "app" [.var "tpTacDim", ctx] => Term.con "app" [Term.var "tacOk", Term.con "app" [Term.var "lit", Term.con "terminal" [Term.lit "𝕀"]]]
      | _ => t

    def tpTacCof (t : Term) : Term :=
      match t with
      | .con "app" [.var "tpTacCof", ctx] => Term.con "app" [Term.var "tacOk", Term.con "app" [Term.var "lit", Term.con "terminal" [Term.lit "Cof"]]]
      | _ => t

    def tpTacPi (t : Term) : Term :=
      match t with
      | .con "tpTacPi" [domTac, codTac, ctx] => Term.con "tacResultBind" [Term.con "tuple" [domTac, ctx], Term.con "app" [Term.var "lam", Term.con "letIn" [Term.lit "(", Term.lit "let", Term.lit "$", Term.var "ctx'", Term.lit "=", Term.con "tpCtxExtend" [ctx, Term.con "app" [Term.var "ix", Term.con "num" [Term.con "number" [Term.lit "0"]]]], Term.lit "in", Term.con "tacResultBind" [Term.con "tuple" [codTac, Term.con "app" [Term.var "ix", Term.con "num" [Term.con "number" [Term.lit "0"]]], Term.var "ctx'"], Term.con "app" [Term.var "lam", Term.con "app" [Term.var "tacOk", Term.con "pi" [Term.con "app" [Term.var "ix", Term.con "num" [Term.con "number" [Term.lit "1"]]], Term.con "app" [Term.var "ix", Term.con "num" [Term.con "number" [Term.lit "0"]]]]]]], Term.lit ")"]]]
      | _ => t

    def tpTacSigma (t : Term) : Term :=
      match t with
      | .con "tpTacSigma" [baseTac, famTac, ctx] => Term.con "tacResultBind" [Term.con "tuple" [baseTac, ctx], Term.con "app" [Term.var "lam", Term.con "letIn" [Term.lit "(", Term.lit "let", Term.lit "$", Term.var "ctx'", Term.lit "=", Term.con "tpCtxExtend" [ctx, Term.con "app" [Term.var "ix", Term.con "num" [Term.con "number" [Term.lit "0"]]]], Term.lit "in", Term.con "tacResultBind" [Term.con "tuple" [famTac, Term.con "app" [Term.var "ix", Term.con "num" [Term.con "number" [Term.lit "0"]]], Term.var "ctx'"], Term.con "app" [Term.var "lam", Term.con "app" [Term.var "tacOk", Term.con "sigma" [Term.con "app" [Term.var "ix", Term.con "num" [Term.con "number" [Term.lit "1"]]], Term.con "app" [Term.var "ix", Term.con "num" [Term.con "number" [Term.lit "0"]]]]]]], Term.lit ")"]]]
      | _ => t

    def tpTacPath (t : Term) : Term :=
      match t with
      | .con "tpTacPath" [tyLineTac, left, right, ctx] => Term.con "tacResultBind" [Term.con "tuple" [tyLineTac, ctx], Term.con "app" [Term.var "lam", Term.con "app" [Term.var "tacOk", Term.con "path" [Term.con "app" [Term.var "ix", Term.con "num" [Term.con "number" [Term.lit "0"]]], left, right]]]]
      | _ => t

    def tpTacSub (t : Term) : Term :=
      match t with
      | .con "tpTacSub" [tyTac, φ, tm, ctx] => Term.con "tacResultBind" [Term.con "tuple" [tyTac, ctx], Term.con "app" [Term.var "lam", Term.con "app" [Term.var "tacOk", Term.con "sub" [Term.con "app" [Term.var "ix", Term.con "num" [Term.con "number" [Term.lit "0"]]], φ, tm]]]]
      | _ => t

    def tpTacMap (t : Term) : Term :=
      match t with
      | .con "tpTacMap" [f, tac, ctx] => Term.con "tacResultMap" [f, Term.con "tuple" [tac, ctx]]
      | _ => t

  end TpTac

  section ChkTac

    def chkTacRun (t : Term) : Term :=
      match t with
      | .con "chkTacRun" [tac, ctx, tp] => Term.con "tuple" [tac, ctx, Term.con "app" [Term.var "chkGoalSimple", tp]]
      | _ => t

    def chkTacBRun (t : Term) : Term :=
      match t with
      | .con "chkTacBRun" [tac, ctx, tp, φ, bdry] => Term.con "tuple" [tac, ctx, Term.con "chkGoalWithBoundary" [tp, φ, bdry]]
      | _ => t

    def chkTacPure (t : Term) : Term :=
      match t with
      | .con "chkTacPure" [e, ctx, goal] => Term.con "app" [Term.var "tacOk", e]
      | _ => t

    def chkTacZero (t : Term) : Term :=
      match t with
      | .con "chkTacZero" [ctx, goal] => Term.con "caseExpr" [Term.lit "(", Term.lit "case", Term.con "app" [Term.var "chkGoalTp", goal], Term.con "arm" [Term.var "nat", Term.lit "=>", Term.con "app" [Term.var "tacOk", Term.con "zero" []]], Term.con "arm" [Term.var "_", Term.lit "=>", Term.con "app" [Term.var "tacError", Term.con "terminal" [Term.lit "expected Nat"]]], Term.lit ")"]
      | _ => t

    def chkTacSuc (t : Term) : Term :=
      match t with
      | .con "chkTacSuc" [tac, ctx, goal] => Term.con "caseExpr" [Term.lit "(", Term.lit "case", Term.con "app" [Term.var "chkGoalTp", goal], Term.con "arm" [Term.var "nat", Term.lit "=>", Term.con "tacResultBind" [Term.con "tuple" [tac, ctx, Term.con "app" [Term.var "chkGoalSimple", Term.con "nat" []]], Term.con "app" [Term.var "lam", Term.con "app" [Term.var "tacOk", Term.con "app" [Term.var "suc", Term.con "app" [Term.var "ix", Term.con "num" [Term.con "number" [Term.lit "0"]]]]]]]], Term.con "arm" [Term.var "_", Term.lit "=>", Term.con "app" [Term.var "tacError", Term.con "terminal" [Term.lit "expected Nat"]]], Term.lit ")"]
      | _ => t

    def chkTacLam (t : Term) : Term :=
      match t with
      | .con "chkTacLam" [bodyTac, ctx, goal] => Term.con "caseExpr" [Term.lit "(", Term.lit "case", Term.con "app" [Term.var "chkGoalTp", goal], Term.con "arm" [Term.lit "(", Term.var "pi", Term.var "dom", Term.var "cod", Term.lit ")", Term.lit "=>", Term.con "letIn" [Term.lit "(", Term.lit "let", Term.lit "$", Term.var "ctx'", Term.lit "=", Term.con "tpCtxExtend" [ctx, Term.var "dom"], Term.lit "in", Term.con "letIn" [Term.lit "(", Term.lit "let", Term.lit "$", Term.var "goalCod", Term.lit "=", Term.con "app" [Term.var "chkGoalSimple", Term.var "cod"], Term.lit "in", Term.con "tacResultBind" [Term.con "tuple" [bodyTac, Term.con "app" [Term.var "ix", Term.con "num" [Term.con "number" [Term.lit "0"]]], Term.var "ctx'", Term.var "goalCod"], Term.con "app" [Term.var "lam", Term.con "app" [Term.var "tacOk", Term.con "app" [Term.var "lam", Term.con "app" [Term.var "ix", Term.con "num" [Term.con "number" [Term.lit "0"]]]]]]], Term.lit ")"], Term.lit ")"]], Term.con "arm" [Term.var "_", Term.lit "=>", Term.con "app" [Term.var "tacError", Term.con "terminal" [Term.lit "expected Pi type"]]], Term.lit ")"]
      | _ => t

    def chkTacPair (t : Term) : Term :=
      match t with
      | .con "chkTacPair" [fstTac, sndTac, ctx, goal] => Term.con "caseExpr" [Term.lit "(", Term.lit "case", Term.con "app" [Term.var "chkGoalTp", goal], Term.con "arm" [Term.lit "(", Term.var "sigma", Term.var "base", Term.var "fam", Term.lit ")", Term.lit "=>", Term.con "tacResultBind" [Term.con "tuple" [fstTac, ctx, Term.con "app" [Term.var "chkGoalSimple", Term.var "base"]], Term.con "app" [Term.var "lam", Term.con "letIn" [Term.lit "(", Term.lit "let", Term.lit "$", Term.var "famSubst", Term.lit "=", Term.con "subst" [Term.con "num" [Term.con "number" [Term.lit "0"]], Term.con "app" [Term.var "ix", Term.con "num" [Term.con "number" [Term.lit "0"]]], Term.var "fam"], Term.lit "in", Term.con "tacResultBind" [Term.con "tuple" [sndTac, ctx, Term.con "app" [Term.var "chkGoalSimple", Term.var "famSubst"]], Term.con "app" [Term.var "lam", Term.con "app" [Term.var "tacOk", Term.con "pair" [Term.con "app" [Term.var "ix", Term.con "num" [Term.con "number" [Term.lit "1"]]], Term.con "app" [Term.var "ix", Term.con "num" [Term.con "number" [Term.lit "0"]]]]]]], Term.lit ")"]]]], Term.con "arm" [Term.var "_", Term.lit "=>", Term.con "app" [Term.var "tacError", Term.con "terminal" [Term.lit "expected Sigma type"]]], Term.lit ")"]
      | _ => t

    def chkTacPlam (t : Term) : Term :=
      match t with
      | .con "chkTacPlam" [bodyTac, ctx, goal] => Term.con "letIn" [Term.lit "(", Term.lit "let", Term.lit "$", Term.var "ctx'", Term.lit "=", Term.con "tpCtxExtend" [ctx, Term.con "app" [Term.var "lit", Term.con "terminal" [Term.lit "𝕀"]]], Term.lit "in", Term.con "tacResultBind" [Term.con "tuple" [bodyTac, Term.con "app" [Term.var "ix", Term.con "num" [Term.con "number" [Term.lit "0"]]], Term.var "ctx'", Term.con "app" [Term.var "chkGoalSimple", Term.con "app" [Term.var "chkGoalTp", goal]]], Term.con "app" [Term.var "lam", Term.con "app" [Term.var "tacOk", Term.con "app" [Term.var "plam", Term.con "app" [Term.var "ix", Term.con "num" [Term.con "number" [Term.lit "0"]]]]]]], Term.lit ")"]
      | _ => t

    def chkTacBase (t : Term) : Term :=
      match t with
      | .con "chkTacBase" [ctx, goal] => Term.con "caseExpr" [Term.lit "(", Term.lit "case", Term.con "app" [Term.var "chkGoalTp", goal], Term.con "arm" [Term.var "S1", Term.lit "=>", Term.con "app" [Term.var "tacOk", Term.con "base" []]], Term.con "arm" [Term.var "_", Term.lit "=>", Term.con "app" [Term.var "tacError", Term.con "terminal" [Term.lit "expected Circle"]]], Term.lit ")"]
      | _ => t

    def chkTacLoop (t : Term) : Term :=
      match t with
      | .con "chkTacLoop" [dimTac, ctx, goal] => Term.con "caseExpr" [Term.lit "(", Term.lit "case", Term.con "app" [Term.var "chkGoalTp", goal], Term.con "arm" [Term.var "S1", Term.lit "=>", Term.con "tacResultBind" [Term.con "tuple" [dimTac, ctx, Term.con "app" [Term.var "chkGoalSimple", Term.con "app" [Term.var "lit", Term.con "terminal" [Term.lit "𝕀"]]]], Term.con "app" [Term.var "lam", Term.con "app" [Term.var "tacOk", Term.con "app" [Term.var "loop", Term.con "app" [Term.var "ix", Term.con "num" [Term.con "number" [Term.lit "0"]]]]]]]], Term.con "arm" [Term.var "_", Term.lit "=>", Term.con "app" [Term.var "tacError", Term.con "terminal" [Term.lit "expected Circle"]]], Term.lit ")"]
      | _ => t

    def chkTacSubIn (t : Term) : Term :=
      match t with
      | .con "chkTacSubIn" [tac, ctx, goal] => Term.con "caseExpr" [Term.lit "(", Term.lit "case", Term.con "app" [Term.var "chkGoalTp", goal], Term.con "arm" [Term.lit "(", Term.var "sub", Term.var "a", Term.var "φ", Term.var "t", Term.lit ")", Term.lit "=>", Term.con "tacResultBind" [Term.con "tuple" [tac, ctx, Term.con "app" [Term.var "chkGoalSimple", Term.var "a"]], Term.con "app" [Term.var "lam", Term.con "app" [Term.var "tacOk", Term.con "app" [Term.var "subIn", Term.con "app" [Term.var "ix", Term.con "num" [Term.con "number" [Term.lit "0"]]]]]]]], Term.con "arm" [Term.var "_", Term.lit "=>", Term.con "app" [Term.var "tacError", Term.con "terminal" [Term.lit "expected Sub type"]]], Term.lit ")"]
      | _ => t

  end ChkTac

  section SynTac

    def synTacRun (t : Term) : Term :=
      match t with
      | .con "synTacRun" [tac, ctx] => Term.con "tuple" [tac, ctx]
      | _ => t

    def synTacPure (t : Term) : Term :=
      match t with
      | .con "synTacPure" [e, ty, ctx] => Term.con "app" [Term.var "tacOk", Term.con "tuple" [Term.lit "(", e, Term.lit ",", ty, Term.lit ")"]]
      | _ => t

    def synTacVar (t : Term) : Term :=
      match t with
      | .con "synTacVar" [n, ctx] => Term.con "caseExpr" [Term.lit "(", Term.lit "case", Term.con "tpCtxLookup" [ctx, n], Term.con "arm" [Term.lit "(", Term.var "some", Term.var "ty", Term.lit ")", Term.lit "=>", Term.con "app" [Term.var "tacOk", Term.con "tuple" [Term.lit "(", Term.con "app" [Term.var "ix", n], Term.lit ",", Term.var "ty", Term.lit ")"]]], Term.con "arm" [Term.var "none", Term.lit "=>", Term.con "app" [Term.var "tacError", Term.con "terminal" [Term.lit "unbound variable"]]], Term.lit ")"]
      | _ => t

    def synTacApp (t : Term) : Term :=
      match t with
      | .con "synTacApp" [fnTac, argTac, ctx] => Term.con "tacResultBind" [Term.con "tuple" [fnTac, ctx], Term.con "app" [Term.var "lam", Term.con "caseExpr" [Term.lit "(", Term.lit "case", Term.con "app" [Term.var "snd", Term.con "app" [Term.var "ix", Term.con "num" [Term.con "number" [Term.lit "0"]]]], Term.con "arm" [Term.lit "(", Term.var "pi", Term.var "dom", Term.var "cod", Term.lit ")", Term.lit "=>", Term.con "tacResultBind" [Term.con "tuple" [argTac, ctx, Term.con "app" [Term.var "chkGoalSimple", Term.var "dom"]], Term.con "app" [Term.var "lam", Term.con "letIn" [Term.lit "(", Term.lit "let", Term.lit "$", Term.var "codSubst", Term.lit "=", Term.con "subst" [Term.con "num" [Term.con "number" [Term.lit "0"]], Term.con "app" [Term.var "ix", Term.con "num" [Term.con "number" [Term.lit "0"]]], Term.var "cod"], Term.lit "in", Term.con "app" [Term.var "tacOk", Term.con "tuple" [Term.lit "(", Term.con "app" [Term.con "app" [Term.var "fst", Term.con "app" [Term.var "ix", Term.con "num" [Term.con "number" [Term.lit "1"]]]], Term.con "app" [Term.var "ix", Term.con "num" [Term.con "number" [Term.lit "0"]]]], Term.lit ",", Term.var "codSubst", Term.lit ")"]], Term.lit ")"]]]], Term.con "arm" [Term.var "_", Term.lit "=>", Term.con "app" [Term.var "tacError", Term.con "terminal" [Term.lit "expected function type"]]], Term.lit ")"]]]
      | _ => t

    def synTacFst (t : Term) : Term :=
      match t with
      | .con "synTacFst" [pairTac, ctx] => Term.con "tacResultBind" [Term.con "tuple" [pairTac, ctx], Term.con "app" [Term.var "lam", Term.con "caseExpr" [Term.lit "(", Term.lit "case", Term.con "app" [Term.var "snd", Term.con "app" [Term.var "ix", Term.con "num" [Term.con "number" [Term.lit "0"]]]], Term.con "arm" [Term.lit "(", Term.var "sigma", Term.var "base", Term.var "fam", Term.lit ")", Term.lit "=>", Term.con "app" [Term.var "tacOk", Term.con "tuple" [Term.lit "(", Term.con "app" [Term.var "fst", Term.con "app" [Term.var "fst", Term.con "app" [Term.var "ix", Term.con "num" [Term.con "number" [Term.lit "0"]]]]], Term.lit ",", Term.var "base", Term.lit ")"]]], Term.con "arm" [Term.var "_", Term.lit "=>", Term.con "app" [Term.var "tacError", Term.con "terminal" [Term.lit "expected Sigma type"]]], Term.lit ")"]]]
      | _ => t

    def synTacSnd (t : Term) : Term :=
      match t with
      | .con "synTacSnd" [pairTac, ctx] => Term.con "tacResultBind" [Term.con "tuple" [pairTac, ctx], Term.con "app" [Term.var "lam", Term.con "caseExpr" [Term.lit "(", Term.lit "case", Term.con "app" [Term.var "snd", Term.con "app" [Term.var "ix", Term.con "num" [Term.con "number" [Term.lit "0"]]]], Term.con "arm" [Term.lit "(", Term.var "sigma", Term.var "base", Term.var "fam", Term.lit ")", Term.lit "=>", Term.con "letIn" [Term.lit "(", Term.lit "let", Term.lit "$", Term.var "fstVal", Term.lit "=", Term.con "app" [Term.var "fst", Term.con "app" [Term.var "fst", Term.con "app" [Term.var "ix", Term.con "num" [Term.con "number" [Term.lit "0"]]]]], Term.lit "in", Term.con "letIn" [Term.lit "(", Term.lit "let", Term.lit "$", Term.var "famSubst", Term.lit "=", Term.con "subst" [Term.con "num" [Term.con "number" [Term.lit "0"]], Term.var "fstVal", Term.var "fam"], Term.lit "in", Term.con "app" [Term.var "tacOk", Term.con "tuple" [Term.lit "(", Term.con "app" [Term.var "snd", Term.con "app" [Term.var "fst", Term.con "app" [Term.var "ix", Term.con "num" [Term.con "number" [Term.lit "0"]]]]], Term.lit ",", Term.var "famSubst", Term.lit ")"]], Term.lit ")"], Term.lit ")"]], Term.con "arm" [Term.var "_", Term.lit "=>", Term.con "app" [Term.var "tacError", Term.con "terminal" [Term.lit "expected Sigma type"]]], Term.lit ")"]]]
      | _ => t

    def synTacPApp (t : Term) : Term :=
      match t with
      | .con "synTacPApp" [pathTac, dimTac, ctx] => Term.con "tacResultBind" [Term.con "tuple" [pathTac, ctx], Term.con "app" [Term.var "lam", Term.con "tacResultBind" [Term.con "tuple" [dimTac, ctx, Term.con "app" [Term.var "chkGoalSimple", Term.con "app" [Term.var "lit", Term.con "terminal" [Term.lit "𝕀"]]]], Term.con "app" [Term.var "lam", Term.con "app" [Term.var "tacOk", Term.con "tuple" [Term.lit "(", Term.con "papp" [Term.con "app" [Term.var "fst", Term.con "app" [Term.var "ix", Term.con "num" [Term.con "number" [Term.lit "1"]]]], Term.con "app" [Term.var "ix", Term.con "num" [Term.con "number" [Term.lit "0"]]]], Term.lit ",", Term.con "app" [Term.var "lit", Term.con "terminal" [Term.lit "path-fiber"]], Term.lit ")"]]]]]]
      | _ => t

    def synTacSubOut (t : Term) : Term :=
      match t with
      | .con "synTacSubOut" [subTac, ctx] => Term.con "tacResultBind" [Term.con "tuple" [subTac, ctx], Term.con "app" [Term.var "lam", Term.con "caseExpr" [Term.lit "(", Term.lit "case", Term.con "app" [Term.var "snd", Term.con "app" [Term.var "ix", Term.con "num" [Term.con "number" [Term.lit "0"]]]], Term.con "arm" [Term.lit "(", Term.var "sub", Term.var "a", Term.var "φ", Term.var "t", Term.lit ")", Term.lit "=>", Term.con "app" [Term.var "tacOk", Term.con "tuple" [Term.lit "(", Term.con "app" [Term.var "subOut", Term.con "app" [Term.var "fst", Term.con "app" [Term.var "ix", Term.con "num" [Term.con "number" [Term.lit "0"]]]]], Term.lit ",", Term.var "a", Term.lit ")"]]], Term.con "arm" [Term.var "_", Term.lit "=>", Term.con "app" [Term.var "tacError", Term.con "terminal" [Term.lit "expected Sub type"]]], Term.lit ")"]]]
      | _ => t

  end SynTac

  section VarTac

    def varTacIntro (t : Term) : Term :=
      match t with
      | .con "varTacIntro" [name, ty, k, ctx] => Term.con "letIn" [Term.lit "(", Term.lit "let", Term.lit "$", Term.var "ctx'", Term.lit "=", Term.con "tpCtxExtend" [ctx, ty], Term.lit "in", Term.con "tuple" [k, Term.con "app" [Term.var "ix", Term.con "num" [Term.con "number" [Term.lit "0"]]], Term.var "ctx'"], Term.lit ")"]
      | _ => t

    def varTacDim (t : Term) : Term :=
      match t with
      | .con "varTacDim" [name, k, ctx] => Term.con "letIn" [Term.lit "(", Term.lit "let", Term.lit "$", Term.var "ctx'", Term.lit "=", Term.con "tpCtxExtend" [ctx, Term.con "app" [Term.var "lit", Term.con "terminal" [Term.lit "𝕀"]]], Term.lit "in", Term.con "tuple" [k, Term.con "app" [Term.var "ix", Term.con "num" [Term.con "number" [Term.lit "0"]]], Term.var "ctx'"], Term.lit ")"]
      | _ => t

    def varTacCof (t : Term) : Term :=
      match t with
      | .con "varTacCof" [φ, k, ctx] => Term.con "letIn" [Term.lit "(", Term.lit "let", Term.lit "$", Term.var "ctx'", Term.lit "=", Term.con "tpCtxAssume" [ctx, φ], Term.lit "in", Term.con "tuple" [k, Term.var "ctx'"], Term.lit ")"]
      | _ => t

  end VarTac

  section TacHelpers

    def tacSequence (t : Term) : Term :=
      match t with
      | .con "tacSequence" [.con "unit" [.lit "(", .lit ")"], ctx, goal] => Term.con "app" [Term.var "tacOk", Term.con "unit" [Term.lit "(", Term.lit ")"]]
      | _ => t

    def tacSequenceCons (t : Term) : Term :=
      match t with
      | .con "tacSequence" [.con "tuple" [tac, rest], ctx, goal] => Term.con "tacResultBind" [Term.con "tuple" [tac, ctx, goal], Term.con "app" [Term.var "lam", Term.con "tacResultBind" [Term.con "tacSequence" [rest, ctx, goal], Term.con "app" [Term.var "lam", Term.con "app" [Term.var "tacOk", Term.con "tuple" [Term.con "app" [Term.lit "(", Term.con "ix" [], Term.con "num" [Term.con "number" [Term.lit "1"]], Term.lit ")"], Term.con "app" [Term.var "ix", Term.con "num" [Term.con "number" [Term.lit "0"]]]]]]]]]
      | _ => t

    def tacChoice (t : Term) : Term :=
      match t with
      | .con "tacChoice" [.con "unit" [.lit "(", .lit ")"], ctx, goal] => Term.con "app" [Term.var "tacError", Term.con "terminal" [Term.lit "no tactics succeeded"]]
      | _ => t

    def tacChoiceCons (t : Term) : Term :=
      match t with
      | .con "tacChoice" [.con "tuple" [tac, rest], ctx, goal] => Term.con "caseExpr" [Term.lit "(", Term.lit "case", Term.con "tuple" [tac, ctx, goal], Term.con "arm" [Term.lit "(", Term.var "tacOk", Term.var "a", Term.lit ")", Term.lit "=>", Term.con "app" [Term.var "tacOk", Term.var "a"]], Term.con "arm" [Term.lit "(", Term.var "tacError", Term.var "msg", Term.lit ")", Term.lit "=>", Term.con "tacChoice" [rest, ctx, goal]], Term.lit ")"]
      | _ => t

    def tacWithFreshVar (t : Term) : Term :=
      match t with
      | .con "tacWithFreshVar" [ty, bodyTac, ctx, goal] => Term.con "letIn" [Term.lit "(", Term.lit "let", Term.lit "$", Term.var "ctx'", Term.lit "=", Term.con "tpCtxExtend" [ctx, ty], Term.lit "in", Term.con "tuple" [bodyTac, Term.con "app" [Term.var "ix", Term.con "num" [Term.con "number" [Term.lit "0"]]], Term.var "ctx'", goal], Term.lit ")"]
      | _ => t

    def tacWithCofAssump (t : Term) : Term :=
      match t with
      | .con "tacWithCofAssump" [φ, bodyTac, ctx, goal] => Term.con "letIn" [Term.lit "(", Term.lit "let", Term.lit "$", Term.var "ctx'", Term.lit "=", Term.con "tpCtxAssume" [ctx, φ], Term.lit "in", Term.con "tuple" [bodyTac, Term.var "ctx'", goal], Term.lit ")"]
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

  end TacHelpers

end Tactic