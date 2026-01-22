/-
  AUTO-GENERATED from .lego files
  Do not edit directly.
-/

import Lego.Algebra

set_option linter.unusedVariables false

open Lego

namespace Semantics

  section EvalCtx

    def evalCtxEmpty (t : Term) : Term :=
      match t with
      | .con "evalCtxEmpty" [] => Term.con "evalCtx" [Term.con "labeledArg" [Term.var "env", Term.lit ":", Term.con "unit" [Term.lit "(", Term.lit ")"]], Term.con "labeledArg" [Term.var "fuel", Term.lit ":", Term.con "num" [Term.con "number" [Term.lit "1000"]]]]
      | _ => t

    def evalCtxExtend (t : Term) : Term :=
      match t with
      | .con "evalCtxExtend" [.con "evalCtx" [.con "labeledArg" [.var "env", .lit ":", env], .con "labeledArg" [.var "fuel", .lit ":", f]], v] => Term.con "evalCtx" [Term.con "labeledArg" [Term.var "env", Term.lit ":", Term.con "tuple" [env, v]], Term.con "labeledArg" [Term.var "fuel", Term.lit ":", f]]
      | _ => t

    def evalCtxLookup (t : Term) : Term :=
      match t with
      | .con "evalCtxLookup" [.con "evalCtx" [.con "labeledArg" [.var "env", .lit ":", env], .con "labeledArg" [.var "fuel", .lit ":", f]], ix] => Term.con "lookupAt" [env, Term.con "minus" [Term.con "app" [Term.var "length", env], Term.con "num" [Term.con "number" [Term.lit "1"]], ix]]
      | _ => t

    def evalCtxDecFuel (t : Term) : Term :=
      match t with
      | .con "app" [.var "evalCtxDecFuel", .con "evalCtx" [.con "labeledArg" [.var "env", .lit ":", env], .con "labeledArg" [.var "fuel", .lit ":", .con "app" [.var "suc", f]]]] => Term.con "evalCtx" [Term.con "labeledArg" [Term.var "env", Term.lit ":", env], Term.con "labeledArg" [Term.var "fuel", Term.lit ":", f]]
      | _ => t

    def evalCtxDecFuel0 (t : Term) : Term :=
      match t with
      | .con "app" [.var "evalCtxDecFuel", .con "evalCtx" [.con "labeledArg" [.var "env", .lit ":", env], .con "labeledArg" [.var "fuel", .lit ":", .con "num" [.con "number" [.lit "0"]]]]] => Term.con "evalCtx" [Term.con "labeledArg" [Term.var "env", Term.lit ":", env], Term.con "labeledArg" [Term.var "fuel", Term.lit ":", Term.con "num" [Term.con "number" [Term.lit "0"]]]]
      | _ => t

  end EvalCtx

  section DispatchResult



  end DispatchResult

  section StableCode

    def isStablePi (t : Term) : Term :=
      match t with
      | .con "app" [.var "isStableCode", .con "pi" [A, B]] => Term.con "true" []
      | _ => t

    def isStableSigma (t : Term) : Term :=
      match t with
      | .con "app" [.var "isStableCode", .con "sigma" [A, B]] => Term.con "true" []
      | _ => t

    def isStablePath (t : Term) : Term :=
      match t with
      | .con "app" [.var "isStableCode", .con "path" [A, l, r]] => Term.con "true" []
      | _ => t

    def isStableNat (t : Term) : Term :=
      match t with
      | .con "app" [.var "isStableCode", .con "nat" []] => Term.con "true" []
      | _ => t

    def isStableCircle (t : Term) : Term :=
      match t with
      | .con "app" [.var "isStableCode", .con "circle" []] => Term.con "true" []
      | _ => t

    def isStableUniv (t : Term) : Term :=
      match t with
      | .con "app" [.var "isStableCode", .con "app" [.var "univ", l]] => Term.con "true" []
      | _ => t

    def isStableSub (t : Term) : Term :=
      match t with
      | .con "app" [.var "isStableCode", .con "sub" [A, φ, a]] => Term.con "true" []
      | _ => t

    def isStableOther (t : Term) : Term :=
      match t with
      | .con "app" [.var "isStableCode", other] => Term.con "false" []
      | _ => t

    def isVCode (t : Term) : Term :=
      match t with
      | .con "app" [.var "isVCode", .con "vtype" [r, A, B, equiv]] => Term.con "true" []
      | _ => t

    def isVCodeOther (t : Term) : Term :=
      match t with
      | .con "app" [.var "isVCode", other] => Term.con "false" []
      | _ => t

    def isHComCode (t : Term) : Term :=
      match t with
      | .con "app" [.var "isHComCode", .con "hcom" [r, s, A, φ, u]] => Term.con "true" []
      | _ => t

    def isHComCodeOther (t : Term) : Term :=
      match t with
      | .con "app" [.var "isHComCode", other] => Term.con "false" []
      | _ => t

  end StableCode

  section DimEq

    def dimEq00 (t : Term) : Term :=
      match t with
      | .con "dimEq" [.con "dim0" [], .con "dim0" []] => Term.con "true" []
      | _ => t

    def dimEq11 (t : Term) : Term :=
      match t with
      | .con "dimEq" [.con "dim1" [], .con "dim1" []] => Term.con "true" []
      | _ => t

    def dimEqIx (t : Term) : Term :=
      match t with
      | .con "dimEq" [.con "app" [.var "ix", n], .con "app" [.var "ix", n_dup]] => Term.con "true" []
      | _ => t

    def dimEqOther (t : Term) : Term :=
      match t with
      | .con "dimEq" [r, s] => Term.con "false" []
      | _ => t

  end DimEq

  section CofTrue

    def cofTrueTop (t : Term) : Term :=
      match t with
      | .con "app" [.var "cofTrue", .con "cof_top" []] => Term.con "true" []
      | _ => t

    def cofTrueEq (t : Term) : Term :=
      match t with
      | .con "app" [.var "cofTrue", .con "cof_eq" [r, s]] => Term.con "dimEq" [r, s]
      | _ => t

    def cofTrueOrL (t : Term) : Term :=
      match t with
      | .con "app" [.var "cofTrue", .con "cof_or" [φ, ψ]] => Term.con "or" [Term.con "app" [Term.var "cofTrue", φ], Term.con "app" [Term.var "cofTrue", ψ]]
      | _ => t

    def cofTrueOther (t : Term) : Term :=
      match t with
      | .con "app" [.var "cofTrue", φ] => Term.con "false" []
      | _ => t

  end CofTrue

  section Eval

    def evalNoFuel (t : Term) : Term :=
      match t with
      | .con "eval" [.con "evalCtx" [.con "labeledArg" [.var "env", .lit ":", env], .con "labeledArg" [.var "fuel", .lit ":", .con "num" [.con "number" [.lit "0"]]]], e] => e
      | _ => t

    def evalIx (t : Term) : Term :=
      match t with
      | .con "eval" [ctx, .con "app" [.var "ix", n]] => Term.con "caseExpr" [Term.lit "(", Term.lit "case", Term.con "evalCtxLookup" [ctx, n], Term.con "arm" [Term.lit "(", Term.var "some", Term.var "v", Term.lit ")", Term.lit "=>", Term.con "eval" [Term.con "app" [Term.var "evalCtxDecFuel", ctx], Term.var "v"]], Term.con "arm" [Term.var "none", Term.lit "=>", Term.con "app" [Term.var "ix", n]], Term.lit ")"]
      | _ => t

    def evalLam (t : Term) : Term :=
      match t with
      | .con "eval" [ctx, .con "app" [.var "lam", body]] => Term.con "app" [Term.var "lam", body]
      | _ => t

    def evalApp (t : Term) : Term :=
      match t with
      | .con "eval" [ctx, .con "app" [.con "app" [.var "lam", body], arg]] => Term.con "eval" [Term.con "app" [Term.var "evalCtxDecFuel", ctx], Term.con "subst" [Term.con "num" [Term.con "number" [Term.lit "0"]], Term.con "eval" [Term.con "app" [Term.var "evalCtxDecFuel", ctx], arg], body]]
      | _ => t

    def evalAppNeutral (t : Term) : Term :=
      match t with
      | .con "eval" [ctx, .con "app" [f, arg]] => Term.con "app" [Term.con "eval" [Term.con "app" [Term.var "evalCtxDecFuel", ctx], f], Term.con "eval" [Term.con "app" [Term.var "evalCtxDecFuel", ctx], arg]]
      | _ => t

    def evalPair (t : Term) : Term :=
      match t with
      | .con "eval" [ctx, .con "pair" [a, b]] => Term.con "pair" [Term.con "eval" [Term.con "app" [Term.var "evalCtxDecFuel", ctx], a], Term.con "eval" [Term.con "app" [Term.var "evalCtxDecFuel", ctx], b]]
      | _ => t

    def evalFst (t : Term) : Term :=
      match t with
      | .con "eval" [ctx, .con "app" [.var "fst", .con "pair" [a, b]]] => Term.con "eval" [Term.con "app" [Term.var "evalCtxDecFuel", ctx], a]
      | _ => t

    def evalFstNeutral (t : Term) : Term :=
      match t with
      | .con "eval" [ctx, .con "app" [.var "fst", p]] => Term.con "app" [Term.var "fst", Term.con "eval" [Term.con "app" [Term.var "evalCtxDecFuel", ctx], p]]
      | _ => t

    def evalSnd (t : Term) : Term :=
      match t with
      | .con "eval" [ctx, .con "app" [.var "snd", .con "pair" [a, b]]] => Term.con "eval" [Term.con "app" [Term.var "evalCtxDecFuel", ctx], b]
      | _ => t

    def evalSndNeutral (t : Term) : Term :=
      match t with
      | .con "eval" [ctx, .con "app" [.var "snd", p]] => Term.con "app" [Term.var "snd", Term.con "eval" [Term.con "app" [Term.var "evalCtxDecFuel", ctx], p]]
      | _ => t

    def evalPlam (t : Term) : Term :=
      match t with
      | .con "eval" [ctx, .con "app" [.var "plam", body]] => Term.con "app" [Term.var "plam", body]
      | _ => t

    def evalPapp (t : Term) : Term :=
      match t with
      | .con "eval" [ctx, .con "papp" [.con "app" [.var "plam", body], r]] => Term.con "eval" [Term.con "app" [Term.var "evalCtxDecFuel", ctx], Term.con "dimSubst" [Term.con "num" [Term.con "number" [Term.lit "0"]], r, body]]
      | _ => t

    def evalPappNeutral (t : Term) : Term :=
      match t with
      | .con "eval" [ctx, .con "papp" [p, r]] => Term.con "papp" [Term.con "eval" [Term.con "app" [Term.var "evalCtxDecFuel", ctx], p], r]
      | _ => t

    def evalCoe (t : Term) : Term :=
      match t with
      | .con "eval" [ctx, .con "coe" [line, r, s, t]] => Term.con "caseExpr" [Term.lit "(", Term.lit "case", Term.con "dimEq" [r, s], Term.con "arm" [Term.var "true", Term.lit "=>", Term.con "eval" [Term.con "app" [Term.var "evalCtxDecFuel", ctx], t]], Term.con "arm" [Term.var "false", Term.lit "=>", Term.con "doRigidCoe" [Term.con "app" [Term.var "evalCtxDecFuel", ctx], Term.con "eval" [Term.con "app" [Term.var "evalCtxDecFuel", ctx], line], r, s, Term.con "eval" [Term.con "app" [Term.var "evalCtxDecFuel", ctx], t]]], Term.lit ")"]
      | _ => t

    def evalHCom (t : Term) : Term :=
      match t with
      | .con "eval" [ctx, .con "hcom" [A, r, s, φ, u]] => Term.con "caseExpr" [Term.lit "(", Term.lit "case", Term.con "or" [Term.con "dimEq" [r, s], Term.con "app" [Term.var "cofTrue", φ]], Term.con "arm" [Term.var "true", Term.lit "=>", Term.con "eval" [Term.con "app" [Term.var "evalCtxDecFuel", ctx], Term.con "app" [Term.con "app" [u, s], Term.con "prf" []]]], Term.con "arm" [Term.var "false", Term.lit "=>", Term.con "doRigidHCom" [Term.con "app" [Term.var "evalCtxDecFuel", ctx], Term.con "eval" [Term.con "app" [Term.var "evalCtxDecFuel", ctx], A], r, s, φ, Term.con "eval" [Term.con "app" [Term.var "evalCtxDecFuel", ctx], u]]], Term.lit ")"]
      | _ => t

  end Eval

  section RigidCoe

    def doRigidCoeNat (t : Term) : Term :=
      match t with
      | .con "doRigidCoe" [ctx, .con "app" [.var "lam", .con "nat" []], r, s, con] => con
      | _ => t

    def doRigidCoeCircle (t : Term) : Term :=
      match t with
      | .con "doRigidCoe" [ctx, .con "app" [.var "lam", .con "circle" []], r, s, con] => con
      | _ => t

    def doRigidCoeUniv (t : Term) : Term :=
      match t with
      | .con "doRigidCoe" [ctx, .con "app" [.var "lam", .con "app" [.var "univ", l]], r, s, con] => con
      | _ => t

    def doRigidCoePi (t : Term) : Term :=
      match t with
      | .con "doRigidCoe" [ctx, .con "app" [.var "lam", .con "pi" [A, B]], r, s, f] => Term.con "app" [Term.var "lam", Term.con "coe" [Term.con "app" [Term.var "lam", Term.con "app" [Term.con "shift" [Term.con "num" [Term.con "number" [Term.lit "0"]], Term.con "num" [Term.con "number" [Term.lit "1"]], B], Term.con "coe" [Term.con "app" [Term.var "lam", A], s, Term.con "app" [Term.var "ix", Term.con "num" [Term.con "number" [Term.lit "0"]]], Term.con "app" [Term.var "ix", Term.con "num" [Term.con "number" [Term.lit "0"]]]]]], r, s, Term.con "app" [f, Term.con "coe" [Term.con "app" [Term.var "lam", A], s, r, Term.con "app" [Term.var "ix", Term.con "num" [Term.con "number" [Term.lit "0"]]]]]]]
      | _ => t

    def doRigidCoeSigma (t : Term) : Term :=
      match t with
      | .con "doRigidCoe" [ctx, .con "app" [.var "lam", .con "sigma" [A, B]], r, s, .con "pair" [a, b]] => Term.con "pair" [Term.con "coe" [Term.con "app" [Term.var "lam", A], r, s, a], Term.con "coe" [Term.con "app" [Term.var "lam", Term.con "app" [Term.con "shift" [Term.con "num" [Term.con "number" [Term.lit "0"]], Term.con "num" [Term.con "number" [Term.lit "1"]], B], Term.con "coe" [Term.con "app" [Term.var "lam", A], r, Term.con "app" [Term.var "ix", Term.con "num" [Term.con "number" [Term.lit "0"]]], Term.con "shift" [Term.con "num" [Term.con "number" [Term.lit "0"]], Term.con "num" [Term.con "number" [Term.lit "1"]], a]]]], r, s, b]]
      | _ => t

    def doRigidCoePath (t : Term) : Term :=
      match t with
      | .con "doRigidCoe" [ctx, .con "app" [.var "lam", .con "path" [A, l, r]], r', s', p] => Term.con "app" [Term.var "plam", Term.con "com" [Term.con "app" [Term.var "lam", A], r', s', Term.con "cof_or" [Term.con "cof_eq" [Term.con "app" [Term.var "ix", Term.con "num" [Term.con "number" [Term.lit "0"]]], Term.con "dim0" []], Term.con "cof_eq" [Term.con "app" [Term.var "ix", Term.con "num" [Term.con "number" [Term.lit "0"]]], Term.con "dim1" []]], Term.con "app" [Term.var "lam", Term.con "app" [Term.var "lam", Term.con "caseExpr" [Term.lit "(", Term.lit "case", Term.con "app" [Term.var "ix", Term.con "num" [Term.con "number" [Term.lit "1"]]], Term.con "arm" [Term.var "dim0", Term.lit "=>", l], Term.con "arm" [Term.var "dim1", Term.lit "=>", r], Term.lit ")"]]], Term.con "papp" [p, Term.con "app" [Term.var "ix", Term.con "num" [Term.con "number" [Term.lit "0"]]]]]]
      | _ => t

    def doRigidCoeDefault (t : Term) : Term :=
      match t with
      | .con "doRigidCoe" [ctx, line, r, s, con] => Term.con "coe" [line, r, s, con]
      | _ => t

  end RigidCoe

  section RigidHCom

    def doRigidHComPi (t : Term) : Term :=
      match t with
      | .con "doRigidHCom" [ctx, .con "pi" [A, B], r, s, φ, u] => Term.con "app" [Term.var "lam", Term.con "hcom" [Term.con "app" [Term.con "shift" [Term.con "num" [Term.con "number" [Term.lit "0"]], Term.con "num" [Term.con "number" [Term.lit "1"]], B], Term.con "app" [Term.var "ix", Term.con "num" [Term.con "number" [Term.lit "0"]]]], r, s, φ, Term.con "app" [Term.var "lam", Term.con "app" [Term.var "lam", Term.con "app" [Term.con "app" [Term.con "app" [Term.con "shift" [Term.con "num" [Term.con "number" [Term.lit "0"]], Term.con "num" [Term.con "number" [Term.lit "2"]], u], Term.con "app" [Term.var "ix", Term.con "num" [Term.con "number" [Term.lit "1"]]]], Term.con "app" [Term.var "ix", Term.con "num" [Term.con "number" [Term.lit "0"]]]], Term.con "app" [Term.var "ix", Term.con "num" [Term.con "number" [Term.lit "2"]]]]]]]]
      | _ => t

    def doRigidHComSigma (t : Term) : Term :=
      match t with
      | .con "doRigidHCom" [ctx, .con "sigma" [A, B], r, s, φ, u] => Term.con "pair" [Term.con "hcom" [A, r, s, φ, Term.con "app" [Term.var "lam", Term.con "app" [Term.var "lam", Term.con "app" [Term.var "fst", Term.con "app" [Term.con "app" [Term.con "shift" [Term.con "num" [Term.con "number" [Term.lit "0"]], Term.con "num" [Term.con "number" [Term.lit "2"]], u], Term.con "app" [Term.var "ix", Term.con "num" [Term.con "number" [Term.lit "1"]]]], Term.con "app" [Term.var "ix", Term.con "num" [Term.con "number" [Term.lit "0"]]]]]]]], Term.con "com" [Term.con "app" [Term.var "lam", Term.con "app" [Term.con "shift" [Term.con "num" [Term.con "number" [Term.lit "0"]], Term.con "num" [Term.con "number" [Term.lit "1"]], B], Term.con "hcom" [A, r, Term.con "app" [Term.var "ix", Term.con "num" [Term.con "number" [Term.lit "0"]]], φ, Term.con "app" [Term.var "lam", Term.con "app" [Term.var "lam", Term.con "app" [Term.var "fst", Term.con "app" [Term.con "app" [Term.con "shift" [Term.con "num" [Term.con "number" [Term.lit "0"]], Term.con "num" [Term.con "number" [Term.lit "2"]], u], Term.con "app" [Term.var "ix", Term.con "num" [Term.con "number" [Term.lit "1"]]]], Term.con "app" [Term.var "ix", Term.con "num" [Term.con "number" [Term.lit "0"]]]]]]]]]], r, s, φ, Term.con "app" [Term.var "lam", Term.con "app" [Term.var "lam", Term.con "app" [Term.var "snd", Term.con "app" [Term.con "app" [Term.con "shift" [Term.con "num" [Term.con "number" [Term.lit "0"]], Term.con "num" [Term.con "number" [Term.lit "2"]], u], Term.con "app" [Term.var "ix", Term.con "num" [Term.con "number" [Term.lit "1"]]]], Term.con "app" [Term.var "ix", Term.con "num" [Term.con "number" [Term.lit "0"]]]]]]], Term.con "app" [Term.var "snd", Term.con "app" [Term.con "app" [u, r], Term.con "prf" []]]]]
      | _ => t

    def doRigidHComPath (t : Term) : Term :=
      match t with
      | .con "doRigidHCom" [ctx, .con "path" [A, l, ep], r, s, φ, u] => Term.con "app" [Term.var "plam", Term.con "hcom" [A, r, s, Term.con "cof_or" [φ, Term.con "cof_or" [Term.con "cof_eq" [Term.con "app" [Term.var "ix", Term.con "num" [Term.con "number" [Term.lit "0"]]], Term.con "dim0" []], Term.con "cof_eq" [Term.con "app" [Term.var "ix", Term.con "num" [Term.con "number" [Term.lit "0"]]], Term.con "dim1" []]]], Term.con "app" [Term.var "lam", Term.con "app" [Term.var "lam", Term.con "caseExpr" [Term.lit "(", Term.lit "case", Term.con "meetsCof" [Term.con "app" [Term.var "ix", Term.con "num" [Term.con "number" [Term.lit "1"]]], φ], Term.con "arm" [Term.var "true", Term.lit "=>", Term.con "papp" [Term.con "app" [Term.con "app" [Term.con "shift" [Term.con "num" [Term.con "number" [Term.lit "0"]], Term.con "num" [Term.con "number" [Term.lit "2"]], u], Term.con "app" [Term.var "ix", Term.con "num" [Term.con "number" [Term.lit "1"]]]], Term.con "app" [Term.var "ix", Term.con "num" [Term.con "number" [Term.lit "0"]]]], Term.con "app" [Term.var "ix", Term.con "num" [Term.con "number" [Term.lit "2"]]]]], Term.con "arm" [Term.var "false", Term.lit "=>", Term.con "caseExpr" [Term.lit "(", Term.lit "case", Term.con "app" [Term.var "ix", Term.con "num" [Term.con "number" [Term.lit "2"]]], Term.con "arm" [Term.var "dim0", Term.lit "=>", l], Term.con "arm" [Term.var "dim1", Term.lit "=>", ep], Term.lit ")"]], Term.lit ")"]]]]]
      | _ => t

    def doRigidHComNat (t : Term) : Term :=
      match t with
      | .con "doRigidHCom" [ctx, .con "nat" [], r, s, φ, u] => Term.con "hcom" [Term.con "nat" [], r, s, φ, u]
      | _ => t

    def doRigidHComCircle (t : Term) : Term :=
      match t with
      | .con "doRigidHCom" [ctx, .con "circle" [], r, s, φ, u] => Term.con "hcom" [Term.con "circle" [], r, s, φ, u]
      | _ => t

    def doRigidHComUniv (t : Term) : Term :=
      match t with
      | .con "doRigidHCom" [ctx, .con "app" [.var "univ", l], r, s, φ, u] => Term.con "hcom" [Term.con "app" [Term.var "univ", l], r, s, φ, u]
      | _ => t

    def doRigidHComDefault (t : Term) : Term :=
      match t with
      | .con "doRigidHCom" [ctx, code, r, s, φ, u] => Term.con "hcom" [code, r, s, φ, u]
      | _ => t

  end RigidHCom

  section SpliceCtx

    def spliceCtxEmpty (t : Term) : Term :=
      match t with
      | .con "spliceCtxEmpty" [] => Term.con "spliceCtx" [Term.con "unit" [Term.lit "(", Term.lit ")"], Term.con "labeledArg" [Term.var "level", Term.lit ":", Term.con "num" [Term.con "number" [Term.lit "0"]]]]
      | _ => t

    def spliceCtxBind (t : Term) : Term :=
      match t with
      | .con "spliceCtxBind" [.con "spliceCtx" [bindings, .con "labeledArg" [.var "level", .lit ":", l]], name, v] => Term.con "record" [Term.lit "(", Term.var "result", Term.lit ":", Term.con "spliceCtx" [Term.con "tuple" [bindings, Term.con "tuple" [Term.lit "(", name, Term.lit ",", v, Term.lit ")"]], Term.con "labeledArg" [Term.var "level", Term.lit ":", Term.con "app" [Term.var "suc", l]]], Term.con "labeledArg" [Term.var "var", Term.lit ":", Term.con "app" [Term.var "ix", l]], Term.lit ")"]
      | _ => t

  end SpliceCtx

  section SpliceDim

    def spliceDim0 (t : Term) : Term :=
      match t with
      | .con "spliceDim" [ctx, .con "dim0" [], k] => Term.con "tuple" [k, ctx, Term.con "dim0" []]
      | _ => t

    def spliceDim1 (t : Term) : Term :=
      match t with
      | .con "spliceDim" [ctx, .con "dim1" [], k] => Term.con "tuple" [k, ctx, Term.con "dim1" []]
      | _ => t

    def spliceDimVar (t : Term) : Term :=
      match t with
      | .con "spliceDim" [ctx, d, k] => Term.con "caseExpr" [Term.lit "(", Term.lit "case", Term.con "spliceCtxBind" [ctx, Term.con "terminal" [Term.lit "i"], d], Term.con "arm" [Term.lit "(", Term.var "result", Term.lit ":", Term.var "ctx'", Term.con "labeledArg" [Term.var "var", Term.lit ":", Term.var "var"], Term.lit ")", Term.lit "=>", Term.con "tuple" [k, Term.var "ctx'", Term.var "var"]], Term.lit ")"]
      | _ => t

  end SpliceDim

  section SpliceCof

    def spliceCofTop (t : Term) : Term :=
      match t with
      | .con "spliceCof" [ctx, .con "cof_top" [], k] => Term.con "tuple" [k, ctx, Term.con "cof_top" []]
      | _ => t

    def spliceCofBot (t : Term) : Term :=
      match t with
      | .con "spliceCof" [ctx, .con "cof_bot" [], k] => Term.con "tuple" [k, ctx, Term.con "cof_bot" []]
      | _ => t

    def spliceCofVar (t : Term) : Term :=
      match t with
      | .con "spliceCof" [ctx, φ, k] => Term.con "caseExpr" [Term.lit "(", Term.lit "case", Term.con "spliceCtxBind" [ctx, Term.con "terminal" [Term.lit "φ"], φ], Term.con "arm" [Term.lit "(", Term.var "result", Term.lit ":", Term.var "ctx'", Term.con "labeledArg" [Term.var "var", Term.lit ":", Term.var "var"], Term.lit ")", Term.lit "=>", Term.con "tuple" [k, Term.var "ctx'", Term.var "var"]], Term.lit ")"]
      | _ => t

  end SpliceCof

  section SpliceCon

    def spliceCon (t : Term) : Term :=
      match t with
      | .con "spliceCon" [ctx, con, k] => Term.con "caseExpr" [Term.lit "(", Term.lit "case", Term.con "spliceCtxBind" [ctx, Term.con "terminal" [Term.lit "x"], con], Term.con "arm" [Term.lit "(", Term.var "result", Term.lit ":", Term.var "ctx'", Term.con "labeledArg" [Term.var "var", Term.lit ":", Term.var "var"], Term.lit ")", Term.lit "=>", Term.con "tuple" [k, Term.var "ctx'", Term.var "var"]], Term.lit ")"]
      | _ => t

  end SpliceCon

  section DoOps

    def doAp (t : Term) : Term :=
      match t with
      | .con "doAp" [ctx, f, a] => Term.con "eval" [ctx, Term.con "app" [f, a]]
      | _ => t

    def doAp2 (t : Term) : Term :=
      match t with
      | .con "doAp2" [ctx, f, a, b] => Term.con "doAp" [ctx, Term.con "doAp" [ctx, f, a], b]
      | _ => t

    def doFst (t : Term) : Term :=
      match t with
      | .con "doFst" [ctx, p] => Term.con "eval" [ctx, Term.con "app" [Term.var "fst", p]]
      | _ => t

    def doSnd (t : Term) : Term :=
      match t with
      | .con "doSnd" [ctx, p] => Term.con "eval" [ctx, Term.con "app" [Term.var "snd", p]]
      | _ => t

    def doPApp (t : Term) : Term :=
      match t with
      | .con "doPApp" [ctx, p, r] => Term.con "eval" [ctx, Term.con "papp" [p, r]]
      | _ => t

    def doSubOut (t : Term) : Term :=
      match t with
      | .con "doSubOut" [ctx, t] => Term.con "eval" [ctx, Term.con "app" [Term.var "subOut", t]]
      | _ => t

  end DoOps

  section El

    def doElNat (t : Term) : Term :=
      match t with
      | .con "doEl" [ctx, .con "app" [.var "lit", .con "terminal" [.lit "nat-code"]]] => Term.con "nat" []
      | _ => t

    def doElCircle (t : Term) : Term :=
      match t with
      | .con "doEl" [ctx, .con "app" [.var "lit", .con "terminal" [.lit "circle-code"]]] => Term.con "circle" []
      | _ => t

    def doElDefault (t : Term) : Term :=
      match t with
      | .con "doEl" [ctx, code] => Term.con "eval" [ctx, code]
      | _ => t

  end El

  section RigidCap

    def doRigidCap (t : Term) : Term :=
      match t with
      | .con "doRigidCap" [ctx, r, s, φ, code, box] => Term.con "app" [Term.var "lit", Term.con "concat" [Term.con "terminal" [Term.lit "cap("], r, Term.con "terminal" [Term.lit ","], s, Term.con "terminal" [Term.lit ","], φ, Term.con "terminal" [Term.lit ","], code, Term.con "terminal" [Term.lit ","], Term.con "eval" [ctx, box], Term.con "terminal" [Term.lit ")"]]]
      | _ => t

  end RigidCap

  section RigidVProj

    def doRigidVProjVIn (t : Term) : Term :=
      match t with
      | .con "doRigidVProj" [ctx, r, pcode, code, pequiv, .con "vin" [r', a, base]] => base
      | _ => t

    def doRigidVProjDefault (t : Term) : Term :=
      match t with
      | .con "doRigidVProj" [ctx, r, pcode, code, pequiv, v] => Term.con "vproj" [r, pcode, code, pequiv, Term.con "eval" [ctx, v]]
      | _ => t

  end RigidVProj

  section TopLevel

    def evaluate (t : Term) : Term :=
      match t with
      | .con "app" [.var "evaluate", e] => Term.con "eval" [Term.con "evalCtxEmpty" [], e]
      | _ => t

    def whnf (t : Term) : Term :=
      match t with
      | .con "app" [.var "whnf", e] => Term.con "eval" [Term.con "evalCtxEmpty" [], e]
      | _ => t

    def whnfTp (t : Term) : Term :=
      match t with
      | .con "app" [.var "whnfTp", tp] => Term.con "app" [Term.var "whnf", tp]
      | _ => t

  end TopLevel

  section Instantiation

    def instClo (t : Term) : Term :=
      match t with
      | .con "instClo" [ctx, body, v] => Term.con "eval" [ctx, Term.con "subst" [Term.con "num" [Term.con "number" [Term.lit "0"]], v, body]]
      | _ => t

    def instTpClo (t : Term) : Term :=
      match t with
      | .con "instTpClo" [ctx, body, v] => Term.con "instClo" [ctx, body, v]
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

  end Instantiation

end Semantics