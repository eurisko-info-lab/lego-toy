/-
  AUTO-GENERATED from .lego files
  Do not edit directly.
-/

import Lego.Algebra

open Lego

namespace Conversion

  section ConvResult

    def convResultIsOk (t : Term) : Term :=
      match t with
      | .con "app" [.var "isOk", .con "ok" []] => Term.con "true" []
      | _ => t

    def convResultIsOkFail (t : Term) : Term :=
      match t with
      | .con "app" [.var "isOk", .con "app" [.var "fail", msg]] => Term.con "false" []
      | _ => t

    def convResultIsOkBlocked (t : Term) : Term :=
      match t with
      | .con "app" [.var "isOk", .con "app" [.var "blocked", n]] => Term.con "false" []
      | _ => t

    def convAndThenOk (t : Term) : Term :=
      match t with
      | .con "andThen" [.con "ok" [], k] => Term.con "tuple" [k, Term.con "unit" []]
      | _ => t

    def convAndThenFail (t : Term) : Term :=
      match t with
      | .con "andThen" [.con "app" [.var "fail", msg], k] => Term.con "app" [Term.var "fail", msg]
      | _ => t

    def convAndThenBlocked (t : Term) : Term :=
      match t with
      | .con "andThen" [.con "app" [.var "blocked", n], k] => Term.con "app" [Term.var "blocked", n]
      | _ => t

  end ConvResult

  section ConvCtx

    def convCtxEmpty (t : Term) : Term :=
      match t with
      | .con "convCtxEmpty" [] => Term.con "convCtx" [Term.con "labeledArg" [Term.var "size", Term.lit ":", Term.con "num" [Term.con "number" [Term.lit "0"]]], Term.con "labeledArg" [Term.var "cof", Term.lit ":", Term.con "cof_top" []]]
      | _ => t

    def convCtxExtend (t : Term) : Term :=
      match t with
      | .con "app" [.var "convCtxExtend", .con "convCtx" [.con "labeledArg" [.var "size", .lit ":", s], .con "labeledArg" [.var "cof", .lit ":", φ]]] => Term.con "convCtx" [Term.con "labeledArg" [Term.var "size", Term.lit ":", Term.con "app" [Term.var "suc", s]], Term.con "labeledArg" [Term.var "cof", Term.lit ":", φ]]
      | _ => t

    def convCtxAssume (t : Term) : Term :=
      match t with
      | .con "convCtxAssume" [.con "convCtx" [.con "labeledArg" [.var "size", .lit ":", s], .con "labeledArg" [.var "cof", .lit ":", φ]], ψ] => Term.con "convCtx" [Term.con "labeledArg" [Term.var "size", Term.lit ":", s], Term.con "labeledArg" [Term.var "cof", Term.lit ":", Term.con "cof_and" [φ, ψ]]]
      | _ => t

  end ConvCtx

  section WHNF

    def defaultFuel (t : Term) : Term :=
      match t with
      | .con "defaultFuel" [] => Term.con "num" [Term.con "number" [Term.lit "1000"]]
      | _ => t

    def whnf (t : Term) : Term :=
      match t with
      | .con "whnf" [fuel, e] => Term.con "whnfStep" [fuel, e]
      | _ => t

    def whnfStep0 (t : Term) : Term :=
      match t with
      | .con "whnfStep" [.con "num" [.con "number" [.lit "0"]], e] => e
      | _ => t

    def whnfStep (t : Term) : Term :=
      match t with
      | .con "whnfStep" [.con "app" [.var "suc", fuel], e] => Term.con "caseExpr" [Term.lit "(", Term.lit "case", Term.con "app" [Term.var "tryStep", e], Term.con "arm" [Term.lit "(", Term.var "some", Term.var "e'", Term.lit ")", Term.lit "=>", Term.con "whnfStep" [fuel, Term.var "e'"]], Term.con "arm" [Term.var "none", Term.lit "=>", e], Term.lit ")"]
      | _ => t

    def tryStepApp (t : Term) : Term :=
      match t with
      | .con "app" [.var "tryStep", .con "app" [.con "app" [.var "lam", body], arg]] => Term.con "app" [Term.var "some", Term.con "subst" [Term.con "num" [Term.con "number" [Term.lit "0"]], arg, body]]
      | _ => t

    def tryStepFst (t : Term) : Term :=
      match t with
      | .con "app" [.var "tryStep", .con "app" [.var "fst", .con "pair" [a, b]]] => Term.con "app" [Term.var "some", a]
      | _ => t

    def tryStepSnd (t : Term) : Term :=
      match t with
      | .con "app" [.var "tryStep", .con "app" [.var "snd", .con "pair" [a, b]]] => Term.con "app" [Term.var "some", b]
      | _ => t

    def tryStepPapp (t : Term) : Term :=
      match t with
      | .con "app" [.var "tryStep", .con "papp" [.con "app" [.var "plam", body], r]] => Term.con "app" [Term.var "some", Term.con "dimSubst" [Term.con "num" [Term.con "number" [Term.lit "0"]], r, body]]
      | _ => t

    def tryStepDefault (t : Term) : Term :=
      match t with
      | .con "app" [.var "tryStep", e] => Term.con "none" []
      | _ => t

  end WHNF

  section EquateDim

    def equateDim (t : Term) : Term :=
      match t with
      | .con "equateDim" [ctx, r1, r2] => Term.con "letIn" [Term.lit "(", Term.lit "let", Term.var "r1'", Term.lit "=", Term.con "whnf" [Term.con "defaultFuel" [], r1], Term.lit "in", Term.con "letIn" [Term.lit "let", Term.var "r2'", Term.lit "=", Term.con "whnf" [Term.con "defaultFuel" [], r2], Term.lit "in", Term.con "equateDim'" [ctx, Term.con "r1'" [], Term.con "r2'" []]], Term.lit ")"]
      | _ => t

    def equateDim'Same (t : Term) : Term :=
      match t with
      | .con "equateDim'" [ctx, r, r_dup] => Term.con "ok" []
      | _ => t

    def equateDim'00 (t : Term) : Term :=
      match t with
      | .con "equateDim'" [ctx, .con "dim0" [], .con "dim0" []] => Term.con "ok" []
      | _ => t

    def equateDim'11 (t : Term) : Term :=
      match t with
      | .con "equateDim'" [ctx, .con "dim1" [], .con "dim1" []] => Term.con "ok" []
      | _ => t

    def equateDim'IxEq (t : Term) : Term :=
      match t with
      | .con "equateDim'" [ctx, .con "app" [.var "ix", n], .con "app" [.var "ix", n_dup]] => Term.con "ok" []
      | _ => t

    def equateDim'IxNeq (t : Term) : Term :=
      match t with
      | .con "equateDim'" [ctx, .con "app" [.var "ix", n], .con "app" [.var "ix", m]] => Term.con "app" [Term.var "fail", Term.con "concat" [Term.con "terminal" [Term.lit "dimensions differ: "], n, Term.con "terminal" [Term.lit " vs "], m]]
      | _ => t

    def equateDim'Other (t : Term) : Term :=
      match t with
      | .con "equateDim'" [ctx, r1, r2] => Term.con "app" [Term.var "fail", Term.con "concat" [Term.con "terminal" [Term.lit "dimensions not equal: "], r1, Term.con "terminal" [Term.lit " vs "], r2]]
      | _ => t

  end EquateDim

  section EquateCof

    def equateCof (t : Term) : Term :=
      match t with
      | .con "equateCof" [ctx, φ1, φ2] => Term.con "letIn" [Term.lit "(", Term.lit "let", Term.var "φ1'", Term.lit "=", Term.con "whnf" [Term.con "defaultFuel" [], φ1], Term.lit "in", Term.con "letIn" [Term.lit "let", Term.var "φ2'", Term.lit "=", Term.con "whnf" [Term.con "defaultFuel" [], φ2], Term.lit "in", Term.con "equateCof'" [ctx, Term.con "φ1'" [], Term.con "φ2'" []]], Term.lit ")"]
      | _ => t

    def equateCof'Same (t : Term) : Term :=
      match t with
      | .con "equateCof'" [ctx, φ, φ_dup] => Term.con "ok" []
      | _ => t

    def equateCof'Top (t : Term) : Term :=
      match t with
      | .con "equateCof'" [ctx, .con "cof_top" [], .con "cof_top" []] => Term.con "ok" []
      | _ => t

    def equateCof'Bot (t : Term) : Term :=
      match t with
      | .con "equateCof'" [ctx, .con "cof_bot" [], .con "cof_bot" []] => Term.con "ok" []
      | _ => t

    def equateCof'Eq (t : Term) : Term :=
      match t with
      | .con "equateCof'" [ctx, .con "cof_eq" [r1, s1], .con "cof_eq" [r2, s2]] => Term.con "andThen" [Term.con "equateDim" [ctx, r1, r2], Term.con "fun" [Term.con "_" [], Term.lit "=>", Term.con "equateDim" [ctx, s1, s2]]]
      | _ => t

    def equateCof'And (t : Term) : Term :=
      match t with
      | .con "equateCof'" [ctx, .con "cof_and" [φ1a, φ1b], .con "cof_and" [φ2a, φ2b]] => Term.con "andThen" [Term.con "equateCof" [ctx, φ1a, φ2a], Term.con "fun" [Term.con "_" [], Term.lit "=>", Term.con "equateCof" [ctx, φ1b, φ2b]]]
      | _ => t

    def equateCof'Or (t : Term) : Term :=
      match t with
      | .con "equateCof'" [ctx, .con "cof_or" [φ1a, φ1b], .con "cof_or" [φ2a, φ2b]] => Term.con "andThen" [Term.con "equateCof" [ctx, φ1a, φ2a], Term.con "fun" [Term.con "_" [], Term.lit "=>", Term.con "equateCof" [ctx, φ1b, φ2b]]]
      | _ => t

    def equateCof'Other (t : Term) : Term :=
      match t with
      | .con "equateCof'" [ctx, φ1, φ2] => Term.con "app" [Term.var "fail", Term.con "concat" [Term.con "terminal" [Term.lit "cofibrations not equal: "], φ1, Term.con "terminal" [Term.lit " vs "], φ2]]
      | _ => t

  end EquateCof

  section EquateTp

    def equateTp (t : Term) : Term :=
      match t with
      | .con "equateTp" [ctx, tp1, tp2] => Term.con "letIn" [Term.lit "(", Term.lit "let", Term.var "tp1'", Term.lit "=", Term.con "whnf" [Term.con "defaultFuel" [], tp1], Term.lit "in", Term.con "letIn" [Term.lit "let", Term.var "tp2'", Term.lit "=", Term.con "whnf" [Term.con "defaultFuel" [], tp2], Term.lit "in", Term.con "equateTp'" [ctx, Term.con "tp1'" [], Term.con "tp2'" []]], Term.lit ")"]
      | _ => t

    def equateTp'Same (t : Term) : Term :=
      match t with
      | .con "equateTp'" [ctx, tp, tp_dup] => Term.con "ok" []
      | _ => t

    def equateTp'Nat (t : Term) : Term :=
      match t with
      | .con "equateTp'" [ctx, .con "nat" [], .con "nat" []] => Term.con "ok" []
      | _ => t

    def equateTp'Circle (t : Term) : Term :=
      match t with
      | .con "equateTp'" [ctx, .con "circle" [], .con "circle" []] => Term.con "ok" []
      | _ => t

    def equateTp'Univ (t : Term) : Term :=
      match t with
      | .con "equateTp'" [ctx, .con "app" [.var "univ", n], .con "app" [.var "univ", n_dup]] => Term.con "ok" []
      | _ => t

    def equateTp'UnivNeq (t : Term) : Term :=
      match t with
      | .con "equateTp'" [ctx, .con "app" [.var "univ", n1], .con "app" [.var "univ", n2]] => Term.con "app" [Term.var "fail", Term.con "concat" [Term.con "terminal" [Term.lit "universe levels differ: "], n1, Term.con "terminal" [Term.lit " vs "], n2]]
      | _ => t

    def equateTp'Dim (t : Term) : Term :=
      match t with
      | .con "equateTp'" [ctx, .con "app" [.var "lit", .con "terminal" [.lit "𝕀"]], .con "app" [.var "lit", .con "terminal" [.lit "𝕀"]]] => Term.con "ok" []
      | _ => t

    def equateTp'Cof (t : Term) : Term :=
      match t with
      | .con "equateTp'" [ctx, .con "app" [.var "lit", .con "terminal" [.lit "𝔽"]], .con "app" [.var "lit", .con "terminal" [.lit "𝔽"]]] => Term.con "ok" []
      | _ => t

    def equateTp'Pi (t : Term) : Term :=
      match t with
      | .con "equateTp'" [ctx, .con "pi" [dom1, cod1], .con "pi" [dom2, cod2]] => Term.con "andThen" [Term.con "equateTp" [ctx, dom1, dom2], Term.con "fun" [Term.con "_" [], Term.lit "=>", Term.con "equateTp" [Term.con "app" [Term.var "convCtxExtend", ctx], cod1, cod2]]]
      | _ => t

    def equateTp'Sigma (t : Term) : Term :=
      match t with
      | .con "equateTp'" [ctx, .con "sigma" [a1, b1], .con "sigma" [a2, b2]] => Term.con "andThen" [Term.con "equateTp" [ctx, a1, a2], Term.con "fun" [Term.con "_" [], Term.lit "=>", Term.con "equateTp" [Term.con "app" [Term.var "convCtxExtend", ctx], b1, b2]]]
      | _ => t

    def equateTp'Path (t : Term) : Term :=
      match t with
      | .con "equateTp'" [ctx, .con "path" [a1, l1, r1], .con "path" [a2, l2, r2]] => Term.con "andThen" [Term.con "equateTp" [ctx, a1, a2], Term.con "fun" [Term.con "_" [], Term.lit "=>", Term.con "andThen" [Term.con "equateCon" [ctx, a1, l1, l2], Term.con "fun" [Term.con "_" [], Term.lit "=>", Term.con "equateCon" [ctx, a1, r1, r2]]]]]
      | _ => t

    def equateTp'Sub (t : Term) : Term :=
      match t with
      | .con "equateTp'" [ctx, .con "sub" [a1, φ1, t1], .con "sub" [a2, φ2, t2]] => Term.con "andThen" [Term.con "equateTp" [ctx, a1, a2], Term.con "fun" [Term.con "_" [], Term.lit "=>", Term.con "andThen" [Term.con "equateCof" [ctx, φ1, φ2], Term.con "fun" [Term.con "_" [], Term.lit "=>", Term.con "equateCon" [Term.con "convCtxAssume" [ctx, φ1], a1, t1, t2]]]]]
      | _ => t

    def equateTp'VType (t : Term) : Term :=
      match t with
      | .con "equateTp'" [ctx, .con "vtype" [r1, a1, b1, e1], .con "vtype" [r2, a2, b2, e2]] => Term.con "andThen" [Term.con "equateDim" [ctx, r1, r2], Term.con "fun" [Term.con "_" [], Term.lit "=>", Term.con "andThen" [Term.con "equateTp" [ctx, a1, a2], Term.con "fun" [Term.con "_" [], Term.lit "=>", Term.con "andThen" [Term.con "equateTp" [ctx, b1, b2], Term.con "fun" [Term.con "_" [], Term.lit "=>", Term.con "equateCon" [ctx, Term.con "app" [Term.var "lit", Term.con "terminal" [Term.lit "Equiv"]], e1, e2]]]]]]]
      | _ => t

    def equateTp'Lit (t : Term) : Term :=
      match t with
      | .con "equateTp'" [ctx, .con "app" [.var "lit", s], .con "app" [.var "lit", s_dup]] => Term.con "ok" []
      | _ => t

    def equateTp'LitNeq (t : Term) : Term :=
      match t with
      | .con "equateTp'" [ctx, .con "app" [.var "lit", s1], .con "app" [.var "lit", s2]] => Term.con "app" [Term.var "fail", Term.con "concat" [Term.con "terminal" [Term.lit "type literals differ: "], s1, Term.con "terminal" [Term.lit " vs "], s2]]
      | _ => t

    def equateTp'Other (t : Term) : Term :=
      match t with
      | .con "equateTp'" [ctx, tp1, tp2] => Term.con "app" [Term.var "fail", Term.con "concat" [Term.con "terminal" [Term.lit "types not equal: "], tp1, Term.con "terminal" [Term.lit " vs "], tp2]]
      | _ => t

  end EquateTp

  section EquateCon

    def equateCon (t : Term) : Term :=
      match t with
      | .con "equateCon" [ctx, tp, t1, t2] => Term.con "letIn" [Term.lit "(", Term.lit "let", Term.var "t1'", Term.lit "=", Term.con "whnf" [Term.con "defaultFuel" [], t1], Term.lit "in", Term.con "letIn" [Term.lit "let", Term.var "t2'", Term.lit "=", Term.con "whnf" [Term.con "defaultFuel" [], t2], Term.lit "in", Term.con "caseExpr" [Term.lit "(", Term.lit "case", Term.con "eq" [Term.con "t1'" [], Term.con "t2'" []], Term.con "arm" [Term.var "true", Term.lit "=>", Term.con "ok" []], Term.con "arm" [Term.var "false", Term.lit "=>", Term.con "equateCon'" [ctx, Term.con "whnf" [Term.con "defaultFuel" [], tp], Term.con "t1'" [], Term.con "t2'" []]], Term.lit ")"]], Term.lit ")"]
      | _ => t

    def equateCon'Pi (t : Term) : Term :=
      match t with
      | .con "equateCon'" [ctx, .con "pi" [dom, cod], t1, t2] => Term.con "letIn" [Term.lit "(", Term.lit "let", Term.var "ctx'", Term.lit "=", Term.con "app" [Term.var "convCtxExtend", ctx], Term.lit "in", Term.con "letIn" [Term.lit "let", Term.var "var", Term.lit "=", Term.con "app" [Term.var "ix", Term.con "num" [Term.con "number" [Term.lit "0"]]], Term.lit "in", Term.con "letIn" [Term.lit "let", Term.var "app1", Term.lit "=", Term.con "app" [Term.con "shift" [Term.con "num" [Term.con "number" [Term.lit "0"]], Term.con "num" [Term.con "number" [Term.lit "1"]], t1], Term.con "var" []], Term.lit "in", Term.con "letIn" [Term.lit "let", Term.var "app2", Term.lit "=", Term.con "app" [Term.con "shift" [Term.con "num" [Term.con "number" [Term.lit "0"]], Term.con "num" [Term.con "number" [Term.lit "1"]], t2], Term.con "var" []], Term.lit "in", Term.con "equateCon" [Term.con "ctx'" [], cod, Term.con "app1" [], Term.con "app2" []]]]], Term.lit ")"]
      | _ => t

    def equateCon'Sigma (t : Term) : Term :=
      match t with
      | .con "equateCon'" [ctx, .con "sigma" [a, b], t1, t2] => Term.con "letIn" [Term.lit "(", Term.lit "let", Term.var "fst1", Term.lit "=", Term.con "app" [Term.var "fst", t1], Term.lit "in", Term.con "letIn" [Term.lit "let", Term.var "fst2", Term.lit "=", Term.con "app" [Term.var "fst", t2], Term.lit "in", Term.con "andThen" [Term.con "equateCon" [ctx, a, Term.con "fst1" [], Term.con "fst2" []], Term.con "fun" [Term.con "_" [], Term.lit "=>", Term.con "letIn" [Term.lit "(", Term.lit "let", Term.var "snd1", Term.lit "=", Term.con "app" [Term.var "snd", t1], Term.lit "in", Term.con "letIn" [Term.lit "let", Term.var "snd2", Term.lit "=", Term.con "app" [Term.var "snd", t2], Term.lit "in", Term.con "letIn" [Term.lit "let", Term.var "b'", Term.lit "=", Term.con "subst" [Term.con "num" [Term.con "number" [Term.lit "0"]], Term.con "fst1" [], b], Term.lit "in", Term.con "equateCon" [ctx, Term.con "b'" [], Term.con "snd1" [], Term.con "snd2" []]]], Term.lit ")"]]]], Term.lit ")"]
      | _ => t

    def equateCon'Path (t : Term) : Term :=
      match t with
      | .con "equateCon'" [ctx, .con "path" [a, l, r], t1, t2] => Term.con "letIn" [Term.lit "(", Term.lit "let", Term.var "ctx'", Term.lit "=", Term.con "app" [Term.var "convCtxExtend", ctx], Term.lit "in", Term.con "letIn" [Term.lit "let", Term.var "var", Term.lit "=", Term.con "app" [Term.var "ix", Term.con "num" [Term.con "number" [Term.lit "0"]]], Term.lit "in", Term.con "letIn" [Term.lit "let", Term.var "papp1", Term.lit "=", Term.con "papp" [Term.con "shift" [Term.con "num" [Term.con "number" [Term.lit "0"]], Term.con "num" [Term.con "number" [Term.lit "1"]], t1], Term.con "var" []], Term.lit "in", Term.con "letIn" [Term.lit "let", Term.var "papp2", Term.lit "=", Term.con "papp" [Term.con "shift" [Term.con "num" [Term.con "number" [Term.lit "0"]], Term.con "num" [Term.con "number" [Term.lit "1"]], t2], Term.con "var" []], Term.lit "in", Term.con "equateCon" [Term.con "ctx'" [], a, Term.con "papp1" [], Term.con "papp2" []]]]], Term.lit ")"]
      | _ => t

    def equateCon'Sub (t : Term) : Term :=
      match t with
      | .con "equateCon'" [ctx, .con "sub" [a, φ, u], t1, t2] => Term.con "letIn" [Term.lit "(", Term.lit "let", Term.var "out1", Term.lit "=", Term.con "app" [Term.var "subOut", t1], Term.lit "in", Term.con "letIn" [Term.lit "let", Term.var "out2", Term.lit "=", Term.con "app" [Term.var "subOut", t2], Term.lit "in", Term.con "equateCon" [ctx, a, Term.con "out1" [], Term.con "out2" []]], Term.lit ")"]
      | _ => t

    def equateCon'NatZero (t : Term) : Term :=
      match t with
      | .con "equateCon'" [ctx, .con "nat" [], .con "zero" [], .con "zero" []] => Term.con "ok" []
      | _ => t

    def equateCon'NatSuc (t : Term) : Term :=
      match t with
      | .con "equateCon'" [ctx, .con "nat" [], .con "app" [.var "suc", n1], .con "app" [.var "suc", n2]] => Term.con "equateCon" [ctx, Term.con "nat" [], n1, n2]
      | _ => t

    def equateCon'Nat (t : Term) : Term :=
      match t with
      | .con "equateCon'" [ctx, .con "nat" [], t1, t2] => Term.con "equateNeutral" [ctx, t1, t2]
      | _ => t

    def equateCon'CircleBase (t : Term) : Term :=
      match t with
      | .con "equateCon'" [ctx, .con "circle" [], .con "base" [], .con "base" []] => Term.con "ok" []
      | _ => t

    def equateCon'CircleLoop (t : Term) : Term :=
      match t with
      | .con "equateCon'" [ctx, .con "circle" [], .con "app" [.var "loop", r1], .con "app" [.var "loop", r2]] => Term.con "equateDim" [ctx, r1, r2]
      | _ => t

    def equateCon'Circle (t : Term) : Term :=
      match t with
      | .con "equateCon'" [ctx, .con "circle" [], t1, t2] => Term.con "equateNeutral" [ctx, t1, t2]
      | _ => t

    def equateCon'Dim (t : Term) : Term :=
      match t with
      | .con "equateCon'" [ctx, .con "app" [.var "lit", .con "terminal" [.lit "𝕀"]], t1, t2] => Term.con "equateDim" [ctx, t1, t2]
      | _ => t

    def equateCon'Cof (t : Term) : Term :=
      match t with
      | .con "equateCon'" [ctx, .con "app" [.var "lit", .con "terminal" [.lit "𝔽"]], t1, t2] => Term.con "equateCof" [ctx, t1, t2]
      | _ => t

    def equateCon'Univ (t : Term) : Term :=
      match t with
      | .con "equateCon'" [ctx, .con "app" [.var "univ", l], t1, t2] => Term.con "equateTp" [ctx, t1, t2]
      | _ => t

    def equateCon'Other (t : Term) : Term :=
      match t with
      | .con "equateCon'" [ctx, tp, t1, t2] => Term.con "equateNeutral" [ctx, t1, t2]
      | _ => t

  end EquateCon

  section EquateNeutral

    def equateNeutralIx (t : Term) : Term :=
      match t with
      | .con "equateNeutral" [ctx, .con "app" [.var "ix", n], .con "app" [.var "ix", n_dup]] => Term.con "ok" []
      | _ => t

    def equateNeutralIxNeq (t : Term) : Term :=
      match t with
      | .con "equateNeutral" [ctx, .con "app" [.var "ix", n1], .con "app" [.var "ix", n2]] => Term.con "app" [Term.var "fail", Term.con "concat" [Term.con "terminal" [Term.lit "variables differ: "], n1, Term.con "terminal" [Term.lit " vs "], n2]]
      | _ => t

    def equateNeutralApp (t : Term) : Term :=
      match t with
      | .con "equateNeutral" [ctx, .con "app" [f1, a1], .con "app" [f2, a2]] => Term.con "andThen" [Term.con "equateNeutral" [ctx, f1, f2], Term.con "fun" [Term.con "_" [], Term.lit "=>", Term.con "equateNeutral" [ctx, a1, a2]]]
      | _ => t

    def equateNeutralPapp (t : Term) : Term :=
      match t with
      | .con "equateNeutral" [ctx, .con "papp" [p1, r1], .con "papp" [p2, r2]] => Term.con "andThen" [Term.con "equateNeutral" [ctx, p1, p2], Term.con "fun" [Term.con "_" [], Term.lit "=>", Term.con "equateDim" [ctx, r1, r2]]]
      | _ => t

    def equateNeutralFst (t : Term) : Term :=
      match t with
      | .con "equateNeutral" [ctx, .con "app" [.var "fst", p1], .con "app" [.var "fst", p2]] => Term.con "equateNeutral" [ctx, p1, p2]
      | _ => t

    def equateNeutralSnd (t : Term) : Term :=
      match t with
      | .con "equateNeutral" [ctx, .con "app" [.var "snd", p1], .con "app" [.var "snd", p2]] => Term.con "equateNeutral" [ctx, p1, p2]
      | _ => t

    def equateNeutralCoe (t : Term) : Term :=
      match t with
      | .con "equateNeutral" [ctx, .con "coe" [a1, r1, s1, t1], .con "coe" [a2, r2, s2, t2]] => Term.con "andThen" [Term.con "equateNeutral" [ctx, a1, a2], Term.con "fun" [Term.con "_" [], Term.lit "=>", Term.con "andThen" [Term.con "equateDim" [ctx, r1, r2], Term.con "fun" [Term.con "_" [], Term.lit "=>", Term.con "andThen" [Term.con "equateDim" [ctx, s1, s2], Term.con "fun" [Term.con "_" [], Term.lit "=>", Term.con "equateNeutral" [ctx, t1, t2]]]]]]]
      | _ => t

    def equateNeutralHCom (t : Term) : Term :=
      match t with
      | .con "equateNeutral" [ctx, .con "hcom" [a1, r1, s1, φ1, u1], .con "hcom" [a2, r2, s2, φ2, u2]] => Term.con "andThen" [Term.con "equateNeutral" [ctx, a1, a2], Term.con "fun" [Term.con "_" [], Term.lit "=>", Term.con "andThen" [Term.con "equateDim" [ctx, r1, r2], Term.con "fun" [Term.con "_" [], Term.lit "=>", Term.con "andThen" [Term.con "equateDim" [ctx, s1, s2], Term.con "fun" [Term.con "_" [], Term.lit "=>", Term.con "andThen" [Term.con "equateCof" [ctx, φ1, φ2], Term.con "fun" [Term.con "_" [], Term.lit "=>", Term.con "equateNeutral" [ctx, u1, u2]]]]]]]]]
      | _ => t

    def equateNeutralLit (t : Term) : Term :=
      match t with
      | .con "equateNeutral" [ctx, .con "app" [.var "lit", s], .con "app" [.var "lit", s_dup]] => Term.con "ok" []
      | _ => t

    def equateNeutralLitNeq (t : Term) : Term :=
      match t with
      | .con "equateNeutral" [ctx, .con "app" [.var "lit", s1], .con "app" [.var "lit", s2]] => Term.con "app" [Term.var "fail", Term.con "concat" [Term.con "terminal" [Term.lit "literals differ: "], s1, Term.con "terminal" [Term.lit " vs "], s2]]
      | _ => t

    def equateNeutralOther (t : Term) : Term :=
      match t with
      | .con "equateNeutral" [ctx, t1, t2] => Term.con "app" [Term.var "fail", Term.con "concat" [Term.con "terminal" [Term.lit "neutral terms not equal: "], t1, Term.con "terminal" [Term.lit " vs "], t2]]
      | _ => t

  end EquateNeutral

  section TopLevel

    def checkTpEq (t : Term) : Term :=
      match t with
      | .con "checkTpEq" [tp1, tp2] => Term.con "equateTp" [Term.con "convCtxEmpty" [], tp1, tp2]
      | _ => t

    def checkEq (t : Term) : Term :=
      match t with
      | .con "checkEq" [tp, t1, t2] => Term.con "equateCon" [Term.con "convCtxEmpty" [], tp, t1, t2]
      | _ => t

    def checkSubtype (t : Term) : Term :=
      match t with
      | .con "checkSubtype" [tp1, tp2] => Term.con "equateTp" [Term.con "convCtxEmpty" [], tp1, tp2]
      | _ => t

  end TopLevel

  section Helpers

    def convResultToBool (t : Term) : Term :=
      match t with
      | .con "app" [.var "toBool", .con "ok" []] => Term.con "true" []
      | _ => t

    def convResultToBoolFail (t : Term) : Term :=
      match t with
      | .con "app" [.var "toBool", .con "app" [.var "fail", msg]] => Term.con "false" []
      | _ => t

    def convResultToBoolBlocked (t : Term) : Term :=
      match t with
      | .con "app" [.var "toBool", .con "app" [.var "blocked", n]] => Term.con "false" []
      | _ => t

    def equal (t : Term) : Term :=
      match t with
      | .con "equal" [tp, t1, t2] => Term.con "app" [Term.var "toBool", Term.con "checkEq" [tp, t1, t2]]
      | _ => t

    def equalTp (t : Term) : Term :=
      match t with
      | .con "equalTp" [tp1, tp2] => Term.con "app" [Term.var "toBool", Term.con "checkTpEq" [tp1, tp2]]
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

    -- Derived conversion check for term
    def convterm (t1 t2 : Term) : Bool :=
      normalizeterm 1000 t1 == normalizeterm 1000 t2

  end Helpers

end Conversion