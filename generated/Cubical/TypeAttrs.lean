/-
  AUTO-GENERATED from .lego files
  Do not edit directly.
-/

import Lego.Algebra

open Lego

namespace TypeAttrs

  section ASTtoIR

    def astType (t : Term) : Term :=
      match t with
      | .con "app" [.var "ast", .con "type" []] => Term.con "app" [Term.var "univ", Term.con "num" [Term.con "number" [Term.lit "0"]]]
      | _ => t

    def astTypeLevel (t : Term) : Term :=
      match t with
      | .con "app" [.var "ast", .con "app" [.var "typeLevel", n]] => Term.con "app" [Term.var "univ", n]
      | _ => t

    def astInterval (t : Term) : Term :=
      match t with
      | .con "app" [.var "ast", .con "interval" []] => Term.con "app" [Term.var "lit", Term.con "terminal" [Term.lit "𝕀"]]
      | _ => t

    def astLamTyped (t : Term) : Term :=
      match t with
      | .con "app" [.var "ast", .con "lam" [.con "app" [.var "binders", .con "typedBinder" [x, A]], body]] => Term.con "lam" [x, A, Term.con "app" [Term.var "ast", body]]
      | _ => t

    def astLamSimple (t : Term) : Term :=
      match t with
      | .con "app" [.var "ast", .con "lam" [.con "app" [.var "binders", .con "app" [.var "simpleBinder", x]], body]] => Term.con "lam" [x, Term.con "hole" [], Term.con "app" [Term.var "ast", body]]
      | _ => t

    def astArrow (t : Term) : Term :=
      match t with
      | .con "app" [.var "ast", .con "Arrow" [A, B]] => Term.con "pi" [Term.con "terminal" [Term.lit "_"], Term.con "app" [Term.var "ast", A], Term.con "app" [Term.var "ast", B]]
      | _ => t

    def astPi (t : Term) : Term :=
      match t with
      | .con "app" [.var "ast", .con "Pi" [.con "cell" [x, A], B]] => Term.con "pi" [x, Term.con "app" [Term.var "ast", A], Term.con "app" [Term.var "ast", B]]
      | _ => t

    def astApp (t : Term) : Term :=
      match t with
      | .con "app" [.var "ast", .con "app" [f, .con "app" [.var "arg", x]]] => Term.con "app" [Term.con "app" [Term.var "ast", f], Term.con "app" [Term.var "ast", x]]
      | _ => t

    def astAppNoArg (t : Term) : Term :=
      match t with
      | .con "app" [.var "ast", .con "app" [.var "app", f]] => Term.con "app" [Term.var "ast", f]
      | _ => t

    def astProd (t : Term) : Term :=
      match t with
      | .con "app" [.var "ast", .con "Prod" [A, B]] => Term.con "sigma" [Term.con "terminal" [Term.lit "_"], Term.con "app" [Term.var "ast", A], Term.con "app" [Term.var "ast", B]]
      | _ => t

    def astSigma (t : Term) : Term :=
      match t with
      | .con "app" [.var "ast", .con "Sigma" [x, A, B]] => Term.con "sigma" [x, Term.con "app" [Term.var "ast", A], Term.con "app" [Term.var "ast", B]]
      | _ => t

    def astPair (t : Term) : Term :=
      match t with
      | .con "app" [.var "ast", .con "pair" [a, b]] => Term.con "pair" [Term.con "app" [Term.var "ast", a], Term.con "app" [Term.var "ast", b]]
      | _ => t

    def astPath (t : Term) : Term :=
      match t with
      | .con "app" [.var "ast", .con "path" [A, a, b]] => Term.con "path" [Term.con "app" [Term.var "ast", A], Term.con "app" [Term.var "ast", a], Term.con "app" [Term.var "ast", b]]
      | _ => t

    def astRefl (t : Term) : Term :=
      match t with
      | .con "app" [.var "ast", .con "refl" []] => Term.con "app" [Term.var "refl", Term.con "hole" []]
      | _ => t

    def astPathAbs (t : Term) : Term :=
      match t with
      | .con "app" [.var "ast", .con "pathAbs" [.con "app" [.var "dims", i], body, sys]] => Term.con "plam" [i, Term.con "app" [Term.var "ast", body], Term.con "app" [Term.var "ast", sys]]
      | _ => t

    def astPathAbsNoSys (t : Term) : Term :=
      match t with
      | .con "app" [.var "ast", .con "pathAbs" [.con "app" [.var "dims", i], body]] => Term.con "plam" [i, Term.con "app" [Term.var "ast", body], Term.con "sys" []]
      | _ => t

    def astCoe (t : Term) : Term :=
      match t with
      | .con "app" [.var "ast", .con "coe" [r, r', A, a]] => Term.con "coe" [Term.con "app" [Term.var "ast", r], Term.con "app" [Term.var "ast", r'], Term.con "app" [Term.var "ast", A], Term.con "app" [Term.var "ast", a]]
      | _ => t

    def astHcom (t : Term) : Term :=
      match t with
      | .con "app" [.var "ast", .con "hcom" [r, r', A, cap, sys]] => Term.con "hcom" [Term.con "app" [Term.var "ast", A], Term.con "app" [Term.var "ast", r], Term.con "app" [Term.var "ast", r'], Term.con "cof_top" [Term.con "app" [Term.var "ast", sys], Term.con "app" [Term.var "ast", cap]]]
      | _ => t

    def astComp (t : Term) : Term :=
      match t with
      | .con "app" [.var "ast", .con "comp" [r, r', A, cap, sys]] => Term.con "com" [Term.con "app" [Term.var "ast", A], Term.con "app" [Term.var "ast", r], Term.con "app" [Term.var "ast", r'], Term.con "cof_top" [Term.con "app" [Term.var "ast", sys], Term.con "app" [Term.var "ast", cap]]]
      | _ => t

    def astLet (t : Term) : Term :=
      match t with
      | .con "app" [.var "ast", .con "let" [x, A, v, body]] => Term.con "let" [x, Term.con "app" [Term.var "ast", A], Term.con "app" [Term.var "ast", v], Term.con "app" [Term.var "ast", body]]
      | _ => t

    def astProjFst (t : Term) : Term :=
      match t with
      | .con "app" [.var "ast", .con "proj" [e, .con "app" [.var "field", .con "terminal" [.lit "fst"]]]] => Term.con "app" [Term.var "fst", Term.con "app" [Term.var "ast", e]]
      | _ => t

    def astProjSnd (t : Term) : Term :=
      match t with
      | .con "app" [.var "ast", .con "proj" [e, .con "app" [.var "field", .con "terminal" [.lit "snd"]]]] => Term.con "app" [Term.var "snd", Term.con "app" [Term.var "ast", e]]
      | _ => t

    def astCircle (t : Term) : Term :=
      match t with
      | .con "app" [.var "ast", .con "circle" []] => Term.con "S1" []
      | _ => t

    def astBase (t : Term) : Term :=
      match t with
      | .con "app" [.var "ast", .con "base" []] => Term.con "base" []
      | _ => t

    def astLoop (t : Term) : Term :=
      match t with
      | .con "app" [.var "ast", .con "app" [.var "loop", i]] => Term.con "app" [Term.var "loop", Term.con "app" [Term.var "ast", i]]
      | _ => t

    def astNat (t : Term) : Term :=
      match t with
      | .con "app" [.var "ast", .con "nat" []] => Term.con "nat" []
      | _ => t

    def astZero (t : Term) : Term :=
      match t with
      | .con "app" [.var "ast", .con "zero" []] => Term.con "zero" []
      | _ => t

    def astSuc (t : Term) : Term :=
      match t with
      | .con "app" [.var "ast", .con "app" [.var "suc", n]] => Term.con "app" [Term.var "suc", Term.con "app" [Term.var "ast", n]]
      | _ => t

    def astVtype (t : Term) : Term :=
      match t with
      | .con "app" [.var "ast", .con "Vtype" [r, A, B, e]] => Term.con "vtype" [Term.con "app" [Term.var "ast", r], Term.con "app" [Term.var "ast", A], Term.con "app" [Term.var "ast", B], Term.con "app" [Term.var "ast", e]]
      | _ => t

    def astVin (t : Term) : Term :=
      match t with
      | .con "app" [.var "ast", .con "Vin" [r, a, b]] => Term.con "vin" [Term.con "app" [Term.var "ast", r], Term.con "app" [Term.var "ast", a], Term.con "app" [Term.var "ast", b]]
      | _ => t

    def astVproj (t : Term) : Term :=
      match t with
      | .con "app" [.var "ast", .con "Vproj" [r, v, A, B, e]] => Term.con "vproj" [Term.con "app" [Term.var "ast", r], Term.con "app" [Term.var "ast", A], Term.con "app" [Term.var "ast", B], Term.con "app" [Term.var "ast", e], Term.con "app" [Term.var "ast", v]]
      | _ => t

    def astGlue (t : Term) : Term :=
      match t with
      | .con "app" [.var "ast", .con "Glue" [A, phi, T, e]] => Term.con "glue" [Term.con "app" [Term.var "ast", A], Term.con "app" [Term.var "ast", phi], Term.con "app" [Term.var "ast", T], Term.con "app" [Term.var "ast", e]]
      | _ => t

    def astGlueEl (t : Term) : Term :=
      match t with
      | .con "app" [.var "ast", .con "glue" [t, a]] => Term.con "glueEl" [Term.con "app" [Term.var "ast", t], Term.con "app" [Term.var "ast", a]]
      | _ => t

    def astUnglue (t : Term) : Term :=
      match t with
      | .con "app" [.var "ast", .con "app" [.var "unglue", g]] => Term.con "app" [Term.var "unglue", Term.con "app" [Term.var "ast", g]]
      | _ => t

    def astDef (t : Term) : Term :=
      match t with
      | .con "app" [.var "ast", .con "def" [name, args, type, body]] => Term.con "def" [name, Term.con "app" [Term.var "ast", args], Term.con "app" [Term.var "ast", type], Term.con "app" [Term.var "ast", body]]
      | _ => t

    def astDefInfer (t : Term) : Term :=
      match t with
      | .con "app" [.var "ast", .con "defInfer" [name, args, body]] => Term.con "def" [name, Term.con "app" [Term.var "ast", args], Term.con "hole" [], Term.con "app" [Term.var "ast", body]]
      | _ => t

  end ASTtoIR

  section IRtoAST

    def irUniv0 (t : Term) : Term :=
      match t with
      | .con "app" [.var "unast", .con "app" [.var "univ", .con "num" [.con "number" [.lit "0"]]]] => Term.con "type" []
      | _ => t

    def irUnivN (t : Term) : Term :=
      match t with
      | .con "app" [.var "unast", .con "app" [.var "univ", n]] => Term.con "app" [Term.var "typeLevel", n]
      | _ => t

    def irPiArrow (t : Term) : Term :=
      match t with
      | .con "app" [.var "unast", .con "pi" [.con "terminal" [.lit "_"], A, B]] => Term.con "Arrow" [Term.con "app" [Term.var "unast", A], Term.con "app" [Term.var "unast", B]]
      | _ => t

    def irPiDep (t : Term) : Term :=
      match t with
      | .con "app" [.var "unast", .con "pi" [x, A, B]] => Term.con "Pi" [Term.con "cell" [x, Term.con "app" [Term.var "unast", A]], Term.con "app" [Term.var "unast", B]]
      | _ => t

    def irSigmaProd (t : Term) : Term :=
      match t with
      | .con "app" [.var "unast", .con "sigma" [.con "terminal" [.lit "_"], A, B]] => Term.con "Prod" [Term.con "app" [Term.var "unast", A], Term.con "app" [Term.var "unast", B]]
      | _ => t

    def irSigmaDep (t : Term) : Term :=
      match t with
      | .con "app" [.var "unast", .con "sigma" [x, A, B]] => Term.con "Sigma" [x, Term.con "app" [Term.var "unast", A], Term.con "app" [Term.var "unast", B]]
      | _ => t

    def irLam (t : Term) : Term :=
      match t with
      | .con "app" [.var "unast", .con "app" [.var "lam", body]] => Term.con "lam" [Term.con "app" [Term.var "binders", Term.con "app" [Term.var "simpleBinder", Term.con "terminal" [Term.lit "_"]]], Term.con "app" [Term.var "unast", body]]
      | _ => t

    def irApp (t : Term) : Term :=
      match t with
      | .con "app" [.var "unast", .con "app" [f, x]] => Term.con "app" [Term.con "app" [Term.var "unast", f], Term.con "app" [Term.var "arg", Term.con "app" [Term.var "unast", x]]]
      | _ => t

    def irPair (t : Term) : Term :=
      match t with
      | .con "app" [.var "unast", .con "pair" [a, b]] => Term.con "pair" [Term.con "app" [Term.var "unast", a], Term.con "app" [Term.var "unast", b]]
      | _ => t

    def irFst (t : Term) : Term :=
      match t with
      | .con "app" [.var "unast", .con "app" [.var "fst", e]] => Term.con "proj" [Term.con "app" [Term.var "unast", e], Term.con "app" [Term.var "field", Term.con "terminal" [Term.lit "fst"]]]
      | _ => t

    def irSnd (t : Term) : Term :=
      match t with
      | .con "app" [.var "unast", .con "app" [.var "snd", e]] => Term.con "proj" [Term.con "app" [Term.var "unast", e], Term.con "app" [Term.var "field", Term.con "terminal" [Term.lit "snd"]]]
      | _ => t

    def irPlam (t : Term) : Term :=
      match t with
      | .con "app" [.var "unast", .con "app" [.var "plam", body]] => Term.con "pathAbs" [Term.con "app" [Term.var "dims", Term.con "terminal" [Term.lit "_"]], Term.con "app" [Term.var "unast", body]]
      | _ => t

    def irPapp (t : Term) : Term :=
      match t with
      | .con "app" [.var "unast", .con "papp" [p, i]] => Term.con "app" [Term.con "app" [Term.var "unast", p], Term.con "app" [Term.var "arg", Term.con "app" [Term.var "unast", i]]]
      | _ => t

    def irNat (t : Term) : Term :=
      match t with
      | .con "app" [.var "unast", .con "nat" []] => Term.con "nat" []
      | _ => t

    def irZero (t : Term) : Term :=
      match t with
      | .con "app" [.var "unast", .con "zero" []] => Term.con "zero" []
      | _ => t

    def irSuc (t : Term) : Term :=
      match t with
      | .con "app" [.var "unast", .con "app" [.var "suc", n]] => Term.con "app" [Term.var "suc", Term.con "app" [Term.var "unast", n]]
      | _ => t

    def irCircle (t : Term) : Term :=
      match t with
      | .con "app" [.var "unast", .con "S1" []] => Term.con "circle" []
      | _ => t

    def irBase (t : Term) : Term :=
      match t with
      | .con "app" [.var "unast", .con "base" []] => Term.con "base" []
      | _ => t

    def irLoop (t : Term) : Term :=
      match t with
      | .con "app" [.var "unast", .con "app" [.var "loop", i]] => Term.con "app" [Term.var "loop", Term.con "app" [Term.var "unast", i]]
      | _ => t

    def irDim0 (t : Term) : Term :=
      match t with
      | .con "app" [.var "unast", .con "dim0" []] => Term.con "app" [Term.var "lit", Term.con "terminal" [Term.lit "0"]]
      | _ => t

    def irDim1 (t : Term) : Term :=
      match t with
      | .con "app" [.var "unast", .con "dim1" []] => Term.con "app" [Term.var "lit", Term.con "terminal" [Term.lit "1"]]
      | _ => t

    def irDefault (t : Term) : Term :=
      match t with
      | .con "app" [.var "unast", e] => e
      | _ => t

  end IRtoAST

  section TypeAttr

    def synTypeUniv (t : Term) : Term :=
      match t with
      | .con "synType" [.con "app" [.var "univ", n], ctx] => Term.con "app" [Term.var "tacOk", Term.con "app" [Term.var "univ", Term.con "app" [Term.var "succ", n]]]
      | _ => t

    def synTypeNat (t : Term) : Term :=
      match t with
      | .con "synType" [.con "nat" [], ctx] => Term.con "app" [Term.var "tacOk", Term.con "app" [Term.var "univ", Term.con "num" [Term.con "number" [Term.lit "0"]]]]
      | _ => t

    def synTypeCircle (t : Term) : Term :=
      match t with
      | .con "synType" [.con "S1" [], ctx] => Term.con "app" [Term.var "tacOk", Term.con "app" [Term.var "univ", Term.con "num" [Term.con "number" [Term.lit "0"]]]]
      | _ => t

    def synTypeVar (t : Term) : Term :=
      match t with
      | .con "synType" [.con "app" [.var "ix", n], ctx] => Term.con "tpCtxLookup" [ctx, n]
      | _ => t

    def synTypePi (t : Term) : Term :=
      match t with
      | .con "synType" [.con "pi" [dom, cod], ctx] => Term.con "tacResultBind" [Term.con "synType" [dom, ctx], Term.con "app" [Term.var "lam", Term.con "letIn" [Term.lit "(", Term.lit "let", Term.lit "$", Term.var "l1", Term.lit "=", Term.con "app" [Term.var "univLevel", Term.con "app" [Term.var "ix", Term.con "num" [Term.con "number" [Term.lit "0"]]]], Term.lit "in", Term.con "tacResultBind" [Term.con "synType" [cod, Term.con "tpCtxExtend" [ctx, dom]], Term.con "app" [Term.var "lam", Term.con "letIn" [Term.lit "(", Term.lit "let", Term.lit "$", Term.var "l2", Term.lit "=", Term.con "app" [Term.var "univLevel", Term.con "app" [Term.var "ix", Term.con "num" [Term.con "number" [Term.lit "0"]]]], Term.lit "in", Term.con "app" [Term.var "tacOk", Term.con "app" [Term.var "univ", Term.con "max" [Term.var "l1", Term.var "l2"]]], Term.lit ")"]]], Term.lit ")"]]]
      | _ => t

    def synTypeSigma (t : Term) : Term :=
      match t with
      | .con "synType" [.con "sigma" [base, fam], ctx] => Term.con "tacResultBind" [Term.con "synType" [base, ctx], Term.con "app" [Term.var "lam", Term.con "letIn" [Term.lit "(", Term.lit "let", Term.lit "$", Term.var "l1", Term.lit "=", Term.con "app" [Term.var "univLevel", Term.con "app" [Term.var "ix", Term.con "num" [Term.con "number" [Term.lit "0"]]]], Term.lit "in", Term.con "tacResultBind" [Term.con "synType" [fam, Term.con "tpCtxExtend" [ctx, base]], Term.con "app" [Term.var "lam", Term.con "letIn" [Term.lit "(", Term.lit "let", Term.lit "$", Term.var "l2", Term.lit "=", Term.con "app" [Term.var "univLevel", Term.con "app" [Term.var "ix", Term.con "num" [Term.con "number" [Term.lit "0"]]]], Term.lit "in", Term.con "app" [Term.var "tacOk", Term.con "app" [Term.var "univ", Term.con "max" [Term.var "l1", Term.var "l2"]]], Term.lit ")"]]], Term.lit ")"]]]
      | _ => t

    def synTypeLam (t : Term) : Term :=
      match t with
      | .con "synType" [.con "app" [.var "lam", body], ctx] => Term.con "app" [Term.var "tacError", Term.con "terminal" [Term.lit "cannot synthesize type of lambda"]]
      | _ => t

    def synTypeApp (t : Term) : Term :=
      match t with
      | .con "synType" [.con "app" [f, x], ctx] => Term.con "tacResultBind" [Term.con "synType" [f, ctx], Term.con "app" [Term.var "lam", Term.con "caseExpr" [Term.lit "(", Term.lit "case", Term.con "app" [Term.var "ix", Term.con "num" [Term.con "number" [Term.lit "0"]]], Term.con "arm" [Term.lit "(", Term.var "pi", Term.var "dom", Term.var "cod", Term.lit ")", Term.lit "=>", Term.con "app" [Term.var "tacOk", Term.con "subst" [Term.con "num" [Term.con "number" [Term.lit "0"]], x, Term.var "cod"]]], Term.con "arm" [Term.var "_", Term.lit "=>", Term.con "app" [Term.var "tacError", Term.con "terminal" [Term.lit "expected function type"]]], Term.lit ")"]]]
      | _ => t

    def synTypeFst (t : Term) : Term :=
      match t with
      | .con "synType" [.con "app" [.var "fst", e], ctx] => Term.con "tacResultBind" [Term.con "synType" [e, ctx], Term.con "app" [Term.var "lam", Term.con "caseExpr" [Term.lit "(", Term.lit "case", Term.con "app" [Term.var "ix", Term.con "num" [Term.con "number" [Term.lit "0"]]], Term.con "arm" [Term.lit "(", Term.var "sigma", Term.var "base", Term.var "fam", Term.lit ")", Term.lit "=>", Term.con "app" [Term.var "tacOk", Term.var "base"]], Term.con "arm" [Term.var "_", Term.lit "=>", Term.con "app" [Term.var "tacError", Term.con "terminal" [Term.lit "expected sigma type"]]], Term.lit ")"]]]
      | _ => t

    def synTypeSnd (t : Term) : Term :=
      match t with
      | .con "synType" [.con "app" [.var "snd", e], ctx] => Term.con "tacResultBind" [Term.con "synType" [e, ctx], Term.con "app" [Term.var "lam", Term.con "caseExpr" [Term.lit "(", Term.lit "case", Term.con "app" [Term.var "ix", Term.con "num" [Term.con "number" [Term.lit "0"]]], Term.con "arm" [Term.lit "(", Term.var "sigma", Term.var "base", Term.var "fam", Term.lit ")", Term.lit "=>", Term.con "app" [Term.var "tacOk", Term.con "subst" [Term.con "num" [Term.con "number" [Term.lit "0"]], Term.con "app" [Term.var "fst", e], Term.var "fam"]]], Term.con "arm" [Term.var "_", Term.lit "=>", Term.con "app" [Term.var "tacError", Term.con "terminal" [Term.lit "expected sigma type"]]], Term.lit ")"]]]
      | _ => t

    def synTypeZero (t : Term) : Term :=
      match t with
      | .con "synType" [.con "zero" [], ctx] => Term.con "app" [Term.var "tacOk", Term.con "nat" []]
      | _ => t

    def synTypeSuc (t : Term) : Term :=
      match t with
      | .con "synType" [.con "app" [.var "suc", n], ctx] => Term.con "tacResultBind" [Term.con "synType" [n, ctx], Term.con "app" [Term.var "lam", Term.con "caseExpr" [Term.lit "(", Term.lit "case", Term.con "app" [Term.var "ix", Term.con "num" [Term.con "number" [Term.lit "0"]]], Term.con "arm" [Term.var "nat", Term.lit "=>", Term.con "app" [Term.var "tacOk", Term.con "nat" []]], Term.con "arm" [Term.var "_", Term.lit "=>", Term.con "app" [Term.var "tacError", Term.con "terminal" [Term.lit "expected nat"]]], Term.lit ")"]]]
      | _ => t

    def synTypeBase (t : Term) : Term :=
      match t with
      | .con "synType" [.con "base" [], ctx] => Term.con "app" [Term.var "tacOk", Term.con "S1" []]
      | _ => t

    def synTypeLoop (t : Term) : Term :=
      match t with
      | .con "synType" [.con "app" [.var "loop", i], ctx] => Term.con "app" [Term.var "tacOk", Term.con "S1" []]
      | _ => t

    def univLevel (t : Term) : Term :=
      match t with
      | .con "app" [.var "univLevel", .con "app" [.var "univ", n]] => n
      | _ => t

    def univLevelDefault (t : Term) : Term :=
      match t with
      | .con "app" [.var "univLevel", e] => Term.con "num" [Term.con "number" [Term.lit "0"]]
      | _ => t

  end TypeAttr

  section CtxAttr

    def inhCtxLam (t : Term) : Term :=
      match t with
      | .con "inhCtx" [.con "app" [.var "lam", body], .con "tpCtx" [.con "labeledArg" [.var "types", .lit ":", ts], .con "labeledArg" [.var "cofs", .lit ":", cs]], expectedTy] => Term.con "caseExpr" [Term.lit "(", Term.lit "case", expectedTy, Term.con "arm" [Term.lit "(", Term.var "pi", Term.var "dom", Term.var "cod", Term.lit ")", Term.lit "=>", Term.con "inhCtx" [body, Term.con "tpCtx" [Term.con "labeledArg" [Term.var "types", Term.lit ":", Term.con "tuple" [Term.var "dom", ts]], Term.con "labeledArg" [Term.var "cofs", Term.lit ":", cs]], Term.var "cod"]], Term.con "arm" [Term.var "_", Term.lit "=>", Term.con "app" [Term.var "tacError", Term.con "terminal" [Term.lit "expected pi type for lambda"]]], Term.lit ")"]
      | _ => t

    def inhCtxPlam (t : Term) : Term :=
      match t with
      | .con "inhCtx" [.con "app" [.var "plam", body], .con "tpCtx" [.con "labeledArg" [.var "types", .lit ":", ts], .con "labeledArg" [.var "cofs", .lit ":", cs]], expectedTy] => Term.con "inhCtx" [body, Term.con "tpCtx" [Term.con "labeledArg" [Term.var "types", Term.lit ":", Term.con "tuple" [Term.con "app" [Term.lit "(", Term.con "lit" [], Term.con "terminal" [Term.lit "𝕀"], Term.lit ")"], ts]], Term.con "labeledArg" [Term.var "cofs", Term.lit ":", cs]], expectedTy]
      | _ => t

    def inhCtxPair (t : Term) : Term :=
      match t with
      | .con "inhCtx" [.con "pair" [a, b], ctx, expectedTy] => Term.con "caseExpr" [Term.lit "(", Term.lit "case", expectedTy, Term.con "arm" [Term.lit "(", Term.var "sigma", Term.var "base", Term.var "fam", Term.lit ")", Term.lit "=>", Term.con "letIn" [Term.lit "(", Term.lit "let", Term.lit "$", Term.var "ctxA", Term.lit "=", Term.con "inhCtx" [a, ctx, Term.var "base"], Term.lit "in", Term.con "letIn" [Term.lit "(", Term.lit "let", Term.lit "$", Term.var "famSubst", Term.lit "=", Term.con "subst" [Term.con "num" [Term.con "number" [Term.lit "0"]], a, Term.var "fam"], Term.lit "in", Term.con "inhCtx" [b, ctx, Term.var "famSubst"], Term.lit ")"], Term.lit ")"]], Term.con "arm" [Term.var "_", Term.lit "=>", Term.con "app" [Term.var "tacError", Term.con "terminal" [Term.lit "expected sigma type for pair"]]], Term.lit ")"]
      | _ => t

  end CtxAttr

  section ElabAttr

    def elabTerm (t : Term) : Term :=
      match t with
      | .con "elab" [term, ctx] => Term.con "tacResultBind" [Term.con "synType" [term, ctx], Term.con "app" [Term.var "lam", Term.con "app" [Term.var "tacOk", Term.con "tuple" [Term.lit "(", term, Term.lit ",", Term.con "app" [Term.var "ix", Term.con "num" [Term.con "number" [Term.lit "0"]]], Term.lit ")"]]]]
      | _ => t

    def elabCheck (t : Term) : Term :=
      match t with
      | .con "elabCheck" [term, ctx, expectedTy] => Term.con "app" [Term.var "tacOk", term]
      | _ => t

    def elabInfer (t : Term) : Term :=
      match t with
      | .con "elabInfer" [term, ctx] => Term.con "synType" [term, ctx]
      | _ => t

  end ElabAttr

  section BiDirect

    def biCheck (t : Term) : Term :=
      match t with
      | .con "biCheck" [term, ctx, expectedTy] => Term.con "tacResultBind" [Term.con "synType" [term, ctx], Term.con "app" [Term.var "lam", Term.con "if" [Term.con "conv" [Term.con "app" [Term.var "ix", Term.con "num" [Term.con "number" [Term.lit "0"]]], expectedTy], Term.con "then" [Term.con "app" [Term.var "tacOk", term], Term.var "else"], Term.con "app" [Term.var "tacError", Term.con "terminal" [Term.lit "type mismatch"]]]]]
      | _ => t

    def biInfer (t : Term) : Term :=
      match t with
      | .con "biInfer" [term, ctx] => Term.con "tacResultBind" [Term.con "synType" [term, ctx], Term.con "app" [Term.var "lam", Term.con "app" [Term.var "tacOk", Term.con "tuple" [Term.lit "(", term, Term.lit ",", Term.con "app" [Term.var "ix", Term.con "num" [Term.con "number" [Term.lit "0"]]], Term.lit ")"]]]]
      | _ => t

    def biSynth (t : Term) : Term :=
      match t with
      | .con "biSynth" [.con "app" [.var "lam", body], ctx] => Term.con "app" [Term.var "tacError", Term.con "terminal" [Term.lit "cannot synthesize lambda"]]
      | _ => t

    def biSynthApp (t : Term) : Term :=
      match t with
      | .con "biSynth" [.con "app" [f, x], ctx] => Term.con "tacResultBind" [Term.con "biInfer" [f, ctx], Term.con "app" [Term.var "lam", Term.con "caseExpr" [Term.lit "(", Term.lit "case", Term.con "app" [Term.var "snd", Term.con "app" [Term.var "ix", Term.con "num" [Term.con "number" [Term.lit "0"]]]], Term.con "arm" [Term.lit "(", Term.var "pi", Term.var "dom", Term.var "cod", Term.lit ")", Term.lit "=>", Term.con "tacResultBind" [Term.con "biCheck" [x, ctx, Term.var "dom"], Term.con "app" [Term.var "lam", Term.con "app" [Term.var "tacOk", Term.con "tuple" [Term.lit "(", Term.con "app" [Term.con "app" [Term.var "fst", Term.con "app" [Term.var "ix", Term.con "num" [Term.con "number" [Term.lit "1"]]]], Term.con "app" [Term.var "ix", Term.con "num" [Term.con "number" [Term.lit "0"]]]], Term.lit ",", Term.con "subst" [Term.con "num" [Term.con "number" [Term.lit "0"]], x, Term.var "cod"], Term.lit ")"]]]]], Term.con "arm" [Term.var "_", Term.lit "=>", Term.con "app" [Term.var "tacError", Term.con "terminal" [Term.lit "expected function type"]]], Term.lit ")"]]]
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

  end BiDirect

end TypeAttrs