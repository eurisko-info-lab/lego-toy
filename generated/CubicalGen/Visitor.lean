/-
  AUTO-GENERATED from .lego files
  Do not edit directly.
-/

import Lego.Algebra

set_option linter.unusedVariables false

open Lego

namespace Visitor

  section VisitorState

    def vstateEmpty (t : Term) : Term :=
      match t with
      | .con "vstateEmpty" [] => Term.con "app" [Term.var "vstate", Term.con "num" [Term.con "number" [Term.lit "0"]]]
      | _ => t

    def vstateDepth (t : Term) : Term :=
      match t with
      | .con "app" [.var "vstateDepth", .con "app" [.var "vstate", d]] => d
      | _ => t

    def vstateIncr (t : Term) : Term :=
      match t with
      | .con "app" [.var "vstateIncr", .con "app" [.var "vstate", d]] => Term.con "app" [Term.var "vstate", Term.con "app" [Term.var "suc", d]]
      | _ => t

  end VisitorState

  section BinderInfo



  end BinderInfo

  section Child

    def childExpr (t : Term) : Term :=
      match t with
      | .con "app" [.var "childExpr", .con "child" [e, bi]] => e
      | _ => t

    def childBinder (t : Term) : Term :=
      match t with
      | .con "app" [.var "childBinder", .con "child" [e, bi]] => bi
      | _ => t

  end Child

  section ExprShape



  end ExprShape

  section Shape

    def shapeIx (t : Term) : Term :=
      match t with
      | .con "app" [.var "exprShape", .con "app" [.var "ix", n]] => Term.con "shape" [Term.con "unit" [Term.lit "(", Term.lit ")"], Term.con "terminal" [Term.lit "ix"]]
      | _ => t

    def shapeLit (t : Term) : Term :=
      match t with
      | .con "app" [.var "exprShape", .con "app" [.var "lit", s]] => Term.con "shape" [Term.con "unit" [Term.lit "(", Term.lit ")"], Term.con "terminal" [Term.lit "lit"]]
      | _ => t

    def shapeDim0 (t : Term) : Term :=
      match t with
      | .con "app" [.var "exprShape", .con "dim0" []] => Term.con "shape" [Term.con "unit" [Term.lit "(", Term.lit ")"], Term.con "terminal" [Term.lit "dim0"]]
      | _ => t

    def shapeDim1 (t : Term) : Term :=
      match t with
      | .con "app" [.var "exprShape", .con "dim1" []] => Term.con "shape" [Term.con "unit" [Term.lit "(", Term.lit ")"], Term.con "terminal" [Term.lit "dim1"]]
      | _ => t

    def shapeDimVar (t : Term) : Term :=
      match t with
      | .con "app" [.var "exprShape", .con "app" [.var "dimVar", n]] => Term.con "shape" [Term.con "unit" [Term.lit "(", Term.lit ")"], Term.con "terminal" [Term.lit "dimVar"]]
      | _ => t

    def shapeCofTop (t : Term) : Term :=
      match t with
      | .con "app" [.var "exprShape", .con "cof_top" []] => Term.con "shape" [Term.con "unit" [Term.lit "(", Term.lit ")"], Term.con "terminal" [Term.lit "cof_top"]]
      | _ => t

    def shapeCofBot (t : Term) : Term :=
      match t with
      | .con "app" [.var "exprShape", .con "cof_bot" []] => Term.con "shape" [Term.con "unit" [Term.lit "(", Term.lit ")"], Term.con "terminal" [Term.lit "cof_bot"]]
      | _ => t

    def shapeNat (t : Term) : Term :=
      match t with
      | .con "app" [.var "exprShape", .con "nat" []] => Term.con "shape" [Term.con "unit" [Term.lit "(", Term.lit ")"], Term.con "terminal" [Term.lit "nat"]]
      | _ => t

    def shapeZero (t : Term) : Term :=
      match t with
      | .con "app" [.var "exprShape", .con "zero" []] => Term.con "shape" [Term.con "unit" [Term.lit "(", Term.lit ")"], Term.con "terminal" [Term.lit "zero"]]
      | _ => t

    def shapeCircle (t : Term) : Term :=
      match t with
      | .con "app" [.var "exprShape", .con "circle" []] => Term.con "shape" [Term.con "unit" [Term.lit "(", Term.lit ")"], Term.con "terminal" [Term.lit "circle"]]
      | _ => t

    def shapeBase (t : Term) : Term :=
      match t with
      | .con "app" [.var "exprShape", .con "base" []] => Term.con "shape" [Term.con "unit" [Term.lit "(", Term.lit ")"], Term.con "terminal" [Term.lit "base"]]
      | _ => t

    def shapeUniv (t : Term) : Term :=
      match t with
      | .con "app" [.var "exprShape", .con "app" [.var "univ", l]] => Term.con "shape" [Term.con "unit" [Term.lit "(", Term.lit ")"], Term.con "terminal" [Term.lit "univ"]]
      | _ => t

    def shapeFst (t : Term) : Term :=
      match t with
      | .con "app" [.var "exprShape", .con "app" [.var "fst", e]] => Term.con "shape" [Term.con "app" [Term.lit "(", Term.con "child" [], e, Term.con "binfoNone" [], Term.lit ")"], Term.con "terminal" [Term.lit "fst"]]
      | _ => t

    def shapeSnd (t : Term) : Term :=
      match t with
      | .con "app" [.var "exprShape", .con "app" [.var "snd", e]] => Term.con "shape" [Term.con "app" [Term.lit "(", Term.con "child" [], e, Term.con "binfoNone" [], Term.lit ")"], Term.con "terminal" [Term.lit "snd"]]
      | _ => t

    def shapeSuc (t : Term) : Term :=
      match t with
      | .con "app" [.var "exprShape", .con "app" [.var "suc", e]] => Term.con "shape" [Term.con "app" [Term.lit "(", Term.con "child" [], e, Term.con "binfoNone" [], Term.lit ")"], Term.con "terminal" [Term.lit "suc"]]
      | _ => t

    def shapeRefl (t : Term) : Term :=
      match t with
      | .con "app" [.var "exprShape", .con "app" [.var "refl", e]] => Term.con "shape" [Term.con "app" [Term.lit "(", Term.con "child" [], e, Term.con "binfoNone" [], Term.lit ")"], Term.con "terminal" [Term.lit "refl"]]
      | _ => t

    def shapeLoop (t : Term) : Term :=
      match t with
      | .con "app" [.var "exprShape", .con "app" [.var "loop", r]] => Term.con "shape" [Term.con "app" [Term.lit "(", Term.con "child" [], r, Term.con "binfoNone" [], Term.lit ")"], Term.con "terminal" [Term.lit "loop"]]
      | _ => t

    def shapeSubIn (t : Term) : Term :=
      match t with
      | .con "app" [.var "exprShape", .con "app" [.var "subIn", e]] => Term.con "shape" [Term.con "app" [Term.lit "(", Term.con "child" [], e, Term.con "binfoNone" [], Term.lit ")"], Term.con "terminal" [Term.lit "subIn"]]
      | _ => t

    def shapeSubOut (t : Term) : Term :=
      match t with
      | .con "app" [.var "exprShape", .con "app" [.var "subOut", e]] => Term.con "shape" [Term.con "app" [Term.lit "(", Term.con "child" [], e, Term.con "binfoNone" [], Term.lit ")"], Term.con "terminal" [Term.lit "subOut"]]
      | _ => t

    def shapeLam (t : Term) : Term :=
      match t with
      | .con "app" [.var "exprShape", .con "app" [.var "lam", body]] => Term.con "shape" [Term.con "app" [Term.lit "(", Term.con "child" [], body, Term.con "app" [Term.var "binfoTerm", Term.con "num" [Term.con "number" [Term.lit "1"]]], Term.lit ")"], Term.con "terminal" [Term.lit "lam"]]
      | _ => t

    def shapePlam (t : Term) : Term :=
      match t with
      | .con "app" [.var "exprShape", .con "app" [.var "plam", body]] => Term.con "shape" [Term.con "app" [Term.lit "(", Term.con "child" [], body, Term.con "app" [Term.var "binfoDim", Term.con "num" [Term.con "number" [Term.lit "1"]]], Term.lit ")"], Term.con "terminal" [Term.lit "plam"]]
      | _ => t

    def shapeApp (t : Term) : Term :=
      match t with
      | .con "app" [.var "exprShape", .con "app" [f, a]] => Term.con "shape" [Term.con "tuple" [Term.con "app" [Term.lit "(", Term.con "child" [], f, Term.con "binfoNone" [], Term.lit ")"], Term.con "child" [a, Term.con "binfoNone" []]], Term.con "terminal" [Term.lit "app"]]
      | _ => t

    def shapePair (t : Term) : Term :=
      match t with
      | .con "app" [.var "exprShape", .con "pair" [a, b]] => Term.con "shape" [Term.con "tuple" [Term.con "app" [Term.lit "(", Term.con "child" [], a, Term.con "binfoNone" [], Term.lit ")"], Term.con "child" [b, Term.con "binfoNone" []]], Term.con "terminal" [Term.lit "pair"]]
      | _ => t

    def shapePapp (t : Term) : Term :=
      match t with
      | .con "app" [.var "exprShape", .con "papp" [p, r]] => Term.con "shape" [Term.con "tuple" [Term.con "app" [Term.lit "(", Term.con "child" [], p, Term.con "binfoNone" [], Term.lit ")"], Term.con "child" [r, Term.con "binfoNone" []]], Term.con "terminal" [Term.lit "papp"]]
      | _ => t

    def shapeCofEq (t : Term) : Term :=
      match t with
      | .con "app" [.var "exprShape", .con "cof_eq" [r, s]] => Term.con "shape" [Term.con "tuple" [Term.con "app" [Term.lit "(", Term.con "child" [], r, Term.con "binfoNone" [], Term.lit ")"], Term.con "child" [s, Term.con "binfoNone" []]], Term.con "terminal" [Term.lit "cof_eq"]]
      | _ => t

    def shapeCofAnd (t : Term) : Term :=
      match t with
      | .con "app" [.var "exprShape", .con "cof_and" [φ, ψ]] => Term.con "shape" [Term.con "tuple" [Term.con "app" [Term.lit "(", Term.con "child" [], φ, Term.con "binfoNone" [], Term.lit ")"], Term.con "child" [ψ, Term.con "binfoNone" []]], Term.con "terminal" [Term.lit "cof_and"]]
      | _ => t

    def shapeCofOr (t : Term) : Term :=
      match t with
      | .con "app" [.var "exprShape", .con "cof_or" [φ, ψ]] => Term.con "shape" [Term.con "tuple" [Term.con "app" [Term.lit "(", Term.con "child" [], φ, Term.con "binfoNone" [], Term.lit ")"], Term.con "child" [ψ, Term.con "binfoNone" []]], Term.con "terminal" [Term.lit "cof_or"]]
      | _ => t

    def shapePi (t : Term) : Term :=
      match t with
      | .con "app" [.var "exprShape", .con "pi" [dom, cod]] => Term.con "shape" [Term.con "tuple" [Term.con "app" [Term.lit "(", Term.con "child" [], dom, Term.con "binfoNone" [], Term.lit ")"], Term.con "child" [cod, Term.con "app" [Term.var "binfoTerm", Term.con "num" [Term.con "number" [Term.lit "1"]]]]], Term.con "terminal" [Term.lit "pi"]]
      | _ => t

    def shapeSigma (t : Term) : Term :=
      match t with
      | .con "app" [.var "exprShape", .con "sigma" [dom, cod]] => Term.con "shape" [Term.con "tuple" [Term.con "app" [Term.lit "(", Term.con "child" [], dom, Term.con "binfoNone" [], Term.lit ")"], Term.con "child" [cod, Term.con "app" [Term.var "binfoTerm", Term.con "num" [Term.con "number" [Term.lit "1"]]]]], Term.con "terminal" [Term.lit "sigma"]]
      | _ => t

    def shapePath (t : Term) : Term :=
      match t with
      | .con "app" [.var "exprShape", .con "path" [A, a, b]] => Term.con "shape" [Term.con "tuple" [Term.con "app" [Term.lit "(", Term.con "child" [], A, Term.con "binfoNone" [], Term.lit ")"], Term.con "child" [a, Term.con "binfoNone" []], Term.con "child" [b, Term.con "binfoNone" []]], Term.con "terminal" [Term.lit "path"]]
      | _ => t

    def shapeSub (t : Term) : Term :=
      match t with
      | .con "app" [.var "exprShape", .con "sub" [A, φ, t]] => Term.con "shape" [Term.con "tuple" [Term.con "app" [Term.lit "(", Term.con "child" [], A, Term.con "binfoNone" [], Term.lit ")"], Term.con "child" [φ, Term.con "binfoNone" []], Term.con "child" [t, Term.con "binfoNone" []]], Term.con "terminal" [Term.lit "sub"]]
      | _ => t

    def shapeLetE (t : Term) : Term :=
      match t with
      | .con "app" [.var "exprShape", .con "letE" [ty, val, body]] => Term.con "shape" [Term.con "tuple" [Term.con "app" [Term.lit "(", Term.con "child" [], ty, Term.con "binfoNone" [], Term.lit ")"], Term.con "child" [val, Term.con "binfoNone" []], Term.con "child" [body, Term.con "app" [Term.var "binfoTerm", Term.con "num" [Term.con "number" [Term.lit "1"]]]]], Term.con "terminal" [Term.lit "letE"]]
      | _ => t

    def shapeCoe (t : Term) : Term :=
      match t with
      | .con "app" [.var "exprShape", .con "coe" [r, r', A, a]] => Term.con "shape" [Term.con "tuple" [Term.con "app" [Term.lit "(", Term.con "child" [], r, Term.con "binfoNone" [], Term.lit ")"], Term.con "child" [r', Term.con "binfoNone" []], Term.con "child" [A, Term.con "app" [Term.var "binfoDim", Term.con "num" [Term.con "number" [Term.lit "1"]]]], Term.con "child" [a, Term.con "binfoNone" []]], Term.con "terminal" [Term.lit "coe"]]
      | _ => t

    def shapeNatElim (t : Term) : Term :=
      match t with
      | .con "app" [.var "exprShape", .con "natElim" [P, z, s, n]] => Term.con "shape" [Term.con "tuple" [Term.con "app" [Term.lit "(", Term.con "child" [], P, Term.con "binfoNone" [], Term.lit ")"], Term.con "child" [z, Term.con "binfoNone" []], Term.con "child" [s, Term.con "app" [Term.var "binfoTerm", Term.con "num" [Term.con "number" [Term.lit "2"]]]], Term.con "child" [n, Term.con "binfoNone" []]], Term.con "terminal" [Term.lit "natElim"]]
      | _ => t

    def shapeCircleElim (t : Term) : Term :=
      match t with
      | .con "app" [.var "exprShape", .con "circleElim" [P, b, l, x]] => Term.con "shape" [Term.con "tuple" [Term.con "app" [Term.lit "(", Term.con "child" [], P, Term.con "binfoNone" [], Term.lit ")"], Term.con "child" [b, Term.con "binfoNone" []], Term.con "child" [l, Term.con "app" [Term.var "binfoDim", Term.con "num" [Term.con "number" [Term.lit "1"]]]], Term.con "child" [x, Term.con "binfoNone" []]], Term.con "terminal" [Term.lit "circleElim"]]
      | _ => t

  end Shape

  section Reconstruct

    def reconstructIx (t : Term) : Term :=
      match t with
      | .con "reconstruct" [.con "terminal" [.lit "ix"], .con "unit" [.lit "(", .lit ")"], orig] => orig
      | _ => t

    def reconstructLit (t : Term) : Term :=
      match t with
      | .con "reconstruct" [.con "terminal" [.lit "lit"], .con "unit" [.lit "(", .lit ")"], orig] => orig
      | _ => t

    def reconstructLam (t : Term) : Term :=
      match t with
      | .con "reconstruct" [.con "terminal" [.lit "lam"], body, .con "app" [.var "lam", oldBody]] => Term.con "app" [Term.var "lam", body]
      | _ => t

    def reconstructApp (t : Term) : Term :=
      match t with
      | .con "reconstruct" [.con "terminal" [.lit "app"], .con "tuple" [f, a], .con "app" [oldF, oldA]] => Term.con "app" [f, a]
      | _ => t

    def reconstructPi (t : Term) : Term :=
      match t with
      | .con "reconstruct" [.con "terminal" [.lit "pi"], .con "tuple" [dom, cod], .con "pi" [oldDom, oldCod]] => Term.con "pi" [dom, cod]
      | _ => t

    def reconstructSigma (t : Term) : Term :=
      match t with
      | .con "reconstruct" [.con "terminal" [.lit "sigma"], .con "tuple" [dom, cod], .con "sigma" [oldDom, oldCod]] => Term.con "sigma" [dom, cod]
      | _ => t

    def reconstructPair (t : Term) : Term :=
      match t with
      | .con "reconstruct" [.con "terminal" [.lit "pair"], .con "tuple" [a, b], .con "pair" [oldA, oldB]] => Term.con "pair" [a, b]
      | _ => t

    def reconstructFst (t : Term) : Term :=
      match t with
      | .con "reconstruct" [.con "terminal" [.lit "fst"], e, .con "app" [.var "fst", oldE]] => Term.con "app" [Term.var "fst", e]
      | _ => t

    def reconstructSnd (t : Term) : Term :=
      match t with
      | .con "reconstruct" [.con "terminal" [.lit "snd"], e, .con "app" [.var "snd", oldE]] => Term.con "app" [Term.var "snd", e]
      | _ => t

    def reconstructPlam (t : Term) : Term :=
      match t with
      | .con "reconstruct" [.con "terminal" [.lit "plam"], body, .con "app" [.var "plam", oldBody]] => Term.con "app" [Term.var "plam", body]
      | _ => t

    def reconstructPapp (t : Term) : Term :=
      match t with
      | .con "reconstruct" [.con "terminal" [.lit "papp"], .con "tuple" [p, r], .con "papp" [oldP, oldR]] => Term.con "papp" [p, r]
      | _ => t

    def reconstructPath (t : Term) : Term :=
      match t with
      | .con "reconstruct" [.con "terminal" [.lit "path"], .con "tuple" [A, a, b], .con "path" [oldA, oldA', oldB]] => Term.con "path" [A, a, b]
      | _ => t

    def reconstructRefl (t : Term) : Term :=
      match t with
      | .con "reconstruct" [.con "terminal" [.lit "refl"], a, .con "app" [.var "refl", oldA]] => Term.con "app" [Term.var "refl", a]
      | _ => t

    def reconstructCofEq (t : Term) : Term :=
      match t with
      | .con "reconstruct" [.con "terminal" [.lit "cof_eq"], .con "tuple" [r, s], .con "cof_eq" [oldR, oldS]] => Term.con "cof_eq" [r, s]
      | _ => t

    def reconstructCofAnd (t : Term) : Term :=
      match t with
      | .con "reconstruct" [.con "terminal" [.lit "cof_and"], .con "tuple" [φ, ψ], .con "cof_and" [oldPhi, oldPsi]] => Term.con "cof_and" [φ, ψ]
      | _ => t

    def reconstructCofOr (t : Term) : Term :=
      match t with
      | .con "reconstruct" [.con "terminal" [.lit "cof_or"], .con "tuple" [φ, ψ], .con "cof_or" [oldPhi, oldPsi]] => Term.con "cof_or" [φ, ψ]
      | _ => t

    def reconstructCoe (t : Term) : Term :=
      match t with
      | .con "reconstruct" [.con "terminal" [.lit "coe"], .con "tuple" [r, r', A, a], .con "coe" [oldR, oldR', oldA, oldA']] => Term.con "coe" [r, r', A, a]
      | _ => t

    def reconstructSuc (t : Term) : Term :=
      match t with
      | .con "reconstruct" [.con "terminal" [.lit "suc"], n, .con "app" [.var "suc", oldN]] => Term.con "app" [Term.var "suc", n]
      | _ => t

    def reconstructNatElim (t : Term) : Term :=
      match t with
      | .con "reconstruct" [.con "terminal" [.lit "natElim"], .con "tuple" [P, z, s, n], .con "natElim" [oldP, oldZ, oldS, oldN]] => Term.con "natElim" [P, z, s, n]
      | _ => t

    def reconstructLoop (t : Term) : Term :=
      match t with
      | .con "reconstruct" [.con "terminal" [.lit "loop"], r, .con "app" [.var "loop", oldR]] => Term.con "app" [Term.var "loop", r]
      | _ => t

    def reconstructCircleElim (t : Term) : Term :=
      match t with
      | .con "reconstruct" [.con "terminal" [.lit "circleElim"], .con "tuple" [P, b, l, x], .con "circleElim" [oldP, oldB, oldL, oldX]] => Term.con "circleElim" [P, b, l, x]
      | _ => t

    def reconstructSub (t : Term) : Term :=
      match t with
      | .con "reconstruct" [.con "terminal" [.lit "sub"], .con "tuple" [A, φ, t], .con "sub" [oldA, oldPhi, oldT]] => Term.con "sub" [A, φ, t]
      | _ => t

    def reconstructSubIn (t : Term) : Term :=
      match t with
      | .con "reconstruct" [.con "terminal" [.lit "subIn"], e, .con "app" [.var "subIn", oldE]] => Term.con "app" [Term.var "subIn", e]
      | _ => t

    def reconstructSubOut (t : Term) : Term :=
      match t with
      | .con "reconstruct" [.con "terminal" [.lit "subOut"], e, .con "app" [.var "subOut", oldE]] => Term.con "app" [Term.var "subOut", e]
      | _ => t

    def reconstructLetE (t : Term) : Term :=
      match t with
      | .con "reconstruct" [.con "terminal" [.lit "letE"], .con "tuple" [ty, val, body], .con "letE" [oldTy, oldVal, oldBody]] => Term.con "letE" [ty, val, body]
      | _ => t

  end Reconstruct

  section FreeVars

    def freeVarsIx (t : Term) : Term :=
      match t with
      | .con "freeVars'" [depth, .con "app" [.var "ix", n]] => Term.con "if" [Term.con "geq" [n, depth], Term.con "cons" [n, Term.con "nil" []], Term.con "nil" []]
      | _ => t

    def freeVarsLit (t : Term) : Term :=
      match t with
      | .con "freeVars'" [depth, .con "app" [.var "lit", s]] => Term.con "nil" []
      | _ => t

    def freeVarsLam (t : Term) : Term :=
      match t with
      | .con "freeVars'" [depth, .con "app" [.var "lam", body]] => Term.con "freeVars'" [Term.con "app" [Term.var "suc", depth], body]
      | _ => t

    def freeVarsApp (t : Term) : Term :=
      match t with
      | .con "freeVars'" [depth, .con "app" [f, a]] => Term.con "append" [Term.con "freeVars'" [depth, f], Term.con "freeVars'" [depth, a]]
      | _ => t

    def freeVarsPi (t : Term) : Term :=
      match t with
      | .con "freeVars'" [depth, .con "pi" [dom, cod]] => Term.con "append" [Term.con "freeVars'" [depth, dom], Term.con "freeVars'" [Term.con "app" [Term.var "suc", depth], cod]]
      | _ => t

    def freeVarsSigma (t : Term) : Term :=
      match t with
      | .con "freeVars'" [depth, .con "sigma" [dom, cod]] => Term.con "append" [Term.con "freeVars'" [depth, dom], Term.con "freeVars'" [Term.con "app" [Term.var "suc", depth], cod]]
      | _ => t

    def freeVarsPair (t : Term) : Term :=
      match t with
      | .con "freeVars'" [depth, .con "pair" [a, b]] => Term.con "append" [Term.con "freeVars'" [depth, a], Term.con "freeVars'" [depth, b]]
      | _ => t

    def freeVarsFst (t : Term) : Term :=
      match t with
      | .con "freeVars'" [depth, .con "app" [.var "fst", e]] => Term.con "freeVars'" [depth, e]
      | _ => t

    def freeVarsSnd (t : Term) : Term :=
      match t with
      | .con "freeVars'" [depth, .con "app" [.var "snd", e]] => Term.con "freeVars'" [depth, e]
      | _ => t

    def freeVarsPlam (t : Term) : Term :=
      match t with
      | .con "freeVars'" [depth, .con "app" [.var "plam", body]] => Term.con "freeVars'" [depth, body]
      | _ => t

    def freeVarsPapp (t : Term) : Term :=
      match t with
      | .con "freeVars'" [depth, .con "papp" [p, r]] => Term.con "freeVars'" [depth, p]
      | _ => t

    def freeVarsUniv (t : Term) : Term :=
      match t with
      | .con "freeVars'" [depth, .con "app" [.var "univ", l]] => Term.con "nil" []
      | _ => t

    def freeVarsPath (t : Term) : Term :=
      match t with
      | .con "freeVars'" [depth, .con "path" [A, a, b]] => Term.con "append" [Term.con "freeVars'" [depth, A], Term.con "append" [Term.con "freeVars'" [depth, a], Term.con "freeVars'" [depth, b]]]
      | _ => t

    def freeVars (t : Term) : Term :=
      match t with
      | .con "app" [.var "freeVars", e] => Term.con "freeVars'" [Term.con "num" [Term.con "number" [Term.lit "0"]], e]
      | _ => t

  end FreeVars

  section FreeIn

    def freeIn (t : Term) : Term :=
      match t with
      | .con "freeIn" [n, e] => Term.con "elem" [n, Term.con "app" [Term.var "freeVars", e]]
      | _ => t

  end FreeIn

  section WHNF

    def whnfAppLam (t : Term) : Term :=
      match t with
      | .con "app" [.var "whnfStep", .con "app" [.con "app" [.var "lam", body], arg]] => Term.con "app" [Term.var "some", Term.con "subst" [Term.con "num" [Term.con "number" [Term.lit "0"]], arg, body]]
      | _ => t

    def whnfAppOther (t : Term) : Term :=
      match t with
      | .con "app" [.var "whnfStep", .con "app" [f, a]] => Term.con "none" []
      | _ => t

    def whnfFstPair (t : Term) : Term :=
      match t with
      | .con "app" [.var "whnfStep", .con "app" [.var "fst", .con "pair" [a, b]]] => Term.con "app" [Term.var "some", a]
      | _ => t

    def whnfSndPair (t : Term) : Term :=
      match t with
      | .con "app" [.var "whnfStep", .con "app" [.var "snd", .con "pair" [a, b]]] => Term.con "app" [Term.var "some", b]
      | _ => t

    def whnfFstOther (t : Term) : Term :=
      match t with
      | .con "app" [.var "whnfStep", .con "app" [.var "fst", p]] => Term.con "none" []
      | _ => t

    def whnfSndOther (t : Term) : Term :=
      match t with
      | .con "app" [.var "whnfStep", .con "app" [.var "snd", p]] => Term.con "none" []
      | _ => t

    def whnfPappPlam (t : Term) : Term :=
      match t with
      | .con "app" [.var "whnfStep", .con "papp" [.con "app" [.var "plam", body], r]] => Term.con "app" [Term.var "some", Term.con "substDim" [Term.con "num" [Term.con "number" [Term.lit "0"]], r, body]]
      | _ => t

    def whnfPappRefl (t : Term) : Term :=
      match t with
      | .con "app" [.var "whnfStep", .con "papp" [.con "app" [.var "refl", a], r]] => Term.con "app" [Term.var "some", a]
      | _ => t

    def whnfPappOther (t : Term) : Term :=
      match t with
      | .con "app" [.var "whnfStep", .con "papp" [p, r]] => Term.con "none" []
      | _ => t

    def whnfLet (t : Term) : Term :=
      match t with
      | .con "app" [.var "whnfStep", .con "letE" [ty, val, body]] => Term.con "app" [Term.var "some", Term.con "subst" [Term.con "num" [Term.con "number" [Term.lit "0"]], val, body]]
      | _ => t

    def whnfStepDefault (t : Term) : Term :=
      match t with
      | .con "app" [.var "whnfStep", e] => Term.con "none" []
      | _ => t

    def whnf' (t : Term) : Term :=
      match t with
      | .con "whnf'" [fuel, e] => Term.con "whnfLoop" [fuel, e]
      | _ => t

    def whnf'Zero (t : Term) : Term :=
      match t with
      | .con "whnf'" [.con "num" [.con "number" [.lit "0"]], e] => e
      | _ => t

    def whnfLoop (t : Term) : Term :=
      match t with
      | .con "whnfLoop" [fuel, e] => Term.con "match" [Term.con "app" [Term.var "whnfStep", e], Term.lit "with", Term.lit "|", Term.con "app" [Term.var "some", Term.var "e'"], Term.lit "=>", Term.con "whnf'" [Term.con "sub" [fuel, Term.con "num" [Term.con "number" [Term.lit "1"]]], Term.var "e'"], Term.lit "|", Term.con "none" [], Term.lit "=>", e]
      | _ => t

  end WHNF

  section TryBetaReduce

    def tryBetaApp (t : Term) : Term :=
      match t with
      | .con "app" [.var "tryBetaReduce", .con "app" [.con "app" [.var "lam", body], arg]] => Term.con "app" [Term.var "some", Term.con "subst" [Term.con "num" [Term.con "number" [Term.lit "0"]], arg, body]]
      | _ => t

    def tryBetaFst (t : Term) : Term :=
      match t with
      | .con "app" [.var "tryBetaReduce", .con "app" [.var "fst", .con "pair" [a, b]]] => Term.con "app" [Term.var "some", a]
      | _ => t

    def tryBetaSnd (t : Term) : Term :=
      match t with
      | .con "app" [.var "tryBetaReduce", .con "app" [.var "snd", .con "pair" [a, b]]] => Term.con "app" [Term.var "some", b]
      | _ => t

    def tryBetaPapp (t : Term) : Term :=
      match t with
      | .con "app" [.var "tryBetaReduce", .con "papp" [.con "app" [.var "plam", body], r]] => Term.con "app" [Term.var "some", Term.con "substDim" [Term.con "num" [Term.con "number" [Term.lit "0"]], r, body]]
      | _ => t

    def tryBetaRefl (t : Term) : Term :=
      match t with
      | .con "app" [.var "tryBetaReduce", .con "papp" [.con "app" [.var "refl", a], r]] => Term.con "app" [Term.var "some", a]
      | _ => t

    def tryBetaNone (t : Term) : Term :=
      match t with
      | .con "app" [.var "tryBetaReduce", e] => Term.con "none" []
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

  end TryBetaReduce

end Visitor