/-
  AUTO-GENERATED from .lego files
  Do not edit directly.
-/

import Lego.Algebra

open Lego

namespace Datatype

  section DataType

    def mkData (t : Term) : Term :=
      match t with
      | .con "mkData" [dlbl, .con "unit" [.lit "(", .lit ")"]] => Term.con "app" [Term.var "lit", Term.con "concat" [Term.con "terminal" [Term.lit "data."], dlbl]]
      | _ => t

    def mkDataParams (t : Term) : Term :=
      match t with
      | .con "mkData" [dlbl, .con "tuple" [p, rest]] => Term.con "app" [Term.con "mkData" [dlbl, rest], p]
      | _ => t

    def isData (t : Term) : Term :=
      match t with
      | .con "app" [.var "isData", e] => Term.con "getDataHead" [e, Term.con "unit" [Term.lit "(", Term.lit ")"]]
      | _ => t

    def getDataHeadLit (t : Term) : Term :=
      match t with
      | .con "getDataHead" [.con "app" [.var "lit", s], acc] => Term.con "caseExpr" [Term.lit "(", Term.lit "case", Term.con "startsWith" [s, Term.con "terminal" [Term.lit "data."]], Term.con "arm" [Term.var "true", Term.lit "=>", Term.con "app" [Term.var "some", Term.con "tuple" [Term.lit "(", Term.con "drop" [Term.con "num" [Term.con "number" [Term.lit "5"]], s], Term.lit ",", acc, Term.lit ")"]]], Term.con "arm" [Term.var "false", Term.lit "=>", Term.con "none" []], Term.lit ")"]
      | _ => t

    def getDataHeadApp (t : Term) : Term :=
      match t with
      | .con "getDataHead" [.con "app" [f, a], acc] => Term.con "getDataHead" [f, Term.con "tuple" [a, acc]]
      | _ => t

    def getDataHeadOther (t : Term) : Term :=
      match t with
      | .con "getDataHead" [e, acc] => Term.con "none" []
      | _ => t

  end DataType

  section Intro

    def mkIntro (t : Term) : Term :=
      match t with
      | .con "mkIntro" [dlbl, clbl, params, args] => Term.con "mkIntro'" [dlbl, clbl, Term.con "app" [Term.var "length", params], params, args]
      | _ => t

    def mkIntro' (t : Term) : Term :=
      match t with
      | .con "mkIntro'" [dlbl, clbl, paramCount, .con "unit" [.lit "(", .lit ")"], .con "unit" [.lit "(", .lit ")"]] => Term.con "app" [Term.var "lit", Term.con "concat" [Term.con "terminal" [Term.lit "intro."], dlbl, Term.con "terminal" [Term.lit "."], clbl, Term.con "terminal" [Term.lit "."], paramCount]]
      | _ => t

    def mkIntro'Params (t : Term) : Term :=
      match t with
      | .con "mkIntro'" [dlbl, clbl, paramCount, .con "tuple" [p, rest], args] => Term.con "app" [Term.con "mkIntro'" [dlbl, clbl, paramCount, rest, args], p]
      | _ => t

    def mkIntro'Args (t : Term) : Term :=
      match t with
      | .con "mkIntro'" [dlbl, clbl, paramCount, .con "unit" [.lit "(", .lit ")"], .con "tuple" [a, rest]] => Term.con "app" [Term.con "mkIntro'" [dlbl, clbl, paramCount, Term.con "unit" [Term.lit "(", Term.lit ")"], rest], a]
      | _ => t

    def isIntro (t : Term) : Term :=
      match t with
      | .con "app" [.var "isIntro", e] => Term.con "letIn" [Term.lit "(", Term.lit "let", Term.var "headArgs", Term.lit "=", Term.con "collectArgs" [e, Term.con "unit" [Term.lit "(", Term.lit ")"]], Term.lit "in", Term.con "parseIntro" [Term.con "app" [Term.var "fst", Term.con "headArgs" []], Term.con "app" [Term.var "snd", Term.con "headArgs" []]], Term.lit ")"]
      | _ => t

    def collectArgsApp (t : Term) : Term :=
      match t with
      | .con "collectArgs" [.con "app" [f, a], acc] => Term.con "collectArgs" [f, Term.con "tuple" [a, acc]]
      | _ => t

    def collectArgsOther (t : Term) : Term :=
      match t with
      | .con "collectArgs" [e, acc] => Term.con "tuple" [Term.lit "(", e, Term.lit ",", acc, Term.lit ")"]
      | _ => t

    def parseIntro (t : Term) : Term :=
      match t with
      | .con "parseIntro" [.con "app" [.var "lit", s], allArgs] => Term.con "caseExpr" [Term.lit "(", Term.lit "case", Term.con "startsWith" [s, Term.con "terminal" [Term.lit "intro."]], Term.con "arm" [Term.var "true", Term.lit "=>", Term.con "parseIntroRest" [Term.con "drop" [Term.con "num" [Term.con "number" [Term.lit "6"]], s], allArgs]], Term.con "arm" [Term.var "false", Term.lit "=>", Term.con "none" []], Term.lit ")"]
      | _ => t

    def parseIntroOther (t : Term) : Term :=
      match t with
      | .con "parseIntro" [e, args] => Term.con "none" []
      | _ => t

    def parseIntroRest (t : Term) : Term :=
      match t with
      | .con "parseIntroRest" [rest, allArgs] => Term.con "caseExpr" [Term.lit "(", Term.lit "case", Term.con "splitOn" [rest, Term.con "terminal" [Term.lit "."]], Term.con "arm" [Term.lit "(", Term.var "dlbl", Term.var "clbl", Term.var "countStr", Term.lit ")", Term.lit "=>", Term.con "letIn" [Term.lit "(", Term.lit "let", Term.var "paramCount", Term.lit "=", Term.con "app" [Term.var "toNat", Term.var "countStr"], Term.lit "in", Term.con "letIn" [Term.lit "let", Term.var "params", Term.lit "=", Term.con "take" [Term.con "paramCount" [], allArgs], Term.lit "in", Term.con "letIn" [Term.lit "let", Term.var "args", Term.lit "=", Term.con "drop" [Term.con "paramCount" [], allArgs], Term.lit "in", Term.con "app" [Term.var "some", Term.con "nTuple" [Term.lit "(", Term.var "dlbl", Term.lit ",", Term.var "clbl", Term.lit ",", Term.con "params" [], Term.con "seq" [Term.lit ",", Term.con "args" []], Term.lit ")"]]]], Term.lit ")"]], Term.con "arm" [Term.lit "(", Term.var "dlbl", Term.var "clbl", Term.lit ")", Term.lit "=>", Term.con "app" [Term.var "some", Term.con "nTuple" [Term.lit "(", Term.var "dlbl", Term.lit ",", Term.var "clbl", Term.lit ",", Term.con "unit" [Term.lit "(", Term.lit ")"], Term.con "seq" [Term.lit ",", allArgs], Term.lit ")"]]], Term.con "arm" [Term.var "_", Term.lit "=>", Term.con "none" []], Term.lit ")"]
      | _ => t

  end Intro

  section ElimClause

    def elimClauseClbl (t : Term) : Term :=
      match t with
      | .con "app" [.var "elimClauseClbl", .con "clause" [.con "labeledArg" [.var "clbl", .lit ":", c], .con "labeledArg" [.var "body", .lit ":", b]]] => c
      | _ => t

    def elimClauseBody (t : Term) : Term :=
      match t with
      | .con "app" [.var "elimClauseBody", .con "clause" [.con "labeledArg" [.var "clbl", .lit ":", c], .con "labeledArg" [.var "body", .lit ":", b]]] => b
      | _ => t

  end ElimClause

  section Elim

    def mkElim (t : Term) : Term :=
      match t with
      | .con "mkElim" [dlbl, params, mot, clauses, scrut] => Term.con "letIn" [Term.lit "(", Term.lit "let", Term.var "base", Term.lit "=", Term.con "app" [Term.var "lit", Term.con "concat" [Term.con "terminal" [Term.lit "elim."], dlbl]], Term.lit "in", Term.con "letIn" [Term.lit "let", Term.var "withParams", Term.lit "=", Term.con "foldl" [Term.con "app" [], Term.con "base" [], params], Term.lit "in", Term.con "letIn" [Term.lit "let", Term.var "withMot", Term.lit "=", Term.con "app" [Term.con "withParams" [], mot], Term.lit "in", Term.con "letIn" [Term.lit "let", Term.var "clauseExpr", Term.lit "=", Term.con "app" [Term.var "encodeClauseList", clauses], Term.lit "in", Term.con "letIn" [Term.lit "let", Term.var "withClauses", Term.lit "=", Term.con "app" [Term.con "withMot" [], Term.con "clauseExpr" []], Term.lit "in", Term.con "app" [Term.con "withClauses" [], scrut]]]]], Term.lit ")"]
      | _ => t

    def encodeClauseListNil (t : Term) : Term :=
      match t with
      | .con "app" [.var "encodeClauseList", .con "unit" [.lit "(", .lit ")"]] => Term.con "app" [Term.var "lit", Term.con "terminal" [Term.lit "clauses.nil"]]
      | _ => t

    def encodeClauseListCons (t : Term) : Term :=
      match t with
      | .con "app" [.var "encodeClauseList", .con "app" [.lit "(", .lit "(", .var "clause", .con "labeledArg" [.var "clbl", .lit ":", c], .con "labeledArg" [.var "body", .lit ":", b], .lit ")", rest, .lit ")"]] => Term.con "letIn" [Term.lit "(", Term.lit "let", Term.var "tag", Term.lit "=", Term.con "app" [Term.var "lit", Term.con "concat" [Term.con "terminal" [Term.lit "clause."], c]], Term.lit "in", Term.con "letIn" [Term.lit "let", Term.var "thisClause", Term.lit "=", Term.con "app" [Term.con "tag" [], b], Term.lit "in", Term.con "app" [Term.con "app" [Term.con "app" [Term.var "lit", Term.con "terminal" [Term.lit "clauses.cons"]], Term.con "thisClause" []], Term.con "app" [Term.var "encodeClauseList", rest]]], Term.lit ")"]
      | _ => t

    def isElim (t : Term) : Term :=
      match t with
      | .con "app" [.var "isElim", e] => Term.con "letIn" [Term.lit "(", Term.lit "let", Term.var "headArgs", Term.lit "=", Term.con "collectArgs" [e, Term.con "unit" [Term.lit "(", Term.lit ")"]], Term.lit "in", Term.con "parseElim" [Term.con "app" [Term.var "fst", Term.con "headArgs" []], Term.con "app" [Term.var "snd", Term.con "headArgs" []]], Term.lit ")"]
      | _ => t

    def parseElim (t : Term) : Term :=
      match t with
      | .con "parseElim" [.con "app" [.var "lit", s], args] => Term.con "caseExpr" [Term.lit "(", Term.lit "case", Term.con "startsWith" [s, Term.con "terminal" [Term.lit "elim."]], Term.con "arm" [Term.var "true", Term.lit "=>", Term.con "app" [Term.var "some", Term.con "drop" [Term.con "num" [Term.con "number" [Term.lit "5"]], s]]], Term.con "arm" [Term.var "false", Term.lit "=>", Term.con "none" []], Term.lit ")"]
      | _ => t

    def parseElimOther (t : Term) : Term :=
      match t with
      | .con "parseElim" [e, args] => Term.con "none" []
      | _ => t

  end Elim

  section EvalIntro

    def evalIntroZero (t : Term) : Term :=
      match t with
      | .con "evalIntro" [.con "app" [.var "lit", .con "terminal" [.lit "intro.Nat.zero.0"]], .con "unit" [.lit "(", .lit ")"]] => Term.con "zero" []
      | _ => t

    def evalIntroSuc (t : Term) : Term :=
      match t with
      | .con "evalIntro" [.con "app" [.var "lit", .con "terminal" [.lit "intro.Nat.suc.0"]], n] => Term.con "app" [Term.var "suc", n]
      | _ => t

    def evalIntroNil (t : Term) : Term :=
      match t with
      | .con "evalIntro" [.con "app" [.var "lit", .con "terminal" [.lit "intro.List.nil.1"]], A] => Term.con "app" [Term.var "nil", A]
      | _ => t

    def evalIntroCons (t : Term) : Term :=
      match t with
      | .con "evalIntro" [.con "app" [.var "lit", .con "terminal" [.lit "intro.List.cons.1"]], .con "tuple" [A, x, xs]] => Term.con "cons" [A, x, xs]
      | _ => t

    def evalIntroBase (t : Term) : Term :=
      match t with
      | .con "evalIntro" [.con "app" [.var "lit", .con "terminal" [.lit "intro.Circle.base.0"]], .con "unit" [.lit "(", .lit ")"]] => Term.con "base" []
      | _ => t

    def evalIntroLoop (t : Term) : Term :=
      match t with
      | .con "evalIntro" [.con "app" [.var "lit", .con "terminal" [.lit "intro.Circle.loop.0"]], r] => Term.con "app" [Term.var "loop", r]
      | _ => t

    def evalIntroDefault (t : Term) : Term :=
      match t with
      | .con "evalIntro" [head, args] => Term.con "foldl" [Term.con "app" [], head, args]
      | _ => t

  end EvalIntro

  section EvalElim

    def evalElimNatZero (t : Term) : Term :=
      match t with
      | .con "evalElim" [.con "terminal" [.lit "Nat"], mot, clauses, .con "zero" []] => Term.con "lookupClause" [clauses, Term.con "terminal" [Term.lit "zero"]]
      | _ => t

    def evalElimNatSuc (t : Term) : Term :=
      match t with
      | .con "evalElim" [.con "terminal" [.lit "Nat"], mot, clauses, .con "app" [.var "suc", n]] => Term.con "letIn" [Term.lit "(", Term.lit "let", Term.var "sucClause", Term.lit "=", Term.con "lookupClause" [clauses, Term.con "terminal" [Term.lit "suc"]], Term.lit "in", Term.con "letIn" [Term.lit "let", Term.var "ih", Term.lit "=", Term.con "evalElim" [Term.con "terminal" [Term.lit "Nat"], mot, clauses, n], Term.lit "in", Term.con "app" [Term.con "app" [Term.con "sucClause" [], n], Term.con "ih" []]], Term.lit ")"]
      | _ => t

    def evalElimListNil (t : Term) : Term :=
      match t with
      | .con "evalElim" [.con "terminal" [.lit "List"], mot, clauses, .con "app" [.var "nil", A]] => Term.con "lookupClause" [clauses, Term.con "terminal" [Term.lit "nil"]]
      | _ => t

    def evalElimListCons (t : Term) : Term :=
      match t with
      | .con "evalElim" [.con "terminal" [.lit "List"], mot, clauses, .con "cons" [A, x, xs]] => Term.con "letIn" [Term.lit "(", Term.lit "let", Term.var "consClause", Term.lit "=", Term.con "lookupClause" [clauses, Term.con "terminal" [Term.lit "cons"]], Term.lit "in", Term.con "letIn" [Term.lit "let", Term.var "ih", Term.lit "=", Term.con "evalElim" [Term.con "terminal" [Term.lit "List"], mot, clauses, xs], Term.lit "in", Term.con "app" [Term.con "app" [Term.con "app" [Term.con "consClause" [], x], xs], Term.con "ih" []]], Term.lit ")"]
      | _ => t

    def evalElimCircleBase (t : Term) : Term :=
      match t with
      | .con "evalElim" [.con "terminal" [.lit "Circle"], mot, clauses, .con "base" []] => Term.con "lookupClause" [clauses, Term.con "terminal" [Term.lit "base"]]
      | _ => t

    def evalElimDefault (t : Term) : Term :=
      match t with
      | .con "evalElim" [dlbl, mot, clauses, scrut] => Term.con "mkElim" [dlbl, Term.con "unit" [Term.lit "(", Term.lit ")"], mot, clauses, scrut]
      | _ => t

    def lookupClauseNil (t : Term) : Term :=
      match t with
      | .con "lookupClause" [.con "app" [.var "lit", .con "terminal" [.lit "clauses.nil"]], clbl] => Term.con "app" [Term.var "lit", Term.con "terminal" [Term.lit "clause-not-found"]]
      | _ => t

    def lookupClauseCons (t : Term) : Term :=
      match t with
      | .con "lookupClause" [.con "app" [.con "app" [.con "app" [.var "lit", .con "terminal" [.lit "clauses.cons"]], clause], rest], clbl] => Term.con "letIn" [Term.lit "(", Term.lit "let", Term.var "clauseTag", Term.lit "=", Term.con "app" [Term.var "getClauseTag", clause], Term.lit "in", Term.con "caseExpr" [Term.lit "case", Term.con "eq" [Term.con "clauseTag" [], clbl], Term.con "arm" [Term.var "true", Term.lit "=>", Term.con "app" [Term.var "getClauseBody", clause]], Term.con "arm" [Term.var "false", Term.lit "=>", Term.con "lookupClause" [rest, clbl]]], Term.lit ")"]
      | _ => t

    def getClauseTag (t : Term) : Term :=
      match t with
      | .con "app" [.var "getClauseTag", .con "app" [.con "app" [.var "lit", tag], body]] => Term.con "drop" [Term.con "num" [Term.con "number" [Term.lit "7"]], tag]
      | _ => t

    def getClauseBody (t : Term) : Term :=
      match t with
      | .con "app" [.var "getClauseBody", .con "app" [.con "app" [.var "lit", tag], body]] => body
      | _ => t

  end EvalElim

  section TypeOfIntro

    def typeOfIntro (t : Term) : Term :=
      match t with
      | .con "typeOfIntro" [env, dlbl, clbl, params, args] => Term.con "caseExpr" [Term.lit "(", Term.lit "case", Term.con "globalEnvLookupDatatype" [env, Term.con "app" [Term.var "gnameNamed", dlbl]], Term.con "arm" [Term.lit "(", Term.var "some", Term.var "desc", Term.lit ")", Term.lit "=>", Term.con "typeOfIntro'" [Term.var "desc", clbl, params, args]], Term.con "arm" [Term.var "none", Term.lit "=>", Term.con "none" []], Term.lit ")"]
      | _ => t

    def typeOfIntro' (t : Term) : Term :=
      match t with
      | .con "typeOfIntro'" [desc, clbl, params, args] => Term.con "caseExpr" [Term.lit "(", Term.lit "case", Term.con "findConstructor" [Term.con "app" [Term.var "gdataDescConstrs", desc], clbl], Term.con "arm" [Term.lit "(", Term.var "some", Term.var "constr", Term.lit ")", Term.lit "=>", Term.con "app" [Term.var "some", Term.con "computeConstrType" [desc, Term.var "constr", params, args]]], Term.con "arm" [Term.var "none", Term.lit "=>", Term.con "none" []], Term.lit ")"]
      | _ => t

    def findConstructorNil (t : Term) : Term :=
      match t with
      | .con "findConstructor" [.con "unit" [.lit "(", .lit ")"], clbl] => Term.con "none" []
      | _ => t

    def findConstructorMatch (t : Term) : Term :=
      match t with
      | .con "findConstructor" [.con "app" [.lit "(", .lit "(", .var "constructor", .con "labeledArg" [.var "name", .lit ":", clbl], .con "labeledArg" [.var "args", .lit ":", a], .con "labeledArg" [.var "boundary", .lit ":", b], .lit ")", rest, .lit ")"], clbl_dup] => Term.con "app" [Term.var "some", Term.con "constructor" [Term.con "labeledArg" [Term.var "name", Term.lit ":", clbl], Term.con "labeledArg" [Term.var "args", Term.lit ":", a], Term.con "labeledArg" [Term.var "boundary", Term.lit ":", b]]]
      | _ => t

    def findConstructorMiss (t : Term) : Term :=
      match t with
      | .con "findConstructor" [.con "tuple" [c, rest], clbl] => Term.con "findConstructor" [rest, clbl]
      | _ => t

    def computeConstrType (t : Term) : Term :=
      match t with
      | .con "computeConstrType" [desc, constr, params, args] => Term.con "mkData" [Term.con "app" [Term.var "gnameName", Term.con "app" [Term.var "gdataDescName", desc]], params]
      | _ => t

  end TypeOfIntro

  section TypeOfElim

    def typeOfElim (t : Term) : Term :=
      match t with
      | .con "typeOfElim" [env, dlbl, params, mot, clauses, scrut] => Term.con "app" [mot, scrut]
      | _ => t

  end TypeOfElim

  section BuiltinDatatypes

    def natDesc (t : Term) : Term :=
      match t with
      | .con "natDesc" [] => Term.con "dataDesc" [Term.con "labeledArg" [Term.var "name", Term.lit ":", Term.con "app" [Term.var "gnameNamed", Term.con "terminal" [Term.lit "Nat"]]], Term.con "labeledArg" [Term.var "params", Term.lit ":", Term.con "unit" [Term.lit "(", Term.lit ")"]], Term.con "labeledArg" [Term.var "level", Term.lit ":", Term.con "lzero" []], Term.con "labeledArg" [Term.var "constrs", Term.lit ":", Term.con "tuple" [Term.con "app" [Term.lit "(", Term.con "constructor" [], Term.con "labeledArg" [Term.var "name", Term.lit ":", Term.con "terminal" [Term.lit "zero"]], Term.con "labeledArg" [Term.var "args", Term.lit ":", Term.con "unit" [Term.lit "(", Term.lit ")"]], Term.con "labeledArg" [Term.var "boundary", Term.lit ":", Term.con "unit" [Term.lit "(", Term.lit ")"]], Term.lit ")"], Term.con "constructor" [Term.con "labeledArg" [Term.var "name", Term.lit ":", Term.con "terminal" [Term.lit "suc"]], Term.con "labeledArg" [Term.var "args", Term.lit ":", Term.con "typed" [Term.lit "(", Term.con "terminal" [Term.lit "n"], Term.lit ":", Term.con "recursive" [], Term.lit ")"]], Term.con "labeledArg" [Term.var "boundary", Term.lit ":", Term.con "unit" [Term.lit "(", Term.lit ")"]]]]]]
      | _ => t

    def listDesc (t : Term) : Term :=
      match t with
      | .con "listDesc" [] => Term.con "dataDesc" [Term.con "labeledArg" [Term.var "name", Term.lit ":", Term.con "app" [Term.var "gnameNamed", Term.con "terminal" [Term.lit "List"]]], Term.con "labeledArg" [Term.var "params", Term.lit ":", Term.con "typed" [Term.lit "(", Term.con "terminal" [Term.lit "A"], Term.lit ":", Term.con "app" [Term.var "univ", Term.con "lzero" []], Term.lit ")"]], Term.con "labeledArg" [Term.var "level", Term.lit ":", Term.con "lzero" []], Term.con "labeledArg" [Term.var "constrs", Term.lit ":", Term.con "tuple" [Term.con "app" [Term.lit "(", Term.con "constructor" [], Term.con "labeledArg" [Term.var "name", Term.lit ":", Term.con "terminal" [Term.lit "nil"]], Term.con "labeledArg" [Term.var "args", Term.lit ":", Term.con "unit" [Term.lit "(", Term.lit ")"]], Term.con "labeledArg" [Term.var "boundary", Term.lit ":", Term.con "unit" [Term.lit "(", Term.lit ")"]], Term.lit ")"], Term.con "constructor" [Term.con "labeledArg" [Term.var "name", Term.lit ":", Term.con "terminal" [Term.lit "cons"]], Term.con "labeledArg" [Term.var "args", Term.lit ":", Term.con "tuple" [Term.con "typed" [Term.lit "(", Term.con "terminal" [Term.lit "x"], Term.lit ":", Term.con "app" [Term.var "const", Term.con "app" [Term.var "ix", Term.con "num" [Term.con "number" [Term.lit "0"]]]], Term.lit ")"], Term.con "typed" [Term.lit "(", Term.con "terminal" [Term.lit "xs"], Term.lit ":", Term.con "recursive" [], Term.lit ")"]]], Term.con "labeledArg" [Term.var "boundary", Term.lit ":", Term.con "unit" [Term.lit "(", Term.lit ")"]]]]]]
      | _ => t

    def circleDesc (t : Term) : Term :=
      match t with
      | .con "circleDesc" [] => Term.con "dataDesc" [Term.con "labeledArg" [Term.var "name", Term.lit ":", Term.con "app" [Term.var "gnameNamed", Term.con "terminal" [Term.lit "Circle"]]], Term.con "labeledArg" [Term.var "params", Term.lit ":", Term.con "unit" [Term.lit "(", Term.lit ")"]], Term.con "labeledArg" [Term.var "level", Term.lit ":", Term.con "lzero" []], Term.con "labeledArg" [Term.var "constrs", Term.lit ":", Term.con "tuple" [Term.con "app" [Term.lit "(", Term.con "constructor" [], Term.con "labeledArg" [Term.var "name", Term.lit ":", Term.con "terminal" [Term.lit "base"]], Term.con "labeledArg" [Term.var "args", Term.lit ":", Term.con "unit" [Term.lit "(", Term.lit ")"]], Term.con "labeledArg" [Term.var "boundary", Term.lit ":", Term.con "unit" [Term.lit "(", Term.lit ")"]], Term.lit ")"], Term.con "constructor" [Term.con "labeledArg" [Term.var "name", Term.lit ":", Term.con "terminal" [Term.lit "loop"]], Term.con "labeledArg" [Term.var "args", Term.lit ":", Term.con "typed" [Term.lit "(", Term.con "terminal" [Term.lit "i"], Term.lit ":", Term.con "dim" [], Term.lit ")"]], Term.con "labeledArg" [Term.var "boundary", Term.lit ":", Term.con "tuple" [Term.con "tuple" [Term.lit "(", Term.con "cof_eq" [Term.con "app" [Term.var "ix", Term.con "num" [Term.con "number" [Term.lit "0"]]], Term.var "dim0"], Term.lit ",", Term.con "base" [], Term.lit ")"], Term.con "tuple" [Term.lit "(", Term.con "cof_eq" [Term.con "app" [Term.var "ix", Term.con "num" [Term.con "number" [Term.lit "0"]]], Term.var "dim1"], Term.lit ",", Term.con "base" [], Term.lit ")"]]]]]]]
      | _ => t

    def boolDesc (t : Term) : Term :=
      match t with
      | .con "boolDesc" [] => Term.con "dataDesc" [Term.con "labeledArg" [Term.var "name", Term.lit ":", Term.con "app" [Term.var "gnameNamed", Term.con "terminal" [Term.lit "Bool"]]], Term.con "labeledArg" [Term.var "params", Term.lit ":", Term.con "unit" [Term.lit "(", Term.lit ")"]], Term.con "labeledArg" [Term.var "level", Term.lit ":", Term.con "lzero" []], Term.con "labeledArg" [Term.var "constrs", Term.lit ":", Term.con "tuple" [Term.con "app" [Term.lit "(", Term.con "constructor" [], Term.con "labeledArg" [Term.var "name", Term.lit ":", Term.con "terminal" [Term.lit "true"]], Term.con "labeledArg" [Term.var "args", Term.lit ":", Term.con "unit" [Term.lit "(", Term.lit ")"]], Term.con "labeledArg" [Term.var "boundary", Term.lit ":", Term.con "unit" [Term.lit "(", Term.lit ")"]], Term.lit ")"], Term.con "constructor" [Term.con "labeledArg" [Term.var "name", Term.lit ":", Term.con "terminal" [Term.lit "false"]], Term.con "labeledArg" [Term.var "args", Term.lit ":", Term.con "unit" [Term.lit "(", Term.lit ")"]], Term.con "labeledArg" [Term.var "boundary", Term.lit ":", Term.con "unit" [Term.lit "(", Term.lit ")"]]]]]]
      | _ => t

    def unitDesc (t : Term) : Term :=
      match t with
      | .con "unitDesc" [] => Term.con "dataDesc" [Term.con "labeledArg" [Term.var "name", Term.lit ":", Term.con "app" [Term.var "gnameNamed", Term.con "terminal" [Term.lit "Unit"]]], Term.con "labeledArg" [Term.var "params", Term.lit ":", Term.con "unit" [Term.lit "(", Term.lit ")"]], Term.con "labeledArg" [Term.var "level", Term.lit ":", Term.con "lzero" []], Term.con "labeledArg" [Term.var "constrs", Term.lit ":", Term.con "app" [Term.lit "(", Term.con "constructor" [], Term.con "labeledArg" [Term.var "name", Term.lit ":", Term.con "terminal" [Term.lit "tt"]], Term.con "labeledArg" [Term.var "args", Term.lit ":", Term.con "unit" [Term.lit "(", Term.lit ")"]], Term.con "labeledArg" [Term.var "boundary", Term.lit ":", Term.con "unit" [Term.lit "(", Term.lit ")"]], Term.lit ")"]]]
      | _ => t

  end BuiltinDatatypes

  section StdEnv

    def stdEnv (t : Term) : Term :=
      match t with
      | .con "stdEnv" [] => Term.con "letIn" [Term.lit "(", Term.lit "let", Term.var "env0", Term.lit "=", Term.con "globalEnvEmpty" [], Term.lit "in", Term.con "letIn" [Term.lit "let", Term.var "env1", Term.lit "=", Term.con "globalEnvDeclareDatatype" [Term.con "env0" [], Term.con "natDesc" []], Term.lit "in", Term.con "letIn" [Term.lit "let", Term.var "env2", Term.lit "=", Term.con "globalEnvDeclareDatatype" [Term.con "env1" [], Term.con "listDesc" []], Term.lit "in", Term.con "letIn" [Term.lit "let", Term.var "env3", Term.lit "=", Term.con "globalEnvDeclareDatatype" [Term.con "env2" [], Term.con "circleDesc" []], Term.lit "in", Term.con "letIn" [Term.lit "let", Term.var "env4", Term.lit "=", Term.con "globalEnvDeclareDatatype" [Term.con "env3" [], Term.con "boolDesc" []], Term.lit "in", Term.con "letIn" [Term.lit "let", Term.var "env5", Term.lit "=", Term.con "globalEnvDeclareDatatype" [Term.con "env4" [], Term.con "unitDesc" []], Term.lit "in", Term.con "env5" []]]]]], Term.lit ")"]
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

    -- Derived catamorphism for term
    partial def cataterm [Inhabited α] (alg : String → List α → α) (varF : String → α) (t : Term) : α :=
      match t with
      | Term.var n => varF n
      | Term.lit s => alg "lit" []
      | Term.con tag args => alg tag (args.map (cataterm alg varF))

    -- Derived structural equality for term
    partial def eqterm (t1 t2 : Term) : Bool :=
      match t1, t2 with
      | Term.var n1, Term.var n2 => n1 == n2
      | Term.lit s1, Term.lit s2 => s1 == s2
      | Term.con tag1 args1, Term.con tag2 args2 =>
        tag1 == tag2 && args1.length == args2.length && (args1.zip args2).all fun (a, b) => eqterm a b
      | _, _ => false

  end StdEnv

end Datatype