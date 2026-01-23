/-
  AUTO-GENERATED from .lego files
  Do not edit directly.
-/

import Lego.Algebra

set_option linter.unusedVariables false

open Lego

namespace RefineMonad

  section RefineError

    def refineErrorToString (t : Term) : Term :=
      match t with
      | .con "app" [.var "refineErrorToString", .con "app" [.var "unboundVariable", n]] => Term.con "strConcat" [Term.con "terminal" [Term.lit "Unbound variable: "], n]
      | _ => t

    def refineErrorToStringExpected (t : Term) : Term :=
      match t with
      | .con "app" [.var "refineErrorToString", .con "app" [.var "expectedType", e]] => Term.con "strConcat" [Term.con "terminal" [Term.lit "Expected type, got: "], Term.con "app" [Term.var "exprToString", e]]
      | _ => t

    def refineErrorToStringMismatch (t : Term) : Term :=
      match t with
      | .con "app" [.var "refineErrorToString", .con "typeMismatch" [e1, e2]] => Term.con "strConcat" [Term.con "terminal" [Term.lit "Type mismatch: "], Term.con "strConcat" [Term.con "app" [Term.var "exprToString", e1], Term.con "strConcat" [Term.con "terminal" [Term.lit " vs "], Term.con "app" [Term.var "exprToString", e2]]]]
      | _ => t

    def refineErrorToStringConnective (t : Term) : Term :=
      match t with
      | .con "app" [.var "refineErrorToString", .con "expectedConnective" [n, e]] => Term.con "strConcat" [Term.con "terminal" [Term.lit "Expected "], Term.con "strConcat" [n, Term.con "strConcat" [Term.con "terminal" [Term.lit ", got: "], Term.con "app" [Term.var "exprToString", e]]]]
      | _ => t

    def refineErrorToStringConv (t : Term) : Term :=
      match t with
      | .con "app" [.var "refineErrorToString", .con "app" [.var "conversionFailed", n]] => Term.con "strConcat" [Term.con "terminal" [Term.lit "Conversion failed: "], n]
      | _ => t

    def refineErrorToStringMeta (t : Term) : Term :=
      match t with
      | .con "app" [.var "refineErrorToString", .con "app" [.var "unboundMeta", n]] => Term.con "strConcat" [Term.con "terminal" [Term.lit "Unbound meta: "], Term.con "app" [Term.var "natToString", n]]
      | _ => t

    def refineErrorToStringOther (t : Term) : Term :=
      match t with
      | .con "app" [.var "refineErrorToString", .con "app" [.var "otherError", n]] => n
      | _ => t

  end RefineError

  section Ident

    def identName (t : Term) : Term :=
      match t with
      | .con "app" [.var "identName", .con "anon" []] => Term.con "none" []
      | _ => t

    def identNameUser (t : Term) : Term :=
      match t with
      | .con "app" [.var "identName", .con "app" [.var "userIdent", s]] => Term.con "app" [Term.var "some", s]
      | _ => t

    def identNameMachine (t : Term) : Term :=
      match t with
      | .con "app" [.var "identName", .con "app" [.var "machineIdent", s]] => Term.con "app" [Term.var "some", s]
      | _ => t

    def identToString (t : Term) : Term :=
      match t with
      | .con "app" [.var "identToString", .con "anon" []] => Term.con "terminal" [Term.lit "_"]
      | _ => t

    def identToStringUser (t : Term) : Term :=
      match t with
      | .con "app" [.var "identToString", .con "app" [.var "userIdent", s]] => s
      | _ => t

    def identToStringMachine (t : Term) : Term :=
      match t with
      | .con "app" [.var "identToString", .con "app" [.var "machineIdent", s]] => s
      | _ => t

  end Ident

  section Cell

    def cellIdent (t : Term) : Term :=
      match t with
      | .con "app" [.var "cellIdent", .con "cell" [.con "labeledArg" [.var "id", .lit ":", i], .con "labeledArg" [.var "tp", .lit ":", t], .con "labeledArg" [.var "val", .lit ":", v]]] => i
      | _ => t

    def cellTp (t : Term) : Term :=
      match t with
      | .con "app" [.var "cellTp", .con "cell" [.con "labeledArg" [.var "id", .lit ":", i], .con "labeledArg" [.var "tp", .lit ":", t], .con "labeledArg" [.var "val", .lit ":", v]]] => t
      | _ => t

    def cellVal (t : Term) : Term :=
      match t with
      | .con "app" [.var "cellVal", .con "cell" [.con "labeledArg" [.var "id", .lit ":", i], .con "labeledArg" [.var "tp", .lit ":", t], .con "labeledArg" [.var "val", .lit ":", v]]] => v
      | _ => t

    def mkCell (t : Term) : Term :=
      match t with
      | .con "mkCell" [ident, tp] => Term.con "cell" [Term.con "labeledArg" [Term.var "id", Term.lit ":", ident], Term.con "labeledArg" [Term.var "tp", Term.lit ":", tp], Term.con "labeledArg" [Term.var "val", Term.lit ":", Term.con "none" []]]
      | _ => t

    def mkCellVal (t : Term) : Term :=
      match t with
      | .con "mkCellVal" [ident, tp, val] => Term.con "cell" [Term.con "labeledArg" [Term.var "id", Term.lit ":", ident], Term.con "labeledArg" [Term.var "tp", Term.lit ":", tp], Term.con "labeledArg" [Term.var "val", Term.lit ":", Term.con "app" [Term.var "some", val]]]
      | _ => t

  end Cell

  section LocalEnv

    def localEnvEmpty (t : Term) : Term :=
      match t with
      | .con "localEnvEmpty" [] => Term.con "localEnv" [Term.con "labeledArg" [Term.var "cells", Term.lit ":", Term.con "unit" [Term.lit "(", Term.lit ")"]], Term.con "labeledArg" [Term.var "cof", Term.lit ":", Term.con "cof_top" []]]
      | _ => t

    def localEnvSize (t : Term) : Term :=
      match t with
      | .con "app" [.var "localEnvSize", .con "localEnv" [.con "labeledArg" [.var "cells", .lit ":", cs], .con "labeledArg" [.var "cof", .lit ":", φ]]] => Term.con "app" [Term.var "length", cs]
      | _ => t

    def localEnvExtend (t : Term) : Term :=
      match t with
      | .con "localEnvExtend" [.con "localEnv" [.con "labeledArg" [.var "cells", .lit ":", cs], .con "labeledArg" [.var "cof", .lit ":", φ]], ident, tp] => Term.con "localEnv" [Term.con "labeledArg" [Term.var "cells", Term.lit ":", Term.con "tuple" [cs, Term.con "mkCell" [ident, tp]]], Term.con "labeledArg" [Term.var "cof", Term.lit ":", φ]]
      | _ => t

    def localEnvExtendVal (t : Term) : Term :=
      match t with
      | .con "localEnvExtendVal" [.con "localEnv" [.con "labeledArg" [.var "cells", .lit ":", cs], .con "labeledArg" [.var "cof", .lit ":", φ]], ident, tp, val] => Term.con "localEnv" [Term.con "labeledArg" [Term.var "cells", Term.lit ":", Term.con "tuple" [cs, Term.con "mkCellVal" [ident, tp, val]]], Term.con "labeledArg" [Term.var "cof", Term.lit ":", φ]]
      | _ => t

    def localEnvGetLocal (t : Term) : Term :=
      match t with
      | .con "localEnvGetLocal" [.con "localEnv" [.con "labeledArg" [.var "cells", .lit ":", cs], .con "labeledArg" [.var "cof", .lit ":", φ]], ix] => Term.con "listGet" [cs, Term.con "minus" [Term.con "app" [Term.var "length", cs], Term.con "num" [Term.con "number" [Term.lit "1"]], ix]]
      | _ => t

    def localEnvGetLocalTp (t : Term) : Term :=
      match t with
      | .con "localEnvGetLocalTp" [env, ix] => Term.con "caseExpr" [Term.lit "(", Term.lit "case", Term.con "localEnvGetLocal" [env, ix], Term.con "arm" [Term.lit "(", Term.var "some", Term.var "c", Term.lit ")", Term.lit "=>", Term.con "app" [Term.var "some", Term.con "app" [Term.var "cellTp", Term.var "c"]]], Term.con "arm" [Term.var "none", Term.lit "=>", Term.con "none" []], Term.lit ")"]
      | _ => t

    def localEnvResolve (t : Term) : Term :=
      match t with
      | .con "localEnvResolve" [.con "localEnv" [.con "labeledArg" [.var "cells", .lit ":", cs], .con "labeledArg" [.var "cof", .lit ":", φ]], name] => Term.con "localEnvResolveRec" [cs, name, Term.con "num" [Term.con "number" [Term.lit "0"]]]
      | _ => t

    def localEnvResolveRec (t : Term) : Term :=
      match t with
      | .con "localEnvResolveRec" [.con "unit" [.lit "(", .lit ")"], name, i] => Term.con "none" []
      | _ => t

    def localEnvResolveRecCons (t : Term) : Term :=
      match t with
      | .con "localEnvResolveRec" [.con "tuple" [cs, c], name, i] => Term.con "caseExpr" [Term.lit "(", Term.lit "case", Term.con "app" [Term.var "identName", Term.con "app" [Term.var "cellIdent", c]], Term.con "arm" [Term.lit "(", Term.var "some", Term.var "n", Term.lit ")", Term.lit "=>", Term.con "if" [Term.con "eq" [Term.var "n", name], Term.con "then" [Term.con "app" [Term.var "some", i], Term.var "else"], Term.con "localEnvResolveRec" [cs, name, Term.con "app" [Term.var "succ", i]]]], Term.con "arm" [Term.var "none", Term.lit "=>", Term.con "localEnvResolveRec" [cs, name, Term.con "app" [Term.var "succ", i]]], Term.lit ")"]
      | _ => t

    def localEnvAssume (t : Term) : Term :=
      match t with
      | .con "localEnvAssume" [.con "localEnv" [.con "labeledArg" [.var "cells", .lit ":", cs], .con "labeledArg" [.var "cof", .lit ":", φ]], ψ] => Term.con "localEnv" [Term.con "labeledArg" [Term.var "cells", Term.lit ":", cs], Term.con "labeledArg" [Term.var "cof", Term.lit ":", Term.con "cof_and" [φ, ψ]]]
      | _ => t

  end LocalEnv

  section GlobalDef

    def globalDefName (t : Term) : Term :=
      match t with
      | .con "app" [.var "globalDefName", .con "globalDef" [.con "labeledArg" [.var "name", .lit ":", n], .con "labeledArg" [.var "tp", .lit ":", t], .con "labeledArg" [.var "val", .lit ":", v]]] => n
      | _ => t

    def globalDefTp (t : Term) : Term :=
      match t with
      | .con "app" [.var "globalDefTp", .con "globalDef" [.con "labeledArg" [.var "name", .lit ":", n], .con "labeledArg" [.var "tp", .lit ":", t], .con "labeledArg" [.var "val", .lit ":", v]]] => t
      | _ => t

    def globalDefVal (t : Term) : Term :=
      match t with
      | .con "app" [.var "globalDefVal", .con "globalDef" [.con "labeledArg" [.var "name", .lit ":", n], .con "labeledArg" [.var "tp", .lit ":", t], .con "labeledArg" [.var "val", .lit ":", v]]] => v
      | _ => t

  end GlobalDef

  section GlobalEnvState

    def globalEnvStateEmpty (t : Term) : Term :=
      match t with
      | .con "globalEnvStateEmpty" [] => Term.con "globalEnvState" [Term.con "labeledArg" [Term.var "defs", Term.lit ":", Term.con "unit" [Term.lit "(", Term.lit ")"]], Term.con "labeledArg" [Term.var "holes", Term.lit ":", Term.con "unit" [Term.lit "(", Term.lit ")"]], Term.con "labeledArg" [Term.var "nextHole", Term.lit ":", Term.con "num" [Term.con "number" [Term.lit "0"]]], Term.con "labeledArg" [Term.var "nextMeta", Term.lit ":", Term.con "num" [Term.con "number" [Term.lit "0"]]]]
      | _ => t

    def globalEnvStateAddDef (t : Term) : Term :=
      match t with
      | .con "globalEnvStateAddDef" [name, tp, val, .con "globalEnvState" [.con "labeledArg" [.var "defs", .lit ":", ds], .con "labeledArg" [.var "holes", .lit ":", hs], .con "labeledArg" [.var "nextHole", .lit ":", nh], .con "labeledArg" [.var "nextMeta", .lit ":", nm]]] => Term.con "globalEnvState" [Term.con "labeledArg" [Term.var "defs", Term.lit ":", Term.con "tuple" [ds, Term.con "globalDef" [Term.con "labeledArg" [Term.var "name", Term.lit ":", name], Term.con "labeledArg" [Term.var "tp", Term.lit ":", tp], Term.con "labeledArg" [Term.var "val", Term.lit ":", val]]]], Term.con "labeledArg" [Term.var "holes", Term.lit ":", hs], Term.con "labeledArg" [Term.var "nextHole", Term.lit ":", nh], Term.con "labeledArg" [Term.var "nextMeta", Term.lit ":", nm]]
      | _ => t

    def globalEnvStateLookupDef (t : Term) : Term :=
      match t with
      | .con "globalEnvStateLookupDef" [name, .con "globalEnvState" [.con "labeledArg" [.var "defs", .lit ":", ds], .con "labeledArg" [.var "holes", .lit ":", hs], .con "labeledArg" [.var "nextHole", .lit ":", nh], .con "labeledArg" [.var "nextMeta", .lit ":", nm]]] => Term.con "lookupDef" [name, ds]
      | _ => t

    def lookupDef (t : Term) : Term :=
      match t with
      | .con "lookupDef" [name, .con "unit" [.lit "(", .lit ")"]] => Term.con "none" []
      | _ => t

    def lookupDefMatch (t : Term) : Term :=
      match t with
      | .con "lookupDef" [name, .con "tuple" [ds, .con "globalDef" [.con "labeledArg" [.var "name", .lit ":", name_dup], .con "labeledArg" [.var "tp", .lit ":", t], .con "labeledArg" [.var "val", .lit ":", v]]]] => Term.con "app" [Term.var "some", Term.con "globalDef" [Term.con "labeledArg" [Term.var "name", Term.lit ":", name], Term.con "labeledArg" [Term.var "tp", Term.lit ":", t], Term.con "labeledArg" [Term.var "val", Term.lit ":", v]]]
      | _ => t

    def lookupDefMiss (t : Term) : Term :=
      match t with
      | .con "lookupDef" [name, .con "tuple" [ds, d]] => Term.con "lookupDef" [name, ds]
      | _ => t

    def globalEnvStateAddHole (t : Term) : Term :=
      match t with
      | .con "globalEnvStateAddHole" [tp, .con "globalEnvState" [.con "labeledArg" [.var "defs", .lit ":", ds], .con "labeledArg" [.var "holes", .lit ":", hs], .con "labeledArg" [.var "nextHole", .lit ":", nh], .con "labeledArg" [.var "nextMeta", .lit ":", nm]]] => Term.con "tuple" [Term.lit "(", Term.con "globalEnvState" [Term.con "labeledArg" [Term.var "defs", Term.lit ":", ds], Term.con "labeledArg" [Term.var "holes", Term.lit ":", Term.con "tuple" [hs, Term.con "nTuple" [Term.lit "(", nh, Term.lit ",", tp, Term.lit ",", Term.con "none" [], Term.lit ")"]]], Term.con "labeledArg" [Term.var "nextHole", Term.lit ":", Term.con "app" [Term.var "succ", nh]], Term.con "labeledArg" [Term.var "nextMeta", Term.lit ":", nm]], Term.lit ",", nh, Term.lit ")"]
      | _ => t

    def globalEnvStateFreshMeta (t : Term) : Term :=
      match t with
      | .con "app" [.var "globalEnvStateFreshMeta", .con "globalEnvState" [.con "labeledArg" [.var "defs", .lit ":", ds], .con "labeledArg" [.var "holes", .lit ":", hs], .con "labeledArg" [.var "nextHole", .lit ":", nh], .con "labeledArg" [.var "nextMeta", .lit ":", nm]]] => Term.con "tuple" [Term.lit "(", Term.con "globalEnvState" [Term.con "labeledArg" [Term.var "defs", Term.lit ":", ds], Term.con "labeledArg" [Term.var "holes", Term.lit ":", hs], Term.con "labeledArg" [Term.var "nextHole", Term.lit ":", nh], Term.con "labeledArg" [Term.var "nextMeta", Term.lit ":", Term.con "app" [Term.var "succ", nm]]], Term.lit ",", nm, Term.lit ")"]
      | _ => t

    def globalEnvStateSolveHole (t : Term) : Term :=
      match t with
      | .con "globalEnvStateSolveHole" [id, sol, .con "globalEnvState" [.con "labeledArg" [.var "defs", .lit ":", ds], .con "labeledArg" [.var "holes", .lit ":", hs], .con "labeledArg" [.var "nextHole", .lit ":", nh], .con "labeledArg" [.var "nextMeta", .lit ":", nm]]] => Term.con "globalEnvState" [Term.con "labeledArg" [Term.var "defs", Term.lit ":", ds], Term.con "labeledArg" [Term.var "holes", Term.lit ":", Term.con "solveHoleInList" [id, sol, hs]], Term.con "labeledArg" [Term.var "nextHole", Term.lit ":", nh], Term.con "labeledArg" [Term.var "nextMeta", Term.lit ":", nm]]
      | _ => t

    def solveHoleInList (t : Term) : Term :=
      match t with
      | .con "solveHoleInList" [id, sol, .con "unit" [.lit "(", .lit ")"]] => Term.con "unit" [Term.lit "(", Term.lit ")"]
      | _ => t

    def solveHoleInListMatch (t : Term) : Term :=
      match t with
      | .con "solveHoleInList" [id, sol, .con "app" [.lit "(", .lit "(", id_dup, .lit ",", tp, .lit ",", old, .lit ")", rest, .lit ")"]] => Term.con "tuple" [Term.con "nTuple" [Term.lit "(", id, Term.lit ",", tp, Term.lit ",", Term.con "app" [Term.var "some", sol], Term.lit ")"], Term.con "solveHoleInList" [id, sol, rest]]
      | _ => t

    def solveHoleInListMiss (t : Term) : Term :=
      match t with
      | .con "solveHoleInList" [id, sol, .con "app" [.lit "(", .lit "(", hid, .lit ",", tp, .lit ",", old, .lit ")", rest, .lit ")"]] => Term.con "tuple" [Term.con "nTuple" [Term.lit "(", hid, Term.lit ",", tp, Term.lit ",", old, Term.lit ")"], Term.con "solveHoleInList" [id, sol, rest]]
      | _ => t

    def globalEnvStateGetHoleSolution (t : Term) : Term :=
      match t with
      | .con "globalEnvStateGetHoleSolution" [id, .con "globalEnvState" [.con "labeledArg" [.var "defs", .lit ":", ds], .con "labeledArg" [.var "holes", .lit ":", hs], .con "labeledArg" [.var "nextHole", .lit ":", nh], .con "labeledArg" [.var "nextMeta", .lit ":", nm]]] => Term.con "getHoleSolution" [id, hs]
      | _ => t

    def getHoleSolution (t : Term) : Term :=
      match t with
      | .con "getHoleSolution" [id, .con "unit" [.lit "(", .lit ")"]] => Term.con "none" []
      | _ => t

    def getHoleSolutionMatch (t : Term) : Term :=
      match t with
      | .con "getHoleSolution" [id, .con "app" [.lit "(", .lit "(", id_dup, .lit ",", tp, .lit ",", sol, .lit ")", rest, .lit ")"]] => sol
      | _ => t

    def getHoleSolutionMiss (t : Term) : Term :=
      match t with
      | .con "getHoleSolution" [id, .con "app" [.lit "(", .lit "(", hid, .lit ",", tp, .lit ",", sol, .lit ")", rest, .lit ")"]] => Term.con "getHoleSolution" [id, rest]
      | _ => t

  end GlobalEnvState

  section SourceLoc

    def sourceLocFile (t : Term) : Term :=
      match t with
      | .con "app" [.var "sourceLocFile", .con "sourceLoc" [.con "labeledArg" [.var "file", .lit ":", f], .con "labeledArg" [.var "line", .lit ":", l], .con "labeledArg" [.var "col", .lit ":", c]]] => f
      | _ => t

    def sourceLocLine (t : Term) : Term :=
      match t with
      | .con "app" [.var "sourceLocLine", .con "sourceLoc" [.con "labeledArg" [.var "file", .lit ":", f], .con "labeledArg" [.var "line", .lit ":", l], .con "labeledArg" [.var "col", .lit ":", c]]] => l
      | _ => t

    def sourceLocCol (t : Term) : Term :=
      match t with
      | .con "app" [.var "sourceLocCol", .con "sourceLoc" [.con "labeledArg" [.var "file", .lit ":", f], .con "labeledArg" [.var "line", .lit ":", l], .con "labeledArg" [.var "col", .lit ":", c]]] => c
      | _ => t

  end SourceLoc

  section RefineCtx

    def refineCtxEmpty (t : Term) : Term :=
      match t with
      | .con "refineCtxEmpty" [] => Term.con "refineCtx" [Term.con "labeledArg" [Term.var "local", Term.lit ":", Term.con "localEnvEmpty" []], Term.con "labeledArg" [Term.var "loc", Term.lit ":", Term.con "none" []]]
      | _ => t

    def refineCtxLocalEnv (t : Term) : Term :=
      match t with
      | .con "app" [.var "refineCtxLocalEnv", .con "refineCtx" [.con "labeledArg" [.var "local", .lit ":", l], .con "labeledArg" [.var "loc", .lit ":", s]]] => l
      | _ => t

    def refineCtxLoc (t : Term) : Term :=
      match t with
      | .con "app" [.var "refineCtxLoc", .con "refineCtx" [.con "labeledArg" [.var "local", .lit ":", l], .con "labeledArg" [.var "loc", .lit ":", s]]] => s
      | _ => t

    def refineCtxSetLocal (t : Term) : Term :=
      match t with
      | .con "refineCtxSetLocal" [env, .con "refineCtx" [.con "labeledArg" [.var "local", .lit ":", l], .con "labeledArg" [.var "loc", .lit ":", s]]] => Term.con "refineCtx" [Term.con "labeledArg" [Term.var "local", Term.lit ":", env], Term.con "labeledArg" [Term.var "loc", Term.lit ":", s]]
      | _ => t

    def refineCtxSetLoc (t : Term) : Term :=
      match t with
      | .con "refineCtxSetLoc" [loc, .con "refineCtx" [.con "labeledArg" [.var "local", .lit ":", l], .con "labeledArg" [.var "loc", .lit ":", s]]] => Term.con "refineCtx" [Term.con "labeledArg" [Term.var "local", Term.lit ":", l], Term.con "labeledArg" [Term.var "loc", Term.lit ":", Term.con "app" [Term.var "some", loc]]]
      | _ => t

  end RefineCtx

  section RefineState

    def refineStateEmpty (t : Term) : Term :=
      match t with
      | .con "refineStateEmpty" [] => Term.con "app" [Term.var "refineState", Term.con "labeledArg" [Term.var "global", Term.lit ":", Term.con "globalEnvStateEmpty" []]]
      | _ => t

    def refineStateGlobal (t : Term) : Term :=
      match t with
      | .con "app" [.var "refineStateGlobal", .con "app" [.var "refineState", .con "labeledArg" [.var "global", .lit ":", g]]] => g
      | _ => t

    def refineStateSetGlobal (t : Term) : Term :=
      match t with
      | .con "refineStateSetGlobal" [g, .con "app" [.var "refineState", .con "labeledArg" [.var "global", .lit ":", old]]] => Term.con "app" [Term.var "refineState", Term.con "labeledArg" [Term.var "global", Term.lit ":", g]]
      | _ => t

  end RefineState

  section RefineResult

    def isRefineOk (t : Term) : Term :=
      match t with
      | .con "app" [.var "isRefineOk", .con "refineOk" [a, s]] => Term.con "true" []
      | _ => t

    def isRefineOkErr (t : Term) : Term :=
      match t with
      | .con "app" [.var "isRefineOk", .con "refineErr" [e, l]] => Term.con "false" []
      | _ => t

    def refineResultVal (t : Term) : Term :=
      match t with
      | .con "app" [.var "refineResultVal", .con "refineOk" [a, s]] => Term.con "app" [Term.var "some", a]
      | _ => t

    def refineResultValErr (t : Term) : Term :=
      match t with
      | .con "app" [.var "refineResultVal", .con "refineErr" [e, l]] => Term.con "none" []
      | _ => t

    def refineResultState (t : Term) : Term :=
      match t with
      | .con "app" [.var "refineResultState", .con "refineOk" [a, s]] => Term.con "app" [Term.var "some", s]
      | _ => t

    def refineResultStateErr (t : Term) : Term :=
      match t with
      | .con "app" [.var "refineResultState", .con "refineErr" [e, l]] => Term.con "none" []
      | _ => t

  end RefineResult

  section RefineM

    def refinePure (t : Term) : Term :=
      match t with
      | .con "refinePure" [a, ctx, st] => Term.con "refineOk" [a, st]
      | _ => t

    def refineBind (t : Term) : Term :=
      match t with
      | .con "refineBind" [ma, f, ctx, st] => Term.con "caseExpr" [Term.lit "(", Term.lit "case", Term.con "tuple" [ma, ctx, st], Term.con "arm" [Term.lit "(", Term.var "refineOk", Term.var "a", Term.var "st'", Term.lit ")", Term.lit "=>", Term.con "tuple" [Term.con "app" [Term.lit "(", f, Term.var "a", Term.lit ")"], ctx, Term.var "st'"]], Term.con "arm" [Term.lit "(", Term.var "refineErr", Term.var "e", Term.var "l", Term.lit ")", Term.lit "=>", Term.con "refineErr" [Term.var "e", Term.var "l"]], Term.lit ")"]
      | _ => t

    def refineGetLocalEnv (t : Term) : Term :=
      match t with
      | .con "refineGetLocalEnv" [ctx, st] => Term.con "refineOk" [Term.con "app" [Term.var "refineCtxLocalEnv", ctx], st]
      | _ => t

    def refineGetGlobalEnv (t : Term) : Term :=
      match t with
      | .con "refineGetGlobalEnv" [ctx, st] => Term.con "refineOk" [Term.con "app" [Term.var "refineStateGlobal", st], st]
      | _ => t

    def refineModifyGlobal (t : Term) : Term :=
      match t with
      | .con "refineModifyGlobal" [f, ctx, st] => Term.con "refineOk" [Term.con "unit" [Term.lit "(", Term.lit ")"], Term.con "refineStateSetGlobal" [Term.con "tuple" [f, Term.con "app" [Term.var "refineStateGlobal", st]], st]]
      | _ => t

    def refineWithLocal (t : Term) : Term :=
      match t with
      | .con "refineWithLocal" [f, ma, ctx, st] => Term.con "tuple" [ma, Term.con "refineCtxSetLocal" [Term.con "tuple" [f, Term.con "app" [Term.var "refineCtxLocalEnv", ctx]], ctx], st]
      | _ => t

    def refineWithLoc (t : Term) : Term :=
      match t with
      | .con "refineWithLoc" [loc, ma, ctx, st] => Term.con "tuple" [ma, Term.con "refineCtxSetLoc" [loc, ctx], st]
      | _ => t

    def refineThrow (t : Term) : Term :=
      match t with
      | .con "refineThrow" [e, ctx, st] => Term.con "refineErr" [e, Term.con "app" [Term.var "refineCtxLoc", ctx]]
      | _ => t

  end RefineM

  section VarOps

    def refineAbstract (t : Term) : Term :=
      match t with
      | .con "refineAbstract" [ident, tp, k, ctx, st] => Term.con "letIn" [Term.lit "(", Term.lit "let", Term.lit "$", Term.var "var", Term.lit "=", Term.con "app" [Term.var "ix", Term.con "app" [Term.var "localEnvSize", Term.con "app" [Term.var "refineCtxLocalEnv", ctx]]], Term.lit "in", Term.con "letIn" [Term.lit "(", Term.lit "let", Term.lit "$", Term.var "newEnv", Term.lit "=", Term.con "localEnvExtend" [Term.con "app" [Term.var "refineCtxLocalEnv", ctx], ident, tp], Term.lit "in", Term.con "tuple" [Term.con "app" [Term.lit "(", k, Term.var "var", Term.lit ")"], Term.con "refineCtxSetLocal" [Term.var "newEnv", ctx], st], Term.lit ")"], Term.lit ")"]
      | _ => t

    def refineGetLocalTp (t : Term) : Term :=
      match t with
      | .con "refineGetLocalTp" [ix, ctx, st] => Term.con "caseExpr" [Term.lit "(", Term.lit "case", Term.con "localEnvGetLocalTp" [Term.con "app" [Term.var "refineCtxLocalEnv", ctx], ix], Term.con "arm" [Term.lit "(", Term.var "some", Term.var "tp", Term.lit ")", Term.lit "=>", Term.con "refineOk" [Term.var "tp", st]], Term.con "arm" [Term.var "none", Term.lit "=>", Term.con "refineErr" [Term.con "app" [Term.var "unboundVariable", Term.con "app" [Term.var "natToString", ix]], Term.con "app" [Term.var "refineCtxLoc", ctx]]], Term.lit ")"]
      | _ => t

    def refineResolveName (t : Term) : Term :=
      match t with
      | .con "refineResolveName" [name, ctx, st] => Term.con "caseExpr" [Term.lit "(", Term.lit "case", Term.con "localEnvResolve" [Term.con "app" [Term.var "refineCtxLocalEnv", ctx], name], Term.con "arm" [Term.lit "(", Term.var "some", Term.var "ix", Term.lit ")", Term.lit "=>", Term.con "refineOk" [Term.con "app" [Term.var "inl", Term.var "ix"], st]], Term.con "arm" [Term.var "none", Term.lit "=>", Term.con "caseExpr" [Term.lit "(", Term.lit "case", Term.con "globalEnvStateLookupDef" [name, Term.con "app" [Term.var "refineStateGlobal", st]], Term.con "arm" [Term.lit "(", Term.var "some", Term.var "def", Term.lit ")", Term.lit "=>", Term.con "refineOk" [Term.con "app" [Term.var "inr", Term.var "def"], st]], Term.con "arm" [Term.var "none", Term.lit "=>", Term.con "refineErr" [Term.con "app" [Term.var "unboundVariable", name], Term.con "app" [Term.var "refineCtxLoc", ctx]]], Term.lit ")"]], Term.lit ")"]
      | _ => t

  end VarOps

  section HoleOps

    def refineFreshHole (t : Term) : Term :=
      match t with
      | .con "refineFreshHole" [tp, ctx, st] => Term.con "letTupleIn" [Term.lit "(", Term.lit "let", Term.lit "(", Term.var "st'", Term.lit ",", Term.var "id", Term.lit ")", Term.lit "=", Term.con "globalEnvStateAddHole" [tp, Term.con "app" [Term.var "refineStateGlobal", st]], Term.lit "in", Term.con "refineOk" [Term.con "tuple" [Term.lit "(", Term.var "id", Term.lit ",", Term.con "app" [Term.var "lit", Term.con "strConcat" [Term.con "terminal" [Term.lit "?"], Term.con "app" [Term.var "natToString", Term.var "id"]]], Term.lit ")"], Term.con "refineStateSetGlobal" [Term.var "st'", st]], Term.lit ")"]
      | _ => t

    def refineFreshMeta (t : Term) : Term :=
      match t with
      | .con "refineFreshMeta" [ctx, st] => Term.con "letTupleIn" [Term.lit "(", Term.lit "let", Term.lit "(", Term.var "g'", Term.lit ",", Term.var "id", Term.lit ")", Term.lit "=", Term.con "app" [Term.var "globalEnvStateFreshMeta", Term.con "app" [Term.var "refineStateGlobal", st]], Term.lit "in", Term.con "refineOk" [Term.var "id", Term.con "refineStateSetGlobal" [Term.var "g'", st]], Term.lit ")"]
      | _ => t

    def refineSolveHole (t : Term) : Term :=
      match t with
      | .con "refineSolveHole" [id, sol, ctx, st] => Term.con "refineOk" [Term.con "unit" [Term.lit "(", Term.lit ")"], Term.con "refineStateSetGlobal" [Term.con "globalEnvStateSolveHole" [id, sol, Term.con "app" [Term.var "refineStateGlobal", st]], st]]
      | _ => t

    def refineGetHoleSolution (t : Term) : Term :=
      match t with
      | .con "refineGetHoleSolution" [id, ctx, st] => Term.con "refineOk" [Term.con "globalEnvStateGetHoleSolution" [id, Term.con "app" [Term.var "refineStateGlobal", st]], st]
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

  end HoleOps

end RefineMonad