/-
  AUTO-GENERATED from .lego files
  Do not edit directly.
-/

import Lego.Algebra

open Lego

namespace Splice

  section SpliceEnv

    def spliceEnvEmpty (t : Term) : Term :=
      match t with
      | .con "spliceEnvEmpty" [] => Term.con "spliceEnv" [Term.con "labeledArg" [Term.var "conEnv", Term.lit ":", Term.con "unit" [Term.lit "(", Term.lit ")"]], Term.con "labeledArg" [Term.var "tpEnv", Term.lit ":", Term.con "unit" [Term.lit "(", Term.lit ")"]]]
      | _ => t

    def spliceEnvAddCon (t : Term) : Term :=
      match t with
      | .con "spliceEnvAddCon" [e, .con "spliceEnv" [.con "labeledArg" [.var "conEnv", .lit ":", cs], .con "labeledArg" [.var "tpEnv", .lit ":", ts]]] => Term.con "spliceEnv" [Term.con "labeledArg" [Term.var "conEnv", Term.lit ":", Term.con "tuple" [e, cs]], Term.con "labeledArg" [Term.var "tpEnv", Term.lit ":", ts]]
      | _ => t

    def spliceEnvAddTp (t : Term) : Term :=
      match t with
      | .con "spliceEnvAddTp" [e, .con "spliceEnv" [.con "labeledArg" [.var "conEnv", .lit ":", cs], .con "labeledArg" [.var "tpEnv", .lit ":", ts]]] => Term.con "spliceEnv" [Term.con "labeledArg" [Term.var "conEnv", Term.lit ":", cs], Term.con "labeledArg" [Term.var "tpEnv", Term.lit ":", Term.con "tuple" [e, ts]]]
      | _ => t

    def spliceEnvConLevel (t : Term) : Term :=
      match t with
      | .con "app" [.var "spliceEnvConLevel", .con "spliceEnv" [.con "labeledArg" [.var "conEnv", .lit ":", cs], .con "labeledArg" [.var "tpEnv", .lit ":", ts]]] => Term.con "app" [Term.var "length", cs]
      | _ => t

    def spliceEnvTpLevel (t : Term) : Term :=
      match t with
      | .con "app" [.var "spliceEnvTpLevel", .con "spliceEnv" [.con "labeledArg" [.var "conEnv", .lit ":", cs], .con "labeledArg" [.var "tpEnv", .lit ":", ts]]] => Term.con "app" [Term.var "length", ts]
      | _ => t

  end SpliceEnv

  section SpliceM

    def spliceRun (t : Term) : Term :=
      match t with
      | .con "app" [.var "spliceRun", s] => Term.con "tuple" [s, Term.con "spliceEnvEmpty" []]
      | _ => t

    def spliceEval (t : Term) : Term :=
      match t with
      | .con "app" [.var "spliceEval", s] => Term.con "app" [Term.var "fst", Term.con "app" [Term.var "spliceRun", s]]
      | _ => t

    def spliceGetEnv (t : Term) : Term :=
      match t with
      | .con "app" [.var "spliceGetEnv", s] => Term.con "app" [Term.var "snd", Term.con "app" [Term.var "spliceRun", s]]
      | _ => t

    def splicePure (t : Term) : Term :=
      match t with
      | .con "splicePure" [a, env] => Term.con "tuple" [Term.lit "(", a, Term.lit ",", env, Term.lit ")"]
      | _ => t

    def spliceBind (t : Term) : Term :=
      match t with
      | .con "spliceBind" [m, f, env] => Term.con "letTupleIn" [Term.lit "(", Term.lit "let", Term.lit "(", Term.var "a", Term.lit ",", Term.var "env'", Term.lit ")", Term.lit "=", Term.con "tuple" [m, env], Term.lit "in", Term.con "tuple" [Term.con "app" [Term.lit "(", f, Term.var "a", Term.lit ")"], Term.var "env'"], Term.lit ")"]
      | _ => t

    def spliceRead (t : Term) : Term :=
      match t with
      | .con "app" [.var "spliceRead", env] => Term.con "tuple" [Term.lit "(", env, Term.lit ",", env, Term.lit ")"]
      | _ => t

    def spliceModify (t : Term) : Term :=
      match t with
      | .con "spliceModify" [f, env] => Term.con "tuple" [Term.lit "(", Term.con "unit" [Term.lit "(", Term.lit ")"], Term.lit ",", Term.con "tuple" [f, env], Term.lit ")"]
      | _ => t

  end SpliceM

  section Foreign

    def foreign (t : Term) : Term :=
      match t with
      | .con "foreign" [con, k, env] => Term.con "letIn" [Term.lit "(", Term.lit "let", Term.lit "$", Term.var "lvl", Term.lit "=", Term.con "app" [Term.var "spliceEnvConLevel", env], Term.lit "in", Term.con "letIn" [Term.lit "(", Term.lit "let", Term.lit "$", Term.var "env'", Term.lit "=", Term.con "spliceEnvAddCon" [con, env], Term.lit "in", Term.con "letIn" [Term.lit "(", Term.lit "let", Term.lit "$", Term.var "var", Term.lit "=", Term.con "app" [Term.var "ix", Term.var "lvl"], Term.lit "in", Term.con "tuple" [Term.con "app" [Term.lit "(", k, Term.var "var", Term.lit ")"], Term.var "env'"], Term.lit ")"], Term.lit ")"], Term.lit ")"]
      | _ => t

    def foreignList (t : Term) : Term :=
      match t with
      | .con "foreignList" [.con "unit" [.lit "(", .lit ")"], k, env] => Term.con "tuple" [Term.con "app" [Term.lit "(", k, Term.con "unit" [Term.lit "(", Term.lit ")"], Term.lit ")"], env]
      | _ => t

    def foreignListCons (t : Term) : Term :=
      match t with
      | .con "foreignList" [.con "tuple" [c, cs], k, env] => Term.con "foreign" [c, Term.con "app" [Term.var "lam", Term.con "foreignList" [cs, Term.con "app" [Term.var "lam", Term.con "app" [Term.lit "(", k, Term.con "tuple" [Term.con "app" [Term.lit "(", Term.con "ix" [], Term.con "num" [Term.con "number" [Term.lit "1"]], Term.lit ")"], Term.con "app" [Term.var "ix", Term.con "num" [Term.con "number" [Term.lit "0"]]]], Term.lit ")"]], Term.var "env'"]], env]
      | _ => t

    def foreignDim (t : Term) : Term :=
      match t with
      | .con "foreignDim" [d, k, env] => Term.con "foreign" [d, k, env]
      | _ => t

    def foreignCof (t : Term) : Term :=
      match t with
      | .con "foreignCof" [φ, k, env] => Term.con "foreign" [φ, k, env]
      | _ => t

    def foreignClo (t : Term) : Term :=
      match t with
      | .con "foreignClo" [clo, k, env] => Term.con "foreign" [Term.con "app" [Term.var "lam", clo], k, env]
      | _ => t

    def foreignTp (t : Term) : Term :=
      match t with
      | .con "foreignTp" [tp, k, env] => Term.con "letIn" [Term.lit "(", Term.lit "let", Term.lit "$", Term.var "lvl", Term.lit "=", Term.con "app" [Term.var "spliceEnvTpLevel", env], Term.lit "in", Term.con "letIn" [Term.lit "(", Term.lit "let", Term.lit "$", Term.var "env'", Term.lit "=", Term.con "spliceEnvAddTp" [tp, env], Term.lit "in", Term.con "letIn" [Term.lit "(", Term.lit "let", Term.lit "$", Term.var "var", Term.lit "=", Term.con "app" [Term.var "ix", Term.var "lvl"], Term.lit "in", Term.con "tuple" [Term.con "app" [Term.lit "(", k, Term.var "var", Term.lit ")"], Term.var "env'"], Term.lit ")"], Term.lit ")"], Term.lit ")"]
      | _ => t

  end Foreign

  section SpliceBuilders

    def spliceLam (t : Term) : Term :=
      match t with
      | .con "spliceLam" [name, bodyBuilder, env] => Term.con "letTupleIn" [Term.lit "(", Term.lit "let", Term.lit "(", Term.var "body", Term.lit ",", Term.var "env'", Term.lit ")", Term.lit "=", Term.con "tuple" [bodyBuilder, Term.con "spliceEnvAddCon" [Term.con "app" [Term.var "ix", Term.con "app" [Term.var "spliceEnvConLevel", env]], env]], Term.lit "in", Term.con "tuple" [Term.lit "(", Term.con "app" [Term.var "lam", Term.var "body"], Term.lit ",", Term.var "env'", Term.lit ")"], Term.lit ")"]
      | _ => t

    def splicePi (t : Term) : Term :=
      match t with
      | .con "splicePi" [name, domBuilder, codBuilder, env] => Term.con "letTupleIn" [Term.lit "(", Term.lit "let", Term.lit "(", Term.var "dom", Term.lit ",", Term.var "env1", Term.lit ")", Term.lit "=", Term.con "tuple" [domBuilder, env], Term.lit "in", Term.con "letTupleIn" [Term.lit "(", Term.lit "let", Term.lit "(", Term.var "cod", Term.lit ",", Term.var "env2", Term.lit ")", Term.lit "=", Term.con "tuple" [codBuilder, Term.con "spliceEnvAddCon" [Term.con "app" [Term.var "ix", Term.con "app" [Term.var "spliceEnvConLevel", Term.var "env1"]], Term.var "env1"]], Term.lit "in", Term.con "tuple" [Term.lit "(", Term.con "pi" [Term.var "dom", Term.var "cod"], Term.lit ",", Term.var "env2", Term.lit ")"], Term.lit ")"], Term.lit ")"]
      | _ => t

    def spliceSigma (t : Term) : Term :=
      match t with
      | .con "spliceSigma" [name, fstTyBuilder, sndTyBuilder, env] => Term.con "letTupleIn" [Term.lit "(", Term.lit "let", Term.lit "(", Term.var "fstTy", Term.lit ",", Term.var "env1", Term.lit ")", Term.lit "=", Term.con "tuple" [fstTyBuilder, env], Term.lit "in", Term.con "letTupleIn" [Term.lit "(", Term.lit "let", Term.lit "(", Term.var "sndTy", Term.lit ",", Term.var "env2", Term.lit ")", Term.lit "=", Term.con "tuple" [sndTyBuilder, Term.con "spliceEnvAddCon" [Term.con "app" [Term.var "ix", Term.con "app" [Term.var "spliceEnvConLevel", Term.var "env1"]], Term.var "env1"]], Term.lit "in", Term.con "tuple" [Term.lit "(", Term.con "sigma" [Term.var "fstTy", Term.var "sndTy"], Term.lit ",", Term.var "env2", Term.lit ")"], Term.lit ")"], Term.lit ")"]
      | _ => t

    def splicePlam (t : Term) : Term :=
      match t with
      | .con "splicePlam" [bodyBuilder, env] => Term.con "letTupleIn" [Term.lit "(", Term.lit "let", Term.lit "(", Term.var "body", Term.lit ",", Term.var "env'", Term.lit ")", Term.lit "=", Term.con "tuple" [bodyBuilder, Term.con "spliceEnvAddCon" [Term.con "app" [Term.var "ix", Term.con "app" [Term.var "spliceEnvConLevel", env]], env]], Term.lit "in", Term.con "tuple" [Term.lit "(", Term.con "app" [Term.var "plam", Term.var "body"], Term.lit ",", Term.var "env'", Term.lit ")"], Term.lit ")"]
      | _ => t

    def splicePath (t : Term) : Term :=
      match t with
      | .con "splicePath" [aBuilder, lBuilder, rBuilder, env] => Term.con "letTupleIn" [Term.lit "(", Term.lit "let", Term.lit "(", Term.var "a", Term.lit ",", Term.var "env1", Term.lit ")", Term.lit "=", Term.con "tuple" [aBuilder, env], Term.lit "in", Term.con "letTupleIn" [Term.lit "(", Term.lit "let", Term.lit "(", Term.var "l", Term.lit ",", Term.var "env2", Term.lit ")", Term.lit "=", Term.con "tuple" [lBuilder, Term.var "env1"], Term.lit "in", Term.con "letTupleIn" [Term.lit "(", Term.lit "let", Term.lit "(", Term.var "r", Term.lit ",", Term.var "env3", Term.lit ")", Term.lit "=", Term.con "tuple" [rBuilder, Term.var "env2"], Term.lit "in", Term.con "tuple" [Term.lit "(", Term.con "path" [Term.var "a", Term.var "l", Term.var "r"], Term.lit ",", Term.var "env3", Term.lit ")"], Term.lit ")"], Term.lit ")"], Term.lit ")"]
      | _ => t

  end SpliceBuilders

  section SpliceDim

    def spliceDim0 (t : Term) : Term :=
      match t with
      | .con "app" [.var "spliceDim0", env] => Term.con "tuple" [Term.lit "(", Term.con "dim0" [], Term.lit ",", env, Term.lit ")"]
      | _ => t

    def spliceDim1 (t : Term) : Term :=
      match t with
      | .con "app" [.var "spliceDim1", env] => Term.con "tuple" [Term.lit "(", Term.con "dim1" [], Term.lit ",", env, Term.lit ")"]
      | _ => t

    def spliceDimVar (t : Term) : Term :=
      match t with
      | .con "spliceDimVar" [i, env] => Term.con "tuple" [Term.lit "(", Term.con "app" [Term.var "ix", i], Term.lit ",", env, Term.lit ")"]
      | _ => t

    def spliceDimMeet (t : Term) : Term :=
      match t with
      | .con "spliceDimMeet" [d1Builder, d2Builder, env] => Term.con "letTupleIn" [Term.lit "(", Term.lit "let", Term.lit "(", Term.var "d1", Term.lit ",", Term.var "env1", Term.lit ")", Term.lit "=", Term.con "tuple" [d1Builder, env], Term.lit "in", Term.con "letTupleIn" [Term.lit "(", Term.lit "let", Term.lit "(", Term.var "d2", Term.lit ",", Term.var "env2", Term.lit ")", Term.lit "=", Term.con "tuple" [d2Builder, Term.var "env1"], Term.lit "in", Term.con "tuple" [Term.lit "(", Term.con "dim_and" [Term.var "d1", Term.var "d2"], Term.lit ",", Term.var "env2", Term.lit ")"], Term.lit ")"], Term.lit ")"]
      | _ => t

    def spliceDimJoin (t : Term) : Term :=
      match t with
      | .con "spliceDimJoin" [d1Builder, d2Builder, env] => Term.con "letTupleIn" [Term.lit "(", Term.lit "let", Term.lit "(", Term.var "d1", Term.lit ",", Term.var "env1", Term.lit ")", Term.lit "=", Term.con "tuple" [d1Builder, env], Term.lit "in", Term.con "letTupleIn" [Term.lit "(", Term.lit "let", Term.lit "(", Term.var "d2", Term.lit ",", Term.var "env2", Term.lit ")", Term.lit "=", Term.con "tuple" [d2Builder, Term.var "env1"], Term.lit "in", Term.con "tuple" [Term.lit "(", Term.con "dim_or" [Term.var "d1", Term.var "d2"], Term.lit ",", Term.var "env2", Term.lit ")"], Term.lit ")"], Term.lit ")"]
      | _ => t

    def spliceDimNeg (t : Term) : Term :=
      match t with
      | .con "spliceDimNeg" [dBuilder, env] => Term.con "letTupleIn" [Term.lit "(", Term.lit "let", Term.lit "(", Term.var "d", Term.lit ",", Term.var "env'", Term.lit ")", Term.lit "=", Term.con "tuple" [dBuilder, env], Term.lit "in", Term.con "tuple" [Term.lit "(", Term.con "app" [Term.var "dim_neg", Term.var "d"], Term.lit ",", Term.var "env'", Term.lit ")"], Term.lit ")"]
      | _ => t

  end SpliceDim

  section SpliceCof

    def spliceCofTop (t : Term) : Term :=
      match t with
      | .con "app" [.var "spliceCofTop", env] => Term.con "tuple" [Term.lit "(", Term.con "cof_top" [], Term.lit ",", env, Term.lit ")"]
      | _ => t

    def spliceCofBot (t : Term) : Term :=
      match t with
      | .con "app" [.var "spliceCofBot", env] => Term.con "tuple" [Term.lit "(", Term.con "cof_bot" [], Term.lit ",", env, Term.lit ")"]
      | _ => t

    def spliceCofEq (t : Term) : Term :=
      match t with
      | .con "spliceCofEq" [d1Builder, d2Builder, env] => Term.con "letTupleIn" [Term.lit "(", Term.lit "let", Term.lit "(", Term.var "d1", Term.lit ",", Term.var "env1", Term.lit ")", Term.lit "=", Term.con "tuple" [d1Builder, env], Term.lit "in", Term.con "letTupleIn" [Term.lit "(", Term.lit "let", Term.lit "(", Term.var "d2", Term.lit ",", Term.var "env2", Term.lit ")", Term.lit "=", Term.con "tuple" [d2Builder, Term.var "env1"], Term.lit "in", Term.con "tuple" [Term.lit "(", Term.con "cof_eq" [Term.var "d1", Term.var "d2"], Term.lit ",", Term.var "env2", Term.lit ")"], Term.lit ")"], Term.lit ")"]
      | _ => t

    def spliceCofAnd (t : Term) : Term :=
      match t with
      | .con "spliceCofAnd" [φ1Builder, φ2Builder, env] => Term.con "letTupleIn" [Term.lit "(", Term.lit "let", Term.lit "(", Term.var "φ1", Term.lit ",", Term.var "env1", Term.lit ")", Term.lit "=", Term.con "tuple" [φ1Builder, env], Term.lit "in", Term.con "letTupleIn" [Term.lit "(", Term.lit "let", Term.lit "(", Term.var "φ2", Term.lit ",", Term.var "env2", Term.lit ")", Term.lit "=", Term.con "tuple" [φ2Builder, Term.var "env1"], Term.lit "in", Term.con "tuple" [Term.lit "(", Term.con "cof_and" [Term.var "φ1", Term.var "φ2"], Term.lit ",", Term.var "env2", Term.lit ")"], Term.lit ")"], Term.lit ")"]
      | _ => t

    def spliceCofOr (t : Term) : Term :=
      match t with
      | .con "spliceCofOr" [φ1Builder, φ2Builder, env] => Term.con "letTupleIn" [Term.lit "(", Term.lit "let", Term.lit "(", Term.var "φ1", Term.lit ",", Term.var "env1", Term.lit ")", Term.lit "=", Term.con "tuple" [φ1Builder, env], Term.lit "in", Term.con "letTupleIn" [Term.lit "(", Term.lit "let", Term.lit "(", Term.var "φ2", Term.lit ",", Term.var "env2", Term.lit ")", Term.lit "=", Term.con "tuple" [φ2Builder, Term.var "env1"], Term.lit "in", Term.con "tuple" [Term.lit "(", Term.con "cof_disj" [Term.var "φ1", Term.var "φ2"], Term.lit ",", Term.var "env2", Term.lit ")"], Term.lit ")"], Term.lit ")"]
      | _ => t

  end SpliceCof

  section SpliceKan

    def spliceCoe (t : Term) : Term :=
      match t with
      | .con "spliceCoe" [rBuilder, r'Builder, tyLineBuilder, elBuilder, env] => Term.con "letTupleIn" [Term.lit "(", Term.lit "let", Term.lit "(", Term.var "r", Term.lit ",", Term.var "env1", Term.lit ")", Term.lit "=", Term.con "tuple" [rBuilder, env], Term.lit "in", Term.con "letTupleIn" [Term.lit "(", Term.lit "let", Term.lit "(", Term.var "r'", Term.lit ",", Term.var "env2", Term.lit ")", Term.lit "=", Term.con "tuple" [r'Builder, Term.var "env1"], Term.lit "in", Term.con "letTupleIn" [Term.lit "(", Term.lit "let", Term.lit "(", Term.var "tyLine", Term.lit ",", Term.var "env3", Term.lit ")", Term.lit "=", Term.con "tuple" [tyLineBuilder, Term.var "env2"], Term.lit "in", Term.con "letTupleIn" [Term.lit "(", Term.lit "let", Term.lit "(", Term.var "el", Term.lit ",", Term.var "env4", Term.lit ")", Term.lit "=", Term.con "tuple" [elBuilder, Term.var "env3"], Term.lit "in", Term.con "tuple" [Term.lit "(", Term.con "coe" [Term.var "r", Term.var "r'", Term.var "tyLine", Term.var "el"], Term.lit ",", Term.var "env4", Term.lit ")"], Term.lit ")"], Term.lit ")"], Term.lit ")"], Term.lit ")"]
      | _ => t

    def spliceHcom (t : Term) : Term :=
      match t with
      | .con "spliceHcom" [rBuilder, r'Builder, tyBuilder, φBuilder, tubesBuilder, capBuilder, env] => Term.con "letTupleIn" [Term.lit "(", Term.lit "let", Term.lit "(", Term.var "r", Term.lit ",", Term.var "env1", Term.lit ")", Term.lit "=", Term.con "tuple" [rBuilder, env], Term.lit "in", Term.con "letTupleIn" [Term.lit "(", Term.lit "let", Term.lit "(", Term.var "r'", Term.lit ",", Term.var "env2", Term.lit ")", Term.lit "=", Term.con "tuple" [r'Builder, Term.var "env1"], Term.lit "in", Term.con "letTupleIn" [Term.lit "(", Term.lit "let", Term.lit "(", Term.var "ty", Term.lit ",", Term.var "env3", Term.lit ")", Term.lit "=", Term.con "tuple" [tyBuilder, Term.var "env2"], Term.lit "in", Term.con "letTupleIn" [Term.lit "(", Term.lit "let", Term.lit "(", Term.var "φ", Term.lit ",", Term.var "env4", Term.lit ")", Term.lit "=", Term.con "tuple" [φBuilder, Term.var "env3"], Term.lit "in", Term.con "letTupleIn" [Term.lit "(", Term.lit "let", Term.lit "(", Term.var "tubes", Term.lit ",", Term.var "env5", Term.lit ")", Term.lit "=", Term.con "tuple" [tubesBuilder, Term.var "env4"], Term.lit "in", Term.con "letTupleIn" [Term.lit "(", Term.lit "let", Term.lit "(", Term.var "cap", Term.lit ",", Term.var "env6", Term.lit ")", Term.lit "=", Term.con "tuple" [capBuilder, Term.var "env5"], Term.lit "in", Term.con "tuple" [Term.lit "(", Term.con "hcom" [Term.var "ty", Term.var "r", Term.var "r'", Term.var "φ", Term.var "tubes", Term.var "cap"], Term.lit ",", Term.var "env6", Term.lit ")"], Term.lit ")"], Term.lit ")"], Term.lit ")"], Term.lit ")"], Term.lit ")"], Term.lit ")"]
      | _ => t

    def spliceCom (t : Term) : Term :=
      match t with
      | .con "spliceCom" [rBuilder, r'Builder, tyLineBuilder, φBuilder, tubesBuilder, capBuilder, env] => Term.con "letTupleIn" [Term.lit "(", Term.lit "let", Term.lit "(", Term.var "r", Term.lit ",", Term.var "env1", Term.lit ")", Term.lit "=", Term.con "tuple" [rBuilder, env], Term.lit "in", Term.con "letTupleIn" [Term.lit "(", Term.lit "let", Term.lit "(", Term.var "r'", Term.lit ",", Term.var "env2", Term.lit ")", Term.lit "=", Term.con "tuple" [r'Builder, Term.var "env1"], Term.lit "in", Term.con "letTupleIn" [Term.lit "(", Term.lit "let", Term.lit "(", Term.var "tyLine", Term.lit ",", Term.var "env3", Term.lit ")", Term.lit "=", Term.con "tuple" [tyLineBuilder, Term.var "env2"], Term.lit "in", Term.con "letTupleIn" [Term.lit "(", Term.lit "let", Term.lit "(", Term.var "φ", Term.lit ",", Term.var "env4", Term.lit ")", Term.lit "=", Term.con "tuple" [φBuilder, Term.var "env3"], Term.lit "in", Term.con "letTupleIn" [Term.lit "(", Term.lit "let", Term.lit "(", Term.var "tubes", Term.lit ",", Term.var "env5", Term.lit ")", Term.lit "=", Term.con "tuple" [tubesBuilder, Term.var "env4"], Term.lit "in", Term.con "letTupleIn" [Term.lit "(", Term.lit "let", Term.lit "(", Term.var "cap", Term.lit ",", Term.var "env6", Term.lit ")", Term.lit "=", Term.con "tuple" [capBuilder, Term.var "env5"], Term.lit "in", Term.con "tuple" [Term.lit "(", Term.con "com" [Term.var "tyLine", Term.var "r", Term.var "r'", Term.var "φ", Term.var "tubes", Term.var "cap"], Term.lit ",", Term.var "env6", Term.lit ")"], Term.lit ")"], Term.lit ")"], Term.lit ")"], Term.lit ")"], Term.lit ")"], Term.lit ")"]
      | _ => t

  end SpliceKan

  section Compile

    def compile (t : Term) : Term :=
      match t with
      | .con "app" [.var "compile", splice] => Term.con "app" [Term.var "spliceRun", splice]
      | _ => t

    def compileResult (t : Term) : Term :=
      match t with
      | .con "app" [.var "compileResult", splice] => Term.con "app" [Term.var "spliceEval", splice]
      | _ => t

    def compileEnv (t : Term) : Term :=
      match t with
      | .con "app" [.var "compileEnv", splice] => Term.con "app" [Term.var "spliceGetEnv", splice]
      | _ => t

  end Compile

  section SpliceEval

    def spliceEvalTerm (t : Term) : Term :=
      match t with
      | .con "spliceEvalTerm" [term, .con "spliceEnv" [.con "labeledArg" [.var "conEnv", .lit ":", cs], .con "labeledArg" [.var "tpEnv", .lit ":", ts]]] => Term.con "substMany" [term, cs]
      | _ => t

    def substMany (t : Term) : Term :=
      match t with
      | .con "substMany" [term, .con "unit" [.lit "(", .lit ")"]] => term
      | _ => t

    def substManyCons (t : Term) : Term :=
      match t with
      | .con "substMany" [term, .con "tuple" [v, rest]] => Term.con "substMany" [Term.con "subst" [Term.con "num" [Term.con "number" [Term.lit "0"]], v, term], rest]
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

  end SpliceEval

end Splice