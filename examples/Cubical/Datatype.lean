/-
  Lego.Cubical.Datatype: User-defined inductive types with constructors and eliminators

  This module provides the machinery for user-defined datatypes like:
    data List (A : Type) where
    | nil
    | cons (x : A) (xs : List A)

  Mathematical structure:
  - Datatypes are initial algebras in the category of algebras
  - Constructors are the algebra structure maps
  - Eliminators give the universal property (recursion/induction)

  The key pieces:
  1. DataType - A type former parameterized by type arguments
  2. Intro - Constructor application (builds data values)
  3. Elim - Pattern matching/elimination (consumes data values)

  Based on redtt's Desc.ml and Val.ml datatype handling
-/

import Lego.Cubical.Core
import Lego.Cubical.GlobalEnv

namespace Lego.Cubical.Datatype

open Lego.Core
open Lego.Cubical

/-! ## Datatype Type Formation

    `Data dlbl params` represents a datatype applied to parameters.

    Examples:
    - `Data "List" [A]` = List A
    - `Data "Vec" [A, n]` = Vec A n
    - `Data "Nat" []` = Nat
-/

/-- Create a datatype type expression -/
def mkData (dlbl : String) (params : List Expr) : Expr :=
  -- Encode as: (lit "data") applied to label and params
  -- data.List.A -> datatype List applied to A
  let dataBase := Expr.lit s!"data.{dlbl}"
  params.foldl Expr.app dataBase

/-- Check if an expression is a datatype type -/
def isData (e : Expr) : Option (String × List Expr) :=
  match getDataHead e [] with
  | some (lbl, params) => some (lbl, params)
  | none => none
where
  getDataHead : Expr → List Expr → Option (String × List Expr)
  | .lit s, acc =>
    if s.startsWith "data." then
      some (s.drop 5, acc)
    else
      none
  | .app f a, acc => getDataHead f (a :: acc)
  | _, _ => none

/-! ## Constructor Introduction

    `Intro dlbl clbl params args` represents a constructor application.

    Examples:
    - `Intro "List" "nil" [A] []` = nil {A}
    - `Intro "List" "cons" [A] [x, xs]` = cons {A} x xs
    - `Intro "Nat" "zero" [] []` = zero
    - `Intro "Nat" "suc" [] [n]` = suc n
-/

/-- Create a constructor application expression -/
def mkIntro (dlbl : String) (clbl : String) (params : List Expr) (args : List Expr) : Expr :=
  -- Encode as: (lit "intro.dlbl.clbl.paramCount") applied to params then args
  let paramCount := params.length
  let introBase := Expr.lit s!"intro.{dlbl}.{clbl}.{paramCount}"
  let withParams := params.foldl Expr.app introBase
  args.foldl Expr.app withParams

/-- Check if an expression is a constructor application -/
def isIntro (e : Expr) : Option (String × String × List Expr × List Expr) := Id.run do
  -- Parse backwards to get all args
  let (head, allArgs) := collectArgs e []
  match head with
  | .lit s =>
    if s.startsWith "intro." then
      let rest := s.drop 6
      match rest.splitOn "." with
      | [dlbl, clbl, countStr] =>
        let paramCount := countStr.toNat?.getD 0
        let params := allArgs.take paramCount
        let args := allArgs.drop paramCount
        some (dlbl, clbl, params, args)
      | [dlbl, clbl] =>
        -- Legacy format without param count
        some (dlbl, clbl, [], allArgs)
      | _ => none
    else
      none
  | _ => none
where
  collectArgs : Expr → List Expr → (Expr × List Expr)
  | .app f a, acc => collectArgs f (a :: acc)
  | e, acc => (e, acc)

/-! ## Eliminator Application

    `Elim dlbl params mot clauses scrut` eliminates a datatype value.

    The motive `mot` is a type family indexed by the datatype.
    Each clause handles one constructor.

    Example for Nat:
    ```
    elim n with
    | zero → z
    | suc n' ih → s n' ih
    ```

    becomes `Elim "Nat" [] mot [("zero", z), ("suc", λn'.λih. s n' ih)] n`
-/

/-- A clause in an eliminator: (constructor name, body with args and IH bound) -/
structure ElimClause where
  clbl : String        -- Constructor label
  body : Expr          -- Body with args and inductive hypotheses bound
  deriving Repr, BEq

/-- Create an eliminator application -/
def mkElim (dlbl : String) (params : List Expr) (mot : Expr)
           (clauses : List ElimClause) (scrut : Expr) : Expr :=
  -- Encode as: (lit "elim.dlbl") applied to params, mot, encoded clauses, scrut
  let elimBase := Expr.lit s!"elim.{dlbl}"
  let withParams := params.foldl Expr.app elimBase
  let withMot := Expr.app withParams mot
  -- Encode clauses as a nested structure
  let clauseExpr := encodeClauseList clauses
  let withClauses := Expr.app withMot clauseExpr
  Expr.app withClauses scrut
where
  encodeClauseList : List ElimClause → Expr
  | [] => .lit "clauses.nil"
  | c :: cs =>
    let tag := Expr.lit s!"clause.{c.clbl}"
    let thisClause := Expr.app tag c.body
    Expr.app (Expr.app (.lit "clauses.cons") thisClause) (encodeClauseList cs)

/-! ## Evaluation of Datatypes

    When evaluating an eliminator applied to an intro form:
    - Match the constructor against the clauses
    - Substitute args and recursive results for bound variables
-/

/-- Find a clause for a given constructor -/
def findClause (clauses : List ElimClause) (clbl : String) : Option Expr :=
  clauses.find? (·.clbl == clbl) |>.map (·.body)

/-- Substitute a value for de Bruijn index 0 and shift -/
def substTop (body : Expr) (val : Expr) : Expr :=
  Expr.subst 0 val body

/-- Substitute multiple values for indices 0, 1, 2, ... -/
def substMany (body : Expr) (vals : List Expr) : Expr :=
  -- vals[0] goes to index 0, vals[1] to index 1, etc.
  -- We substitute in reverse order: last binding first
  vals.reverse.foldl (fun b v => substTop b v) body

/-! ## Step Rules for Datatype Elimination

    The key computation rule:
    elim (intro dlbl clbl params args) with mot clauses
    ~> clause[clbl] applied to args and recursive calls
-/

/-- Step an eliminator applied to an intro -/
def stepElim (env : GlobalEnv) (dlbl : String) (params : List Expr)
              (mot : Expr) (clauses : List ElimClause) (scrut : Expr)
              : Option Expr := do
  -- Check if scrut is an intro form
  let (dlbl', clbl, _introParams, args) ← isIntro scrut
  guard (dlbl == dlbl')

  -- Find the clause for this constructor
  let clauseBody ← findClause clauses clbl

  -- Get the datatype descriptor to know about recursive positions
  let desc ← env.lookupDatatype (GName.named dlbl)
  let constr ← desc.constrs.find? (·.name == clbl)

  -- Build the substitution: args and inductive hypotheses
  -- For each recursive argument, we need to compute the IH
  let mut substs : List Expr := []
  let mut argIdx := 0

  for (_, spec) in constr.args do
    match spec with
    | GArgSpec.const _ =>
      -- Non-recursive: just the arg
      if let some arg := args[argIdx]? then
        substs := substs ++ [arg]
      argIdx := argIdx + 1
    | GArgSpec.recursive =>
      -- Recursive: include both the arg AND the inductive hypothesis
      if let some arg := args[argIdx]? then
        substs := substs ++ [arg]
        -- IH = recursive call to elim with this arg
        let ih := mkElim dlbl params mot clauses arg
        substs := substs ++ [ih]
      argIdx := argIdx + 1
    | GArgSpec.dim =>
      -- Dimension argument (for HITs)
      if let some arg := args[argIdx]? then
        substs := substs ++ [arg]
      argIdx := argIdx + 1

  -- Substitute all the bindings into the clause body
  return substMany clauseBody substs

/-- Simplified step for elimination - works for basic cases without full environment lookup
    Assumes: every arg after params is either constant (1 binding) or recursive (2 bindings)
    This is a heuristic for testing - use stepElim with GlobalEnv for real evaluation -/
def stepElimSimple (dlbl : String) (params : List Expr)
                    (mot : Expr) (clauses : List ElimClause) (scrut : Expr)
                    (argSpecs : List GArgSpec := [])
                    : Option Expr := do
  -- Check if scrut is an intro form
  let (dlbl', clbl, _introParams, args) ← isIntro scrut
  guard (dlbl == dlbl')

  -- Find the clause for this constructor
  let clauseBody ← findClause clauses clbl

  -- Build substitutions based on specs or assume all const
  let specs := if argSpecs.isEmpty then args.map (fun _ => GArgSpec.const .nat) else argSpecs
  let mut substs : List Expr := []
  let mut argIdx := 0

  for spec in specs do
    match spec with
    | GArgSpec.const _ =>
      if let some arg := args[argIdx]? then
        substs := substs ++ [arg]
      argIdx := argIdx + 1
    | GArgSpec.recursive =>
      if let some arg := args[argIdx]? then
        substs := substs ++ [arg]
        -- IH = recursive call to elim
        let ih := mkElim dlbl params mot clauses arg
        substs := substs ++ [ih]
      argIdx := argIdx + 1
    | GArgSpec.dim =>
      if let some arg := args[argIdx]? then
        substs := substs ++ [arg]
      argIdx := argIdx + 1

  return substMany clauseBody substs

/-- Convenience: step Nat eliminator -/
def stepNatElim (mot : Expr) (zeroCase : Expr) (sucCase : Expr) (scrut : Expr) : Option Expr := do
  let clauses := [
    { clbl := "zero", body := zeroCase },
    { clbl := "suc", body := sucCase }
  ]
  stepElimSimple "Nat" [] mot clauses scrut [GArgSpec.recursive]

/-- Convenience: step Bool eliminator -/
def stepBoolElim (mot : Expr) (trueCase : Expr) (falseCase : Expr) (scrut : Expr) : Option Expr := do
  let clauses := [
    { clbl := "true", body := trueCase },
    { clbl := "false", body := falseCase }
  ]
  stepElimSimple "Bool" [] mot clauses scrut []

/-! ## Worked Example: Natural Numbers

    Given:
    ```
    data Nat where
    | zero
    | suc (n : Nat)
    ```

    `natElim P z s (suc (suc zero))`

    Reduces as:
    1. scrut = suc (suc zero), matches "suc" clause
    2. args = [suc zero], has one recursive arg
    3. substs = [suc zero, natElim P z s (suc zero)]  (arg and IH)
    4. body = s, expecting two args: n and ih
    5. result = s (suc zero) (natElim P z s (suc zero))

    Then that IH reduces further.
-/

/-! ## Creating Standard Datatypes

    Helper functions to create common datatypes programmatically.
-/

/-- Create the Nat datatype descriptor -/
def mkNatDesc : GDataDesc := {
  name := GName.named "Nat"
  params := []
  level := Level.zero
  constrs := [
    { name := "zero", args := [], boundary := [] },
    { name := "suc", args := [("n", GArgSpec.recursive)], boundary := [] }
  ]
}

/-- Create the List datatype descriptor -/
def mkListDesc : GDataDesc := {
  name := GName.named "List"
  params := [("A", .univ Level.zero)]  -- List (A : Type)
  level := Level.zero
  constrs := [
    { name := "nil", args := [], boundary := [] },
    { name := "cons",
      args := [("x", GArgSpec.const (.ix 0)),     -- x : A (A is at index 0 in params)
               ("xs", GArgSpec.recursive)],        -- xs : List A
      boundary := [] }
  ]
}

/-- Create the Bool datatype descriptor -/
def mkBoolDesc : GDataDesc := {
  name := GName.named "Bool"
  params := []
  level := Level.zero
  constrs := [
    { name := "true", args := [], boundary := [] },
    { name := "false", args := [], boundary := [] }
  ]
}

/-- Create the Unit datatype descriptor -/
def mkUnitDesc : GDataDesc := {
  name := GName.named "Unit"
  params := []
  level := Level.zero
  constrs := [
    { name := "star", args := [], boundary := [] }
  ]
}

/-- Create the Maybe/Option datatype descriptor -/
def mkMaybeDesc : GDataDesc := {
  name := GName.named "Maybe"
  params := [("A", .univ Level.zero)]
  level := Level.zero
  constrs := [
    { name := "nothing", args := [], boundary := [] },
    { name := "just", args := [("x", GArgSpec.const (.ix 0))], boundary := [] }
  ]
}

/-- Create the Either datatype descriptor -/
def mkEitherDesc : GDataDesc := {
  name := GName.named "Either"
  params := [("A", .univ Level.zero), ("B", .univ Level.zero)]
  level := Level.zero
  constrs := [
    { name := "left", args := [("x", GArgSpec.const (.ix 1))], boundary := [] },   -- A is at index 1
    { name := "right", args := [("y", GArgSpec.const (.ix 0))], boundary := [] }   -- B is at index 0
  ]
}

/-- Create the Prod (pair) datatype descriptor -/
def mkProdDesc : GDataDesc := {
  name := GName.named "Prod"
  params := [("A", .univ Level.zero), ("B", .univ Level.zero)]
  level := Level.zero
  constrs := [
    { name := "pair",
      args := [("fst", GArgSpec.const (.ix 1)),   -- A
               ("snd", GArgSpec.const (.ix 0))],  -- B
      boundary := [] }
  ]
}

/-! ## Register Standard Datatypes -/

/-- Create an environment with standard datatypes -/
def stdEnvWithDatatypes : GlobalEnv :=
  GlobalEnv.empty
  |>.declareDatatype mkBoolDesc
  |>.declareDatatype mkUnitDesc
  |>.declareDatatype mkNatDesc
  |>.declareDatatype mkMaybeDesc
  |>.declareDatatype mkEitherDesc
  |>.declareDatatype mkProdDesc
  |>.declareDatatype mkListDesc

/-! ## Type Checking for Datatypes

    Type rules for Data, Intro, and Elim:

    1. Data formation:
       Γ ⊢ params : Params(D)
       -------------------------
       Γ ⊢ Data D params : Type

    2. Introduction:
       Γ ⊢ args : ArgsFor(D.C, params)
       --------------------------------
       Γ ⊢ Intro D C params args : Data D params

    3. Elimination:
       Γ ⊢ scrut : Data D params
       Γ, x : Data D params ⊢ mot : Type
       For each C: Γ, args, ihs ⊢ clause_C : mot[intro D C params args/x]
       -----------------------------------------------------------------
       Γ ⊢ Elim D params mot clauses scrut : mot[scrut/x]
-/

/-- Check if a type is well-formed.
    A type is well-formed if it can be inferred to have a universe type.
    Uses the basic type inference from GlobalEnv. -/
def checkType (env : GlobalEnv) (ctx : List Expr) (ty : Expr) : Bool :=
  let typingCtx : TypingCtx := {
    global := env
    local_ := ctx
    dimCtx := []
  }
  match inferG typingCtx ty with
  | .ok inferredTy =>
    -- Type is well-formed if its type is a universe
    match evalWithGlobals env inferredTy with
    | .univ _ => true
    | _ => false
  | .error _ => false
  | .unsolvedMeta _ _ => false  -- Unsolved metas mean we can't verify

/-- Infer the type of a datatype expression -/
def inferDataType (env : GlobalEnv) (dlbl : String) (params : List Expr) : Option Expr := do
  let desc ← env.lookupDatatype (GName.named dlbl)
  -- Check params match descriptor
  guard (params.length == desc.params.length)
  -- Datatype has type Type at its level
  some (.univ desc.level)

/-- Infer the type of a constructor application -/
def inferIntroType (env : GlobalEnv) (dlbl : String) (_clbl : String)
                    (params : List Expr) (_args : List Expr) : Option Expr := do
  let _desc ← env.lookupDatatype (GName.named dlbl)
  -- Result type is the datatype applied to params
  some (mkData dlbl params)

/-- Infer the type of an eliminator application -/
def inferElimType (_env : GlobalEnv) (_dlbl : String) (_params : List Expr)
                   (mot : Expr) (scrut : Expr) : Option Expr := do
  -- Result is mot applied to scrut
  some (Expr.app mot scrut)

/-! ## Smart Constructors for Common Patterns -/

/-- Create a Nat value -/
def mkNat (n : Nat) : Expr :=
  match n with
  | 0 => mkIntro "Nat" "zero" [] []
  | n + 1 => mkIntro "Nat" "suc" [] [mkNat n]

/-- Create a Bool value -/
def mkBool (b : Bool) : Expr :=
  if b then mkIntro "Bool" "true" [] []
  else mkIntro "Bool" "false" [] []

/-- Create a List value -/
def mkList (elemType : Expr) (elems : List Expr) : Expr :=
  elems.foldr (fun x acc => mkIntro "List" "cons" [elemType] [x, acc])
              (mkIntro "List" "nil" [elemType] [])

/-- Create a Maybe value -/
def mkJust (elemType : Expr) (x : Expr) : Expr :=
  mkIntro "Maybe" "just" [elemType] [x]

def mkNothing (elemType : Expr) : Expr :=
  mkIntro "Maybe" "nothing" [elemType] []

/-! ## Pretty Printing -/

/-- Pretty print a datatype expression -/
def ppData (dlbl : String) (params : List Expr) : String :=
  if params.isEmpty then dlbl
  else
    let paramStrs := params.map (fun (e : Expr) => ToString.toString e)
    s!"{dlbl} {String.intercalate " " paramStrs}"

/-- Pretty print a constructor application -/
def ppIntro (_dlbl : String) (clbl : String) (params : List Expr) (args : List Expr) : String :=
  let constr := clbl
  let paramStrs : List String := params.map (fun (e : Expr) => ToString.toString e)
  let argStrs : List String := args.map (fun (e : Expr) => ToString.toString e)
  let paramStr := if params.isEmpty then "" else " {" ++ String.intercalate ", " paramStrs ++ "}"
  let argStr := if args.isEmpty then "" else " " ++ String.intercalate " " argStrs
  constr ++ paramStr ++ argStr

end Lego.Cubical.Datatype
