/-
  Lego.RedValidation: Validation for .red file format (redtt/cooltt)

  This module provides validation specific to the Red format used by
  redtt and cooltt proof assistants. It extends the general cubical
  validation with Red-specific checks:

  1. Scope checking - variables in scope before use
  2. Dimension binding - dimension variables properly bound
  3. System agreement - partial elements agree on overlapping faces
  4. Type well-formedness - types are valid in their context

  Architecture: Pure validation functions, no IO.
  Called after parsing .red files.
-/

import Lego.Algebra
import Lego.Validation
import Lego.Normalize

namespace Lego.RedValidation

open Lego
open Lego.Validation
open Lego.Cubical

/-! ## Red-Specific Error Types -/

/-- Errors specific to Red format validation -/
inductive RedError where
  | unboundVariable (name : String) (ctx : String) : RedError
  | unboundDimension (name : String) (ctx : String) : RedError
  | systemDisagreement (face1 : String) (face2 : String) (reason : String) : RedError
  | invalidTypeAnnotation (term : String) (expected : String) : RedError
  | missingTypeAnnotation (term : String) : RedError
  | invalidDataDecl (name : String) (reason : String) : RedError
  | invalidImport (path : String) (reason : String) : RedError
  | cyclicDefinition (names : List String) : RedError
  | levelMismatch (expected : String) (got : String) (ctx : String) : RedError
  deriving Repr, BEq

def RedError.format : RedError → String
  | .unboundVariable name ctx =>
      s!"RED ERROR: Unbound variable '{name}' in {ctx}\n" ++
      s!"  Hint: Check that the variable is defined before use"
  | .unboundDimension name ctx =>
      s!"RED ERROR: Unbound dimension '{name}' in {ctx}\n" ++
      s!"  Hint: Dimension variables must be bound with λ [i] or in path types"
  | .systemDisagreement face1 face2 reason =>
      s!"RED ERROR: System branches disagree on faces '{face1}' and '{face2}': {reason}\n" ++
      s!"  Hint: Partial elements must agree on overlapping faces"
  | .invalidTypeAnnotation term expected =>
      s!"RED ERROR: Invalid type annotation on '{term}', expected: {expected}"
  | .missingTypeAnnotation term =>
      s!"RED ERROR: Missing type annotation on '{term}'\n" ++
      s!"  Hint: Add explicit type with ':'"
  | .invalidDataDecl name reason =>
      s!"RED ERROR: Invalid data declaration '{name}': {reason}"
  | .invalidImport path reason =>
      s!"RED ERROR: Invalid import '{path}': {reason}"
  | .cyclicDefinition names =>
      s!"RED ERROR: Cyclic definition(s): {", ".intercalate names}"
  | .levelMismatch expected got ctx =>
      s!"RED ERROR: Universe level mismatch in {ctx}: expected {expected}, got {got}"

/-! ## Scope Checking Context -/

/-- Context for scope checking -/
structure ScopeCtx where
  /-- Bound term variables with their types (if known) -/
  termVars : List (String × Option Term) := []
  /-- Bound dimension variables -/
  dimVars : List String := []
  /-- Defined names (from def declarations) -/
  defs : List String := []
  /-- Current definition being checked (for cycle detection) -/
  currentDef : Option String := none
  /-- Module imports -/
  imports : List String := []
  deriving Repr, Inhabited

def ScopeCtx.empty : ScopeCtx := {}

def ScopeCtx.addTerm (ctx : ScopeCtx) (name : String) (ty : Option Term := none) : ScopeCtx :=
  { ctx with termVars := (name, ty) :: ctx.termVars }

def ScopeCtx.addDim (ctx : ScopeCtx) (name : String) : ScopeCtx :=
  { ctx with dimVars := name :: ctx.dimVars }

def ScopeCtx.addDef (ctx : ScopeCtx) (name : String) : ScopeCtx :=
  { ctx with defs := name :: ctx.defs }

def ScopeCtx.hasTerm (ctx : ScopeCtx) (name : String) : Bool :=
  ctx.termVars.any (·.1 == name) || ctx.defs.contains name

def ScopeCtx.hasDim (ctx : ScopeCtx) (name : String) : Bool :=
  ctx.dimVars.contains name

/-! ## Variable Scope Checking -/

/-- Check if all variables in a term are in scope -/
partial def checkScope (ctx : ScopeCtx) (t : Term) : List RedError :=
  match t with
  | .var name =>
    -- Check if it's a term variable or dimension variable
    if ctx.hasTerm name || ctx.hasDim name then []
    else if name.startsWith "$" then []  -- Pattern variable
    else [.unboundVariable name "expression"]

  | .con "dimVar" [.var name] =>
    if ctx.hasDim name then []
    else [.unboundDimension name "dimension expression"]

  | .con "lam" [.var x, body] =>
    checkScope (ctx.addTerm x) body

  | .con "pi" [.var x, dom, cod] =>
    checkScope ctx dom ++ checkScope (ctx.addTerm x (some dom)) cod

  | .con "sigma" [.var x, dom, cod] =>
    checkScope ctx dom ++ checkScope (ctx.addTerm x (some dom)) cod

  | .con "plam" [.var i, body] =>
    checkScope (ctx.addDim i) body

  | .con "extLam" [.con "dims" dims, body] =>
    let dimNames := dims.filterMap fun d => match d with
      | .var n => some n
      | _ => none
    let ctx' := dimNames.foldl ScopeCtx.addDim ctx
    checkScope ctx' body

  | .con "path" [ty, a, b] =>
    checkScope ctx ty ++ checkScope ctx a ++ checkScope ctx b

  | .con "ext" [.con "dims" dims, ty, sys] =>
    let dimNames := dims.filterMap fun d => match d with
      | .var n => some n
      | _ => none
    let ctx' := dimNames.foldl ScopeCtx.addDim ctx
    checkScope ctx' ty ++ checkScope ctx' sys

  | .con "letE" [.var x, ty, val, body] =>
    let tyErrs := match ty with
      | .con "noType" [] => []
      | _ => checkScope ctx ty
    tyErrs ++ checkScope ctx val ++ checkScope (ctx.addTerm x (some ty)) body

  | .con _ args =>
    args.flatMap (checkScope ctx)

  | _ => []

/-! ## Dimension Binding Validation -/

/-- Check dimension variables are properly bound in Kan operations -/
partial def checkDimBindings (ctx : ScopeCtx) (t : Term) : List RedError :=
  match t with
  | .con "coe" [r, s, ty, tm] =>
    let checkDim d name := match d with
      | .var n => if ctx.hasDim n then [] else [RedError.unboundDimension n s!"coe {name}"]
      | .con "dim0" [] | .con "dim1" [] => []
      | _ => checkDimBindings ctx d
    checkDim r "start" ++ checkDim s "end" ++ checkDimBindings ctx ty ++ checkDimBindings ctx tm

  | .con "hcom" [r, s, ty, cap, sys] =>
    let checkDim d name := match d with
      | .var n => if ctx.hasDim n then [] else [RedError.unboundDimension n s!"hcom {name}"]
      | .con "dim0" [] | .con "dim1" [] => []
      | _ => checkDimBindings ctx d
    checkDim r "start" ++ checkDim s "end" ++
    checkDimBindings ctx ty ++ checkDimBindings ctx cap ++ checkDimBindings ctx sys

  | .con "plam" [.var i, body] =>
    checkDimBindings (ctx.addDim i) body

  | .con _ args =>
    args.flatMap (checkDimBindings ctx)

  | _ => []

/-! ## System Agreement Checking -/

/-- Check that system branches agree on overlapping faces -/
def checkSystemAgreement (rules : List (Term × Term)) (sys : Term) : List RedError :=
  match sys with
  | .con "sys" branches =>
    -- Extract face-value pairs
    let pairs := branches.filterMap fun b => match b with
      | .con "sysBranch" [cof, val] => some (cof, val)
      | .con "tube" [cof, val] => some (cof, val)
      | _ => none

    -- Check pairwise agreement (where faces overlap)
    let rec checkPairs (ps : List (Term × Term)) : List RedError :=
      match ps with
      | [] => []
      | (cof1, val1) :: rest =>
        let errs := rest.filterMap fun (cof2, val2) =>
          -- Check if faces can both be true (non-disjoint)
          let overlap := simplifyCof (.con "cof_and" [cof1, cof2])
          if overlap == .con "cof_bot" [] then none
          else
            -- Faces overlap - values must be equal
            let val1' := normalize 1000 rules val1
            let val2' := normalize 1000 rules val2
            if val1' == val2' then none
            else some (RedError.systemDisagreement (toString cof1) (toString cof2)
                        s!"values differ: {val1'} vs {val2'}")
        errs ++ checkPairs rest
    checkPairs pairs

  | _ => []

/-! ## Data Declaration Validation -/

/-- Validate a data declaration (inductive type) -/
def validateDataDecl (ctx : ScopeCtx) (name : String) (params : List Term) (constrs : List Term) : List RedError :=
  -- Check parameter names are unique
  let paramNames := params.filterMap fun p => match p with
    | .con "param" [.var n, _] => some n
    | .var n => some n
    | _ => none
  let hasDupes := paramNames.length != paramNames.eraseDups.length
  let dupeErr := if hasDupes then [RedError.invalidDataDecl name "duplicate parameter names"] else []

  -- Check constructors reference valid params
  let ctx' := paramNames.foldl ScopeCtx.addTerm ctx
  let ctx'' := ctx'.addDef name  -- The type itself is in scope
  let constrErrs := constrs.flatMap (checkScope ctx'')

  dupeErr ++ constrErrs

/-! ## Main Validation Entry Points -/

/-- Result of Red validation -/
structure RedValidationResult where
  errors : List RedError
  warnings : List ValidationWarning
  deriving Repr, Inhabited

def RedValidationResult.empty : RedValidationResult := ⟨[], []⟩

instance : Append RedValidationResult where
  append r1 r2 := ⟨r1.errors ++ r2.errors, r1.warnings ++ r2.warnings⟩

def RedValidationResult.passed (r : RedValidationResult) : Bool := r.errors.isEmpty

def RedValidationResult.format (r : RedValidationResult) : String :=
  let errStr := r.errors.map RedError.format |> "\n".intercalate
  let warnStr := r.warnings.map ValidationWarning.format |> "\n".intercalate
  s!"Red Validation: {r.errors.length} errors, {r.warnings.length} warnings\n{errStr}\n{warnStr}"

/-- Validate a single Red definition -/
def validateRedDef (ctx : ScopeCtx) (rules : List (Term × Term)) (def_ : Term) : RedValidationResult :=
  match def_ with
  | .con "def" [.var name, ty, body] =>
    let scopeErrs := checkScope ctx ty ++ checkScope (ctx.addDef name) body
    let dimErrs := checkDimBindings ctx body
    ⟨scopeErrs ++ dimErrs, []⟩

  | .con "data" [.var name, .con "params" params, .con "constrs" constrs] =>
    let errs := validateDataDecl ctx name params constrs
    ⟨errs, []⟩

  | _ => RedValidationResult.empty

/-- Validate an entire Red file (list of declarations) -/
def validateRedFile (rules : List (Term × Term)) (decls : List Term) : RedValidationResult :=
  let rec go (ctx : ScopeCtx) (ds : List Term) : RedValidationResult :=
    match ds with
    | [] => RedValidationResult.empty
    | d :: rest =>
      let result := validateRedDef ctx rules d
      -- Add definition to context
      let ctx' := match d with
        | .con "def" [.var name, _, _] => ctx.addDef name
        | .con "data" [.var name, _, _] => ctx.addDef name
        | _ => ctx
      result ++ go ctx' rest
  go ScopeCtx.empty decls

/-- Validate Red AST with system agreement checking -/
def validateRedAST (rules : List (Term × Term)) (ast : Term) : RedValidationResult :=
  let scopeResult : RedValidationResult := ⟨checkScope ScopeCtx.empty ast, []⟩
  let dimResult : RedValidationResult := ⟨checkDimBindings ScopeCtx.empty ast, []⟩

  -- Find and check all systems
  let systemErrors := extractSystems ast |>.flatMap (checkSystemAgreement rules)

  ⟨scopeResult.errors ++ dimResult.errors ++ systemErrors, scopeResult.warnings ++ dimResult.warnings⟩
where
  extractSystems (t : Term) : List Term :=
    match t with
    | .con "sys" _ => [t]
    | .con _ args => args.flatMap extractSystems
    | _ => []

/-! ## Integration with General Validation -/

/-- Combined validation: general cubical + Red-specific -/
def validateRedFull (typeRules : List TypeRule) (rules : List (Term × Term)) (ast : Term)
    : (FullValidationResult × RedValidationResult) :=
  let generalResult := validateFull {} [] typeRules ast
  let redResult := validateRedAST rules ast
  (generalResult, redResult)

end Lego.RedValidation
