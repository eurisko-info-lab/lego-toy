/-
  Lego.AttrEval: Attribute Evaluation Runtime

  Phase 8: Actual attribute evaluation for type checking
  Phase 9: Error reporting with source locations

  This module connects the abstract attribute machinery to
  concrete type-checking operations.
-/

import Lego.Attr
import Lego.Loader
import Lego.Util

namespace Lego

/-! ## Source Locations for Error Reporting -/

/-- Source location: file, line, column, span -/
structure SourceLoc where
  file   : String
  line   : Nat
  column : Nat
  span   : Nat := 0
  deriving Repr, BEq, Inhabited

namespace SourceLoc

def unknown : SourceLoc := ⟨"<unknown>", 0, 0, 0⟩

def toString (loc : SourceLoc) : String :=
  s!"{loc.file}:{loc.line}:{loc.column}"

instance : ToString SourceLoc := ⟨toString⟩

end SourceLoc

/-! ## Type Errors -/

/-- Error severity levels -/
inductive Severity where
  | error   : Severity  -- Type error
  | warning : Severity  -- Potential issue
  | info    : Severity  -- Informational
  deriving Repr, BEq

/-- A type error with location and context -/
structure TypeError where
  message  : String
  loc      : SourceLoc
  severity : Severity
  expected : Option Term  -- Expected type (if applicable)
  actual   : Option Term  -- Actual type (if applicable)
  context  : List (String × Term)  -- Relevant context bindings
  deriving Repr

namespace TypeError

def formatBase (e : TypeError) : String :=
  let sevStr := match e.severity with
    | .error => "error"
    | .warning => "warning"
    | .info => "info"
  let loc := e.loc.toString
  s!"{loc}: {sevStr}: {e.message}"

def formatExpectedActual (expected actual : Option Term) : String :=
  match expected, actual with
  | some exp, some act => s!"\n  expected: {repr exp}\n  actual: {repr act}"
  | _, _ => ""

def error (msg : String) (loc : SourceLoc := SourceLoc.unknown) : TypeError :=
  ⟨msg, loc, .error, none, none, []⟩

def mismatch (expected actual : Term) (loc : SourceLoc := SourceLoc.unknown) : TypeError :=
  ⟨"type mismatch", loc, .error, some expected, some actual, []⟩

def undefined (name : String) (loc : SourceLoc := SourceLoc.unknown) : TypeError :=
  ⟨s!"undefined: {name}", loc, .error, none, none, []⟩

def toString (e : TypeError) : String :=
  let base := formatBase e
  base ++ formatExpectedActual e.expected e.actual

instance : ToString TypeError := ⟨toString⟩

end TypeError

/-! ## Evaluation Result with Errors -/

/-- Result of attribute evaluation: either success with value, or errors -/
inductive EvalResult (α : Type) where
  | ok     : α → List TypeError → EvalResult α  -- Success (may have warnings)
  | failed : List TypeError → EvalResult α       -- Failure with errors
  deriving Repr

namespace EvalResult

def pure (a : α) : EvalResult α := .ok a []

def map (f : α → β) : EvalResult α → EvalResult β
  | .ok a errs => .ok (f a) errs
  | .failed errs => .failed errs

def bind (ma : EvalResult α) (f : α → EvalResult β) : EvalResult β :=
  match ma with
  | .ok a errs =>
    match f a with
    | .ok b errs' => .ok b (errs ++ errs')
    | .failed errs' => .failed (errs ++ errs')
  | .failed errs => .failed errs

instance : Monad EvalResult where
  pure := pure
  bind := bind

def addError (e : TypeError) : EvalResult α → EvalResult α
  | .ok a errs => .ok a (e :: errs)
  | .failed errs => .failed (e :: errs)

def withWarning (msg : String) (r : EvalResult α) : EvalResult α :=
  addError (TypeError.error msg) r

def getErrors : EvalResult α → List TypeError
  | .ok _ errs => errs
  | .failed errs => errs

def isOk : EvalResult α → Bool
  | .ok _ _ => true
  | .failed _ => false

end EvalResult

/-! ## Typing Context -/

/-- A binding in the typing context -/
structure Binding where
  name : String
  type : Term
  value : Option Term  -- For let-bindings
  loc : SourceLoc
  deriving Repr

/-- Typing context: list of bindings (most recent first) -/
structure Context where
  bindings : List Binding
  deriving Repr, Inhabited

namespace Context

def empty : Context := ⟨[]⟩

def extend (ctx : Context) (name : String) (type : Term) (loc : SourceLoc := SourceLoc.unknown) : Context :=
  ⟨{ name, type, value := none, loc } :: ctx.bindings⟩

def extendLet (ctx : Context) (name : String) (type : Term) (value : Term) (loc : SourceLoc := SourceLoc.unknown) : Context :=
  ⟨{ name, type, value := some value, loc } :: ctx.bindings⟩

def lookup (ctx : Context) (name : String) : Option Binding :=
  ctx.bindings.find? (·.name == name)

def lookupType (ctx : Context) (name : String) : Option Term :=
  (ctx.lookup name).map (·.type)

def names (ctx : Context) : List String :=
  ctx.bindings.map (·.name)

def toList (ctx : Context) : List (String × Term) :=
  ctx.bindings.map (fun b => (b.name, b.type))

end Context

/-! ## Variable Context (Generic)

This is a generic variable context that can track any kind of
scoped variables - term variables, dimension variables, etc.
The specific interpretation depends on the language being processed.
-/

/-- Generic variable context for scoped variables -/
structure VarContext where
  vars : List String
  deriving Repr, Inhabited

namespace VarContext

def empty : VarContext := ⟨[]⟩

def extend (ctx : VarContext) (name : String) : VarContext :=
  ⟨name :: ctx.vars⟩

def contains (ctx : VarContext) (name : String) : Bool :=
  ctx.vars.contains name

end VarContext

/-! ## Extended Attribute Environment -/

/-- Extended environment with typing context and errors -/
structure EvalEnv where
  attrs   : AttrEnv        -- Computed attributes
  ctx     : Context        -- Typing context
  varCtx  : VarContext     -- Scoped variable context (generic)
  errors  : List TypeError -- Accumulated errors
  loc     : SourceLoc      -- Current location
  deriving Repr

namespace EvalEnv

def empty : EvalEnv :=
  ⟨AttrEnv.empty, Context.empty, VarContext.empty, [], SourceLoc.unknown⟩

def withCtx (env : EvalEnv) (ctx : Context) : EvalEnv :=
  { env with ctx }

def withLoc (env : EvalEnv) (loc : SourceLoc) : EvalEnv :=
  { env with loc }

def addBinding (env : EvalEnv) (name : String) (type : Term) : EvalEnv :=
  { env with ctx := env.ctx.extend name type env.loc }

/-- Add a scoped variable (generic - works for any variable kind) -/
def addVar (env : EvalEnv) (name : String) : EvalEnv :=
  { env with varCtx := env.varCtx.extend name }

def addError (env : EvalEnv) (e : TypeError) : EvalEnv :=
  { env with errors := e :: env.errors }

def addTypeError (env : EvalEnv) (msg : String) : EvalEnv :=
  env.addError (TypeError.error msg env.loc)

def addMismatch (env : EvalEnv) (expected actual : Term) : EvalEnv :=
  env.addError (TypeError.mismatch expected actual env.loc)

def setAttr (env : EvalEnv) (path : AttrPath) (name : String) (val : Term) : EvalEnv :=
  { env with attrs := env.attrs.insert path name val }

def getAttr (env : EvalEnv) (path : AttrPath) (name : String) : Option Term :=
  env.attrs.lookup path name

def hasErrors (env : EvalEnv) : Bool :=
  !env.errors.isEmpty

end EvalEnv

/-! ## Bidirectional Mode -/

/-- Bidirectional typing mode -/
inductive Mode where
  | infer : Mode  -- Synthesize type
  | check : Mode  -- Check against expected
  deriving Repr, BEq

/-! ## Substitution -/

/-- Substitute a variable with a term in an expression -/
partial def subst (name : String) (replacement : Term) : Term → Term
  | .var n => if n == name then replacement else .var n
  | .lit s => .lit s
  | .con c args => .con c (args.map (subst name replacement))

/-- Capture-avoiding substitution (renames binders if needed) -/
partial def substAvoid (name : String) (replacement : Term) (freeVars : List String) : Term → Term
  | .var n => if n == name then replacement else .var n
  | .lit s => .lit s
  | .con "lam" [.var x, ty, body] =>
    if x == name then
      -- Shadowed, don't substitute in body
      .con "lam" [.var x, substAvoid name replacement freeVars ty, body]
    else if freeVars.contains x then
      -- x appears free in replacement, need to rename
      let x' := freshName x freeVars
      let body' := subst x (.var x') body
      .con "lam" [.var x', substAvoid name replacement freeVars ty,
                  substAvoid name replacement (x' :: freeVars) body']
    else
      .con "lam" [.var x, substAvoid name replacement freeVars ty,
                  substAvoid name replacement freeVars body]
  | .con "Pi" [.var x, dom, cod] =>
    if x == name then
      .con "Pi" [.var x, substAvoid name replacement freeVars dom, cod]
    else if freeVars.contains x then
      let x' := freshName x freeVars
      let cod' := subst x (.var x') cod
      .con "Pi" [.var x', substAvoid name replacement freeVars dom,
                 substAvoid name replacement (x' :: freeVars) cod']
    else
      .con "Pi" [.var x, substAvoid name replacement freeVars dom,
                 substAvoid name replacement freeVars cod]
  | .con c args => .con c (args.map (substAvoid name replacement freeVars))
where
  freshName (base : String) (avoid : List String) : String :=
    let rec go (i : Nat) : String :=
      let candidate := if i == 0 then base else s!"{base}{i}"
      if avoid.contains candidate then go (i + 1) else candidate
    go 0

/-- Get free variables in a term -/
partial def freeVars : Term → List String
  | .var n => [n]
  | .lit _ => []
  | .con "lam" [.var x, ty, body] =>
    freeVars ty ++ (freeVars body).filter (· != x)
  | .con "Pi" [.var x, dom, cod] =>
    freeVars dom ++ (freeVars cod).filter (· != x)
  | .con _ args => args.flatMap freeVars

/-! ## Definitional Equality -/

/-- Check if two types are definitionally equal (α-equivalence) -/
partial def typeEq (t1 t2 : Term) : Bool :=
  alphaEq [] t1 t2
where
  /-- Alpha-equivalence with bound variable tracking -/
  alphaEq (binds : List (String × String)) (a b : Term) : Bool :=
    match a, b with
    | .var x, .var y =>
      -- Check if bound variables correspond
      match binds.find? (·.1 == x) with
      | some (_, y') => y == y'
      | none => match binds.find? (·.2 == y) with
        | some _ => false  -- y is bound but x isn't
        | none => x == y   -- Both free, must be same name
    | .lit s1, .lit s2 => s1 == s2
    | .con "lam" [.var x, ty1, body1], .con "lam" [.var y, ty2, body2] =>
      alphaEq binds ty1 ty2 && alphaEq ((x, y) :: binds) body1 body2
    | .con "Pi" [.var x, dom1, cod1], .con "Pi" [.var y, dom2, cod2] =>
      alphaEq binds dom1 dom2 && alphaEq ((x, y) :: binds) cod1 cod2
    | .con c1 args1, .con c2 args2 =>
      c1 == c2 && args1.length == args2.length &&
      (args1.zip args2).all fun (a, b) => alphaEq binds a b
    | _, _ => false

/-! ## Core Type Operations -/

/-- Get domain of a function type -/
def getDomain (ty : Term) : Option Term :=
  match ty with
  | .con "Pi" [_, dom, _] => some dom
  | .con "Arrow" [dom, _] => some dom
  | _ => none

/-- Get codomain of a function type -/
def getCodomain (ty : Term) : Option Term :=
  match ty with
  | .con "Pi" [_, _, cod] => some cod
  | .con "Arrow" [_, cod] => some cod
  | _ => none

/-- Substitute argument in dependent function codomain -/
def substCodomain (ty : Term) (arg : Term) : Term :=
  match ty with
  | .con "Pi" [.var name, _, cod] =>
    substAvoid name arg (freeVars arg) cod
  | .con "Arrow" [_, cod] => cod  -- Non-dependent, no substitution needed
  | _ => ty

/-! ## Attribute-Based Type Checking -/

/-- Configuration for evaluation -/
structure EvalConfig where
  maxDepth : Nat := 1000  -- Fuel for recursion
  tracing : Bool := false
  deriving Repr


/-- Helper: merge EvalEnv -/
def mergeEvalEnv (acc child : EvalEnv) : EvalEnv :=
  { acc with
    attrs := AttrEnv.merge acc.attrs child.attrs
    errors := acc.errors ++ child.errors }

/-- Productions that bind variables: (prod, binderChildIdx, typeChildIdx, bodyChildIdx) -/
def binderProductions : List (String × Nat × Nat × Nat) :=
  [ ("lam", 0, 1, 2)    -- λ x : A . body
  , ("Pi", 0, 1, 2)     -- Π x : A . B
  , ("Sigma", 0, 1, 2)  -- Σ x : A . B
  , ("let", 0, 1, 3)    -- let x : A = v in body (body is child 3)
  ]

/-- Get binder info if this is a binder production -/
def getBinderInfo (prod : String) : Option (Nat × Nat × Nat) :=
  binderProductions.find? (·.1 == prod) |>.map (fun (_, a, b, c) => (a, b, c))

/-- Extract variable name from a term (handles var and lit) -/
def extractName (t : Term) : Option String :=
  match t with
  | .var n => some n
  | .lit n => some n
  | _ => none

/-- Evaluate synthesized attributes bottom-up with error handling.

    For each node:
    1. Recursively evaluate children (with scope extension for binders)
    2. Collect children's synthesized attributes
    3. Evaluate this node's rules using children's attributes
    4. Report errors for missing/invalid attributes -/
partial def evalSynWithErrors
    (config : EvalConfig)
    (defs : List AttrDef)
    (term : Term)
    (parentEnv : EvalEnv)
    : EvalEnv :=
  if config.maxDepth == 0 then
    parentEnv.addTypeError "evaluation depth exceeded"
  else
    let config' := { config with maxDepth := config.maxDepth - 1 }
    match term with
    | .con prod children =>
      -- Check if this is a binder production
      let binderInfo := getBinderInfo prod

      -- Step 1: Recursively evaluate children with scope handling
      let childResults := Util.enumerate children |>.map fun (i, child) =>
        -- Check if this child is in a binding position (binder name in lam/Pi/etc)
        let isBindingPosition := match binderInfo with
          | some (binderIdx, _, _) => i == binderIdx
          | none => false

        -- For binder productions, extend context before evaluating body
        let evalEnv := match binderInfo with
          | some (binderIdx, typeIdx, bodyIdx) =>
            if i == bodyIdx then
              -- This is the body - extend context with the binder
              let binderTerm := children[binderIdx]?
              let typeTerm := children[typeIdx]?
              match binderTerm, typeTerm with
              | some bt, some tt =>
                match extractName bt with
                | some name => parentEnv.addBinding name tt
                | none => parentEnv
              | _, _ => parentEnv
            else
              parentEnv
          | none => parentEnv

        -- Skip variable lookup for binding positions
        let childEnv := if isBindingPosition then
          match child with
          | .var name =>
            -- Binder name - don't look up, just set name attribute
            evalEnv.setAttr [] "name" (.lit name)
          | _ => evalSynWithErrors config' defs child evalEnv
        else
          evalSynWithErrors config' defs child evalEnv
        let childName := s!"child{i}"
        -- Prefix child's attributes
        let prefixed : AttrEnv := ⟨childEnv.attrs.values.map fun ((path, name), val) =>
          ((childName :: path, name), val)⟩
        (childEnv, prefixed)

      let childEnvs := childResults.map (·.1)
      let childAttrs := childResults.map (·.2)

      -- Step 2: Build environment with children's attributes
      let baseEnv := childEnvs.foldl mergeEvalEnv parentEnv
      let env := childAttrs.foldl (fun e a => { e with attrs := AttrEnv.merge e.attrs a }) baseEnv

      -- Step 3: Evaluate rules for each syn attribute
      defs.filter (·.flow == .syn) |>.foldl (fun env def_ =>
        match findRule prod [] def_.rules with
        | some rule =>
          let val := evalAttrExpr rule.expr env.attrs
          env.setAttr [] def_.name val
        | none =>
          -- No rule for this production - might be ok depending on grammar
          env
      ) env

    | .var name =>
      -- Variable: look up in context
      match parentEnv.ctx.lookupType name with
      | some ty =>
        parentEnv.setAttr [] "type" ty
                 |>.setAttr [] "elab" (.var name)
      | none =>
        parentEnv.addError (TypeError.undefined name parentEnv.loc)

    | .lit s =>
      -- Literal: could be number, string, etc.
      parentEnv.setAttr [] "elab" (.lit s)

/-- Evaluate inherited attributes top-down with error handling.

    For binder productions (lam, Pi, Sigma, let), extends context before
    evaluating body children. -/
partial def evalInhWithErrors
    (config : EvalConfig)
    (defs : List AttrDef)
    (term : Term)
    (parentEnv : EvalEnv)
    : EvalEnv :=
  if config.maxDepth == 0 then
    parentEnv.addTypeError "evaluation depth exceeded"
  else
    let config' := { config with maxDepth := config.maxDepth - 1 }
    match term with
    | .con prod children =>
      -- Check if this is a binder production
      let binderInfo := getBinderInfo prod

      -- For each child, compute inherited attributes
      let inhDefs := defs.filter (fun d => d.flow == .inh)
      let childEnvs := Util.enumerate children |>.map fun (i, child) =>
        let childName := s!"child{i}"

        -- For each inh attribute, check for rules targeting this child
        let childEnv := inhDefs.foldl (fun (env : EvalEnv) (def_ : AttrDef) =>
          match findRule prod [childName] def_.rules with
          | some rule =>
            let val := evalAttrExpr rule.expr parentEnv.attrs
            env.setAttr [] def_.name val
          | none =>
            -- Inherit from parent if no specific rule
            match parentEnv.getAttr [] def_.name with
            | some val => env.setAttr [] def_.name val
            | none => env
        ) EvalEnv.empty

        -- For binder productions, extend context before evaluating body
        let childEnvWithScope := match binderInfo with
          | some (binderIdx, typeIdx, bodyIdx) =>
            if i == bodyIdx then
              let binderTerm := children[binderIdx]?
              let typeTerm := children[typeIdx]?
              match binderTerm, typeTerm with
              | some bt, some tt =>
                match extractName bt with
                | some name =>
                  { childEnv with ctx := childEnv.ctx.extend name tt }
                | none => childEnv
              | _, _ => childEnv
            else
              childEnv
          | none => childEnv

        -- Recurse into child
        evalInhWithErrors config' defs child childEnvWithScope

      -- Merge all child environments
      childEnvs.foldl (fun acc env =>
        { acc with errors := acc.errors ++ env.errors }
      ) parentEnv

    | _ => parentEnv


/-! ## Full Two-Pass Evaluation -/

/-- Evaluate all attributes using two-pass algorithm:
    1. Top-down: inherited attributes (context propagation)
    2. Bottom-up: synthesized attributes (type inference) -/
def evalAllAttrs
    (config : EvalConfig := {})
    (defs : List AttrDef)
    (term : Term)
    (initialCtx : Context := Context.empty)
    : EvalEnv :=
  let env := { EvalEnv.empty with ctx := initialCtx }

  -- Pass 1: inherited (top-down)
  let inhEnv := evalInhWithErrors config defs term env

  -- Pass 2: synthesized (bottom-up)
  let synEnv := evalSynWithErrors config defs term inhEnv

  synEnv

/-! ## Convenient API -/

/-- Typecheck a term and get the type attribute -/
def typecheck (defs : List AttrDef) (term : Term) (ctx : Context := Context.empty) : EvalResult Term :=
  let env := evalAllAttrs {} defs term ctx
  match env.getAttr [] "type" with
  | some ty =>
    if env.hasErrors then
      .failed env.errors
    else
      .ok ty env.errors
  | none =>
    .failed (TypeError.error "failed to infer type" :: env.errors)

/-- Get the elaborated term -/
def elaborateTerm (defs : List AttrDef) (term : Term) (ctx : Context := Context.empty) : EvalResult Term :=
  let env := evalAllAttrs {} defs term ctx
  match env.getAttr [] "elab" with
  | some elabTerm =>
    if env.hasErrors then
      .failed env.errors
    else
      .ok elabTerm env.errors
  | none =>
    .failed (TypeError.error "failed to elaborate" :: env.errors)

/-! ## Error Reporting Utilities -/

/-- Format all errors for display -/
def formatErrors (errors : List TypeError) : String :=
  errors.map TypeError.toString |> String.intercalate "\n"

/-- Count errors by severity -/
def countBySeverity (errors : List TypeError) : Nat × Nat × Nat :=
  errors.foldl (fun (e, w, i) err =>
    match err.severity with
    | .error => (e + 1, w, i)
    | .warning => (e, w + 1, i)
    | .info => (e, w, i + 1)
  ) (0, 0, 0)

/-- Pretty print error summary -/
def errorSummary (errors : List TypeError) : String :=
  let (e, w, i) := countBySeverity errors
  s!"{e} error(s), {w} warning(s), {i} info"

/-! ## TypeRule to AttrDef Conversion -/

/-- Convert a TypeRule to an AttrRule for the "type" synthesized attribute.

    This bridges the declarative type rule syntax:
      type foo : (typeof (Con $a $b)) : (SomeType $a)

    To the attribute grammar rule format:
      { prod := "Con", target := [], expr := (SomeType child0.type) }

    The key insight: TypeRules pattern match on `(typeof term)` and produce a type,
    while AttrRules are keyed by production name and compute attributes. -/
def typeRuleToAttrRule (tr : TypeRule) : Option AttrRule :=
  match extractProdName tr.subject with
  | some prodName =>
    -- The type expression may reference children via metavars $a, $b, etc.
    -- For now, we keep the expression as-is and let evalAttrExpr handle substitution
    some { prod := prodName, target := [], expr := tr.type }
  | none => none

/-- Create an AttrDef for synthesized "type" attribute from TypeRules.

    This is the bridge from the declarative type rules in .lego files
    to the executable attribute grammar system. The resulting AttrDef:
    - has flow = syn (synthesized, bottom-up)
    - has one rule per TypeRule that matched a specific production -/
def typeRulesToAttrDef (typeRules : List TypeRule) : AttrDef :=
  let rules := typeRules.filterMap typeRuleToAttrRule
  { name := "type"
    flow := .syn
    type := none  -- Polymorphic over type universe
    rules := rules }

/-- Type check a term using TypeRules via the attribute grammar system.

    This is the main entry point for AG-based type checking:
    1. Convert TypeRules to an AttrDef
    2. Run the two-pass AG evaluation (inherited then synthesized)
    3. Extract the "type" attribute from the result -/
def typecheckWithRules (typeRules : List TypeRule) (term : Term) (ctx : Context := Context.empty) : EvalResult Term :=
  let attrDef := typeRulesToAttrDef typeRules
  typecheck [attrDef] term ctx

end Lego
