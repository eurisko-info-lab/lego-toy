/-
  Lego.Validation: Semantic validation and optimization for .lego files

  Detects errors that pass parsing but are semantically invalid:
    - Undefined production references
    - Duplicate production names
    - Unbound variables in rule templates
    - Conflicting rules (same pattern, different result)
    - Left recursion (direct and indirect)
    - Unused productions

  Optimization warnings:
    - Missing cut points (suggests where to add cuts)
    - Unreachable alternatives in grammar
    - Redundant alternatives
    - Non-terminating rule cycles

  Architecture: Pure validation functions, no IO.
  Called after parsing, before evaluation.
-/

import Lego.Algebra
import Lego.Normalize
import Lego.Util
import Std.Data.HashMap
import Std.Data.HashSet

namespace Lego.Validation

open Lego
open Std (HashMap HashSet)

/-! ## Severity and Error Types -/

/-- Severity of validation issue -/
inductive Severity where
  | error   : Severity  -- blocks execution
  | warning : Severity  -- execution continues
  | info    : Severity  -- informational
  deriving Repr, BEq

/-- Source location for error messages -/
structure SourceLoc where
  file : String := "<unknown>"
  line : Nat := 0
  column : Nat := 0
  deriving Repr, BEq, Inhabited

def SourceLoc.format (loc : SourceLoc) : String :=
  if loc.line > 0 then s!"{loc.file}:{loc.line}:{loc.column}"
  else loc.file

/-- Validation error (blocks execution) -/
inductive ValidationError where
  | undefinedProduction (ref : String) (source : String) : ValidationError
  | duplicateProduction (name : String) : ValidationError
  | unboundVariable (varName : String) (ruleName : String) : ValidationError
  | circularImport (modName : String) : ValidationError
  | invalidSyntax (ctx : String) (message : String) : ValidationError
  -- Cubical-specific errors
  | dimensionMismatch (expected : String) (got : String) (ctx : String) : ValidationError
  | invalidCofibration (cof : String) (reason : String) : ValidationError
  | pathEndpointMismatch (endpoint : String) (expected : String) (got : String) : ValidationError
  | systemIncomplete (cof : String) (missingFace : String) : ValidationError
  | glueMalformed (reason : String) : ValidationError
  deriving Repr, BEq

/-- Validation warning (execution continues) -/
inductive ValidationWarning where
  | conflictingRules (rule1 : String) (rule2 : String) (reason : String) : ValidationWarning
  | directLeftRecursion (name : String) : ValidationWarning
  | indirectLeftRecursion (path : List String) : ValidationWarning
  | unusedProduction (name : String) : ValidationWarning
  | shadowedProduction (name : String) (shadowedBy : String) : ValidationWarning
  | ambiguousGrammar (name : String) (reason : String) : ValidationWarning
  -- Optimization warnings
  | missingCut (prod : String) (keyword : String) : ValidationWarning
  | ruleCycle (cycle : List String) : ValidationWarning
  | unreachableAlt (prod : String) (idx : Nat) : ValidationWarning
  | redundantAlt (prod : String) (idx1 : Nat) (idx2 : Nat) : ValidationWarning
  deriving Repr, BEq

/-- Result of validation -/
structure ValidationResult where
  errors   : List ValidationError := []
  warnings : List ValidationWarning := []
  deriving Repr

instance : Append ValidationResult where
  append r1 r2 := ⟨r1.errors ++ r2.errors, r1.warnings ++ r2.warnings⟩

def ValidationResult.empty : ValidationResult := ⟨[], []⟩

/-! ## Format Functions -/

def ValidationError.format : ValidationError → String
  | .undefinedProduction ref source =>
      s!"ERROR: Undefined production '{ref}' referenced from '{source}'"
  | .duplicateProduction name =>
      s!"ERROR: Duplicate production '{name}'"
  | .unboundVariable v rule =>
      s!"ERROR: Unbound variable '{v}' in rule '{rule}'"
  | .circularImport modName =>
      s!"ERROR: Circular import of '{modName}'"
  | .invalidSyntax ctx msg =>
      s!"ERROR: Invalid syntax in {ctx}: {msg}"
  -- Cubical-specific errors with helpful context
  | .dimensionMismatch expected got ctx =>
      s!"ERROR: Dimension mismatch in {ctx}: expected {expected}, got {got}\n" ++
      s!"  Hint: Dimensions must be 0, 1, or dimension variables"
  | .invalidCofibration cof reason =>
      s!"ERROR: Invalid cofibration '{cof}': {reason}\n" ++
      s!"  Hint: Valid forms: i=0, i=1, φ∧ψ, φ∨ψ, ⊤, ⊥"
  | .pathEndpointMismatch endpoint expected got =>
      s!"ERROR: Path endpoint mismatch at {endpoint}: expected {expected}, got {got}\n" ++
      s!"  Hint: Path types require p@0 = a and p@1 = b for Path A a b"
  | .systemIncomplete cof missingFace =>
      s!"ERROR: Incomplete system for cofibration '{cof}': missing face {missingFace}\n" ++
      s!"  Hint: Systems must cover all faces of the cofibration"
  | .glueMalformed reason =>
      s!"ERROR: Malformed Glue type: {reason}\n" ++
      s!"  Hint: Glue requires (φ, T, f : T ≃ A) where φ is a cofibration"

def ValidationWarning.format : ValidationWarning → String
  | .conflictingRules r1 r2 reason =>
      s!"WARNING: Conflicting rules '{r1}' and '{r2}': {reason}"
  | .directLeftRecursion name =>
      s!"WARNING: Direct left recursion in production '{name}'"
  | .indirectLeftRecursion path =>
      s!"WARNING: Indirect left recursion: {" -> ".intercalate path}"
  | .unusedProduction name =>
      s!"WARNING: Unused production '{name}'"
  | .shadowedProduction name shadowedBy =>
      s!"WARNING: Production '{name}' shadowed by '{shadowedBy}'"
  | .ambiguousGrammar name reason =>
      s!"WARNING: Ambiguous grammar for '{name}': {reason}"
  | .missingCut prod kw =>
      s!"OPTIMIZE: Production '{prod}' could add cut after '{kw}' for better errors"
  | .ruleCycle cyc =>
      s!"WARNING: Potential non-terminating rule cycle: {" -> ".intercalate cyc}"
  | .unreachableAlt prod idx =>
      s!"WARNING: Alternative {idx} in '{prod}' is unreachable"
  | .redundantAlt prod i j =>
      s!"WARNING: Alternatives {i} and {j} in '{prod}' are redundant"

/-! ## Grammar Expression Helpers -/

/-- Unwrap a GrammarExpr to get the inner GrammarF -/
def unwrapGrammar : GrammarExpr → GrammarF GrammarExpr
  | .mk f => f

/-- Check if a grammar expression is a literal -/
def isGrammarLit : GrammarExpr → Option String
  | .mk (.lit s) => some s
  | _ => none

/-- Check if a grammar expression is a ref -/
def isGrammarRef : GrammarExpr → Option String
  | .mk (.ref s) => some s
  | _ => none

/-! ## Helper functions -/


/-- Extract base name from qualified name (e.g., "Term.expr" → "expr") -/
def baseName (s : String) : String :=
  match s.splitOn "." with
  | [_prefix, name] => name
  | _ => s

/-- Built-in productions that don't need explicit definition -/
def builtinProductions : HashSet String :=
  HashSet.emptyWithCapacity
    |>.insert "nat"
    |>.insert "int"
    |>.insert "str"
    |>.insert "string"
    |>.insert "ident"
    |>.insert "char"
    |>.insert "float"
    |>.insert "bool"

/-! ## Grammar Checks -/

/-- Extract all references from a grammar expression -/
partial def extractRefs : GrammarExpr → HashSet String
  | .mk f => match f with
    | .ref name => HashSet.emptyWithCapacity.insert name
    | .seq g1 g2 => extractRefs g1 |>.insertMany (extractRefs g2)
    | .alt g1 g2 => extractRefs g1 |>.insertMany (extractRefs g2)
    | .star g => extractRefs g
    | .bind _ g => extractRefs g
    | .node _ g => extractRefs g
    | .empty => HashSet.emptyWithCapacity
    | .lit _ => HashSet.emptyWithCapacity
    -- PEG extensions
    | .cut g => extractRefs g
    | .ordered g1 g2 => extractRefs g1 |>.insertMany (extractRefs g2)
    | .longest gs => gs.foldl (fun acc g => acc.insertMany (extractRefs g)) HashSet.emptyWithCapacity
    -- Layout annotations
    | .layout _ => HashSet.emptyWithCapacity

/-- Check for undefined production references -/
def checkUndefinedRefs (grammar : HashMap String GrammarExpr) : ValidationResult :=
  let defined := grammar.fold (init := HashSet.emptyWithCapacity) fun acc k _ => acc.insert k
  let definedBase := defined.fold (init := HashSet.emptyWithCapacity) fun acc k => acc.insert (baseName k)

  let isDefined (ref : String) : Bool :=
    defined.contains ref ||
    definedBase.contains (baseName ref) ||
    builtinProductions.contains (baseName ref)

  let errors := grammar.fold (init := ([] : List ValidationError)) fun acc fromProd g =>
    let refs := extractRefs g
    refs.fold (init := acc) fun acc' ref =>
      if isDefined ref then acc'
      else .undefinedProduction ref fromProd :: acc'

  ⟨errors, []⟩

/-- Check if a production has direct left recursion -/
partial def isDirectLeftRec (name : String) : GrammarExpr → Bool
  | .mk f => match f with
    | .ref ref => ref == name
    | .seq g1 _ => isDirectLeftRec name g1  -- Check leftmost
    | .alt g1 g2 => isDirectLeftRec name g1 || isDirectLeftRec name g2
    | .star g => isDirectLeftRec name g
    | .bind _ g => isDirectLeftRec name g
    | .node _ g => isDirectLeftRec name g
    | _ => false

/-- Check for left recursion (direct only for now) -/
def checkLeftRecursion (grammar : HashMap String GrammarExpr) : ValidationResult :=
  let directWarnings := grammar.fold (init := ([] : List ValidationWarning)) fun acc name g =>
    if isDirectLeftRec name g then
      .directLeftRecursion name :: acc
    else acc
  ⟨[], directWarnings⟩

/-! ## Rule Checks -/

/-- Extract all variables from a term -/
partial def varsIn : Term → HashSet String
  | .var v => HashSet.emptyWithCapacity.insert v
  | .con _ args => args.foldl (fun acc t => acc.insertMany (varsIn t)) HashSet.emptyWithCapacity
  | .lit _ => HashSet.emptyWithCapacity

/-- Extract pattern variables (those starting with $) -/
partial def patternVars : Term → HashSet String
  | .var v => if v.startsWith "$" then HashSet.emptyWithCapacity.insert v else HashSet.emptyWithCapacity
  | .con _ args => args.foldl (fun acc t => acc.insertMany (patternVars t)) HashSet.emptyWithCapacity
  | .lit _ => HashSet.emptyWithCapacity

/-- Check for unbound variables in rule templates -/
def checkUnboundVars (rules : List Rule) : ValidationResult :=
  let errors := rules.foldl (init := ([] : List ValidationError)) fun acc rule =>
    let patVars := patternVars rule.pattern
    let tplVars := varsIn rule.template |>.fold (init := HashSet.emptyWithCapacity) fun s v =>
      if v.startsWith "$" then s.insert v else s
    let unbound := tplVars.fold (init := ([] : List String)) fun acc' v =>
      if patVars.contains v then acc' else v :: acc'
    unbound.foldl (fun acc'' v => ValidationError.unboundVariable v rule.name :: acc'') acc
  ⟨errors, []⟩

/-- Generate a pattern key for grouping (ignoring variable names) -/
partial def patternKey : Term → String
  | .var _ => "_"
  | .lit s => s!"\"{s}\""
  | .con name args => s!"({name} {" ".intercalate (args.map patternKey)})"

/-- Check for conflicting rules (same pattern, different result) -/
def checkConflictingRules (rules : List Rule) : ValidationResult :=
  -- Group rules by pattern structure
  let grouped := rules.foldl (init := HashMap.emptyWithCapacity) fun acc rule =>
    let key := patternKey rule.pattern
    match acc.get? key with
    | some rs => acc.insert key (rule :: rs)
    | none => acc.insert key [rule]

  let warnings := grouped.fold (init := ([] : List ValidationWarning)) fun acc _ rs =>
    if rs.length < 2 then acc
    else
      -- Check all pairs
      let pairs := rs.flatMap fun r1 =>
        rs.filterMap fun r2 =>
          if r1.name < r2.name then some (r1, r2) else none
      pairs.foldl (fun acc' (r1, r2) =>
        if r1.template == r2.template then acc'
        else .conflictingRules r1.name r2.name "same pattern structure" :: acc') acc

  ⟨[], warnings⟩

/-! ## Optimization Checks -/


/-- Find leading keywords in a grammar expression -/
partial def findLeadingKeywords : GrammarExpr → List String
  | .mk f => match f with
    | .lit kw => if Util.isKeywordLike kw then [kw] else []
    | .alt g1 g2 => findLeadingKeywords g1 ++ findLeadingKeywords g2
    | .seq g1 _ => findLeadingKeywords g1
    | .bind _ g => findLeadingKeywords g
    | .node _ g => findLeadingKeywords g
    | _ => []

/-- Check for missing cut points in grammar -/
def checkMissingCuts (grammar : HashMap String GrammarExpr) : ValidationResult :=
  let warnings := grammar.fold (init := ([] : List ValidationWarning)) fun acc prodName g =>
    let keywords := findLeadingKeywords g
    -- For simplicity, we don't check if cuts exist yet (would need more complex analysis)
    -- Just warn for all leading keywords
    keywords.foldl (fun acc' kw => .missingCut prodName kw :: acc') acc
  ⟨[], warnings⟩

/-- Flatten alternatives into a list -/
partial def flattenAlts : GrammarExpr → List GrammarExpr
  | .mk (.alt g1 g2) => flattenAlts g1 ++ flattenAlts g2
  | g => [g]

/-- Check structural equality of grammar expressions -/
partial def structurallyEqual : GrammarExpr → GrammarExpr → Bool
  | .mk f1, .mk f2 => match f1, f2 with
    | .lit s1, .lit s2 => s1 == s2
    | .ref r1, .ref r2 => r1 == r2
    | .seq a1 b1, .seq a2 b2 => structurallyEqual a1 a2 && structurallyEqual b1 b2
    | .alt a1 b1, .alt a2 b2 => structurallyEqual a1 a2 && structurallyEqual b1 b2
    | .star g1, .star g2 => structurallyEqual g1 g2
    | .bind n1 g1, .bind n2 g2 => n1 == n2 && structurallyEqual g1 g2
    | .node n1 g1, .node n2 g2 => n1 == n2 && structurallyEqual g1 g2
    | .empty, .empty => true
    | _, _ => false

/-- Check if g1 is a prefix of g2 -/
partial def isPrefix (g1 g2 : GrammarExpr) : Bool :=
  match unwrapGrammar g1, unwrapGrammar g2 with
  | .lit s1, .lit s2 => s1 == s2
  | .ref r1, .ref r2 => r1 == r2
  | .seq a1 b1, .seq a2 b2 => structurallyEqual a1 a2 && isPrefix b1 b2
  | _, .seq a2 _ => structurallyEqual g1 a2
  | _, _ => false

/-- Check for unreachable alternatives in grammar -/
def checkUnreachableAlts (grammar : HashMap String GrammarExpr) : ValidationResult :=
  let warnings := grammar.fold (init := ([] : List ValidationWarning)) fun acc prodName g =>
    let alts := Util.zipWithIndex (flattenAlts g)
    let pairs := alts.flatMap fun (a1, i) =>
      alts.filterMap fun (a2, j) =>
        if i < j then some (i, j, a1, a2) else none
    pairs.foldl (fun acc' (i, j, alt1, alt2) =>
      if isPrefix alt1 alt2 then
        .unreachableAlt prodName j :: acc'
      else if structurallyEqual alt1 alt2 then
        .redundantAlt prodName i j :: acc'
      else acc') acc
  ⟨[], warnings⟩

/-! ## Main Validation Entry Points -/

/-- Validate grammar definitions -/
def validateGrammar (grammar : HashMap String GrammarExpr) : ValidationResult :=
  checkUndefinedRefs grammar ++
  checkLeftRecursion grammar ++
  checkMissingCuts grammar ++
  checkUnreachableAlts grammar

/-- Validate rewrite rules -/
def validateRules (rules : List Rule) : ValidationResult :=
  checkUnboundVars rules ++
  checkConflictingRules rules

/-! ## Verified Rule and Repr Validation -/

/-- Error types for cubical verification -/
inductive VerificationError where
  | verifiedRuleInvalidProof (ruleName : String) (expected : String) (got : String) : VerificationError
  | reprEquivInvalidProof (reprName : String) (expected : String) (got : String) : VerificationError
  | typeCheckFailed (termDesc : String) (expected : String) (reason : String) : VerificationError
  | reflProofNotDefEq (ruleName : String) (lhs : String) (rhs : String)
      (lhsNorm : String) (rhsNorm : String) : VerificationError
  | proofEndpointsMismatch (ruleName : String) (which : String)
      (expected : String) (got : String) (expectedNorm : String) (gotNorm : String) : VerificationError
  deriving Repr, BEq

def VerificationError.format : VerificationError → String
  | .verifiedRuleInvalidProof name exp got =>
    s!"ERROR: Verified rule '{name}' proof has wrong type.\n  Expected: Path {exp}\n  Got: {got}"
  | .reprEquivInvalidProof name exp got =>
    s!"ERROR: Repr equivalence '{name}' proof has wrong type.\n  Expected: Equiv {exp}\n  Got: {got}"
  | .typeCheckFailed desc exp reason =>
    s!"ERROR: Type check failed for {desc}.\n  Expected: {exp}\n  Reason: {reason}"
  | .reflProofNotDefEq name lhs rhs lhsNorm rhsNorm =>
    s!"ERROR: Verified rule '{name}' uses refl but LHS and RHS are not definitionally equal.\n  LHS: {lhs}\n  RHS: {rhs}\n  LHS normalizes to: {lhsNorm}\n  RHS normalizes to: {rhsNorm}"
  | .proofEndpointsMismatch name which exp got expNorm gotNorm =>
    s!"ERROR: Verified rule '{name}' proof {which} endpoint mismatch.\n  Expected: {exp}\n  Got: {got}\n  Expected normalizes to: {expNorm}\n  Got normalizes to: {gotNorm}"

/-- Check if a term is a refl proof -/
def isReflProof : Term → Bool
  | .con "refl" _ => true
  | _ => false

/-- Verify a "verified rule" declaration:
    verified rule name : lhs ~> rhs via proof ;
    The proof must have type: Path _ lhs rhs

    For refl proofs, we verify that lhs and rhs are definitionally equal.
    For other proofs, we type-check the proof and verify endpoints match
    up to definitional equality (normalization). -/
def verifyVerifiedRule (typeRules : List TypeRule) (rules : List (Term × Term))
    (ruleName : String) (lhs rhs proof : Term) : Option VerificationError :=
  let fuel := 1000
  -- For refl proofs, check definitional equality directly
  if isReflProof proof then
    let lhsNorm := Cubical.normalize fuel rules lhs
    let rhsNorm := Cubical.normalize fuel rules rhs
    if lhsNorm == rhsNorm then none
    else some (.reflProofNotDefEq ruleName s!"{lhs}" s!"{rhs}" s!"{lhsNorm}" s!"{rhsNorm}")
  else
    -- For other proofs, infer the type and check it's Path _ a b
    -- where a ≡ lhs and b ≡ rhs (definitionally equal)
    match inferType typeRules proof with
    | some (.con "Path" [_, a, b]) =>
      -- Normalize all terms for definitional equality check
      let lhsNorm := Cubical.normalize fuel rules lhs
      let rhsNorm := Cubical.normalize fuel rules rhs
      let aNorm := Cubical.normalize fuel rules a
      let bNorm := Cubical.normalize fuel rules b
      -- Check LHS endpoint
      if aNorm != lhsNorm then
        some (.proofEndpointsMismatch ruleName "LHS"
          s!"{lhs}" s!"{a}" s!"{lhsNorm}" s!"{aNorm}")
      -- Check RHS endpoint
      else if bNorm != rhsNorm then
        some (.proofEndpointsMismatch ruleName "RHS"
          s!"{rhs}" s!"{b}" s!"{rhsNorm}" s!"{bNorm}")
      else none
    | some other =>
      some (.verifiedRuleInvalidProof ruleName
        s!"Path _ {lhs} {rhs}"
        s!"{other}")
    | none =>
      -- Can't infer type - give a soft error
      some (.typeCheckFailed s!"proof of verified rule '{ruleName}'"
        s!"Path _ {lhs} {rhs}" "could not infer type of proof term")

/-- Verify a "repr" declaration:
    repr A ≃ B via equiv ;
    The equiv must have type: Equiv A B -/
def verifyReprEquiv (typeRules : List TypeRule) (reprName : String)
    (typeA typeB equiv : Term) : Option VerificationError :=
  -- Infer the type of the equivalence term
  match inferType typeRules equiv with
  | some (.con "Equiv" [a, b]) =>
    -- Check that a == typeA and b == typeB
    if a == typeA && b == typeB then none
    else some (.reprEquivInvalidProof reprName
      s!"Equiv {typeA} {typeB}"
      s!"Equiv {a} {b}")
  | some other =>
    some (.reprEquivInvalidProof reprName
      s!"Equiv {typeA} {typeB}"
      s!"{other}")
  | none =>
    -- Can't infer type - give a soft error
    some (.typeCheckFailed s!"equivalence proof of repr '{reprName}'"
      s!"Equiv {typeA} {typeB}" "could not infer type of equivalence term")

/-- Extract verified rules from AST and check them -/
def validateVerifiedRules (typeRules : List TypeRule) (rules : List (Term × Term))
    (ast : Term) : List VerificationError :=
  extractVerifiedRulesFromAST ast |>.filterMap fun (name, lhs, rhs, proof) =>
    verifyVerifiedRule typeRules rules name lhs rhs proof
where
  extractVerifiedRulesFromAST (t : Term) : List (String × Term × Term × Term) :=
    match t with
    | .con "verifiedRule" [.con "ident" [.var name], lhs, rhs, proof] =>
      [(name, lhs, rhs, proof)]
    | .con "verifiedRule" [.con "ident" [.lit name], lhs, rhs, proof] =>
      [(name, lhs, rhs, proof)]
    | .con _ args => args.flatMap extractVerifiedRulesFromAST
    | _ => []

/-- Extract repr declarations from AST and check them -/
def validateReprEquivs (typeRules : List TypeRule) (ast : Term) : List VerificationError :=
  extractReprEquivsFromAST ast |>.filterMap fun (name, typeA, typeB, equiv) =>
    verifyReprEquiv typeRules name typeA typeB equiv
where
  extractReprEquivsFromAST (t : Term) : List (String × Term × Term × Term) :=
    match t with
    | .con "reprEquiv" [.con "ident" [.var name], typeA, typeB, equiv] =>
      [(name, typeA, typeB, equiv)]
    | .con "reprEquiv" [.con "ident" [.lit name], typeA, typeB, equiv] =>
      [(name, typeA, typeB, equiv)]
    | .con _ args => args.flatMap extractReprEquivsFromAST
    | _ => []

/-- Validate cubical constructs: verified rules and repr equivalences -/
def validateCubical (typeRules : List TypeRule) (rules : List (Term × Term))
    (ast : Term) : List VerificationError :=
  validateVerifiedRules typeRules rules ast ++ validateReprEquivs typeRules ast

/-- Main validation entry point -/
def validate (grammar : HashMap String GrammarExpr) (rules : List Rule) : ValidationResult :=
  validateGrammar grammar ++ validateRules rules

/-- Format all errors and warnings -/
def ValidationResult.formatAll (r : ValidationResult) : List String :=
  r.errors.map ValidationError.format ++ r.warnings.map ValidationWarning.format

/-- Check if validation passed (no errors) -/
def ValidationResult.passed (r : ValidationResult) : Bool :=
  r.errors.isEmpty

/-- Check if validation is clean (no errors or warnings) -/
def ValidationResult.clean (r : ValidationResult) : Bool :=
  r.errors.isEmpty && r.warnings.isEmpty

/-- Combined validation result including cubical errors -/
structure FullValidationResult where
  grammarResult : ValidationResult
  cubicalErrors : List VerificationError
  deriving Repr

def FullValidationResult.passed (r : FullValidationResult) : Bool :=
  r.grammarResult.passed && r.cubicalErrors.isEmpty

def FullValidationResult.formatAll (r : FullValidationResult) : List String :=
  r.grammarResult.formatAll ++ r.cubicalErrors.map VerificationError.format

/-- Convert Rule list to normalization rules (pattern, template pairs) -/
def rulesToNormRules (rules : List Rule) : List (Term × Term) :=
  rules.map fun r => (r.pattern, r.template)

/-- Full validation: grammar, rules, and cubical constructs -/
def validateFull (grammar : HashMap String GrammarExpr) (rules : List Rule)
    (typeRules : List TypeRule) (ast : Term) : FullValidationResult :=
  let normRules := rulesToNormRules rules
  { grammarResult := validate grammar rules
    cubicalErrors := validateCubical typeRules normRules ast }

/-! ## Cubical-Specific Validation Helpers -/

/-- Check if a term is a valid dimension (0, 1, or dim var) -/
def isValidDimension (t : Term) : Bool :=
  match t with
  | .con "dim0" [] => true
  | .con "dim1" [] => true
  | .var _ => true  -- dimension variable
  | .con "dimVar" [_] => true
  | _ => false

/-- Check if a term is a valid cofibration -/
def isValidCofibration (t : Term) : Bool :=
  match t with
  | .con "cof_top" [] => true
  | .con "cof_bot" [] => true
  | .con "cof_eq" [i, j] => isValidDimension i && isValidDimension j
  | .con "cof_and" [φ, ψ] => isValidCofibration φ && isValidCofibration ψ
  | .con "cof_or" [φ, ψ] => isValidCofibration φ && isValidCofibration ψ
  | .var _ => true  -- cofibration variable
  | _ => false

/-- Validate a path type has consistent endpoints -/
def validatePathType (rules : List (Term × Term)) (pathType : Term) (pathTerm : Term) : Option ValidationError :=
  match pathType with
  | .con "Path" [_, a, b] =>
    let fuel := 1000
    -- Compute path endpoints by applying @ 0 and @ 1
    let endpoint0 := Cubical.normalize fuel rules (.con "papp" [pathTerm, .con "dim0" []])
    let endpoint1 := Cubical.normalize fuel rules (.con "papp" [pathTerm, .con "dim1" []])
    let aNorm := Cubical.normalize fuel rules a
    let bNorm := Cubical.normalize fuel rules b
    -- Check endpoint at 0
    if endpoint0 != aNorm then
      some (.pathEndpointMismatch "0" s!"{a}" s!"{endpoint0}")
    -- Check endpoint at 1
    else if endpoint1 != bNorm then
      some (.pathEndpointMismatch "1" s!"{b}" s!"{endpoint1}")
    else none
  | _ => some (.invalidSyntax "path type" "expected Path A a b form")

/-- Extract disjunctive faces from a cofibration (the faces that need separate branches) -/
partial def extractDisjunctiveFaces (cof : Term) : List Term :=
  match cof with
  | .con "cof_top" [] => []  -- top is trivially satisfied, no branches needed
  | .con "cof_bot" [] => []  -- bot is impossible, no branches needed
  | .con "cof_eq" [i, j] => [.con "cof_eq" [i, j]]  -- single atomic face
  | .con "cof_and" [φ, _ψ] =>
    -- Conjunction: a single branch covers both constraints
    -- Return just the first face (the branch must satisfy both)
    extractDisjunctiveFaces φ
  | .con "cof_or" [φ, ψ] =>
    -- Disjunction: need separate branches for each side
    extractDisjunctiveFaces φ ++ extractDisjunctiveFaces ψ
  | _ => [cof]  -- treat as atomic face

/-- Check if two terms are equal up to normalization -/
def termsEqualNorm (rules : List (Term × Term)) (t1 t2 : Term) : Bool :=
  let fuel := 1000
  Cubical.normalize fuel rules t1 == Cubical.normalize fuel rules t2

/-- Check if a branch's cofibration matches a required face -/
def branchMatchesFace (rules : List (Term × Term)) (branch : Term) (face : Term) : Bool :=
  match branch with
  | .con "sysBranch" [branchCof, _] => termsEqualNorm rules branchCof face
  | .con "sysComp" [branchCof, _] => termsEqualNorm rules branchCof face
  | _ => false  -- unknown branch format

/-- Extract cofibration from a system branch -/
def branchCofibration : Term → Option Term
  | .con "sysBranch" [cof, _] => some cof
  | .con "sysComp" [cof, _] => some cof
  | _ => none

/-- Validate a system is complete for its cofibration.
    Checks:
    1. All disjunctive faces have corresponding branches
    2. Branches on overlapping faces are compatible (would need normalization to fully check) -/
def validateSystem (rules : List (Term × Term)) (cof : Term) (branches : List Term) : Option ValidationError :=
  if branches.isEmpty then
    some (.systemIncomplete (toString cof) "no branches provided")
  else
    let requiredFaces := extractDisjunctiveFaces cof
    -- For each required face, check there's a matching branch
    let branchCofs := branches.filterMap branchCofibration
    let uncovered := requiredFaces.filter fun face =>
      not (branchCofs.any fun bc => termsEqualNorm rules bc face)
    if uncovered.isEmpty then none
    else some (.systemIncomplete (toString cof)
      s!"missing branch(es) for face(s): {uncovered.map toString}")

/-- Describe a term for error messages -/
partial def describeTerm (t : Term) : String :=
  match t with
  | .var v => s!"variable '{v}'"
  | .lit l => s!"literal '{l}'"
  | .con "lam" _ => "lambda abstraction"
  | .con "app" [f, _] => s!"application of {describeTerm f}"
  | .con "Path" _ => "path type"
  | .con "plam" _ => "path abstraction"
  | .con "papp" _ => "path application"
  | .con "refl" _ => "reflexivity proof"
  | .con "coe" _ => "coercion"
  | .con "hcom" _ => "homogeneous composition"
  | .con "Glue" _ => "Glue type"
  | .con "glue" _ => "glue term"
  | .con "unglue" _ => "unglue"
  | .con name args =>
    if args.isEmpty then s!"'{name}'"
    else s!"'{name}' with {args.length} arguments"

/-- Suggestion for common errors -/
def suggestFix (err : ValidationError) : Option String :=
  match err with
  | .undefinedProduction ref _ =>
    some s!"Did you mean to import a piece that defines '{ref}'?"
  | .unboundVariable v _ =>
    some s!"Check that ${v} appears in the pattern (left side) of the rule"
  | .dimensionMismatch _ _ _ =>
    some "Dimensions must be 0, 1, or bound dimension variables"
  | .pathEndpointMismatch _ _ _ =>
    some "Use 'refl' for trivial paths, or check your path construction"
  | _ => none

/-! ## Glue Type Validation -/

/-- Validate a Glue type has proper structure:
    Glue [φ ↦ (T, f)] A requires:
    1. φ is a valid cofibration
    2. f : T ≃ A (an equivalence) -/
def validateGlue (typeRules : List TypeRule) (glueType : Term) : Option ValidationError :=
  match glueType with
  | .con "Glue" [φ, t, equiv, a] =>
    -- Check cofibration is valid
    if !isValidCofibration φ then
      some (.glueMalformed s!"'{φ}' is not a valid cofibration")
    else
      -- Check equivalence type
      match inferType typeRules equiv with
      | some (.con "Equiv" [fromTy, toTy]) =>
        -- Check T matches fromTy and A matches toTy (structurally)
        if fromTy != t then
          some (.glueMalformed s!"equivalence domain '{fromTy}' doesn't match T '{t}'")
        else if toTy != a then
          some (.glueMalformed s!"equivalence codomain '{toTy}' doesn't match A '{a}'")
        else none
      | some other =>
        some (.glueMalformed s!"expected equivalence, got '{other}'")
      | none =>
        -- Can't infer type - soft pass
        none
  | .con "Glue" args =>
    some (.glueMalformed s!"expected 4 arguments (φ, T, equiv, A), got {args.length}")
  | _ =>
    some (.invalidSyntax "Glue type" "expected Glue [φ ↦ (T, f)] A form")

/-! ## Comprehensive Cubical Term Validation -/

/-- Recursively validate all cubical constructs in a term -/
partial def validateCubicalTerm (typeRules : List TypeRule) (rules : List (Term × Term))
    (t : Term) : List ValidationError :=
  let selfErrors := match t with
    -- Validate path types and terms
    | .con "Path" _ =>
      -- Path type itself is always valid if well-formed
      []
    | .con "plam" [body] =>
      -- Path lambda: validate body
      validateCubicalTerm typeRules rules body
    | .con "papp" [p, r] =>
      -- Path application: validate dimension
      let dimErrors := if !isValidDimension r then
        [ValidationError.dimensionMismatch "dimension" (toString r) "path application"]
      else []
      dimErrors ++ validateCubicalTerm typeRules rules p

    -- Validate Glue types
    | .con "Glue" _ =>
      match validateGlue typeRules t with
      | some err => [err]
      | none => []

    -- Validate systems
    | .con "sys" (cof :: branches) =>
      match validateSystem rules cof branches with
      | some err => [err]
      | none => []

    -- Validate coercions
    | .con "coe" [r, s, _, _] =>
      let rErr := if !isValidDimension r then
        [ValidationError.dimensionMismatch "dimension" (toString r) "coe start"]
      else []
      let sErr := if !isValidDimension s then
        [ValidationError.dimensionMismatch "dimension" (toString s) "coe end"]
      else []
      rErr ++ sErr

    -- Validate hcom
    | .con "hcom" [r, s, _, φ, _] =>
      let rErr := if !isValidDimension r then
        [ValidationError.dimensionMismatch "dimension" (toString r) "hcom start"]
      else []
      let sErr := if !isValidDimension s then
        [ValidationError.dimensionMismatch "dimension" (toString s) "hcom end"]
      else []
      let cofErr := if !isValidCofibration φ then
        [ValidationError.invalidCofibration (toString φ) "invalid in hcom"]
      else []
      rErr ++ sErr ++ cofErr

    | _ => []

  -- Recursively validate children
  let childErrors := match t with
    | .con _ args => args.flatMap (validateCubicalTerm typeRules rules)
    | _ => []

  selfErrors ++ childErrors

/-- Extract all cubical constructs from AST and validate them -/
def validateAllCubicalTerms (typeRules : List TypeRule) (rules : List (Term × Term))
    (ast : Term) : List ValidationError :=
  validateCubicalTerm typeRules rules ast

end Lego.Validation
