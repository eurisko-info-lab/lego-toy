/-
  Lego.Normalize: Normalization engine with cubical operations

  This module provides:
  - De Bruijn index operations (shift, subst)
  - Dimension substitution for cubical types
  - Cofibration evaluation and simplification
  - Kan operations (coe, hcom)
  - NbE (Normalization by Evaluation)
  - Standard reduction rules
  - Memoization for normalized terms (performance optimization)
-/

import Lego.Algebra
import Std.Data.HashMap

namespace Lego

open Std (HashMap)

/-- Configuration for normalization -/
structure NormalizeConfig where
  /-- Maximum reduction steps (fuel) -/
  maxSteps : Nat := 1000
  /-- Whether to enable built-in operations (subst, etc.) -/
  enableBuiltins : Bool := true
  /-- Whether to enable cubical operations -/
  enableCubical : Bool := true
  /-- Whether to enable memoization -/
  enableMemo : Bool := true
  deriving Inhabited

/-- Result of normalization with optional trace -/
structure NormalizeResult where
  /-- The normalized term -/
  term : Term
  /-- Trace of (ruleName, intermediate term) pairs if tracing enabled -/
  trace : List (String × Term) := []
  deriving Inhabited

/-! ## Memoization Cache -/

/-- Global memoization cache for normalized terms.
    Uses term hash for fast lookup. -/
structure NormCache where
  /-- Map from term hash to normalized term -/
  cache : HashMap UInt64 Term := HashMap.emptyWithCapacity
  /-- Cache hits counter -/
  hits : Nat := 0
  /-- Cache misses counter -/
  misses : Nat := 0

instance : Inhabited NormCache where
  default := { cache := HashMap.emptyWithCapacity, hits := 0, misses := 0 }

/-- Hash a term for memoization -/
partial def termHash (t : Term) : UInt64 :=
  match t with
  | .var s => hash s
  | .lit s => hash s + 1
  | .con name args =>
    let nameHash := hash name
    args.foldl (init := nameHash) fun acc arg => acc * 31 + termHash arg

/-- Lookup in cache -/
def NormCache.lookup (cache : NormCache) (t : Term) : Option Term :=
  cache.cache.get? (termHash t)

/-- Insert into cache -/
def NormCache.insert (cache : NormCache) (t : Term) (result : Term) : NormCache :=
  { cache with cache := cache.cache.insert (termHash t) result }

/-! ## Rule Indexing -/

/-- Rule index: maps head constructor to applicable rules -/
abbrev RuleIndex := HashMap String (List (Term × Term))

/-- Get head constructor of a term (for indexing) -/
def getHead (t : Term) : Option String :=
  match t with
  | .con name _ => some name
  | _ => none

/-- Build index from rules for O(1) lookup -/
def buildRuleIndex (rules : List (Term × Term)) : RuleIndex :=
  rules.foldl (init := HashMap.emptyWithCapacity) fun idx (pat, tmpl) =>
    match getHead pat with
    | some head =>
      let existing := idx.getD head []
      idx.insert head ((pat, tmpl) :: existing)
    | none => idx

/-- Lookup rules by head constructor -/
def lookupRules (index : RuleIndex) (t : Term) : List (Term × Term) :=
  match getHead t with
  | some head => index.getD head []
  | none => []

/-! ## Cubical Operations -/

namespace Cubical

/-! ## De Bruijn Index Operations -/

/-- Shift (weaken) a term: increment free variables >= cutoff by amount -/
partial def shift (cutoff : Nat) (amount : Nat) (t : Term) : Term :=
  match t with
  | .con "ix" [.lit n] =>
    let idx := n.toNat!
    if idx >= cutoff then .con "ix" [.lit (toString (idx + amount))]
    else t
  | .con "lam" [body] =>
    .con "lam" [shift (cutoff + 1) amount body]
  | .con "pi" [dom, cod] =>
    .con "pi" [shift cutoff amount dom, shift (cutoff + 1) amount cod]
  | .con "sigma" [fst, snd] =>
    .con "sigma" [shift cutoff amount fst, shift (cutoff + 1) amount snd]
  | .con "letE" [ty, val, body] =>
    .con "letE" [shift cutoff amount ty, shift cutoff amount val, shift (cutoff + 1) amount body]
  | .con "plam" [body] =>
    .con "plam" [shift (cutoff + 1) amount body]
  | .con "path" [ty, a, b] =>
    .con "path" [shift (cutoff + 1) amount ty, shift cutoff amount a, shift cutoff amount b]
  | .con name args =>
    .con name (args.map (shift cutoff amount))
  | _ => t

/-- Substitute: replace variable at index with term, adjusting indices -/
partial def subst (idx : Nat) (replacement : Term) (t : Term) : Term :=
  match t with
  | .con "ix" [.lit n] =>
    let i := n.toNat!
    if i == idx then replacement
    else if i > idx then .con "ix" [.lit (toString (i - 1))]
    else t
  | .con "lam" [body] =>
    .con "lam" [subst (idx + 1) (shift 0 1 replacement) body]
  | .con "pi" [dom, cod] =>
    .con "pi" [subst idx replacement dom, subst (idx + 1) (shift 0 1 replacement) cod]
  | .con "sigma" [fst, snd] =>
    .con "sigma" [subst idx replacement fst, subst (idx + 1) (shift 0 1 replacement) snd]
  | .con "letE" [ty, val, body] =>
    .con "letE" [subst idx replacement ty, subst idx replacement val,
                 subst (idx + 1) (shift 0 1 replacement) body]
  | .con "plam" [body] =>
    .con "plam" [subst (idx + 1) (shift 0 1 replacement) body]
  | .con "path" [ty, a, b] =>
    .con "path" [subst (idx + 1) (shift 0 1 replacement) ty,
                 subst idx replacement a, subst idx replacement b]
  | .con name args =>
    .con name (args.map (subst idx replacement))
  | _ => t

/-! ## Dimension Operations -/

/-- Substitute dimension in a term (for path application) -/
partial def substDim (idx : Nat) (dim : Term) (t : Term) : Term :=
  match t with
  | .con "dimVar" [.lit n] =>
    let i := n.toNat!
    if i == idx then dim else t
  | .con "plam" [body] =>
    .con "plam" [substDim (idx + 1) dim body]
  | .con "path" [ty, a, b] =>
    .con "path" [substDim (idx + 1) dim ty, substDim idx dim a, substDim idx dim b]
  | .con name args =>
    .con name (args.map (substDim idx dim))
  | _ => t

/-- Check if term contains a dimension variable at given index -/
partial def containsDimVar (idx : Nat) (t : Term) : Bool :=
  match t with
  | .con "dimVar" [.lit n] => n.toNat! == idx
  | .con _ args => args.any (containsDimVar idx)
  | _ => false

/-! ## Cofibration Operations -/

/-- Check if a cofibration is satisfied (evaluates to true) -/
def evalCof (φ : Term) : Bool :=
  match φ with
  | .con "cof_top" [] => true
  | .con "cof_bot" [] => false
  | .con "cof_eq" [r, s] => r == s
  | .con "cof_and" [φ₁, φ₂] => evalCof φ₁ && evalCof φ₂
  | .con "cof_or" [φ₁, φ₂] => evalCof φ₁ || evalCof φ₂
  | .con "cof_neg" [φ'] => !evalCof φ'
  | _ => false

/-- Simplify dimension expression -/
partial def simplifyDim (d : Term) : Term :=
  match d with
  -- Double negation
  | .con "dimNeg" [.con "dimNeg" [r]] => simplifyDim r
  -- Negation of constants
  | .con "dimNeg" [.con "dim0" []] => .con "dim1" []
  | .con "dimNeg" [.con "dim1" []] => .con "dim0" []
  -- Max simplifications
  | .con "dimMax" [.con "dim0" [], r] => simplifyDim r
  | .con "dimMax" [r, .con "dim0" []] => simplifyDim r
  | .con "dimMax" [.con "dim1" [], _] => .con "dim1" []
  | .con "dimMax" [_, .con "dim1" []] => .con "dim1" []
  | .con "dimMax" [r, s] =>
    let r' := simplifyDim r
    let s' := simplifyDim s
    if r' == s' then r'
    else if r' == .con "dim0" [] then s'
    else if s' == .con "dim0" [] then r'
    else if r' == .con "dim1" [] || s' == .con "dim1" [] then .con "dim1" []
    -- Max with negation: max(i, 1-i) = 1
    else match r', s' with
      | r'', .con "dimNeg" [r'''] => if r'' == r''' then .con "dim1" [] else .con "dimMax" [r', s']
      | .con "dimNeg" [r'''], r'' => if r'' == r''' then .con "dim1" [] else .con "dimMax" [r', s']
      | _, _ => .con "dimMax" [r', s']
  -- Min simplifications
  | .con "dimMin" [.con "dim0" [], _] => .con "dim0" []
  | .con "dimMin" [_, .con "dim0" []] => .con "dim0" []
  | .con "dimMin" [.con "dim1" [], r] => simplifyDim r
  | .con "dimMin" [r, .con "dim1" []] => simplifyDim r
  | .con "dimMin" [r, s] =>
    let r' := simplifyDim r
    let s' := simplifyDim s
    if r' == s' then r'
    else if r' == .con "dim1" [] then s'
    else if s' == .con "dim1" [] then r'
    else if r' == .con "dim0" [] || s' == .con "dim0" [] then .con "dim0" []
    -- Min with negation: min(i, 1-i) = 0
    else match r', s' with
      | r'', .con "dimNeg" [r'''] => if r'' == r''' then .con "dim0" [] else .con "dimMin" [r', s']
      | .con "dimNeg" [r'''], r'' => if r'' == r''' then .con "dim0" [] else .con "dimMin" [r', s']
      | _, _ => .con "dimMin" [r', s']
  -- De Morgan for dimension negation through max/min
  | .con "dimNeg" [.con "dimMax" [r, s]] =>
    simplifyDim (.con "dimMin" [.con "dimNeg" [r], .con "dimNeg" [s]])
  | .con "dimNeg" [.con "dimMin" [r, s]] =>
    simplifyDim (.con "dimMax" [.con "dimNeg" [r], .con "dimNeg" [s]])
  | _ => d

/-- Simplify cofibration algebraically with full De Morgan and idempotence -/
partial def simplifyCof (φ : Term) : Term :=
  match φ with
  | .con "cof_eq" [r, s] =>
    let r' := simplifyDim r
    let s' := simplifyDim s
    if r' == s' then .con "cof_top" []
    else match r', s' with
      | .con "dim0" [], .con "dim1" [] => .con "cof_bot" []
      | .con "dim1" [], .con "dim0" [] => .con "cof_bot" []
      | _, _ => .con "cof_eq" [r', s']
  -- And with top/bot
  | .con "cof_and" [.con "cof_top" [], ψ] => simplifyCof ψ
  | .con "cof_and" [ψ, .con "cof_top" []] => simplifyCof ψ
  | .con "cof_and" [.con "cof_bot" [], _] => .con "cof_bot" []
  | .con "cof_and" [_, .con "cof_bot" []] => .con "cof_bot" []
  -- Or with top/bot
  | .con "cof_or" [.con "cof_top" [], _] => .con "cof_top" []
  | .con "cof_or" [_, .con "cof_top" []] => .con "cof_top" []
  | .con "cof_or" [.con "cof_bot" [], ψ] => simplifyCof ψ
  | .con "cof_or" [ψ, .con "cof_bot" []] => simplifyCof ψ
  -- Idempotence
  | .con "cof_and" [φ₁, φ₂] =>
    let φ₁' := simplifyCof φ₁
    let φ₂' := simplifyCof φ₂
    if φ₁' == φ₂' then φ₁'
    -- Complement: φ ∧ ¬φ = ⊥
    else match φ₂' with
      | .con "cof_neg" [φ₂''] => if φ₁' == φ₂'' then .con "cof_bot" [] else .con "cof_and" [φ₁', φ₂']
      | _ => match φ₁' with
        | .con "cof_neg" [φ₁''] => if φ₁'' == φ₂' then .con "cof_bot" [] else .con "cof_and" [φ₁', φ₂']
        | _ => .con "cof_and" [φ₁', φ₂']
  | .con "cof_or" [φ₁, φ₂] =>
    let φ₁' := simplifyCof φ₁
    let φ₂' := simplifyCof φ₂
    if φ₁' == φ₂' then φ₁'
    -- Complement: φ ∨ ¬φ = ⊤
    else match φ₂' with
      | .con "cof_neg" [φ₂''] => if φ₁' == φ₂'' then .con "cof_top" [] else .con "cof_or" [φ₁', φ₂']
      | _ => match φ₁' with
        | .con "cof_neg" [φ₁''] => if φ₁'' == φ₂' then .con "cof_top" [] else .con "cof_or" [φ₁', φ₂']
        | _ => .con "cof_or" [φ₁', φ₂']
  -- Double negation
  | .con "cof_neg" [.con "cof_neg" [ψ]] => simplifyCof ψ
  | .con "cof_neg" [.con "cof_top" []] => .con "cof_bot" []
  | .con "cof_neg" [.con "cof_bot" []] => .con "cof_top" []
  -- De Morgan laws
  | .con "cof_neg" [.con "cof_and" [φ₁, φ₂]] =>
    simplifyCof (.con "cof_or" [.con "cof_neg" [φ₁], .con "cof_neg" [φ₂]])
  | .con "cof_neg" [.con "cof_or" [φ₁, φ₂]] =>
    simplifyCof (.con "cof_and" [.con "cof_neg" [φ₁], .con "cof_neg" [φ₂]])
  | _ => φ

/-! ## Level Operations -/

/-- Simplify level expressions -/
partial def simplifyLevel (l : Term) : Term :=
  match l with
  | .con "lmax" [l₁, l₂] =>
    let l₁' := simplifyLevel l₁
    let l₂' := simplifyLevel l₂
    if l₁' == l₂' then l₁'
    else match l₁', l₂' with
      | .con "lzero" [], _ => l₂'
      | _, .con "lzero" [] => l₁'
      | .con "lsuc" [a], .con "lsuc" [b] =>
        .con "lsuc" [simplifyLevel (.con "lmax" [a, b])]
      | _, _ => .con "lmax" [l₁', l₂']
  | _ => l

/-! ## Kan Operations -/

/-- Coercion along a line of types -/
def coe (r s : Term) (ty : Term) (tm : Term) : Term :=
  if r == s then tm
  else .con "coe" [r, s, ty, tm]

/-- Homogeneous composition -/
def hcom (r s : Term) (ty : Term) (φ : Term) (cap : Term) : Term :=
  if r == s then cap
  else if evalCof φ then cap  -- φ is satisfied, use boundary
  else .con "hcom" [r, s, ty, φ, cap]

/-- V-in: introduction for V-types (Glue types for univalence) -/
def vin (r : Term) (a b : Term) : Term :=
  match r with
  | .con "dim0" [] => a
  | .con "dim1" [] => b
  | _ => .con "vin" [r, a, b]

/-! ## Proof Combinators -/

/-- Symmetry of paths: sym p = λi. p(1-i) -/
def pathSym (p : Term) : Term :=
  match p with
  | .con "refl" [a] => .con "refl" [a]  -- sym (refl a) = refl a
  | .con "plam" [body] =>
    -- sym (plam body) = plam (substDim 0 (1-i) body)
    -- We represent 1-i as dimNeg
    .con "plam" [.con "substDimNeg" [body]]
  | _ => .con "sym" [p]

/-- Transitivity of paths: trans p q -/
def pathTrans (p q : Term) : Term :=
  match p, q with
  | .con "refl" [_], _ => q  -- trans (refl a) q = q
  | _, .con "refl" [_] => p  -- trans p (refl b) = p
  | _, _ => .con "trans" [p, q]

/-- Congruence: cong f p where f : A → B, p : Path A a a' -/
def pathCong (f p : Term) : Term :=
  match p with
  | .con "refl" [a] => .con "refl" [.con "app" [f, a]]  -- cong f (refl a) = refl (f a)
  | _ => .con "cong" [f, p]

/-- Function extensionality: funExt h where h : (x : A) → Path B (f x) (g x) -/
def funExt (h : Term) : Term :=
  .con "funExt" [h]

/-- Apply funExt at a point: happly p x -/
def happly (p x : Term) : Term :=
  match p with
  | .con "funExt" [h] => .con "app" [h, x]  -- happly (funExt h) x = h x
  | .con "refl" [f] => .con "refl" [.con "app" [f, x]]  -- happly (refl f) x = refl (f x)
  | _ => .con "happly" [p, x]

/-! ## Equivalences -/

/-- Identity equivalence -/
def idEquiv (a : Term) : Term :=
  .con "idEquiv" [a]

/-- Extract forward function from equivalence -/
def equivFun (e : Term) : Term :=
  match e with
  | .con "idEquiv" [_] => .con "lam" [.con "ix" [.lit "0"]]  -- id function
  | _ => .con "equivFun" [e]

/-- Univalence: ua e gives path from equiv e -/
def ua (e : Term) : Term :=
  match e with
  | .con "idEquiv" [a] => .con "refl" [a]  -- ua (idEquiv A) = refl A
  | _ => .con "ua" [e]

/-- Compose equivalences -/
def compEquiv (e1 e2 : Term) : Term :=
  match e1, e2 with
  | .con "idEquiv" [_], _ => e2
  | _, .con "idEquiv" [_] => e1
  | _, _ => .con "compEquiv" [e1, e2]

/-- Inverse equivalence -/
def invEquiv (e : Term) : Term :=
  match e with
  | .con "idEquiv" [a] => .con "idEquiv" [a]
  | _ => .con "invEquiv" [e]

/-! ## Sigma Types (Dependent Pairs) -/

/-- First projection of dependent pair -/
def dfst (p : Term) : Term :=
  match p with
  | .con "dpair" [a, _] => a
  | _ => .con "dfst" [p]

/-- Second projection of dependent pair -/
def dsnd (p : Term) : Term :=
  match p with
  | .con "dpair" [_, b] => b
  | _ => .con "dsnd" [p]

/-! ## Contractibility -/

/-- Extract center from contractibility proof -/
def center (c : Term) : Term :=
  match c with
  | .con "mkContr" [cen, _] => cen
  | _ => .con "center" [c]

/-- Extract paths from contractibility proof -/
def contrPaths (c : Term) : Term :=
  match c with
  | .con "mkContr" [_, paths] => paths
  | _ => .con "paths" [c]

/-! ## Propositional Truncation -/

/-- Eliminate from propositional truncation -/
def propElim (p isPropB f a : Term) : Term :=
  match a with
  | .con "squash" [x] => .con "app" [f, x]
  | _ => .con "propElim" [p, isPropB, f, a]

/-! ## Transport -/

/-- J eliminator (path induction) -/
def pathJ (a p d b path : Term) : Term :=
  match path with
  | .con "refl" [_] => d  -- J A a P d a (refl a) = d
  | _ => .con "J" [a, p, d, b, path]

/-- Transport along a path -/
def transp (ty phi a : Term) : Term :=
  match phi with
  | .con "cof_top" [] => a  -- transp A ⊤ a = a
  | _ => .con "transp" [ty, phi, a]

/-! ## NbE: Normalization by Evaluation -/

/-- Domain environment lookup -/
def denvLookup (idx : Nat) (env : Term) : Term :=
  match env with
  | .con "denvCons" [v, rest] =>
    if idx == 0 then v else denvLookup (idx - 1) rest
  | _ => .con "error" [.lit s!"index {idx} not found"]

/-- NbE: Evaluate term to domain value -/
partial def nbeEval (env : Term) (t : Term) : Term :=
  match t with
  | .con "ix" [.lit n] =>
    denvLookup n.toNat! env
  | .con "lam" [body] =>
    .con "dlam" [.con "dclo" [body, env]]
  | .con "app" [f, a] =>
    let vf := nbeEval env f
    let va := nbeEval env a
    match vf with
    | .con "dlam" [.con "dclo" [body, cloEnv]] =>
      nbeEval (.con "denvCons" [va, cloEnv]) body
    | _ => .con "dneu" [.con "dapp" [vf, va]]
  | .con "pair" [a, b] =>
    .con "dpair" [nbeEval env a, nbeEval env b]
  | .con "fst" [p] =>
    match nbeEval env p with
    | .con "dpair" [a, _] => a
    | other => .con "dneu" [.con "dfst" [other]]
  | .con "snd" [p] =>
    match nbeEval env p with
    | .con "dpair" [_, b] => b
    | other => .con "dneu" [.con "dsnd" [other]]
  | .lit s => .con "dlit" [.lit s]
  | _ => t

mutual
/-- NbE: Quote neutral term -/
partial def nbeQuoteNeu (level : Nat) (neu : Term) : Term :=
  match neu with
  | .con "dvar" [.lit l] =>
    .con "ix" [.lit (toString (level - l.toNat! - 1))]
  | .con "dapp" [f, a] =>
    .con "app" [nbeQuoteNeu level f, nbeQuote level a]
  | .con "dfst" [p] =>
    .con "fst" [nbeQuoteNeu level p]
  | .con "dsnd" [p] =>
    .con "snd" [nbeQuoteNeu level p]
  | _ => .con "error" [.lit "unknown neutral"]

/-- NbE: Quote domain value to syntax -/
partial def nbeQuote (level : Nat) (v : Term) : Term :=
  match v with
  | .con "dlit" [.lit s] => .lit s
  | .con "dlam" [.con "dclo" [body, cloEnv]] =>
    let generic := .con "dneu" [.con "dvar" [.lit (toString level)]]
    let bodyVal := nbeEval (.con "denvCons" [generic, cloEnv]) body
    .con "lam" [nbeQuote (level + 1) bodyVal]
  | .con "dpair" [a, b] =>
    .con "pair" [nbeQuote level a, nbeQuote level b]
  | .con "dneu" [neu] => nbeQuoteNeu level neu
  | _ => v
end

/-- NbE: Full normalization -/
def nbeNormalize (t : Term) : Term :=
  nbeQuote 0 (nbeEval (.con "denvNil" []) t)

/-! ## Single-Step Reduction -/

/-- Fast check: is term already a value (no redexes)? -/
def isValue (t : Term) : Bool :=
  match t with
  | .var _ => true
  | .lit _ => true
  | .con "lam" _ => true        -- λ is a value
  | .con "plam" _ => true       -- path λ is a value
  | .con "pair" _ => true       -- pairs are values
  | .con "refl" _ => true       -- refl is a value
  | .con "idEquiv" _ => true    -- idEquiv is a value
  | .con "dim0" [] => true      -- dimension endpoints are values
  | .con "dim1" [] => true
  | .con "cof_top" [] => true   -- cofibration constants
  | .con "cof_bot" [] => true
  | .con "base" [] => true      -- HIT points
  | .con "north" [] => true
  | .con "south" [] => true
  | .con "zero" [] => true      -- natural numbers
  | .con "suc" _ => true
  | _ => false

/-- One step of reduction (built-in rules) -/
partial def step (rules : List (Term × Term)) (t : Term) : Option Term :=
  -- Fast path: values don't reduce
  if isValue t then none
  else
  -- Try β-reduction first
  match t with
  -- Lambda calculus
  | .con "app" [.con "lam" [body], arg] =>
    some (subst 0 arg body)
  | .con "fst" [.con "pair" [a, _]] =>
    some a
  | .con "snd" [.con "pair" [_, b]] =>
    some b
  | .con "letE" [_, val, body] =>
    some (subst 0 val body)

  -- Path types
  | .con "papp" [.con "plam" [body], r] =>
    some (substDim 0 r body)
  | .con "papp" [.con "refl" [a], _] =>
    some a

  -- Path combinators
  | .con "sym" [.con "refl" [a]] =>
    some (.con "refl" [a])  -- sym (refl a) = refl a
  | .con "trans" [.con "refl" [_], q] =>
    some q  -- trans (refl a) q = q
  | .con "trans" [p, .con "refl" [_]] =>
    some p  -- trans p (refl b) = p
  | .con "cong" [_, .con "refl" [a]] =>
    some (.con "refl" [.con "app" [.con "ix" [.lit "0"], a]])  -- cong f (refl a) = refl (f a)

  -- Function extensionality
  | .con "happly" [.con "funExt" [h], x] =>
    some (.con "app" [h, x])  -- happly (funExt h) x = h x
  | .con "happly" [.con "refl" [f], x] =>
    some (.con "refl" [.con "app" [f, x]])  -- happly (refl f) x = refl (f x)
  | .con "papp" [.con "funExt" [.con "plam" [body]], i] =>
    some (.con "plam" [.con "papp" [body, i]])  -- funExt applies pointwise

  -- Equivalences
  | .con "equivFun" [.con "idEquiv" [_]] =>
    some (.con "lam" [.con "ix" [.lit "0"]])  -- equivFun (idEquiv A) = λx.x
  | .con "ua" [.con "idEquiv" [a]] =>
    some (.con "refl" [a])  -- ua (idEquiv A) = refl A
  | .con "compEquiv" [.con "idEquiv" [_], e] =>
    some e  -- compEquiv (idEquiv A) e = e
  | .con "compEquiv" [e, .con "idEquiv" [_]] =>
    some e  -- compEquiv e (idEquiv B) = e
  | .con "invEquiv" [.con "idEquiv" [a]] =>
    some (.con "idEquiv" [a])  -- invEquiv (idEquiv A) = idEquiv A

  -- Sigma types (dependent pairs)
  | .con "dfst" [.con "dpair" [a, _]] =>
    some a
  | .con "dsnd" [.con "dpair" [_, b]] =>
    some b

  -- Contractibility
  | .con "center" [.con "mkContr" [c, _]] =>
    some c
  | .con "paths" [.con "mkContr" [_, p]] =>
    some p

  -- Propositional truncation
  | .con "propElim" [_, _, f, .con "squash" [x]] =>
    some (.con "app" [f, x])

  -- Transport
  | .con "transp" [_, .con "cof_top" [], a] =>
    some a  -- transp A ⊤ a = a

  -- J eliminator (path induction)
  | .con "J" [_, _, _, d, _, .con "refl" [_]] =>
    some d  -- J A a P d a (refl a) = d

  -- Proof tactics
  | .con "have" [_, _, proof, body] =>
    some (subst 0 proof body)
  | .con "let_" [_, _, val, body] =>
    some (subst 0 val body)
  | .con "exact" [e] =>
    some e

  -- Pi types
  | .con "piPath" [.con "plam" [h]] =>
    some (.con "plam" [.con "lam" [.con "papp" [h, .con "ix" [.lit "0"]]]])
  | .con "happly" [.con "piPath" [h], x] =>
    some (.con "app" [h, x])

  -- Univalence computation (uaβ) - MUST come before general coe
  | .con "coe" [.con "dim0" [], .con "dim1" [], .con "plam" [.con "papp" [.con "ua" [e], _]], a] =>
    some (.con "app" [.con "equivFun" [e], a])  -- coe 0 1 (λi. ua e @ i) a = equivFun e a

  -- Kan operations
  | .con "coe" [r, s, ty, tm] =>
    if r == s then some tm
    else
      -- Coercion along constant type line is identity
      match ty with
      | .con "plam" [tyBody] =>
        if !containsDimVar 0 tyBody then some tm else none
      | _ => none
  | .con "hcom" [r, s, _, φ, cap] =>
    if r == s then some cap
    else if φ == .con "cof_bot" [] then some cap
    else none

  -- V-types (Glue types)
  | .con "vin" [.con "dim0" [], a, _] => some a
  | .con "vin" [.con "dim1" [], _, b] => some b

  -- Cofibrations
  | .con "cof_eq" [_, _] =>
    let simplified := simplifyCof t
    if simplified != t then some simplified else none
  | .con "cof_and" _ =>
    let simplified := simplifyCof t
    if simplified != t then some simplified else none
  | .con "cof_or" _ =>
    let simplified := simplifyCof t
    if simplified != t then some simplified else none

  -- Levels
  | .con "lmax" _ =>
    let simplified := simplifyLevel t
    if simplified != t then some simplified else none

  -- Circle (HIT)
  | .con "loop" [.con "dim0" []] => some (.con "base" [])
  | .con "loop" [.con "dim1" []] => some (.con "base" [])
  | .con "circleElim" [_, b, _, .con "base" []] => some b

  -- Natural numbers
  | .con "natElim" [_, z, _, .con "zero" []] => some z
  | .con "natElim" [p, z, s, .con "suc" [n]] =>
    some (.con "app" [.con "app" [s, n], .con "natElim" [p, z, s, n]])

  -- Subtypes
  | .con "subOut" [.con "subIn" [e]] => some e

  -- Domain operations (for NbE)
  | .con "dimEqD" [.con "ddim0" [], .con "ddim0" []] => some (.con "true" [])
  | .con "dimEqD" [.con "ddim1" [], .con "ddim1" []] => some (.con "true" [])
  | .con "dimEqD" [.con "ddim0" [], .con "ddim1" []] => some (.con "false" [])
  | .con "dimEqD" [.con "ddim1" [], .con "ddim0" []] => some (.con "false" [])
  | .con "dCofIsTrue" [.con "dcof_top" []] => some (.con "true" [])
  | .con "dCofIsTrue" [.con "dcof_bot" []] => some (.con "false" [])
  | .con "denvLookup" [.lit n, .con "denvCons" [v, rest]] =>
    let idx := n.toNat!
    if idx == 0 then some (.con "some" [v])
    else some (.con "denvLookup" [.lit (toString (idx - 1)), rest])
  | .con "denvLookup" [_, .con "denvNil" []] => some (.con "none" [])
  | .con "dApply" [.con "dlam" [.con "dclo" [body, cloEnv]], arg] =>
    some (.con "deval" [.con "denvCons" [arg, cloEnv], body])
  | .con "dFst" [.con "dpair" [a, _]] => some a
  | .con "dSnd" [.con "dpair" [_, b]] => some b

  -- NbE
  | .con "nbe" [inner] => some (nbeNormalize inner)

  -- Dimension checks
  | .con "isDim0" [.con "dim0" []] => some (.con "true" [])
  | .con "isDim0" [_] => some (.con "false" [])
  | .con "isDim1" [.con "dim1" []] => some (.con "true" [])
  | .con "isDim1" [_] => some (.con "false" [])
  | .con "dimEq" [r, s] => some (if r == s then .con "true" [] else .con "false" [])

  -- Cofibration truth
  | .con "cofTrue" [.con "cof_top" []] => some (.con "true" [])
  | .con "cofTrue" [.con "cof_bot" []] => some (.con "false" [])
  | .con "cofTrue" [.con "cof_eq" [r, s]] =>
    some (if r == s then .con "true" [] else .con "false" [])

  -- Boolean operations
  | .con "and" [.con "true" [], .con "true" []] => some (.con "true" [])
  | .con "and" [.con "false" [], _] => some (.con "false" [])
  | .con "and" [_, .con "false" []] => some (.con "false" [])
  | .con "or" [.con "true" [], _] => some (.con "true" [])
  | .con "or" [_, .con "true" []] => some (.con "true" [])
  | .con "or" [.con "false" [], .con "false" []] => some (.con "false" [])

  -- Direction degenerate check
  | .con "dirIsDegenerate" [.con "dir" [d1, d2]] =>
    some (if d1 == d2 then .con "true" [] else .con "false" [])

  -- Language Designer Cubical Constructs

  -- Verified Transformations
  | .con "transport_prop" [.con "idEquiv" [_], p, a] =>
    some (.con "app" [p, a])  -- transport_prop (idEquiv A) P a = P a
  | .con "optimize" [_, .con "refl" [e]] =>
    some e  -- optimize rule (refl e) = e

  -- Quotient Types
  | .con "quotElim" [_, f, _, .con "quot" [a]] =>
    some (.con "app" [f, a])  -- quotElim B f resp (quot a) = f a

  -- Representation Independence
  | .con "coerce_repr" [e, a] =>
    some (.con "app" [.con "equivFun" [e], a])  -- coerce_repr e a = equivFun e a
  | .con "lift_prop" [.con "idEquiv" [_], p, x] =>
    some (.con "app" [p, x])  -- lift_prop (idEquiv A) P x = P x
  | .con "project" [_, .con "embed" [_, t]] =>
    some t  -- project e (embed e' t) = t (simplified: assumes e == e')

  -- Observational Equality
  | .con "by_obs" [.con "obs_refl" [a]] =>
    some (.con "refl" [a])  -- by_obs (obs_refl a) = refl a
  | .con "by_obs" [.con "obs_sym" [p]] =>
    some (.con "sym" [.con "by_obs" [p]])  -- by_obs (obs_sym p) = sym (by_obs p)
  | .con "by_obs" [.con "obs_trans" [p, q]] =>
    some (.con "trans" [.con "by_obs" [p], .con "by_obs" [q]])

  -- Refinement Types
  | .con "unrefine" [.con "refine" [a, _]] =>
    some a  -- unrefine (refine a p) = a
  | .con "refine_proof" [.con "refine" [_, p]] =>
    some p  -- refine_proof (refine a p) = p

  -- Inductive Families
  | .con "ind_path" [_, .con "refl" [_], x] =>
    some (.con "refl" [x])  -- ind_path F (refl i) x = refl x

  -- Language Composition
  | .con "lift_rule" [e, .con "refl" [t]] =>
    some (.con "refl" [.con "embed" [e, t]])  -- lift_rule e (refl t) = refl (embed e t)

  | _ =>
    -- Try user rules
    rules.findSome? fun (lhs, rhs) =>
      match Term.matchPattern lhs t with
      | some bindings => some (Term.substitute rhs bindings)
      | none => none

/-- Normalize term recursively -/
partial def normalizeInner (rules : List (Term × Term)) (t : Term) : Term :=
  -- First normalize subterms
  let t' := match t with
    | .con name args => .con name (args.map (normalizeInner rules))
    | _ => t
  -- Then try reduction
  match step rules t' with
  | some reduced => normalizeInner rules reduced
  | none => t'

/-- Normalize with fuel limit -/
partial def normalize (fuel : Nat) (rules : List (Term × Term)) (t : Term) : Term :=
  if fuel == 0 then t
  else
    match step rules t with
    | some t' => normalize (fuel - 1) rules t'
    | none =>
      -- Try normalizing subterms
      match t with
      | .con name args =>
        let args' := args.map (normalize fuel rules)
        if args' == args then t else .con name args'
      | _ => t

/-- Normalize with memoization for better performance on repeated subterms.
    This is especially important for cubical type theory where the same
    cofibration or dimension expression may appear many times. -/
partial def normalizeMemo (fuel : Nat) (rules : List (Term × Term))
    (cache : NormCache) (t : Term) : Term × NormCache :=
  if fuel == 0 then (t, cache)
  else
    -- Check cache first
    match cache.lookup t with
    | some result => (result, { cache with hits := cache.hits + 1 })
    | none =>
      let cache' := { cache with misses := cache.misses + 1 }
      -- Try one step
      match step rules t with
      | some t' =>
        let (result, cache'') := normalizeMemo (fuel - 1) rules cache' t'
        (result, cache''.insert t result)
      | none =>
        -- Try normalizing subterms
        match t with
        | .con name args =>
          let (args', cache'') := args.foldl (init := ([], cache')) fun (acc, c) arg =>
            let (arg', c') := normalizeMemo fuel rules c arg
            (acc ++ [arg'], c')
          let result := if args' == args then t else .con name args'
          (result, cache''.insert t result)
        | _ => (t, cache'.insert t t)

/-- Normalize with memoization (simplified interface) -/
def normalizeWithCache (fuel : Nat) (rules : List (Term × Term)) (t : Term) : Term :=
  (normalizeMemo fuel rules {} t).1

/-! ## Conversion Checking -/

/-- Check if two terms are convertible (definitionally equal) -/
partial def conv (rules : List (Term × Term)) (fuel : Nat) (t1 t2 : Term) : Bool :=
  let n1 := normalize fuel rules t1
  let n2 := normalize fuel rules t2
  n1 == n2

/-! ## Arithmetic Builtins -/

def add (a b : Nat) : Nat := a + b
def cubicalSub (a b : Nat) : Nat := a - b
def gt (a b : Nat) : Bool := a > b
def geq (a b : Nat) : Bool := a >= b
def eq (a b : Nat) : Bool := a == b
def neq (a b : Nat) : Bool := a != b

end Cubical

end Lego
