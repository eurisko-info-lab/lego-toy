{-|
Module      : Cubical.Runtime
Description : Cubical Runtime Library for Haskell
Copyright   : (c) 2024
License     : MIT

This module provides the runtime infrastructure for Cubical type theory
generated from .lego specifications via the cubical2rosetta → rosetta2hs pipeline.

It includes:
- Core Term type (shared with Lego.Runtime)
- Cubical-specific types (Dim, Cof, Level)
- De Bruijn index operations (shift, subst)
- Normalization engine
- Cubical operations (coe, hcom, com)

Generated code should: import Cubical.Runtime
-}

{-# LANGUAGE LambdaCase #-}

module Cubical.Runtime
  ( -- * Core Types
    Term(..)
    -- * Cubical Types
  , Dim(..)
  , Cof(..)
  , Level(..)
  , Tube(..)
    -- * De Bruijn Operations
  , shift
  , subst
  , substDim
    -- * Cofibration Operations
  , evalCof
  , simplifyCof
    -- * Level Operations
  , simplifyLevel
    -- * Kan Operations
  , coe
  , hcom
  , vin
    -- * Normalization
  , matchPattern
  , substitute
  , step
  , normalize
  , conv
    -- * Arithmetic
  , add, sub, gt, geq
  ) where

import qualified Data.Map.Strict as Map
import Data.List (find)

--------------------------------------------------------------------------------
-- Core Types
--------------------------------------------------------------------------------

-- | The universal Term type for AST representation
data Term
  = Var String
  | Lit String
  | Con String [Term]
  deriving (Eq, Show)

-- | Smart constructor for de Bruijn index
ix :: Int -> Term
ix n = Con "ix" [Lit (show n)]

--------------------------------------------------------------------------------
-- Cubical-Specific Types
--------------------------------------------------------------------------------

-- | Dimension values (interval endpoints and variables)
data Dim
  = I0                    -- ^ 0 endpoint
  | I1                    -- ^ 1 endpoint
  | IVar Int              -- ^ dimension variable
  deriving (Eq, Show)

-- | Cofibrations (face formulas)
data Cof
  = CTop                  -- ^ ⊤ (always true)
  | CBot                  -- ^ ⊥ (always false)
  | CEq Dim Dim           -- ^ r = s
  | CConj Cof Cof         -- ^ φ ∧ ψ
  | CDisj Cof Cof         -- ^ φ ∨ ψ
  deriving (Eq, Show)

-- | Universe levels
data Level
  = LZero
  | LSuc Level
  | LMax Level Level
  | LVar Int
  deriving (Eq, Show)

-- | Tube element: (cofibration, partial element)
data Tube = Tube
  { tubeCof :: Term
  , tubeElement :: Term
  } deriving (Eq, Show)

--------------------------------------------------------------------------------
-- De Bruijn Index Operations
--------------------------------------------------------------------------------

-- | Shift (weaken) a term: increment free variables >= cutoff by amount
shift :: Int -> Int -> Term -> Term
shift cutoff amount t = case t of
  Con "ix" [Lit n] ->
    let idx = read n :: Int
    in if idx >= cutoff
       then Con "ix" [Lit (show (idx + amount))]
       else t
  Con "lam" [body] ->
    Con "lam" [shift (cutoff + 1) amount body]
  Con "pi" [dom, cod] ->
    Con "pi" [shift cutoff amount dom, shift (cutoff + 1) amount cod]
  Con "sigma" [fst', snd'] ->
    Con "sigma" [shift cutoff amount fst', shift (cutoff + 1) amount snd']
  Con "letE" [ty, val, body] ->
    Con "letE" [shift cutoff amount ty, shift cutoff amount val, shift (cutoff + 1) amount body]
  Con "plam" [body] ->
    Con "plam" [shift (cutoff + 1) amount body]
  Con name args ->
    Con name (map (shift cutoff amount) args)
  _ -> t

-- | Substitute: replace variable at index with term, adjusting indices
subst :: Int -> Term -> Term -> Term
subst idx replacement t = case t of
  Con "ix" [Lit n] ->
    let i = read n :: Int
    in if i == idx then replacement
       else if i > idx then Con "ix" [Lit (show (i - 1))]
       else t
  Con "lam" [body] ->
    Con "lam" [subst (idx + 1) (shift 0 1 replacement) body]
  Con "pi" [dom, cod] ->
    Con "pi" [subst idx replacement dom, subst (idx + 1) (shift 0 1 replacement) cod]
  Con "sigma" [fst', snd'] ->
    Con "sigma" [subst idx replacement fst', subst (idx + 1) (shift 0 1 replacement) snd']
  Con "letE" [ty, val, body] ->
    Con "letE" [subst idx replacement ty, subst idx replacement val,
                subst (idx + 1) (shift 0 1 replacement) body]
  Con "plam" [body] ->
    Con "plam" [subst (idx + 1) (shift 0 1 replacement) body]
  Con name args ->
    Con name (map (subst idx replacement) args)
  _ -> t

-- | Substitute dimension in a term
substDim :: Int -> Term -> Term -> Term
substDim idx dim t = case t of
  Con "dimVar" [Lit n] ->
    let i = read n :: Int
    in if i == idx then dim else t
  Con "plam" [body] ->
    Con "plam" [substDim (idx + 1) dim body]
  Con name args ->
    Con name (map (substDim idx dim) args)
  _ -> t

--------------------------------------------------------------------------------
-- Cofibration Evaluation
--------------------------------------------------------------------------------

-- | Check if a cofibration is satisfied (true)
evalCof :: Term -> Bool
evalCof = \case
  Con "cof_top" [] -> True
  Con "cof_bot" [] -> False
  Con "cof_eq" [r, s] -> r == s
  Con "cof_and" [phi1, phi2] -> evalCof phi1 && evalCof phi2
  Con "cof_or" [phi1, phi2] -> evalCof phi1 || evalCof phi2
  _ -> False

-- | Simplify cofibration
simplifyCof :: Term -> Term
simplifyCof phi = case phi of
  Con "cof_eq" [r, s]
    | r == s -> Con "cof_top" []
    | otherwise -> case (r, s) of
        (Con "dim0" [], Con "dim1" []) -> Con "cof_bot" []
        (Con "dim1" [], Con "dim0" []) -> Con "cof_bot" []
        _ -> phi
  Con "cof_and" [Con "cof_top" [], psi] -> simplifyCof psi
  Con "cof_and" [psi, Con "cof_top" []] -> simplifyCof psi
  Con "cof_and" [Con "cof_bot" [], _] -> Con "cof_bot" []
  Con "cof_and" [_, Con "cof_bot" []] -> Con "cof_bot" []
  Con "cof_or" [Con "cof_top" [], _] -> Con "cof_top" []
  Con "cof_or" [_, Con "cof_top" []] -> Con "cof_top" []
  Con "cof_or" [Con "cof_bot" [], psi] -> simplifyCof psi
  Con "cof_or" [psi, Con "cof_bot" []] -> simplifyCof psi
  _ -> phi

--------------------------------------------------------------------------------
-- Level Operations
--------------------------------------------------------------------------------

-- | Simplify level expressions
simplifyLevel :: Term -> Term
simplifyLevel l = case l of
  Con "lmax" [l1, l2] ->
    let l1' = simplifyLevel l1
        l2' = simplifyLevel l2
    in if l1' == l2' then l1'
       else case (l1', l2') of
         (Con "lzero" [], _) -> l2'
         (_, Con "lzero" []) -> l1'
         (Con "lsuc" [a], Con "lsuc" [b]) ->
           Con "lsuc" [simplifyLevel (Con "lmax" [a, b])]
         _ -> Con "lmax" [l1', l2']
  _ -> l

--------------------------------------------------------------------------------
-- Kan Operations
--------------------------------------------------------------------------------

-- | Coercion along a line of types
coe :: Term -> Term -> Term -> Term -> Term
coe r s ty tm
  | r == s = tm
  | otherwise = Con "coe" [r, s, ty, tm]

-- | Homogeneous composition
hcom :: Term -> Term -> Term -> Term -> Term -> Term
hcom r s ty phi cap
  | r == s = cap
  | evalCof phi = cap
  | otherwise = Con "hcom" [r, s, ty, phi, cap]

-- | V-in: introduction for V-types
vin :: Term -> Term -> Term -> Term
vin r a b = case r of
  Con "dim0" [] -> a
  Con "dim1" [] -> b
  _ -> Con "vin" [r, a, b]

--------------------------------------------------------------------------------
-- Normalization Engine
--------------------------------------------------------------------------------

-- | Pattern matching for rules
matchPattern :: Term -> Term -> Maybe (Map.Map String Term)
matchPattern pattern term = matchInner pattern term Map.empty

matchInner :: Term -> Term -> Map.Map String Term -> Maybe (Map.Map String Term)
matchInner pattern term bindings = case (pattern, term) of
  (Var name, _) ->
    case Map.lookup name bindings of
      Just existing -> if existing == term then Just bindings else Nothing
      Nothing -> Just (Map.insert name term bindings)
  (Lit p, Lit t) | p == t -> Just bindings
  (Con pname pargs, Con tname targs)
    | pname == tname && length pargs == length targs ->
      foldM (\bs (p, t) -> matchInner p t bs) bindings (zip pargs targs)
  _ -> Nothing

-- | Substitute bindings into a template
substitute :: Map.Map String Term -> Term -> Term
substitute bindings template = case template of
  Var name -> Map.findWithDefault template name bindings
  Con name args -> Con name (map (substitute bindings) args)
  _ -> template

-- | One step of reduction
step :: [(Term, Term)] -> Term -> Maybe Term
step rules t = case t of
  -- β-reduction
  Con "app" [Con "lam" [body], arg] -> Just (subst 0 arg body)
  Con "fst" [Con "pair" [a, _]] -> Just a
  Con "snd" [Con "pair" [_, b]] -> Just b
  Con "letE" [_, val, body] -> Just (subst 0 val body)
  Con "papp" [Con "plam" [body], r] -> Just (substDim 0 r body)
  Con "papp" [Con "refl" [a], _] -> Just a
  
  -- Kan operations
  Con "coe" [r, s, _, tm] | r == s -> Just tm
  Con "hcom" [r, s, _, _, cap] | r == s -> Just cap
  
  -- V-types
  Con "vin" [Con "dim0" [], a, _] -> Just a
  Con "vin" [Con "dim1" [], _, b] -> Just b
  
  -- Cofibration simplification
  Con "cof_eq" _ ->
    let simplified = simplifyCof t
    in if simplified /= t then Just simplified else Nothing
  Con "cof_and" _ ->
    let simplified = simplifyCof t
    in if simplified /= t then Just simplified else Nothing
  Con "cof_or" _ ->
    let simplified = simplifyCof t
    in if simplified /= t then Just simplified else Nothing
  
  -- Level simplification
  Con "lmax" _ ->
    let simplified = simplifyLevel t
    in if simplified /= t then Just simplified else Nothing
  
  -- Circle
  Con "loop" [Con "dim0" []] -> Just (Con "base" [])
  Con "loop" [Con "dim1" []] -> Just (Con "base" [])
  Con "circleElim" [_, b, _, Con "base" []] -> Just b
  
  -- Natural numbers
  Con "natElim" [_, z, _, Con "zero" []] -> Just z
  Con "natElim" [p, z, s, Con "suc" [n]] ->
    let rec = Con "natElim" [p, z, s, n]
    in Just (Con "app" [Con "app" [s, n], rec])
  
  -- Subtypes
  Con "subOut" [Con "subIn" [e]] -> Just e
  
  -- User rules
  _ -> findRuleMatch rules t

findRuleMatch :: [(Term, Term)] -> Term -> Maybe Term
findRuleMatch [] _ = Nothing
findRuleMatch ((lhs, rhs):rules) t =
  case matchPattern lhs t of
    Just bindings -> Just (substitute bindings rhs)
    Nothing -> findRuleMatch rules t

-- | Normalize with fuel limit
normalize :: Int -> [(Term, Term)] -> Term -> Term
normalize 0 _ t = t
normalize fuel rules t =
  case step rules t of
    Just t' -> normalize (fuel - 1) rules t'
    Nothing ->
      -- Try normalizing subterms
      case t of
        Con name args ->
          let args' = map (normalize fuel rules) args
          in if args' == args then t else Con name args'
        _ -> t

-- | Check if two terms are convertible
conv :: [(Term, Term)] -> Int -> Term -> Term -> Bool
conv rules fuel t1 t2 =
  let n1 = normalize fuel rules t1
      n2 = normalize fuel rules t2
  in n1 == n2

--------------------------------------------------------------------------------
-- Arithmetic Builtins
--------------------------------------------------------------------------------

add :: Int -> Int -> Int
add = (+)

sub :: Int -> Int -> Int
sub = (-)

gt :: Int -> Int -> Bool
gt = (>)

geq :: Int -> Int -> Bool
geq = (>=)
