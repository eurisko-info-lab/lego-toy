{-|
Module      : Lego.Runtime
Description : Lego Runtime Library for Haskell
Copyright   : (c) 2024
License     : MIT

This module provides the core runtime infrastructure for Lego-generated Haskell code.
It includes:
- Core types (Term, GrammarExpr, etc.)
- Parsing engine (parseGrammar, lexGrammar)
- IO operations (readFile, writeFile)
- Memoization (Map-based Packrat)

Generated Rosetta code should: import Lego.Runtime
-}

{-# LANGUAGE LambdaCase #-}

module Lego.Runtime
  ( -- * Core Types
    Term(..)
  , GrammarExpr(..)
  , Production(..)
  , Productions
  , Rule(..)
    -- * Token Types
  , Token(..)
    -- * Parse State
  , MemoEntry(..)
  , ParseState(..)
  , ParseResult
    -- * Parsing Engine
  , parseGrammar
  , findProduction
  , findAllProductions
    -- * IO Operations
  , readFileContent
  , writeFileContent
  , doesFileExist
    -- * Term Utilities
  , matchPattern
  , substitute
  , applyRule
  , normalize
  ) where

import qualified Data.Map.Strict as Map
import Data.List (find)
import Control.Monad (foldM)
import System.Directory (doesFileExist)

--------------------------------------------------------------------------------
-- Core Types
--------------------------------------------------------------------------------

-- | The universal Term type for AST representation
data Term
  = Var String
  | Lit String
  | Con String [Term]
  deriving (Eq, Show)

-- | Grammar expression algebra
data GrammarExpr
  = Empty
  | GLit String
  | Ref String
  | Seq GrammarExpr GrammarExpr
  | Alt GrammarExpr GrammarExpr
  | Star GrammarExpr
  | Plus GrammarExpr
  | Opt GrammarExpr
  | Node String GrammarExpr
  deriving (Eq, Show)

-- | Grammar production: (name, grammar, annotation)
data Production = Production
  { prodName :: String
  , prodGrammar :: GrammarExpr
  , prodAnnotation :: String
  } deriving (Eq, Show)

-- | Production list type
type Productions = [Production]

-- | Rewrite rule: name, lhs pattern, rhs template
data Rule = Rule
  { ruleName :: String
  , ruleLhs :: Term
  , ruleRhs :: Term
  } deriving (Eq, Show)

--------------------------------------------------------------------------------
-- Token Types
--------------------------------------------------------------------------------

-- | Token types for lexing
data Token
  = TokLit String      -- ^ String literal "..."
  | TokIdent String    -- ^ Identifier
  | TokSym String      -- ^ Symbol/operator
  | TokNumber String   -- ^ Numeric literal
  deriving (Eq, Show)

showToken :: Token -> String
showToken = \case
  TokLit s -> "\"" ++ s ++ "\""
  TokIdent s -> s
  TokSym s -> s
  TokNumber s -> s

--------------------------------------------------------------------------------
-- Parse State
--------------------------------------------------------------------------------

-- | Packrat memoization entry
data MemoEntry = MemoEntry
  { memoResult :: Maybe (Term, Int, [(String, Term)])
  } deriving (Show)

-- | Parse state
data ParseState = ParseState
  { psTokens :: [Token]
  , psPos :: Int
  , psMemo :: Map.Map (Int, String) MemoEntry
  , psBinds :: [(String, Term)]
  } deriving (Show)

-- | Initial parse state
initParseState :: [Token] -> ParseState
initParseState toks = ParseState toks 0 Map.empty []

-- | Parse result: (parsed term, new state) or failure
type ParseResult = (Maybe (Term, ParseState), Map.Map (Int, String) MemoEntry)

--------------------------------------------------------------------------------
-- Core Parsing Engine
--------------------------------------------------------------------------------

-- | Find a production by name
findProduction :: Productions -> String -> Maybe GrammarExpr
findProduction prods name = prodGrammar <$> find ((== name) . prodName) prods

-- | Find all productions with the same base name and combine with alt
findAllProductions :: Productions -> String -> Maybe GrammarExpr
findAllProductions prods name =
  case filter ((== name) . prodName) prods of
    [] -> Nothing
    [p] -> Just (prodGrammar p)
    (p:ps) -> Just $ foldl (\acc prod -> Alt acc (prodGrammar prod)) (prodGrammar p) ps

-- | Combine two terms in sequence
combineSeq :: Term -> Term -> Term
combineSeq (Con "unit" []) t = t
combineSeq t (Con "unit" []) = t
combineSeq (Con "seq" ts) t = Con "seq" (ts ++ [t])
combineSeq t (Con "seq" ts) = Con "seq" (t : ts)
combineSeq t1 t2 = Con "seq" [t1, t2]

-- | Wrap term in a constructor node
wrapNode :: String -> Term -> Term
wrapNode name t = Con name [t]

-- | Parse grammar expression (main parsing engine)
--   Uses fuel for termination and Packrat memoization for efficiency
parseGrammar :: Int -> Productions -> GrammarExpr -> ParseState -> ParseResult
parseGrammar fuel prods g st
  | fuel <= 0 = (Nothing, psMemo st)
  | otherwise = case g of

  Empty -> (Just (Con "unit" [], st), psMemo st)

  GLit s -> case psTokens st of
    TokLit l : rest | l == s ->
      (Just (Lit s, st { psTokens = rest, psPos = psPos st + 1 }), psMemo st)
    TokSym l : rest | l == s ->
      (Just (Lit s, st { psTokens = rest, psPos = psPos st + 1 }), psMemo st)
    TokIdent l : rest | l == s ->
      (Just (Lit s, st { psTokens = rest, psPos = psPos st + 1 }), psMemo st)
    _ -> (Nothing, psMemo st)

  Ref name
    -- Handle built-in token types (TOKEN.*)
    | "TOKEN." `isPrefixOf` name ->
      let tokType = drop 6 name
      in case (tokType, psTokens st) of
        ("ident", TokIdent s : rest) ->
          (Just (Var s, st { psTokens = rest, psPos = psPos st + 1 }), psMemo st)
        ("string", TokLit s : rest) | head s == '"' ->
          (Just (Lit s, st { psTokens = rest, psPos = psPos st + 1 }), psMemo st)
        ("number", TokNumber s : rest) ->
          (Just (Lit s, st { psTokens = rest, psPos = psPos st + 1 }), psMemo st)
        ("sym", TokSym s : rest) ->
          (Just (Var s, st { psTokens = rest, psPos = psPos st + 1 }), psMemo st)
        _ -> (Nothing, psMemo st)
    | otherwise ->
      -- Packrat memoization for production references
      let key = (psPos st, name)
      in case Map.lookup key (psMemo st) of
        Just entry -> case memoResult entry of
          Just (term, endPos, newBinds) ->
            let tokenCount = endPos - psPos st
                newTokens = drop tokenCount (psTokens st)
            in (Just (term, st { psTokens = newTokens, psPos = endPos, psBinds = newBinds }), psMemo st)
          Nothing -> (Nothing, psMemo st)
        Nothing -> case findAllProductions prods name of
          Just g' ->
            let (result, memo') = parseGrammar (fuel - 1) prods g' st
            in case result of
              Just (term, st') ->
                let entry = MemoEntry (Just (term, psPos st', psBinds st'))
                    memo'' = Map.insert key entry memo'
                in (Just (term, st' { psMemo = memo'' }), memo'')
              Nothing ->
                let entry = MemoEntry Nothing
                    memo'' = Map.insert key entry memo'
                in (Nothing, memo'')
          Nothing -> (Nothing, psMemo st)

  Seq g1 g2 ->
    let (r1, memo1) = parseGrammar (fuel - 1) prods g1 st
    in case r1 of
      Just (t1, st1) ->
        let st1' = st1 { psMemo = memo1 }
            (r2, memo2) = parseGrammar (fuel - 1) prods g2 st1'
        in case r2 of
          Just (t2, st2) -> (Just (combineSeq t1 t2, st2), memo2)
          Nothing -> (Nothing, memo2)
      Nothing -> (Nothing, memo1)

  Alt g1 g2 ->
    let (r1, memo1) = parseGrammar (fuel - 1) prods g1 st
    in case r1 of
      Just result -> (Just result, memo1)
      Nothing ->
        let st' = st { psMemo = memo1 }
        in parseGrammar (fuel - 1) prods g2 st'

  Star g' -> loop [] st (psMemo st) (fuel - 1)
    where
      loop acc currSt memo loopFuel
        | loopFuel <= 0 =
          let result = if null acc then Con "unit" [] else Con "seq" (reverse acc)
          in (Just (result, currSt), memo)
        | otherwise =
          let currSt' = currSt { psMemo = memo }
              (r, memo') = parseGrammar (fuel - 1) prods g' currSt'
          in case r of
            Just (t, st'') -> loop (t : acc) st'' memo' (loopFuel - 1)
            Nothing ->
              let result = if null acc then Con "unit" [] else Con "seq" (reverse acc)
              in (Just (result, currSt { psMemo = memo' }), memo')

  Plus g' ->
    let (first, memo1) = parseGrammar (fuel - 1) prods g' st
    in case first of
      Nothing -> (Nothing, memo1)
      Just (t, st') ->
        let (rest, memo2) = parseGrammar (fuel - 1) prods (Star g') (st' { psMemo = memo1 })
        in case rest of
          Just (Con "unit" [], st'') -> (Just (t, st''), memo2)
          Just (ts, st'') -> (Just (combineSeq t ts, st''), memo2)
          Nothing -> (Just (t, st'), memo2)

  Opt g' ->
    let (r, memo') = parseGrammar (fuel - 1) prods g' st
    in case r of
      Just result -> (Just result, memo')
      Nothing -> (Just (Con "unit" [], st { psMemo = memo' }), memo')

  Node name g' ->
    let (r, memo') = parseGrammar (fuel - 1) prods g' st
    in case r of
      Just (t, st') -> (Just (wrapNode name t, st'), memo')
      Nothing -> (Nothing, memo')

  where
    isPrefixOf :: String -> String -> Bool
    isPrefixOf prefix str = take (length prefix) str == prefix

--------------------------------------------------------------------------------
-- IO Operations
--------------------------------------------------------------------------------

-- | Read file contents
readFileContent :: FilePath -> IO String
readFileContent = readFile

-- | Write file contents
writeFileContent :: FilePath -> String -> IO ()
writeFileContent = writeFile

--------------------------------------------------------------------------------
-- Term Utilities
--------------------------------------------------------------------------------

-- | Pattern match helper
matchPattern :: Term -> Term -> Maybe [(String, Term)]
matchPattern (Var x) t = Just [(x, t)]
matchPattern (Lit s1) (Lit s2)
  | s1 == s2 = Just []
  | otherwise = Nothing
matchPattern (Con n1 args1) (Con n2 args2)
  | n1 == n2 && length args1 == length args2 =
    let results = zipWith matchPattern args1 args2
    in if all isJust results
       then Just (concat $ map fromJust results)
       else Nothing
  | otherwise = Nothing
  where
    isJust (Just _) = True
    isJust Nothing = False
    fromJust (Just x) = x
    fromJust Nothing = []
matchPattern _ _ = Nothing

-- | Substitute bindings in a term
substitute :: [(String, Term)] -> Term -> Term
substitute binds (Var x) = case lookup x binds of
  Just t -> t
  Nothing -> Var x
substitute _ (Lit s) = Lit s
substitute binds (Con n args) = Con n (map (substitute binds) args)

-- | Apply a single rewrite rule
applyRule :: Rule -> Term -> Maybe Term
applyRule rule t = do
  binds <- matchPattern (ruleLhs rule) t
  return $ substitute binds (ruleRhs rule)

-- | Normalize term using rewrite rules
normalize :: [Rule] -> Term -> Int -> Term
normalize _ t fuel | fuel <= 0 = t
normalize rules t fuel =
  -- Try each rule
  case firstJust (\r -> applyRule r t) rules of
    Just t' -> normalize rules t' (fuel - 1)
    Nothing ->
      -- Recursively normalize children
      case t of
        Con n args -> Con n (map (\a -> normalize rules a (fuel - 1)) args)
        other -> other
  where
    firstJust :: (a -> Maybe b) -> [a] -> Maybe b
    firstJust _ [] = Nothing
    firstJust f (x:xs) = case f x of
      Just y -> Just y
      Nothing -> firstJust f xs
