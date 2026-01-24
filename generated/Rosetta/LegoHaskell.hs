-- generated/Rosetta/LegoHaskell.hs
-- What Lego.rosetta would generate via rosetta2haskell
-- This is a MANUAL rendering for verification

{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}

module LegoHaskell where

import Data.Maybe (fromMaybe)
import Control.Monad (guard)

-- From Lego.rosetta adt Iso → Haskell data
data Iso a b = MkIso
  { forward  :: a -> Maybe b
  , backward :: b -> Maybe a
  }

-- From: rewrite id: Iso.id ~> ...
isoId :: Iso a a
isoId = MkIso Just Just

-- From: rewrite comp: (Iso.comp $f $g) ~> ...
isoComp :: Iso a b -> Iso b c -> Iso a c
isoComp f g = MkIso
  { forward  = \a -> forward f a >>= forward g
  , backward = \c -> backward g c >>= backward f
  }

-- From: rewrite par: (Iso.par $f $g) ~> ...
isoPar :: Iso a b -> Iso c d -> Iso (a, c) (b, d)
isoPar f g = MkIso
  { forward  = \(a, c) -> do
      b <- forward f a
      d <- forward g c
      return (b, d)
  , backward = \(b, d) -> do
      a <- backward f b
      c <- backward g d
      return (a, c)
  }

-- From: rewrite choice: (Iso.choice $f $g) ~> ...
isoChoice :: Iso a c -> Iso b c -> Iso (Either a b) c
isoChoice f g = MkIso
  { forward  = \case
      Left a  -> forward f a
      Right b -> forward g b
  , backward = \c -> case backward f c of
      Just a  -> Just (Left a)
      Nothing -> fmap Right (backward g c)
  }

-- From: rewrite orElse: (Iso.orElse $f $g) ~> ...
isoOrElse :: Iso a b -> Iso a b -> Iso a b
isoOrElse f g = MkIso
  { forward  = \a -> forward f a <|> forward g a
  , backward = \b -> backward f b <|> backward g b
  }
  where
    Nothing <|> y = y
    x       <|> _ = x

-- From: rewrite sym: (Iso.sym $f) ~> ...
isoSym :: Iso a b -> Iso b a
isoSym f = MkIso (backward f) (forward f)

-- From Lego.rosetta adt Term → Haskell data
data Term
  = Var String
  | Lit String
  | Con String [Term]
  deriving (Show, Eq)

-- From: rewrite atom: (Term.atom $s) ~> (Con $s Nil)
atom :: String -> Term
atom s = Con s []

-- From: rewrite app: (Term.app $f $args) ~> (Con $f $args)
app :: String -> [Term] -> Term
app = Con

-- From: rewrite matchPattern: ...
matchPattern :: Term -> Term -> Maybe [(String, Term)]
matchPattern (Var name) t
  | "$" `isPrefixOf` name = Just [(name, t)]
  | Var name == t         = Just []
  | otherwise             = Nothing
matchPattern (Lit a) (Lit b)
  | a == b    = Just []
  | otherwise = Nothing
matchPattern (Con c1 args1) (Con c2 args2)
  | c1 == c2 && length args1 == length args2 = matchList args1 args2
  | otherwise = Nothing
matchPattern _ _ = Nothing

matchList :: [Term] -> [Term] -> Maybe [(String, Term)]
matchList [] [] = Just []
matchList (p:ps) (t:ts) = do
  m1 <- matchPattern p t
  m2 <- matchList ps ts
  return (m1 ++ m2)
matchList _ _ = Nothing

-- From: rewrite substVar, substLit, substCon
substitute :: Term -> [(String, Term)] -> Term
substitute (Var name) env
  | "$" `isPrefixOf` name = fromMaybe (Var name) (lookup name env)
  | otherwise             = Var name
substitute (Lit s) _ = Lit s
substitute (Con c args) env = Con c (map (`substitute` env) args)

isPrefixOf :: String -> String -> Bool
isPrefixOf [] _          = True
isPrefixOf _ []          = False
isPrefixOf (x:xs) (y:ys) = x == y && isPrefixOf xs ys

-- From Lego.rosetta adt Token → Haskell data
data Token
  = Ident String
  | TLit String
  | Sym String
  | Number String
  deriving (Show, Eq)

-- From: rewrite toString: (Token.toString (Ident $s)) ~> $s
tokenToString :: Token -> String
tokenToString (Ident s)  = s
tokenToString (TLit s)   = s
tokenToString (Sym s)    = s
tokenToString (Number s) = s

-- From Lego.rosetta adt GrammarExpr → Haskell data (functor + fix)
data GrammarF a
  = Empty
  | GLit String
  | Ref String
  | Seq a a
  | Alt a a
  | Star a
  | Bind String a
  | Node String a
  | Cut a
  | Ordered a a
  | Longest [a]
  deriving (Show, Eq, Functor)

newtype GrammarExpr = GrammarExpr { unGrammar :: GrammarF GrammarExpr }
  deriving (Show, Eq)

-- Smart constructors
grammarEmpty :: GrammarExpr
grammarEmpty = GrammarExpr Empty

grammarLit :: String -> GrammarExpr
grammarLit s = GrammarExpr (GLit s)

grammarRef :: String -> GrammarExpr
grammarRef s = GrammarExpr (Ref s)

grammarSeq :: GrammarExpr -> GrammarExpr -> GrammarExpr
grammarSeq a b = GrammarExpr (Seq a b)

grammarAlt :: GrammarExpr -> GrammarExpr -> GrammarExpr
grammarAlt a b = GrammarExpr (Alt a b)

grammarStar :: GrammarExpr -> GrammarExpr
grammarStar g = GrammarExpr (Star g)

-- From: rewrite plus: (Grammar.plus $g) ~> (Seq $g (Star $g))
grammarPlus :: GrammarExpr -> GrammarExpr
grammarPlus g = grammarSeq g (grammarStar g)

-- From: rewrite opt: (Grammar.opt $g) ~> (Alt $g Empty)
grammarOpt :: GrammarExpr -> GrammarExpr
grammarOpt g = grammarAlt g grammarEmpty

-- From Lego.rosetta adt Rule → Haskell data
data Rule = Rule
  { ruleName     :: String
  , rulePattern  :: Term
  , ruleTemplate :: Term
  }
  deriving (Show, Eq)

-- From: rewrite applyRule: (Rule.apply (MkRule $name $pat $repl) $term) ~> ...
applyRule :: Rule -> Term -> Maybe Term
applyRule (Rule _ pat repl) term = do
  bindings <- matchPattern pat term
  return (substitute repl bindings)

-- From: rewrite applyFirst: (Rule.applyFirst Nil $term) ~> None
applyFirst :: [Rule] -> Term -> Maybe Term
applyFirst [] _ = Nothing
applyFirst (r:rs) term = case applyRule r term of
  Just t  -> Just t
  Nothing -> applyFirst rs term

-- From: rewrite normalize: (Rule.normalize $rules $term) ~> ...
normalize :: [Rule] -> Term -> Term
normalize rules term = case applyFirst rules term of
  Nothing -> term
  Just t' -> normalize rules t'

-- From Lego.rosetta adt ParseResult → Haskell data
data ParseResult
  = Success [Token] Term
  | Failure String
  deriving (Show, Eq)
