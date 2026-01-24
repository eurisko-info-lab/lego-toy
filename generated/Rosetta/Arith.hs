{-
  Generated from Rosetta IR
  Module: Arith
-}

{-# LANGUAGE GADTs #-}
{-# LANGUAGE StandaloneDeriving #-}

module Arith where

data term where

  deriving (Show, Eq)

data zero where

  deriving (Show, Eq)

data succ where

  deriving (Show, Eq)

data add where

  deriving (Show, Eq)

data mul where

  deriving (Show, Eq)

data pred where

  deriving (Show, Eq)

data rec where

  deriving (Show, Eq)

data fib where

  deriving (Show, Eq)

data fact where

  deriving (Show, Eq)

add_zero :: Expr -> Maybe Expr
add_zero (Add Z n) = Just (n)
add_zero _ = Nothing

add_succ :: Expr -> Maybe Expr
add_succ (Add (S m) n) = Just ((S (Add m n)))
add_succ _ = Nothing

mul_zero :: Expr -> Maybe Expr
mul_zero (Mul Z n) = Just (Z)
mul_zero _ = Nothing

mul_succ :: Expr -> Maybe Expr
mul_succ (Mul (S m) n) = Just ((Add n (Mul m n)))
mul_succ _ = Nothing

pred_zero :: Expr -> Maybe Expr
pred_zero (Pred Z) = Just (Z)
pred_zero _ = Nothing

pred_succ :: Expr -> Maybe Expr
pred_succ (Pred (S n)) = Just (n)
pred_succ _ = Nothing

fib_zero :: Expr -> Maybe Expr
fib_zero (Fib Z) = Just (Z)
fib_zero _ = Nothing

fib_one :: Expr -> Maybe Expr
fib_one (Fib (S Z)) = Just ((S Z))
fib_one _ = Nothing

fib_succ :: Expr -> Maybe Expr
fib_succ (Fib (S (S n))) = Just ((Add (Fib (S n)) (Fib n)))
fib_succ _ = Nothing

fact_zero :: Expr -> Maybe Expr
fact_zero (Fact Z) = Just ((S Z))
fact_zero _ = Nothing

fact_succ :: Expr -> Maybe Expr
fact_succ (Fact (S n)) = Just ((Mul (S n) (Fact n)))
fact_succ _ = Nothing
