/-
  Generated from Rosetta IR
  Module: Arith
-/

inductive term where

  deriving Repr, BEq

inductive zero where

  deriving Repr, BEq

inductive succ where

  deriving Repr, BEq

inductive add where

  deriving Repr, BEq

inductive mul where

  deriving Repr, BEq

inductive pred where

  deriving Repr, BEq

inductive rec where

  deriving Repr, BEq

inductive fib where

  deriving Repr, BEq

inductive fact where

  deriving Repr, BEq

def add_zero : Expr → Option Expr
  | (.add .z n) => some n
  | _ => none

def add_succ : Expr → Option Expr
  | (.add (.s m) n) => some (.s (.add m n))
  | _ => none

def mul_zero : Expr → Option Expr
  | (.mul .z n) => some .z
  | _ => none

def mul_succ : Expr → Option Expr
  | (.mul (.s m) n) => some (.add n (.mul m n))
  | _ => none

def pred_zero : Expr → Option Expr
  | (.pred .z) => some .z
  | _ => none

def pred_succ : Expr → Option Expr
  | (.pred (.s n)) => some n
  | _ => none

def fib_zero : Expr → Option Expr
  | (.fib .z) => some .z
  | _ => none

def fib_one : Expr → Option Expr
  | (.fib (.s .z)) => some (.s .z)
  | _ => none

def fib_succ : Expr → Option Expr
  | (.fib (.s (.s n))) => some (.add (.fib (.s n)) (.fib n))
  | _ => none

def fact_zero : Expr → Option Expr
  | (.fact .z) => some (.s .z)
  | _ => none

def fact_succ : Expr → Option Expr
  | (.fact (.s n)) => some (.mul (.s n) (.fact n))
  | _ => none
