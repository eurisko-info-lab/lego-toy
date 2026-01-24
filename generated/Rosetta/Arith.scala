// Generated from Rosetta IR
// Module: Arith

package generated

enum term:


enum zero:


enum succ:


enum add:


enum mul:


enum pred:


enum rec:


enum fib:


enum fact:


def add_zero(e: Expr): Option[Expr] = e match
  case Add(Z(), n) => Some(n)
  case _ => None

def add_succ(e: Expr): Option[Expr] = e match
  case Add(S(m), n) => Some(S(Add(m, n)))
  case _ => None

def mul_zero(e: Expr): Option[Expr] = e match
  case Mul(Z(), n) => Some(Z())
  case _ => None

def mul_succ(e: Expr): Option[Expr] = e match
  case Mul(S(m), n) => Some(Add(n, Mul(m, n)))
  case _ => None

def pred_zero(e: Expr): Option[Expr] = e match
  case Pred(Z()) => Some(Z())
  case _ => None

def pred_succ(e: Expr): Option[Expr] = e match
  case Pred(S(n)) => Some(n)
  case _ => None

def fib_zero(e: Expr): Option[Expr] = e match
  case Fib(Z()) => Some(Z())
  case _ => None

def fib_one(e: Expr): Option[Expr] = e match
  case Fib(S(Z())) => Some(S(Z()))
  case _ => None

def fib_succ(e: Expr): Option[Expr] = e match
  case Fib(S(S(n))) => Some(Add(Fib(S(n)), Fib(n)))
  case _ => None

def fact_zero(e: Expr): Option[Expr] = e match
  case Fact(Z()) => Some(S(Z()))
  case _ => None

def fact_succ(e: Expr): Option[Expr] = e match
  case Fact(S(n)) => Some(Mul(S(n), Fact(n)))
  case _ => None
