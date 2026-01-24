// Generated from Rosetta IR
// Module: Arith

#[derive(Debug, Clone, PartialEq)]
pub enum term {

}

#[derive(Debug, Clone, PartialEq)]
pub enum zero {

}

#[derive(Debug, Clone, PartialEq)]
pub enum succ {

}

#[derive(Debug, Clone, PartialEq)]
pub enum add {

}

#[derive(Debug, Clone, PartialEq)]
pub enum mul {

}

#[derive(Debug, Clone, PartialEq)]
pub enum pred {

}

#[derive(Debug, Clone, PartialEq)]
pub enum rec {

}

#[derive(Debug, Clone, PartialEq)]
pub enum fib {

}

#[derive(Debug, Clone, PartialEq)]
pub enum fact {

}

pub fn add_zero(e: &Expr) -> Option<Expr> {
    match e {
        Expr::Add { arg1: Expr::Z, arg2: n } => Some(n.clone()),
        _ => None,
    }
}

pub fn add_succ(e: &Expr) -> Option<Expr> {
    match e {
        Expr::Add { arg1: Expr::S { arg1: m }, arg2: n } => Some(Expr::S { arg1: Box::new(Expr::Add { arg1: Box::new(m.clone()), arg2: Box::new(n.clone()) }) }),
        _ => None,
    }
}

pub fn mul_zero(e: &Expr) -> Option<Expr> {
    match e {
        Expr::Mul { arg1: Expr::Z, arg2: n } => Some(Expr::Z),
        _ => None,
    }
}

pub fn mul_succ(e: &Expr) -> Option<Expr> {
    match e {
        Expr::Mul { arg1: Expr::S { arg1: m }, arg2: n } => Some(Expr::Add { arg1: Box::new(n.clone()), arg2: Box::new(Expr::Mul { arg1: Box::new(m.clone()), arg2: Box::new(n.clone()) }) }),
        _ => None,
    }
}

pub fn pred_zero(e: &Expr) -> Option<Expr> {
    match e {
        Expr::Pred { arg1: Expr::Z } => Some(Expr::Z),
        _ => None,
    }
}

pub fn pred_succ(e: &Expr) -> Option<Expr> {
    match e {
        Expr::Pred { arg1: Expr::S { arg1: n } } => Some(n.clone()),
        _ => None,
    }
}

pub fn fib_zero(e: &Expr) -> Option<Expr> {
    match e {
        Expr::Fib { arg1: Expr::Z } => Some(Expr::Z),
        _ => None,
    }
}

pub fn fib_one(e: &Expr) -> Option<Expr> {
    match e {
        Expr::Fib { arg1: Expr::S { arg1: Expr::Z } } => Some(Expr::S { arg1: Box::new(Expr::Z) }),
        _ => None,
    }
}

pub fn fib_succ(e: &Expr) -> Option<Expr> {
    match e {
        Expr::Fib { arg1: Expr::S { arg1: Expr::S { arg1: n } } } => Some(Expr::Add { arg1: Box::new(Expr::Fib { arg1: Box::new(Expr::S { arg1: Box::new(n.clone()) }) }), arg2: Box::new(Expr::Fib { arg1: Box::new(n.clone()) }) }),
        _ => None,
    }
}

pub fn fact_zero(e: &Expr) -> Option<Expr> {
    match e {
        Expr::Fact { arg1: Expr::Z } => Some(Expr::S { arg1: Box::new(Expr::Z) }),
        _ => None,
    }
}

pub fn fact_succ(e: &Expr) -> Option<Expr> {
    match e {
        Expr::Fact { arg1: Expr::S { arg1: n } } => Some(Expr::Mul { arg1: Box::new(Expr::S { arg1: Box::new(n.clone()) }), arg2: Box::new(Expr::Fact { arg1: Box::new(n.clone()) }) }),
        _ => None,
    }
}
