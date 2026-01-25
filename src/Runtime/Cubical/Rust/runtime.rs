//! Cubical Runtime Library for Rust
//!
//! This module provides the runtime infrastructure for Cubical type theory
//! generated from .lego specifications via the cubical2rosetta → rosetta2rust pipeline.
//!
//! It includes:
//! - Core Term type (shared with lego_runtime)
//! - Cubical-specific types (Dim, Cof, Level)
//! - De Bruijn index operations (shift, subst)
//! - Normalization engine
//! - Cubical operations (coe, hcom, com)
//!
//! Generated code should: use cubical_runtime::*;

use std::collections::HashMap;

//============================================================================
// Core Types (re-export or define if standalone)
//============================================================================

/// The universal Term type for AST representation
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Term {
    Var(String),
    Lit(String),
    Con(String, Vec<Term>),
}

impl Term {
    pub fn var(s: impl Into<String>) -> Self {
        Term::Var(s.into())
    }

    pub fn lit(s: impl Into<String>) -> Self {
        Term::Lit(s.into())
    }

    pub fn con(name: impl Into<String>, args: Vec<Term>) -> Self {
        Term::Con(name.into(), args)
    }
    
    pub fn ix(n: usize) -> Self {
        Term::Con("ix".into(), vec![Term::Lit(n.to_string())])
    }
}

//============================================================================
// Cubical-Specific Types
//============================================================================

/// Dimension values (interval endpoints and variables)
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Dim {
    I0,                     // 0 endpoint
    I1,                     // 1 endpoint
    IVar(usize),           // dimension variable
}

/// Cofibrations (face formulas)
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Cof {
    Top,                    // ⊤ (always true)
    Bot,                    // ⊥ (always false)
    Eq(Dim, Dim),          // r = s
    Conj(Box<Cof>, Box<Cof>), // φ ∧ ψ
    Disj(Box<Cof>, Box<Cof>), // φ ∨ ψ
}

/// Universe levels
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Level {
    LZero,
    LSuc(Box<Level>),
    LMax(Box<Level>, Box<Level>),
    LVar(usize),
}

/// Tube element: (cofibration, partial element)
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Tube {
    pub cof: Term,
    pub element: Term,
}

//============================================================================
// De Bruijn Index Operations
//============================================================================

/// Shift (weaken) a term: increment free variables >= cutoff by amount
pub fn shift(cutoff: usize, amount: usize, t: &Term) -> Term {
    match t {
        Term::Con(name, args) if name == "ix" && args.len() == 1 => {
            if let Term::Lit(n) = &args[0] {
                let idx: usize = n.parse().unwrap_or(0);
                if idx >= cutoff {
                    Term::Con("ix".into(), vec![Term::Lit((idx + amount).to_string())])
                } else {
                    t.clone()
                }
            } else {
                t.clone()
            }
        }
        Term::Con(name, args) if name == "lam" && args.len() == 1 => {
            Term::Con("lam".into(), vec![shift(cutoff + 1, amount, &args[0])])
        }
        Term::Con(name, args) if name == "pi" && args.len() == 2 => {
            Term::Con("pi".into(), vec![
                shift(cutoff, amount, &args[0]),
                shift(cutoff + 1, amount, &args[1]),
            ])
        }
        Term::Con(name, args) if name == "sigma" && args.len() == 2 => {
            Term::Con("sigma".into(), vec![
                shift(cutoff, amount, &args[0]),
                shift(cutoff + 1, amount, &args[1]),
            ])
        }
        Term::Con(name, args) if name == "letE" && args.len() == 3 => {
            Term::Con("letE".into(), vec![
                shift(cutoff, amount, &args[0]),
                shift(cutoff, amount, &args[1]),
                shift(cutoff + 1, amount, &args[2]),
            ])
        }
        Term::Con(name, args) if name == "plam" && args.len() == 1 => {
            Term::Con("plam".into(), vec![shift(cutoff + 1, amount, &args[0])])
        }
        Term::Con(name, args) => {
            Term::Con(name.clone(), args.iter().map(|a| shift(cutoff, amount, a)).collect())
        }
        _ => t.clone(),
    }
}

/// Substitute: replace variable at index with term, adjusting indices
pub fn subst(idx: usize, replacement: &Term, t: &Term) -> Term {
    match t {
        Term::Con(name, args) if name == "ix" && args.len() == 1 => {
            if let Term::Lit(n) = &args[0] {
                let i: usize = n.parse().unwrap_or(0);
                if i == idx {
                    replacement.clone()
                } else if i > idx {
                    Term::Con("ix".into(), vec![Term::Lit((i - 1).to_string())])
                } else {
                    t.clone()
                }
            } else {
                t.clone()
            }
        }
        Term::Con(name, args) if name == "lam" && args.len() == 1 => {
            Term::Con("lam".into(), vec![
                subst(idx + 1, &shift(0, 1, replacement), &args[0])
            ])
        }
        Term::Con(name, args) if name == "pi" && args.len() == 2 => {
            Term::Con("pi".into(), vec![
                subst(idx, replacement, &args[0]),
                subst(idx + 1, &shift(0, 1, replacement), &args[1]),
            ])
        }
        Term::Con(name, args) if name == "sigma" && args.len() == 2 => {
            Term::Con("sigma".into(), vec![
                subst(idx, replacement, &args[0]),
                subst(idx + 1, &shift(0, 1, replacement), &args[1]),
            ])
        }
        Term::Con(name, args) if name == "letE" && args.len() == 3 => {
            Term::Con("letE".into(), vec![
                subst(idx, replacement, &args[0]),
                subst(idx, replacement, &args[1]),
                subst(idx + 1, &shift(0, 1, replacement), &args[2]),
            ])
        }
        Term::Con(name, args) if name == "plam" && args.len() == 1 => {
            Term::Con("plam".into(), vec![
                subst(idx + 1, &shift(0, 1, replacement), &args[0])
            ])
        }
        Term::Con(name, args) => {
            Term::Con(name.clone(), args.iter().map(|a| subst(idx, replacement, a)).collect())
        }
        _ => t.clone(),
    }
}

/// Substitute dimension in a term
pub fn subst_dim(idx: usize, dim: &Term, t: &Term) -> Term {
    match t {
        Term::Con(name, args) if name == "dimVar" && args.len() == 1 => {
            if let Term::Lit(n) = &args[0] {
                let i: usize = n.parse().unwrap_or(0);
                if i == idx { dim.clone() } else { t.clone() }
            } else {
                t.clone()
            }
        }
        Term::Con(name, args) if name == "plam" && args.len() == 1 => {
            Term::Con("plam".into(), vec![subst_dim(idx + 1, dim, &args[0])])
        }
        Term::Con(name, args) => {
            Term::Con(name.clone(), args.iter().map(|a| subst_dim(idx, dim, a)).collect())
        }
        _ => t.clone(),
    }
}

//============================================================================
// Cofibration Evaluation
//============================================================================

/// Check if a cofibration is satisfied (true)
pub fn eval_cof(phi: &Term) -> bool {
    match phi {
        Term::Con(name, args) => match name.as_str() {
            "cof_top" if args.is_empty() => true,
            "cof_bot" if args.is_empty() => false,
            "cof_eq" if args.len() == 2 => args[0] == args[1],
            "cof_and" if args.len() == 2 => eval_cof(&args[0]) && eval_cof(&args[1]),
            "cof_or" if args.len() == 2 => eval_cof(&args[0]) || eval_cof(&args[1]),
            _ => false,
        },
        _ => false,
    }
}

/// Simplify cofibration
pub fn simplify_cof(phi: &Term) -> Term {
    match phi {
        Term::Con(name, args) => match name.as_str() {
            "cof_eq" if args.len() == 2 => {
                if args[0] == args[1] {
                    Term::Con("cof_top".into(), vec![])
                } else {
                    match (&args[0], &args[1]) {
                        (Term::Con(n1, a1), Term::Con(n2, a2))
                            if (n1 == "dim0" && n2 == "dim1" || n1 == "dim1" && n2 == "dim0")
                                && a1.is_empty() && a2.is_empty() =>
                        {
                            Term::Con("cof_bot".into(), vec![])
                        }
                        _ => phi.clone(),
                    }
                }
            }
            "cof_and" if args.len() == 2 => {
                match &args[0] {
                    Term::Con(n, a) if n == "cof_top" && a.is_empty() => simplify_cof(&args[1]),
                    Term::Con(n, a) if n == "cof_bot" && a.is_empty() => Term::Con("cof_bot".into(), vec![]),
                    _ => match &args[1] {
                        Term::Con(n, a) if n == "cof_top" && a.is_empty() => simplify_cof(&args[0]),
                        Term::Con(n, a) if n == "cof_bot" && a.is_empty() => Term::Con("cof_bot".into(), vec![]),
                        _ => phi.clone(),
                    }
                }
            }
            "cof_or" if args.len() == 2 => {
                match &args[0] {
                    Term::Con(n, a) if n == "cof_top" && a.is_empty() => Term::Con("cof_top".into(), vec![]),
                    Term::Con(n, a) if n == "cof_bot" && a.is_empty() => simplify_cof(&args[1]),
                    _ => match &args[1] {
                        Term::Con(n, a) if n == "cof_top" && a.is_empty() => Term::Con("cof_top".into(), vec![]),
                        Term::Con(n, a) if n == "cof_bot" && a.is_empty() => simplify_cof(&args[0]),
                        _ => phi.clone(),
                    }
                }
            }
            _ => phi.clone(),
        },
        _ => phi.clone(),
    }
}

//============================================================================
// Level Operations
//============================================================================

/// Simplify level expressions
pub fn simplify_level(l: &Term) -> Term {
    match l {
        Term::Con(name, args) if name == "lmax" && args.len() == 2 => {
            let l1 = simplify_level(&args[0]);
            let l2 = simplify_level(&args[1]);
            if l1 == l2 {
                l1
            } else {
                match (&l1, &l2) {
                    (Term::Con(n, a), _) if n == "lzero" && a.is_empty() => l2,
                    (_, Term::Con(n, a)) if n == "lzero" && a.is_empty() => l1,
                    (Term::Con(n1, a1), Term::Con(n2, a2))
                        if n1 == "lsuc" && n2 == "lsuc" && a1.len() == 1 && a2.len() == 1 =>
                    {
                        Term::Con("lsuc".into(), vec![
                            simplify_level(&Term::Con("lmax".into(), vec![a1[0].clone(), a2[0].clone()]))
                        ])
                    }
                    _ => Term::Con("lmax".into(), vec![l1, l2]),
                }
            }
        }
        _ => l.clone(),
    }
}

//============================================================================
// Kan Operations
//============================================================================

/// Coercion along a line of types
pub fn coe(r: &Term, s: &Term, ty: &Term, tm: &Term) -> Term {
    if r == s {
        tm.clone()
    } else {
        Term::Con("coe".into(), vec![r.clone(), s.clone(), ty.clone(), tm.clone()])
    }
}

/// Homogeneous composition
pub fn hcom(r: &Term, s: &Term, ty: &Term, phi: &Term, cap: &Term) -> Term {
    if r == s {
        cap.clone()
    } else if eval_cof(phi) {
        cap.clone()
    } else {
        Term::Con("hcom".into(), vec![r.clone(), s.clone(), ty.clone(), phi.clone(), cap.clone()])
    }
}

/// V-in: introduction for V-types
pub fn vin(r: &Term, a: &Term, b: &Term) -> Term {
    match r {
        Term::Con(name, args) if name == "dim0" && args.is_empty() => a.clone(),
        Term::Con(name, args) if name == "dim1" && args.is_empty() => b.clone(),
        _ => Term::Con("vin".into(), vec![r.clone(), a.clone(), b.clone()]),
    }
}

//============================================================================
// Normalization Engine
//============================================================================

/// Pattern matching for rules
pub fn match_pattern(pattern: &Term, term: &Term) -> Option<HashMap<String, Term>> {
    let mut bindings = HashMap::new();
    if match_inner(pattern, term, &mut bindings) {
        Some(bindings)
    } else {
        None
    }
}

fn match_inner(pattern: &Term, term: &Term, bindings: &mut HashMap<String, Term>) -> bool {
    match (pattern, term) {
        (Term::Var(name), _) => {
            if let Some(existing) = bindings.get(name) {
                existing == term
            } else {
                bindings.insert(name.clone(), term.clone());
                true
            }
        }
        (Term::Lit(p), Term::Lit(t)) => p == t,
        (Term::Con(pname, pargs), Term::Con(tname, targs)) => {
            pname == tname && pargs.len() == targs.len() &&
            pargs.iter().zip(targs.iter()).all(|(p, t)| match_inner(p, t, bindings))
        }
        _ => false,
    }
}

/// Substitute bindings into a template
pub fn substitute(bindings: &HashMap<String, Term>, template: &Term) -> Term {
    match template {
        Term::Var(name) => bindings.get(name).cloned().unwrap_or_else(|| template.clone()),
        Term::Con(name, args) => {
            Term::Con(name.clone(), args.iter().map(|a| substitute(bindings, a)).collect())
        }
        _ => template.clone(),
    }
}

/// One step of reduction
pub fn step(rules: &[(Term, Term)], t: &Term) -> Option<Term> {
    // Try β-reduction first
    match t {
        Term::Con(name, args) => match name.as_str() {
            "app" if args.len() == 2 => {
                if let Term::Con(fname, fargs) = &args[0] {
                    if fname == "lam" && fargs.len() == 1 {
                        return Some(subst(0, &args[1], &fargs[0]));
                    }
                }
                None
            }
            "fst" if args.len() == 1 => {
                if let Term::Con(pname, pargs) = &args[0] {
                    if pname == "pair" && pargs.len() == 2 {
                        return Some(pargs[0].clone());
                    }
                }
                None
            }
            "snd" if args.len() == 1 => {
                if let Term::Con(pname, pargs) = &args[0] {
                    if pname == "pair" && pargs.len() == 2 {
                        return Some(pargs[1].clone());
                    }
                }
                None
            }
            "letE" if args.len() == 3 => Some(subst(0, &args[1], &args[2])),
            "papp" if args.len() == 2 => {
                if let Term::Con(pname, pargs) = &args[0] {
                    if pname == "plam" && pargs.len() == 1 {
                        return Some(subst_dim(0, &args[1], &pargs[0]));
                    }
                    if pname == "refl" && pargs.len() == 1 {
                        return Some(pargs[0].clone());
                    }
                }
                None
            }
            "coe" if args.len() == 4 && args[0] == args[1] => Some(args[3].clone()),
            "hcom" if args.len() == 5 && args[0] == args[1] => Some(args[4].clone()),
            "vin" if args.len() == 3 => {
                match &args[0] {
                    Term::Con(n, a) if n == "dim0" && a.is_empty() => Some(args[1].clone()),
                    Term::Con(n, a) if n == "dim1" && a.is_empty() => Some(args[2].clone()),
                    _ => None,
                }
            }
            "cof_eq" | "cof_and" | "cof_or" => {
                let simplified = simplify_cof(t);
                if &simplified != t { Some(simplified) } else { None }
            }
            "lmax" => {
                let simplified = simplify_level(t);
                if &simplified != t { Some(simplified) } else { None }
            }
            "loop" if args.len() == 1 => {
                match &args[0] {
                    Term::Con(n, a) if (n == "dim0" || n == "dim1") && a.is_empty() => {
                        Some(Term::Con("base".into(), vec![]))
                    }
                    _ => None,
                }
            }
            "circleElim" if args.len() == 4 => {
                if let Term::Con(n, a) = &args[3] {
                    if n == "base" && a.is_empty() {
                        return Some(args[1].clone());
                    }
                }
                None
            }
            "natElim" if args.len() == 4 => {
                match &args[3] {
                    Term::Con(n, a) if n == "zero" && a.is_empty() => Some(args[1].clone()),
                    Term::Con(n, sargs) if n == "suc" && sargs.len() == 1 => {
                        let rec = Term::Con("natElim".into(), vec![
                            args[0].clone(), args[1].clone(), args[2].clone(), sargs[0].clone()
                        ]);
                        Some(Term::Con("app".into(), vec![
                            Term::Con("app".into(), vec![args[2].clone(), sargs[0].clone()]),
                            rec
                        ]))
                    }
                    _ => None,
                }
            }
            "subOut" if args.len() == 1 => {
                if let Term::Con(n, a) = &args[0] {
                    if n == "subIn" && a.len() == 1 {
                        return Some(a[0].clone());
                    }
                }
                None
            }
            _ => {
                // Try user rules
                for (lhs, rhs) in rules {
                    if let Some(bindings) = match_pattern(lhs, t) {
                        return Some(substitute(&bindings, rhs));
                    }
                }
                None
            }
        },
        _ => None,
    }
}

/// Normalize with fuel limit
pub fn normalize(mut fuel: usize, rules: &[(Term, Term)], t: &Term) -> Term {
    if fuel == 0 {
        return t.clone();
    }
    
    if let Some(t_new) = step(rules, t) {
        normalize(fuel - 1, rules, &t_new)
    } else {
        // Try normalizing subterms
        match t {
            Term::Con(name, args) => {
                let args_new: Vec<Term> = args.iter().map(|a| normalize(fuel, rules, a)).collect();
                if &args_new != args {
                    Term::Con(name.clone(), args_new)
                } else {
                    t.clone()
                }
            }
            _ => t.clone(),
        }
    }
}

//============================================================================
// Conversion Checking
//============================================================================

/// Check if two terms are convertible
pub fn conv(rules: &[(Term, Term)], fuel: usize, t1: &Term, t2: &Term) -> bool {
    let n1 = normalize(fuel, rules, t1);
    let n2 = normalize(fuel, rules, t2);
    n1 == n2
}

//============================================================================
// Tests
//============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_beta_reduction() {
        let lam_body = Term::ix(0);
        let lam = Term::Con("lam".into(), vec![lam_body]);
        let arg = Term::Lit("x".into());
        let app = Term::Con("app".into(), vec![lam, arg.clone()]);
        
        let result = step(&[], &app);
        assert_eq!(result, Some(arg));
    }

    #[test]
    fn test_shift() {
        let t = Term::ix(0);
        let shifted = shift(0, 1, &t);
        assert_eq!(shifted, Term::ix(1));
    }

    #[test]
    fn test_cof_simplify() {
        let cof = Term::Con("cof_eq".into(), vec![
            Term::Con("dim0".into(), vec![]),
            Term::Con("dim0".into(), vec![]),
        ]);
        let simplified = simplify_cof(&cof);
        assert_eq!(simplified, Term::Con("cof_top".into(), vec![]));
    }
}
