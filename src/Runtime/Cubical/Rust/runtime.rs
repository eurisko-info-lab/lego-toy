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

/// A test case: name, input term, expected output
#[derive(Debug, Clone)]
pub struct TestCase {
    pub name: String,
    pub input: Term,
    pub expected: Term,
}

/// Result of running a test
#[derive(Debug)]
pub enum TestResult {
    Pass(String),
    Fail(String, Term, Term),  // name, got, expected
}

/// Run a single test case
pub fn run_test(rules: &[(Term, Term)], fuel: usize, tc: &TestCase) -> TestResult {
    let result = normalize(fuel, rules, &tc.input);
    if result == tc.expected {
        TestResult::Pass(tc.name.clone())
    } else {
        TestResult::Fail(tc.name.clone(), result, tc.expected.clone())
    }
}

/// Run all test cases
pub fn run_tests(rules: &[(Term, Term)], fuel: usize, tests: &[TestCase]) -> Vec<TestResult> {
    tests.iter().map(|tc| run_test(rules, fuel, tc)).collect()
}

/// Count passed and failed tests
pub fn count_results(results: &[TestResult]) -> (usize, usize) {
    let mut passed = 0;
    let mut failed = 0;
    for r in results {
        match r {
            TestResult::Pass(_) => passed += 1,
            TestResult::Fail(_, _, _) => failed += 1,
        }
    }
    (passed, failed)
}

/// Print test results
pub fn print_results(results: &[TestResult]) {
    let mut passed = 0;
    let mut failed = 0;
    for r in results {
        match r {
            TestResult::Pass(name) => {
                println!("✓ {}", name);
                passed += 1;
            }
            TestResult::Fail(name, got, expected) => {
                println!("✗ {}", name);
                println!("  Expected: {:?}", expected);
                println!("  Got:      {:?}", got);
                failed += 1;
            }
        }
    }
    println!();
    println!("Results: {}/{} passed", passed, passed + failed);
}

/// Standard Cubical tests
pub fn standard_tests() -> Vec<TestCase> {
    vec![
        // Cofibration tests
        TestCase {
            name: "eq-refl".into(),
            input: Term::con("cof_eq", vec![Term::con("dim0", vec![]), Term::con("dim0", vec![])]),
            expected: Term::con("cof_top", vec![]),
        },
        TestCase {
            name: "eq-01".into(),
            input: Term::con("cof_eq", vec![Term::con("dim0", vec![]), Term::con("dim1", vec![])]),
            expected: Term::con("cof_bot", vec![]),
        },
        TestCase {
            name: "eq-10".into(),
            input: Term::con("cof_eq", vec![Term::con("dim1", vec![]), Term::con("dim0", vec![])]),
            expected: Term::con("cof_bot", vec![]),
        },
        TestCase {
            name: "and-top".into(),
            input: Term::con("cof_and", vec![Term::con("cof_top", vec![]), Term::con("cof_top", vec![])]),
            expected: Term::con("cof_top", vec![]),
        },
        TestCase {
            name: "and-bot".into(),
            input: Term::con("cof_and", vec![Term::con("cof_bot", vec![]), Term::con("cof_top", vec![])]),
            expected: Term::con("cof_bot", vec![]),
        },
        TestCase {
            name: "or-top".into(),
            input: Term::con("cof_or", vec![Term::con("cof_top", vec![]), Term::con("cof_bot", vec![])]),
            expected: Term::con("cof_top", vec![]),
        },
        TestCase {
            name: "or-bot".into(),
            input: Term::con("cof_or", vec![Term::con("cof_bot", vec![]), Term::con("cof_bot", vec![])]),
            expected: Term::con("cof_bot", vec![]),
        },
        
        // Level tests
        TestCase {
            name: "max-idem".into(),
            input: Term::con("lmax", vec![
                Term::con("lsuc", vec![Term::con("lzero", vec![])]),
                Term::con("lsuc", vec![Term::con("lzero", vec![])])
            ]),
            expected: Term::con("lsuc", vec![Term::con("lzero", vec![])]),
        },
        TestCase {
            name: "max-zero-l".into(),
            input: Term::con("lmax", vec![
                Term::con("lzero", vec![]),
                Term::con("lsuc", vec![Term::con("lzero", vec![])])
            ]),
            expected: Term::con("lsuc", vec![Term::con("lzero", vec![])]),
        },
        
        // Beta reduction tests
        TestCase {
            name: "beta".into(),
            input: Term::con("app", vec![
                Term::con("lam", vec![Term::con("ix", vec![Term::lit("0")])]),
                Term::lit("x")
            ]),
            expected: Term::lit("x"),
        },
        TestCase {
            name: "fst".into(),
            input: Term::con("fst", vec![Term::con("pair", vec![Term::lit("a"), Term::lit("b")])]),
            expected: Term::lit("a"),
        },
        TestCase {
            name: "snd".into(),
            input: Term::con("snd", vec![Term::con("pair", vec![Term::lit("a"), Term::lit("b")])]),
            expected: Term::lit("b"),
        },
        
        // Path tests
        TestCase {
            name: "refl-app".into(),
            input: Term::con("papp", vec![
                Term::con("refl", vec![Term::lit("a")]),
                Term::con("dim0", vec![])
            ]),
            expected: Term::lit("a"),
        },
        
        // Kan operation tests
        TestCase {
            name: "coe-refl".into(),
            input: Term::con("coe", vec![
                Term::con("dim0", vec![]),
                Term::con("dim0", vec![]),
                Term::con("univ", vec![Term::con("lzero", vec![])]),
                Term::lit("A")
            ]),
            expected: Term::lit("A"),
        },
        
        // V-type tests
        TestCase {
            name: "vin-0".into(),
            input: Term::con("vin", vec![Term::con("dim0", vec![]), Term::lit("a"), Term::lit("b")]),
            expected: Term::lit("a"),
        },
        TestCase {
            name: "vin-1".into(),
            input: Term::con("vin", vec![Term::con("dim1", vec![]), Term::lit("a"), Term::lit("b")]),
            expected: Term::lit("b"),
        },
        
        // Natural number tests
        TestCase {
            name: "nat-elim-zero".into(),
            input: Term::con("natElim", vec![
                Term::var("P"),
                Term::var("z"),
                Term::var("s"),
                Term::con("zero", vec![])
            ]),
            expected: Term::var("z"),
        },
        
        // Circle tests
        TestCase {
            name: "loop-0".into(),
            input: Term::con("loop", vec![Term::con("dim0", vec![])]),
            expected: Term::con("base", vec![]),
        },
        TestCase {
            name: "loop-1".into(),
            input: Term::con("loop", vec![Term::con("dim1", vec![])]),
            expected: Term::con("base", vec![]),
        },
        TestCase {
            name: "circle-elim-base".into(),
            input: Term::con("circleElim", vec![
                Term::var("P"),
                Term::var("b"),
                Term::var("l"),
                Term::con("base", vec![])
            ]),
            expected: Term::var("b"),
        },
        
        // Subtype tests
        TestCase {
            name: "sub-beta".into(),
            input: Term::con("subOut", vec![Term::con("subIn", vec![Term::lit("x")])]),
            expected: Term::lit("x"),
        },
    ]
}

/// Run standard Cubical tests
pub fn run_standard_tests() {
    println!("Running Cubical Standard Tests (Rust Runtime)");
    println!("==============================================");
    let tests = standard_tests();
    let results = run_tests(&[], 1000, &tests);
    print_results(&results);
}

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

    #[test]
    fn test_all_standard_cubical_tests() {
        let tests = standard_tests();
        let results = run_tests(&[], 1000, &tests);
        let (passed, failed) = count_results(&results);
        
        // Print failures for debugging
        for r in &results {
            if let TestResult::Fail(name, got, expected) = r {
                println!("FAIL: {} - got {:?}, expected {:?}", name, got, expected);
            }
        }
        
        assert_eq!(failed, 0, "Expected all tests to pass, but {} failed", failed);
        println!("All {} standard Cubical tests passed!", passed);
    }
}
