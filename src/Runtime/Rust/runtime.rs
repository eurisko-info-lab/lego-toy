//! Lego Runtime Library for Rust
//!
//! This module provides the core runtime infrastructure for Lego-generated Rust code.
//! It includes:
//! - Core types (Term, GrammarExpr, etc.)
//! - Parsing engine (parse_grammar, lex_grammar)
//! - IO operations (read_file, write_file)
//! - Memoization (HashMap-based Packrat)
//!
//! Generated Rosetta code should: use lego_runtime::*;

use std::collections::HashMap;
use std::fs;
use std::path::Path;

//============================================================================
// Core Types
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

    pub fn unit() -> Self {
        Term::Con("unit".into(), vec![])
    }
}

/// Grammar expression algebra
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum GrammarExpr {
    Empty,
    Lit(String),
    Ref(String),
    Seq(Box<GrammarExpr>, Box<GrammarExpr>),
    Alt(Box<GrammarExpr>, Box<GrammarExpr>),
    Star(Box<GrammarExpr>),
    Plus(Box<GrammarExpr>),
    Opt(Box<GrammarExpr>),
    Node(String, Box<GrammarExpr>),
}

impl GrammarExpr {
    pub fn seq(g1: GrammarExpr, g2: GrammarExpr) -> Self {
        GrammarExpr::Seq(Box::new(g1), Box::new(g2))
    }

    pub fn alt(g1: GrammarExpr, g2: GrammarExpr) -> Self {
        GrammarExpr::Alt(Box::new(g1), Box::new(g2))
    }

    pub fn star(g: GrammarExpr) -> Self {
        GrammarExpr::Star(Box::new(g))
    }

    pub fn plus(g: GrammarExpr) -> Self {
        GrammarExpr::Plus(Box::new(g))
    }

    pub fn opt(g: GrammarExpr) -> Self {
        GrammarExpr::Opt(Box::new(g))
    }

    pub fn node(name: impl Into<String>, g: GrammarExpr) -> Self {
        GrammarExpr::Node(name.into(), Box::new(g))
    }
}

/// Grammar production: (name, grammar, annotation)
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Production {
    pub name: String,
    pub grammar: GrammarExpr,
    pub annotation: String,
}

impl Production {
    pub fn new(name: impl Into<String>, grammar: GrammarExpr) -> Self {
        Production {
            name: name.into(),
            grammar,
            annotation: String::new(),
        }
    }

    pub fn with_annotation(name: impl Into<String>, grammar: GrammarExpr, annotation: impl Into<String>) -> Self {
        Production {
            name: name.into(),
            grammar,
            annotation: annotation.into(),
        }
    }
}

/// Production list type
pub type Productions = Vec<Production>;

/// Rewrite rule: name, lhs pattern, rhs template
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Rule {
    pub name: String,
    pub lhs: Term,
    pub rhs: Term,
}

impl Rule {
    pub fn new(name: impl Into<String>, lhs: Term, rhs: Term) -> Self {
        Rule {
            name: name.into(),
            lhs,
            rhs,
        }
    }
}

//============================================================================
// Token Types
//============================================================================

/// Token types for lexing
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Token {
    Lit(String),      // String literal "..."
    Ident(String),    // Identifier
    Sym(String),      // Symbol/operator
    Number(String),   // Numeric literal
}

impl std::fmt::Display for Token {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Token::Lit(s) => write!(f, "\"{}\"", s),
            Token::Ident(s) => write!(f, "{}", s),
            Token::Sym(s) => write!(f, "{}", s),
            Token::Number(s) => write!(f, "{}", s),
        }
    }
}

//============================================================================
// Parse State
//============================================================================

/// Packrat memoization entry
#[derive(Debug, Clone)]
pub struct MemoEntry {
    pub result: Option<(Term, usize, Vec<(String, Term)>)>,
}

/// Parse state
#[derive(Debug, Clone)]
pub struct ParseState {
    pub tokens: Vec<Token>,
    pub pos: usize,
    pub memo: HashMap<(usize, String), MemoEntry>,
    pub binds: Vec<(String, Term)>,
}

impl ParseState {
    pub fn new(tokens: Vec<Token>) -> Self {
        ParseState {
            tokens,
            pos: 0,
            memo: HashMap::with_capacity(256),
            binds: Vec::new(),
        }
    }

    pub fn current_token(&self) -> Option<&Token> {
        self.tokens.get(self.pos)
    }

    pub fn advance(&mut self) {
        if self.pos < self.tokens.len() {
            self.pos += 1;
        }
    }
}

/// Parse result: (parsed term, new state) or failure
pub type ParseResult = (Option<(Term, ParseState)>, HashMap<(usize, String), MemoEntry>);

//============================================================================
// Core Parsing Engine
//============================================================================

/// Find a production by name
pub fn find_production(prods: &Productions, name: &str) -> Option<GrammarExpr> {
    prods.iter()
        .find(|p| p.name == name)
        .map(|p| p.grammar.clone())
}

/// Find all productions with the same base name and combine with alt
pub fn find_all_productions(prods: &Productions, name: &str) -> Option<GrammarExpr> {
    let matching: Vec<_> = prods.iter()
        .filter(|p| p.name == name)
        .collect();

    match matching.as_slice() {
        [] => None,
        [p] => Some(p.grammar.clone()),
        [p, ps @ ..] => {
            let mut result = p.grammar.clone();
            for prod in ps {
                result = GrammarExpr::alt(result, prod.grammar.clone());
            }
            Some(result)
        }
    }
}

/// Combine two terms in sequence
pub fn combine_seq(t1: Term, t2: Term) -> Term {
    match (&t1, &t2) {
        (Term::Con(n, args), _) if n == "unit" && args.is_empty() => t2,
        (_, Term::Con(n, args)) if n == "unit" && args.is_empty() => t1,
        (Term::Con(n, args), _) if n == "seq" => {
            let mut new_args = args.clone();
            new_args.push(t2);
            Term::Con("seq".into(), new_args)
        }
        (_, Term::Con(n, args)) if n == "seq" => {
            let mut new_args = vec![t1];
            new_args.extend(args.clone());
            Term::Con("seq".into(), new_args)
        }
        _ => Term::Con("seq".into(), vec![t1, t2]),
    }
}

/// Wrap term in a constructor node
pub fn wrap_node(name: &str, t: Term) -> Term {
    Term::Con(name.into(), vec![t])
}

/// Parse grammar expression (main parsing engine)
/// Uses fuel for termination and Packrat memoization for efficiency
pub fn parse_grammar(
    fuel: usize,
    prods: &Productions,
    g: &GrammarExpr,
    st: ParseState,
) -> ParseResult {
    if fuel == 0 {
        return (None, st.memo);
    }

    match g {
        GrammarExpr::Empty => (Some((Term::unit(), st.clone())), st.memo),

        GrammarExpr::Lit(s) => {
            if let Some(tok) = st.tokens.get(st.pos) {
                let matches = match tok {
                    Token::Lit(l) => l == s,
                    Token::Sym(l) => l == s,
                    Token::Ident(l) => l == s,
                    _ => false,
                };
                if matches {
                    let mut new_st = st.clone();
                    new_st.pos += 1;
                    (Some((Term::Lit(s.clone()), new_st)), st.memo)
                } else {
                    (None, st.memo)
                }
            } else {
                (None, st.memo)
            }
        }

        GrammarExpr::Ref(name) => {
            // Handle built-in token types (TOKEN.*)
            if name.starts_with("TOKEN.") {
                let tok_type = &name[6..];
                if let Some(tok) = st.tokens.get(st.pos) {
                    let result = match (tok_type, tok) {
                        ("ident", Token::Ident(s)) => Some(Term::Var(s.clone())),
                        ("string", Token::Lit(s)) if s.starts_with('"') => Some(Term::Lit(s.clone())),
                        ("number", Token::Number(s)) => Some(Term::Lit(s.clone())),
                        ("sym", Token::Sym(s)) => Some(Term::Var(s.clone())),
                        _ => None,
                    };
                    if let Some(term) = result {
                        let mut new_st = st.clone();
                        new_st.pos += 1;
                        return (Some((term, new_st)), st.memo);
                    }
                }
                return (None, st.memo);
            }

            // Packrat memoization for production references
            let key = (st.pos, name.clone());
            if let Some(entry) = st.memo.get(&key) {
                if let Some((term, end_pos, new_binds)) = &entry.result {
                    let token_count = end_pos - st.pos;
                    let mut new_st = st.clone();
                    new_st.pos = *end_pos;
                    new_st.binds = new_binds.clone();
                    return (Some((term.clone(), new_st)), st.memo);
                } else {
                    return (None, st.memo);
                }
            }

            if let Some(g2) = find_all_productions(prods, name) {
                let (result, mut memo) = parse_grammar(fuel - 1, prods, &g2, st.clone());
                match result {
                    Some((term, st2)) => {
                        let entry = MemoEntry {
                            result: Some((term.clone(), st2.pos, st2.binds.clone())),
                        };
                        memo.insert(key, entry);
                        let mut new_st = st2;
                        new_st.memo = memo.clone();
                        (Some((term, new_st)), memo)
                    }
                    None => {
                        let entry = MemoEntry { result: None };
                        memo.insert(key, entry);
                        (None, memo)
                    }
                }
            } else {
                (None, st.memo)
            }
        }

        GrammarExpr::Seq(g1, g2) => {
            let (r1, memo1) = parse_grammar(fuel - 1, prods, g1, st);
            match r1 {
                Some((t1, mut st1)) => {
                    st1.memo = memo1;
                    let (r2, memo2) = parse_grammar(fuel - 1, prods, g2, st1);
                    match r2 {
                        Some((t2, st2)) => (Some((combine_seq(t1, t2), st2)), memo2),
                        None => (None, memo2),
                    }
                }
                None => (None, memo1),
            }
        }

        GrammarExpr::Alt(g1, g2) => {
            let (r1, memo1) = parse_grammar(fuel - 1, prods, g1, st.clone());
            match r1 {
                Some(result) => (Some(result), memo1),
                None => {
                    let mut st2 = st;
                    st2.memo = memo1;
                    parse_grammar(fuel - 1, prods, g2, st2)
                }
            }
        }

        GrammarExpr::Star(g2) => {
            let mut acc = Vec::new();
            let mut curr_st = st;
            let mut curr_memo = curr_st.memo.clone();
            let mut loop_fuel = fuel - 1;

            while loop_fuel > 0 {
                curr_st.memo = curr_memo.clone();
                let (r, memo2) = parse_grammar(fuel - 1, prods, g2, curr_st.clone());
                match r {
                    Some((t, st2)) => {
                        acc.push(t);
                        curr_st = st2;
                        curr_memo = memo2;
                        loop_fuel -= 1;
                    }
                    None => {
                        curr_memo = memo2;
                        break;
                    }
                }
            }

            let result = if acc.is_empty() {
                Term::unit()
            } else {
                Term::Con("seq".into(), acc)
            };
            curr_st.memo = curr_memo.clone();
            (Some((result, curr_st)), curr_memo)
        }

        GrammarExpr::Plus(g2) => {
            let (first, memo1) = parse_grammar(fuel - 1, prods, g2, st);
            match first {
                None => (None, memo1),
                Some((t, mut st2)) => {
                    st2.memo = memo1;
                    let (rest, memo2) = parse_grammar(fuel - 1, prods, &GrammarExpr::star((**g2).clone()), st2);
                    match rest {
                        Some((Term::Con(n, args), st3)) if n == "unit" && args.is_empty() => {
                            (Some((t, st3)), memo2)
                        }
                        Some((ts, st3)) => (Some((combine_seq(t, ts), st3)), memo2),
                        None => (Some((t, st2.clone())), memo2),
                    }
                }
            }
        }

        GrammarExpr::Opt(g2) => {
            let (r, memo2) = parse_grammar(fuel - 1, prods, g2, st.clone());
            match r {
                Some(result) => (Some(result), memo2),
                None => {
                    let mut new_st = st;
                    new_st.memo = memo2.clone();
                    (Some((Term::unit(), new_st)), memo2)
                }
            }
        }

        GrammarExpr::Node(name, g2) => {
            let (r, memo2) = parse_grammar(fuel - 1, prods, g2, st);
            match r {
                Some((t, st2)) => (Some((wrap_node(name, t), st2)), memo2),
                None => (None, memo2),
            }
        }
    }
}

//============================================================================
// IO Operations
//============================================================================

/// Read file contents
pub fn read_file<P: AsRef<Path>>(path: P) -> std::io::Result<String> {
    fs::read_to_string(path)
}

/// Write file contents
pub fn write_file<P: AsRef<Path>>(path: P, content: &str) -> std::io::Result<()> {
    fs::write(path, content)
}

/// Check if file exists
pub fn file_exists<P: AsRef<Path>>(path: P) -> bool {
    path.as_ref().exists()
}

//============================================================================
// Term Utilities
//============================================================================

/// Pattern match helper
pub fn match_pattern(pattern: &Term, t: &Term) -> Option<Vec<(String, Term)>> {
    match (pattern, t) {
        (Term::Var(x), t) => Some(vec![(x.clone(), t.clone())]),
        (Term::Lit(s1), Term::Lit(s2)) if s1 == s2 => Some(vec![]),
        (Term::Con(n1, args1), Term::Con(n2, args2))
            if n1 == n2 && args1.len() == args2.len() =>
        {
            let mut all_binds = Vec::new();
            for (p, t) in args1.iter().zip(args2.iter()) {
                match match_pattern(p, t) {
                    Some(binds) => all_binds.extend(binds),
                    None => return None,
                }
            }
            Some(all_binds)
        }
        _ => None,
    }
}

/// Substitute bindings in a term
pub fn substitute(binds: &[(String, Term)], t: &Term) -> Term {
    match t {
        Term::Var(x) => {
            binds.iter()
                .find(|(name, _)| name == x)
                .map(|(_, val)| val.clone())
                .unwrap_or_else(|| t.clone())
        }
        Term::Lit(s) => Term::Lit(s.clone()),
        Term::Con(n, args) => {
            Term::Con(n.clone(), args.iter().map(|a| substitute(binds, a)).collect())
        }
    }
}

/// Apply a single rewrite rule
pub fn apply_rule(rule: &Rule, t: &Term) -> Option<Term> {
    match_pattern(&rule.lhs, t).map(|binds| substitute(&binds, &rule.rhs))
}

/// Normalize term using rewrite rules
pub fn normalize(rules: &[Rule], t: &Term, fuel: usize) -> Term {
    if fuel == 0 {
        return t.clone();
    }

    // Try each rule
    for rule in rules {
        if let Some(t2) = apply_rule(rule, t) {
            return normalize(rules, &t2, fuel - 1);
        }
    }

    // Recursively normalize children
    match t {
        Term::Con(n, args) => {
            Term::Con(n.clone(), args.iter().map(|a| normalize(rules, a, fuel - 1)).collect())
        }
        other => other.clone(),
    }
}

//============================================================================
// Tests
//============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_term_construction() {
        let t = Term::con("add", vec![Term::lit("1"), Term::lit("2")]);
        assert_eq!(t, Term::Con("add".into(), vec![Term::Lit("1".into()), Term::Lit("2".into())]));
    }

    #[test]
    fn test_pattern_match() {
        let pattern = Term::con("add", vec![Term::var("x"), Term::var("y")]);
        let term = Term::con("add", vec![Term::lit("1"), Term::lit("2")]);

        let result = match_pattern(&pattern, &term);
        assert!(result.is_some());

        let binds = result.unwrap();
        assert_eq!(binds.len(), 2);
    }

    #[test]
    fn test_substitute() {
        let binds = vec![
            ("x".into(), Term::lit("1")),
            ("y".into(), Term::lit("2")),
        ];
        let template = Term::con("result", vec![Term::var("x"), Term::var("y")]);

        let result = substitute(&binds, &template);
        assert_eq!(result, Term::con("result", vec![Term::lit("1"), Term::lit("2")]));
    }
}
