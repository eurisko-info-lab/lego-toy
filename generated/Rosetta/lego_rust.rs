// generated/Rosetta/lego_rust.rs
// What Lego.rosetta would generate via rosetta2rust
// This is a MANUAL rendering for verification

// From Lego.rosetta adt Iso → Rust struct with closures
pub struct Iso<A, B> {
    pub forward: Box<dyn Fn(&A) -> Option<B>>,
    pub backward: Box<dyn Fn(&B) -> Option<A>>,
}

impl<A: 'static, B: 'static> Iso<A, B> {
    pub fn new(
        forward: impl Fn(&A) -> Option<B> + 'static,
        backward: impl Fn(&B) -> Option<A> + 'static,
    ) -> Self {
        Iso {
            forward: Box::new(forward),
            backward: Box::new(backward),
        }
    }
}

// From: rewrite id: Iso.id ~> ...
pub fn iso_id<A: Clone + 'static>() -> Iso<A, A> {
    Iso::new(|a: &A| Some(a.clone()), |a: &A| Some(a.clone()))
}

// From: rewrite comp: (Iso.comp $f $g) ~> ...
// Note: Rust's ownership makes this tricky; using references
pub fn iso_comp<'a, A: 'static, B: 'static, C: 'static>(
    f: &'a Iso<A, B>,
    g: &'a Iso<B, C>,
) -> impl Fn(&A) -> Option<C> + 'a {
    move |a| (f.forward)(a).and_then(|b| (g.forward)(&b))
}

// From: rewrite sym: (Iso.sym $f) ~> ...
pub fn iso_sym<A: 'static, B: 'static>(f: Iso<A, B>) -> Iso<B, A> {
    Iso {
        forward: f.backward,
        backward: f.forward,
    }
}

// From Lego.rosetta adt Term → Rust enum
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Term {
    Var(String),
    Lit(String),
    Con(String, Vec<Term>),
}

impl Term {
    // From: rewrite atom: (Term.atom $s) ~> (Con $s Nil)
    pub fn atom(s: impl Into<String>) -> Self {
        Term::Con(s.into(), vec![])
    }

    // From: rewrite app: (Term.app $f $args) ~> (Con $f $args)
    pub fn app(f: impl Into<String>, args: Vec<Term>) -> Self {
        Term::Con(f.into(), args)
    }

    // From: rewrite matchPattern: ...
    pub fn match_pattern(&self, t: &Term) -> Option<Vec<(String, Term)>> {
        match (self, t) {
            (Term::Var(name), _) if name.starts_with('$') => {
                Some(vec![(name.clone(), t.clone())])
            }
            (Term::Var(n1), Term::Var(n2)) if n1 == n2 => Some(vec![]),
            (Term::Lit(a), Term::Lit(b)) if a == b => Some(vec![]),
            (Term::Con(c1, args1), Term::Con(c2, args2))
                if c1 == c2 && args1.len() == args2.len() =>
            {
                Self::match_list(args1, args2)
            }
            _ => None,
        }
    }

    fn match_list(pats: &[Term], terms: &[Term]) -> Option<Vec<(String, Term)>> {
        match (pats, terms) {
            ([], []) => Some(vec![]),
            ([p, ps @ ..], [t, ts @ ..]) => {
                let m1 = p.match_pattern(t)?;
                let m2 = Self::match_list(ps, ts)?;
                let mut result = m1;
                result.extend(m2);
                Some(result)
            }
            _ => None,
        }
    }

    // From: rewrite substVar, substLit, substCon
    pub fn substitute(&self, env: &[(String, Term)]) -> Term {
        match self {
            Term::Var(name) if name.starts_with('$') => env
                .iter()
                .find(|(k, _)| k == name)
                .map(|(_, v)| v.clone())
                .unwrap_or_else(|| self.clone()),
            Term::Var(_) => self.clone(),
            Term::Lit(s) => Term::Lit(s.clone()),
            Term::Con(c, args) => {
                Term::Con(c.clone(), args.iter().map(|a| a.substitute(env)).collect())
            }
        }
    }
}

// From Lego.rosetta adt Token → Rust enum
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Token {
    Ident(String),
    TLit(String),
    Sym(String),
    Number(String),
}

impl Token {
    // From: rewrite toString: (Token.toString (Ident $s)) ~> $s
    pub fn as_str(&self) -> &str {
        match self {
            Token::Ident(s) => s,
            Token::TLit(s) => s,
            Token::Sym(s) => s,
            Token::Number(s) => s,
        }
    }
}

// From Lego.rosetta adt GrammarExpr → Rust enum (recursive via Box)
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum GrammarF<A> {
    Empty,
    GLit(String),
    Ref(String),
    Seq(A, A),
    Alt(A, A),
    Star(A),
    Bind(String, A),
    Node(String, A),
    Cut(A),
    Ordered(A, A),
    Longest(Vec<A>),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct GrammarExpr(pub Box<GrammarF<GrammarExpr>>);

impl GrammarExpr {
    pub fn empty() -> Self {
        GrammarExpr(Box::new(GrammarF::Empty))
    }

    pub fn lit(s: impl Into<String>) -> Self {
        GrammarExpr(Box::new(GrammarF::GLit(s.into())))
    }

    pub fn r#ref(s: impl Into<String>) -> Self {
        GrammarExpr(Box::new(GrammarF::Ref(s.into())))
    }

    pub fn seq(a: GrammarExpr, b: GrammarExpr) -> Self {
        GrammarExpr(Box::new(GrammarF::Seq(a, b)))
    }

    pub fn alt(a: GrammarExpr, b: GrammarExpr) -> Self {
        GrammarExpr(Box::new(GrammarF::Alt(a, b)))
    }

    pub fn star(g: GrammarExpr) -> Self {
        GrammarExpr(Box::new(GrammarF::Star(g)))
    }

    // From: rewrite plus: (Grammar.plus $g) ~> (Seq $g (Star $g))
    pub fn plus(g: GrammarExpr) -> Self {
        Self::seq(g.clone(), Self::star(g))
    }

    // From: rewrite opt: (Grammar.opt $g) ~> (Alt $g Empty)
    pub fn opt(g: GrammarExpr) -> Self {
        Self::alt(g, Self::empty())
    }
}

// From Lego.rosetta adt Rule → Rust struct
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Rule {
    pub name: String,
    pub pattern: Term,
    pub template: Term,
}

impl Rule {
    pub fn new(name: impl Into<String>, pattern: Term, template: Term) -> Self {
        Rule {
            name: name.into(),
            pattern,
            template,
        }
    }

    // From: rewrite applyRule: (Rule.apply (MkRule $name $pat $repl) $term) ~> ...
    pub fn apply(&self, term: &Term) -> Option<Term> {
        self.pattern
            .match_pattern(term)
            .map(|bindings| self.template.substitute(&bindings))
    }
}

// From: rewrite applyFirst: (Rule.applyFirst Nil $term) ~> None
pub fn apply_first(rules: &[Rule], term: &Term) -> Option<Term> {
    rules.iter().find_map(|r| r.apply(term))
}

// From: rewrite normalize: (Rule.normalize $rules $term) ~> ...
pub fn normalize(rules: &[Rule], term: Term) -> Term {
    match apply_first(rules, &term) {
        None => term,
        Some(t) => normalize(rules, t),
    }
}

// From Lego.rosetta adt ParseResult → Rust enum
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ParseResult {
    Success { remaining: Vec<Token>, term: Term },
    Failure(String),
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_term_atom() {
        assert_eq!(Term::atom("foo"), Term::Con("foo".into(), vec![]));
    }

    #[test]
    fn test_pattern_match() {
        let pat = Term::Var("$x".into());
        let term = Term::Lit("hello".into());
        let result = pat.match_pattern(&term);
        assert_eq!(result, Some(vec![("$x".into(), Term::Lit("hello".into()))]));
    }

    #[test]
    fn test_substitute() {
        let term = Term::Var("$x".into());
        let env = vec![("$x".into(), Term::Lit("world".into()))];
        assert_eq!(term.substitute(&env), Term::Lit("world".into()));
    }

    #[test]
    fn test_rule_apply() {
        // Beta rule: (App (Lam $x . $body) $arg) -> (Subst $x $arg $body)
        let rule = Rule::new(
            "beta",
            Term::Con(
                "App".into(),
                vec![
                    Term::Con("Lam".into(), vec![Term::Var("$x".into()), Term::Var("$body".into())]),
                    Term::Var("$arg".into()),
                ],
            ),
            Term::Con(
                "Subst".into(),
                vec![Term::Var("$x".into()), Term::Var("$arg".into()), Term::Var("$body".into())],
            ),
        );

        let term = Term::Con(
            "App".into(),
            vec![
                Term::Con("Lam".into(), vec![Term::Lit("x".into()), Term::Var("y".into())]),
                Term::Lit("z".into()),
            ],
        );

        let result = rule.apply(&term);
        assert!(result.is_some());
    }

    #[test]
    fn test_grammar_plus() {
        let g = GrammarExpr::lit("a");
        let plus = GrammarExpr::plus(g);
        // plus(a) = seq(a, star(a))
        match &*plus.0 {
            GrammarF::Seq(_, _) => (),
            _ => panic!("Expected Seq"),
        }
    }
}
