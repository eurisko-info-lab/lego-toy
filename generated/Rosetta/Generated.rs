#![allow(dead_code)]
#![allow(unused_variables)]

// Helper function to extract argument from Term (returns reference into boxed term)
fn get_arg(t: &Term, i: usize) -> &Term {
    match t {
        Term::Con(_, args) => &*args[i],
        _ => panic!("get_arg called on non-Con")
    }
}

#[derive(Clone)]
pub enum Iso<A, B> {
  MkIso( fn(A) -> Option<B> ,  fn(B) -> Option<A>),
  }

#[derive(Clone)]
pub enum Term {
  Var( String),
  Lit( String),
  Con( String ,  Vec<Box<Term>>),
  }

#[derive(Clone)]
pub enum AST<A> {
  MkAST( fn(String) -> A ,  fn(String) -> A ,  fn(String) -> fn(Vec<A>) -> A),
  }

#[derive(Clone)]
pub enum PieceLevel {
  TokenLevel ,
  SyntaxLevel ,
  }

#[derive(Clone)]
pub enum Rule {
  MkRule( String ,  Term ,  Term),
  }

#[derive(Clone)]
pub enum TypeRule {
  MkTypeRule( String ,  Term ,  Term),
  }

#[derive(Clone)]
pub enum GrammarExpr {
  GEmpty ,
  GLit( String),
  GRef( String),
  GSeq( Box<GrammarExpr> ,  Box<GrammarExpr>),
  GAlt( Box<GrammarExpr> ,  Box<GrammarExpr>),
  GStar( Box<GrammarExpr>),
  GPlus( Box<GrammarExpr>),
  GOpt( Box<GrammarExpr>),
  GNot( Box<GrammarExpr>),
  GAnd( Box<GrammarExpr>),
  GCon( String ,  Box<GrammarExpr>),
  }

#[derive(Clone)]
pub enum GrammarProduction {
  MkGrammarProduction( String ,  GrammarExpr ,  String),
  }

#[derive(Clone)]
pub enum Piece {
  MkPiece( String ,  PieceLevel ,  Vec<GrammarProduction> ,  Vec<Rule> ,  Vec<TypeRule>),
  }

#[derive(Clone)]
pub enum Language {
  MkLanguage( String ,  Vec<Piece>),
  }

#[derive(Clone)]
pub enum SourceLoc {
  MkSourceLoc( String ,  i64 ,  i64 ,  i64),
  UnknownLoc ,
  }

#[derive(Clone)]
pub enum Severity {
  SevError ,
  SevWarning ,
  SevInfo ,
  }

#[derive(Clone)]
pub enum Binding {
  MkBinding( String ,  Term ,  Option<Term> ,  SourceLoc),
  }

#[derive(Clone)]
pub enum TypeError {
  MkTypeError( String ,  SourceLoc ,  Severity ,  Option<Term> ,  Option<Term> ,  Vec<Binding>),
  }

#[derive(Clone)]
pub enum EvalResult {
  EvalOk( Term ,  Vec<TypeError>),
  EvalFailed( Vec<TypeError>),
  }

#[derive(Clone)]
pub enum Context {
  EmptyContext ,
  ContextCons( Binding ,  Box<Context>),
  }

#[derive(Clone)]
pub enum VarContext {
  EmptyVarContext ,
  VarContextCons( String ,  Box<VarContext>),
  }

#[derive(Clone)]
pub enum EvalEnv {
  MkEvalEnv( AttrEnv ,  Context ,  VarContext ,  Vec<TypeError> ,  SourceLoc),
  }

#[derive(Clone)]
pub enum Mode {
  Infer ,
  Check ,
  }

#[derive(Clone)]
pub enum AttrFlow {
  Syn ,
  Inh ,
  SynInh ,
  }

#[derive(Clone)]
pub enum AttrPath {
  Empty ,
  PathCon( String ,  Box<AttrPath>),
  }

#[derive(Clone)]
pub enum AttrRef {
  MkAttrRef( AttrPath ,  String),
  }

#[derive(Clone)]
pub enum AttrRule {
  MkAttrRule( String ,  AttrPath ,  Term),
  }

#[derive(Clone)]
pub enum AttrDef {
  MkAttrDef( String ,  AttrFlow ,  Option<Term> ,  Vec<AttrRule>),
  }

#[derive(Clone)]
pub enum AttrEnv {
  EmptyAttrEnv ,
  AttrEnvCons( AttrPath ,  String ,  Term ,  Box<AttrEnv>),
  }

#[derive(Clone)]
pub enum AttrLanguage {
  MkAttrLanguage( String ,  Vec<GrammarProduction> ,  Vec<AttrDef>),
  }

#[derive(Clone)]
pub enum Token {
  TokIdent( String),
  TokString( String),
  TokInt( i64),
  TokSym( String),
  TokEOF ,
  }

#[derive(Clone)]
pub enum ParseState {
  MkState( Vec<Token> ,  i64),
  }

#[derive(Clone)]
pub enum ParseResult {
  ParseOk( Term ,  ParseState),
  ParseFail( String ,  ParseState),
  }

#[derive(Clone)]
pub enum PrintResult {
  PrintOk( Vec<Token>),
  PrintFail( String),
  }

#[derive(Clone)]
pub enum Env {
  EnvEmpty ,
  Bind( String ,  Term ,  Box<Env>),
  }

#[derive(Clone)]
pub enum Symbol {
  Terminal( String),
  NonTerminal( String),
  Epsilon ,
  }

#[derive(Clone)]
pub enum Production {
  MkProd( String ,  Vec<Symbol> ,  String),
  }

#[derive(Clone)]
pub enum Grammar {
  MkGrammar( Vec<Production>),
  }

#[derive(Clone)]
pub enum Parser {
  MkParser( Grammar ,  fn(String) -> Option<Term>),
  }

#[derive(Clone)]
pub enum Printer {
  MkPrinter( Grammar ,  fn(Term) -> Option<String>),
  }

#[derive(Clone)]
pub enum LoadedGrammar {
  LoadedGrammarMkGrammar( Vec<Production> ,  Vec<Production> ,  Vec<String> ,  String),
  }

#[derive(Clone)]
pub enum Runtime {
  MkRuntime( LoadedGrammar ,  Vec<Rule>),
  }

#[derive(Clone)]
pub enum ValidationSeverity {
  ValError ,
  ValWarning ,
  ValInfo ,
  }

#[derive(Clone)]
pub enum ValidationError {
  UndefinedProduction( String ,  String),
  DuplicateProduction( String),
  UnboundVariable( String ,  String),
  CircularImport( String),
  InvalidSyntax( String ,  String),
  }

#[derive(Clone)]
pub enum ValidationWarning {
  ConflictingRules( String ,  String ,  String),
  DirectLeftRecursion( String),
  IndirectLeftRecursion( Vec<String>),
  UnusedProduction( String),
  ShadowedProduction( String ,  String),
  AmbiguousGrammar( String ,  String),
  MissingCut( String ,  String),
  RuleCycle( Vec<String>),
  UnreachableAlt( String ,  i64),
  RedundantAlt( String ,  i64 ,  i64),
  }

#[derive(Clone)]
pub enum ValidationResult {
  MkValidationResult( Vec<ValidationError> ,  Vec<ValidationWarning>),
  }

pub fn iso_id(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "isoId" && a.is_empty()) {
        Some(Term::Con("MkIso".to_string(), vec![Box::new(Term::Con("Lam".to_string(), vec![Box::new(Term::Con("binder".to_string(), vec![Box::new(Term::Lit("x".to_string())), Box::new(Term::Con("Some".to_string(), vec![Box::new(Term::Con("x".to_string(), vec![]))]))]))])), Box::new(Term::Con("Lam".to_string(), vec![Box::new(Term::Con("binder".to_string(), vec![Box::new(Term::Lit("x".to_string())), Box::new(Term::Con("Some".to_string(), vec![Box::new(Term::Con("x".to_string(), vec![]))]))]))]))]))
    } else {
        None
    }
}

pub fn iso_comp(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "comp" && a.len() == 2) && matches!(get_arg(t, 0), Term::Con(ref n, ref a) if n == "MkIso" && a.len() == 2) && matches!(get_arg(t, 1), Term::Con(ref n, ref a) if n == "MkIso" && a.len() == 2) {
    let f1 = get_arg(get_arg(t, 0), 0).clone();
    let b1 = get_arg(get_arg(t, 0), 1).clone();
    let f2 = get_arg(get_arg(t, 1), 0).clone();
    let b2 = get_arg(get_arg(t, 1), 1).clone();
        Some(Term::Con("MkIso".to_string(), vec![Box::new(Term::Con("Lam".to_string(), vec![Box::new(Term::Con("binder".to_string(), vec![Box::new(Term::Lit("a".to_string())), Box::new(Term::Con("bind".to_string(), vec![Box::new(Term::Con("App".to_string(), vec![Box::new(f1.clone()), Box::new(Term::Con("a".to_string(), vec![]))])), Box::new(Term::Con("b".to_string(), vec![])), Box::new(Term::Con("App".to_string(), vec![Box::new(f2.clone()), Box::new(Term::Con("b".to_string(), vec![]))]))]))]))])), Box::new(Term::Con("Lam".to_string(), vec![Box::new(Term::Con("binder".to_string(), vec![Box::new(Term::Lit("c".to_string())), Box::new(Term::Con("bind".to_string(), vec![Box::new(Term::Con("App".to_string(), vec![Box::new(b2.clone()), Box::new(Term::Con("c".to_string(), vec![]))])), Box::new(Term::Con("b".to_string(), vec![])), Box::new(Term::Con("App".to_string(), vec![Box::new(b1.clone()), Box::new(Term::Con("b".to_string(), vec![]))]))]))]))]))]))
    } else {
        None
    }
}

pub fn iso_sym(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "sym" && a.len() == 1) && matches!(get_arg(t, 0), Term::Con(ref n, ref a) if n == "MkIso" && a.len() == 2) {
    let fwd = get_arg(get_arg(t, 0), 0).clone();
    let bwd = get_arg(get_arg(t, 0), 1).clone();
        Some(Term::Con("MkIso".to_string(), vec![Box::new(bwd.clone()), Box::new(fwd.clone())]))
    } else {
        None
    }
}

pub fn iso_forward(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "forward" && a.len() == 2) && matches!(get_arg(t, 0), Term::Con(ref n, ref a) if n == "MkIso" && a.len() == 2) {
    let fwd = get_arg(get_arg(t, 0), 0).clone();
    let bwd = get_arg(get_arg(t, 0), 1).clone();
    let x = get_arg(t, 1).clone();
        Some(Term::Con("App".to_string(), vec![Box::new(fwd.clone()), Box::new(x.clone())]))
    } else {
        None
    }
}

pub fn iso_backward(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "backward" && a.len() == 2) && matches!(get_arg(t, 0), Term::Con(ref n, ref a) if n == "MkIso" && a.len() == 2) {
    let fwd = get_arg(get_arg(t, 0), 0).clone();
    let bwd = get_arg(get_arg(t, 0), 1).clone();
    let x = get_arg(t, 1).clone();
        Some(Term::Con("App".to_string(), vec![Box::new(bwd.clone()), Box::new(x.clone())]))
    } else {
        None
    }
}

pub fn iso_par(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "par" && a.len() == 2) && matches!(get_arg(t, 0), Term::Con(ref n, ref a) if n == "MkIso" && a.len() == 2) && matches!(get_arg(t, 1), Term::Con(ref n, ref a) if n == "MkIso" && a.len() == 2) {
    let f1 = get_arg(get_arg(t, 0), 0).clone();
    let b1 = get_arg(get_arg(t, 0), 1).clone();
    let f2 = get_arg(get_arg(t, 1), 0).clone();
    let b2 = get_arg(get_arg(t, 1), 1).clone();
        Some(Term::Con("MkIso".to_string(), vec![Box::new(Term::Con("Lam".to_string(), vec![Box::new(Term::Con("binder".to_string(), vec![Box::new(Term::Lit("p".to_string())), Box::new(Term::Con("bind".to_string(), vec![Box::new(Term::Con("App".to_string(), vec![Box::new(f1.clone()), Box::new(Term::Con("Fst".to_string(), vec![Box::new(Term::Con("p".to_string(), vec![]))]))])), Box::new(Term::Con("x".to_string(), vec![])), Box::new(Term::Con("bind".to_string(), vec![Box::new(Term::Con("App".to_string(), vec![Box::new(f2.clone()), Box::new(Term::Con("Snd".to_string(), vec![Box::new(Term::Con("p".to_string(), vec![]))]))])), Box::new(Term::Con("y".to_string(), vec![])), Box::new(Term::Con("Some".to_string(), vec![Box::new(Term::Con("Pair".to_string(), vec![Box::new(Term::Con("x".to_string(), vec![])), Box::new(Term::Con("y".to_string(), vec![]))]))]))]))]))]))])), Box::new(Term::Con("Lam".to_string(), vec![Box::new(Term::Con("binder".to_string(), vec![Box::new(Term::Lit("p".to_string())), Box::new(Term::Con("bind".to_string(), vec![Box::new(Term::Con("App".to_string(), vec![Box::new(b1.clone()), Box::new(Term::Con("Fst".to_string(), vec![Box::new(Term::Con("p".to_string(), vec![]))]))])), Box::new(Term::Con("x".to_string(), vec![])), Box::new(Term::Con("bind".to_string(), vec![Box::new(Term::Con("App".to_string(), vec![Box::new(b2.clone()), Box::new(Term::Con("Snd".to_string(), vec![Box::new(Term::Con("p".to_string(), vec![]))]))])), Box::new(Term::Con("y".to_string(), vec![])), Box::new(Term::Con("Some".to_string(), vec![Box::new(Term::Con("Pair".to_string(), vec![Box::new(Term::Con("x".to_string(), vec![])), Box::new(Term::Con("y".to_string(), vec![]))]))]))]))]))]))]))]))
    } else {
        None
    }
}

pub fn iso_or_else(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "orElse" && a.len() == 2) && matches!(get_arg(t, 0), Term::Con(ref n, ref a) if n == "MkIso" && a.len() == 2) && matches!(get_arg(t, 1), Term::Con(ref n, ref a) if n == "MkIso" && a.len() == 2) {
    let f1 = get_arg(get_arg(t, 0), 0).clone();
    let b1 = get_arg(get_arg(t, 0), 1).clone();
    let f2 = get_arg(get_arg(t, 1), 0).clone();
    let b2 = get_arg(get_arg(t, 1), 1).clone();
        Some(Term::Con("MkIso".to_string(), vec![Box::new(Term::Con("Lam".to_string(), vec![Box::new(Term::Con("binder".to_string(), vec![Box::new(Term::Lit("a".to_string())), Box::new(Term::Con("case".to_string(), vec![Box::new(Term::Con("App".to_string(), vec![Box::new(f1.clone()), Box::new(Term::Con("a".to_string(), vec![]))])), Box::new(Term::Con("Some".to_string(), vec![Box::new(Term::Var("x".to_string()))])), Box::new(Term::Con("Some".to_string(), vec![Box::new(Term::Var("x".to_string()))])), Box::new(Term::Con("None".to_string(), vec![])), Box::new(Term::Con("App".to_string(), vec![Box::new(f2.clone()), Box::new(Term::Con("a".to_string(), vec![]))]))]))]))])), Box::new(Term::Con("Lam".to_string(), vec![Box::new(Term::Con("binder".to_string(), vec![Box::new(Term::Lit("b".to_string())), Box::new(Term::Con("case".to_string(), vec![Box::new(Term::Con("App".to_string(), vec![Box::new(b1.clone()), Box::new(Term::Con("b".to_string(), vec![]))])), Box::new(Term::Con("Some".to_string(), vec![Box::new(Term::Var("x".to_string()))])), Box::new(Term::Con("Some".to_string(), vec![Box::new(Term::Var("x".to_string()))])), Box::new(Term::Con("None".to_string(), vec![])), Box::new(Term::Con("App".to_string(), vec![Box::new(b2.clone()), Box::new(Term::Con("b".to_string(), vec![]))]))]))]))]))]))
    } else {
        None
    }
}

pub fn term_atom(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "atom" && a.len() == 1) {
    let s = get_arg(t, 0).clone();
        Some(Term::Con("Con".to_string(), vec![Box::new(s.clone()), Box::new(Term::Con("Nil".to_string(), vec![]))]))
    } else {
        None
    }
}

pub fn term_app(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "app" && a.len() == 2) {
    let f = get_arg(t, 0).clone();
    let args = get_arg(t, 1).clone();
        Some(Term::Con("Con".to_string(), vec![Box::new(f.clone()), Box::new(args.clone())]))
    } else {
        None
    }
}

pub fn match_meta(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "matchPat" && a.len() == 2) && matches!(get_arg(t, 0), Term::Con(ref n, ref a) if n == "Var" && a.len() == 1) {
    let name = get_arg(get_arg(t, 0), 0).clone();
    let v_t = get_arg(t, 1).clone();
        Some(Term::Con("Some".to_string(), vec![Box::new(Term::Con("Cons".to_string(), vec![Box::new(Term::Con("Pair".to_string(), vec![Box::new(name.clone()), Box::new(v_t.clone())])), Box::new(Term::Con("Nil".to_string(), vec![]))]))]))
    } else {
        None
    }
}

pub fn match_var_same(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "matchPat" && a.len() == 2) && matches!(get_arg(t, 0), Term::Con(ref n, ref a) if n == "Var" && a.len() == 1) && matches!(get_arg(t, 1), Term::Con(ref n, ref a) if n == "Var" && a.len() == 1) {
    let name = get_arg(get_arg(t, 0), 0).clone();
        Some(Term::Con("Some".to_string(), vec![Box::new(Term::Con("Nil".to_string(), vec![]))]))
    } else {
        None
    }
}

pub fn match_var_diff(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "matchPat" && a.len() == 2) && matches!(get_arg(t, 0), Term::Con(ref n, ref a) if n == "Var" && a.len() == 1) && matches!(get_arg(t, 1), Term::Con(ref n, ref a) if n == "Var" && a.len() == 1) {
    let a = get_arg(get_arg(t, 0), 0).clone();
    let b = get_arg(get_arg(t, 1), 0).clone();
        Some(Term::Con("None".to_string(), vec![]))
    } else {
        None
    }
}

pub fn match_lit_same(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "matchPat" && a.len() == 2) && matches!(get_arg(t, 0), Term::Con(ref n, ref a) if n == "Lit" && a.len() == 1) && matches!(get_arg(t, 1), Term::Con(ref n, ref a) if n == "Lit" && a.len() == 1) {
    let s = get_arg(get_arg(t, 0), 0).clone();
        Some(Term::Con("Some".to_string(), vec![Box::new(Term::Con("Nil".to_string(), vec![]))]))
    } else {
        None
    }
}

pub fn match_lit_diff(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "matchPat" && a.len() == 2) && matches!(get_arg(t, 0), Term::Con(ref n, ref a) if n == "Lit" && a.len() == 1) && matches!(get_arg(t, 1), Term::Con(ref n, ref a) if n == "Lit" && a.len() == 1) {
    let a = get_arg(get_arg(t, 0), 0).clone();
    let b = get_arg(get_arg(t, 1), 0).clone();
        Some(Term::Con("None".to_string(), vec![]))
    } else {
        None
    }
}

pub fn match_con_same(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "matchPat" && a.len() == 2) && matches!(get_arg(t, 0), Term::Con(ref n, ref a) if n == "Con" && a.len() == 2) && matches!(get_arg(t, 1), Term::Con(ref n, ref a) if n == "Con" && a.len() == 2) {
    let n = get_arg(get_arg(t, 0), 0).clone();
    let pats = get_arg(get_arg(t, 0), 1).clone();
    let args = get_arg(get_arg(t, 1), 1).clone();
        Some(Term::Con("matchArgs".to_string(), vec![Box::new(pats.clone()), Box::new(args.clone())]))
    } else {
        None
    }
}

pub fn match_con_diff(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "matchPat" && a.len() == 2) && matches!(get_arg(t, 0), Term::Con(ref n, ref a) if n == "Con" && a.len() == 2) && matches!(get_arg(t, 1), Term::Con(ref n, ref a) if n == "Con" && a.len() == 2) {
    let n1 = get_arg(get_arg(t, 0), 0).clone();
    let pats = get_arg(get_arg(t, 0), 1).clone();
    let n2 = get_arg(get_arg(t, 1), 0).clone();
    let args = get_arg(get_arg(t, 1), 1).clone();
        Some(Term::Con("None".to_string(), vec![]))
    } else {
        None
    }
}

pub fn match_args_nil(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "matchArgs" && a.len() == 2) && matches!(get_arg(t, 0), Term::Con(ref n, ref a) if n == "Nil" && a.is_empty()) && matches!(get_arg(t, 1), Term::Con(ref n, ref a) if n == "Nil" && a.is_empty()) {
        Some(Term::Con("Some".to_string(), vec![Box::new(Term::Con("Nil".to_string(), vec![]))]))
    } else {
        None
    }
}

pub fn match_args_cons(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "matchArgs" && a.len() == 2) && matches!(get_arg(t, 0), Term::Con(ref n, ref a) if n == "Cons" && a.len() == 2) && matches!(get_arg(t, 1), Term::Con(ref n, ref a) if n == "Cons" && a.len() == 2) {
    let p = get_arg(get_arg(t, 0), 0).clone();
    let ps = get_arg(get_arg(t, 0), 1).clone();
    let a = get_arg(get_arg(t, 1), 0).clone();
    let v_as = get_arg(get_arg(t, 1), 1).clone();
        Some(Term::Con("merge".to_string(), vec![Box::new(Term::Con("matchPat".to_string(), vec![Box::new(p.clone()), Box::new(a.clone())])), Box::new(Term::Con("matchArgs".to_string(), vec![Box::new(ps.clone()), Box::new(v_as.clone())]))]))
    } else {
        None
    }
}

pub fn match_args_mismatch(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "matchArgs" && a.len() == 2) {
    let ps = get_arg(t, 0).clone();
    let v_as = get_arg(t, 1).clone();
        Some(Term::Con("None".to_string(), vec![]))
    } else {
        None
    }
}

pub fn merge_bindings(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "merge" && a.len() == 2) && matches!(get_arg(t, 0), Term::Con(ref n, ref a) if n == "Some" && a.len() == 1) && matches!(get_arg(t, 1), Term::Con(ref n, ref a) if n == "Some" && a.len() == 1) {
    let bs1 = get_arg(get_arg(t, 0), 0).clone();
    let bs2 = get_arg(get_arg(t, 1), 0).clone();
        Some(Term::Con("Some".to_string(), vec![Box::new(Term::Con("append".to_string(), vec![Box::new(bs1.clone()), Box::new(bs2.clone())]))]))
    } else {
        None
    }
}

pub fn merge_fail(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "merge" && a.len() == 2) && matches!(get_arg(t, 0), Term::Con(ref n, ref a) if n == "None" && a.is_empty()) {
    let x = get_arg(t, 1).clone();
        Some(Term::Con("None".to_string(), vec![]))
    } else {
        None
    }
}

pub fn subst_var(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "subst" && a.len() == 2) && matches!(get_arg(t, 0), Term::Con(ref n, ref a) if n == "Var" && a.len() == 1) {
    let name = get_arg(get_arg(t, 0), 0).clone();
    let bindings = get_arg(t, 1).clone();
        Some(Term::Con("lookup".to_string(), vec![Box::new(name.clone()), Box::new(bindings.clone())]))
    } else {
        None
    }
}

pub fn subst_lit(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "subst" && a.len() == 2) && matches!(get_arg(t, 0), Term::Con(ref n, ref a) if n == "Lit" && a.len() == 1) {
    let s = get_arg(get_arg(t, 0), 0).clone();
    let bindings = get_arg(t, 1).clone();
        Some(Term::Con("Lit".to_string(), vec![Box::new(s.clone())]))
    } else {
        None
    }
}

pub fn subst_con(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "subst" && a.len() == 2) && matches!(get_arg(t, 0), Term::Con(ref n, ref a) if n == "Con" && a.len() == 2) {
    let n = get_arg(get_arg(t, 0), 0).clone();
    let args = get_arg(get_arg(t, 0), 1).clone();
    let bindings = get_arg(t, 1).clone();
        Some(Term::Con("Con".to_string(), vec![Box::new(n.clone()), Box::new(Term::Con("map".to_string(), vec![Box::new(Term::Con("Lam".to_string(), vec![Box::new(Term::Con("binder".to_string(), vec![Box::new(Term::Lit("t".to_string())), Box::new(Term::Con("subst".to_string(), vec![Box::new(Term::Con("t".to_string(), vec![])), Box::new(bindings.clone())]))]))])), Box::new(args.clone())]))]))
    } else {
        None
    }
}

pub fn lookup_hit(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "lookup" && a.len() == 2) && matches!(get_arg(t, 1), Term::Con(ref n, ref a) if n == "Cons" && a.len() == 2) && matches!(get_arg(get_arg(t, 1), 0), Term::Con(ref n, ref a) if n == "Pair" && a.len() == 2) {
    let name = get_arg(t, 0).clone();
    let val = get_arg(get_arg(get_arg(t, 1), 0), 1).clone();
    let rest = get_arg(get_arg(t, 1), 1).clone();
        Some(val.clone())
    } else {
        None
    }
}

pub fn lookup_miss(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "lookup" && a.len() == 2) && matches!(get_arg(t, 1), Term::Con(ref n, ref a) if n == "Cons" && a.len() == 2) && matches!(get_arg(get_arg(t, 1), 0), Term::Con(ref n, ref a) if n == "Pair" && a.len() == 2) {
    let name = get_arg(t, 0).clone();
    let other = get_arg(get_arg(get_arg(t, 1), 0), 0).clone();
    let val = get_arg(get_arg(get_arg(t, 1), 0), 1).clone();
    let rest = get_arg(get_arg(t, 1), 1).clone();
        Some(Term::Con("lookup".to_string(), vec![Box::new(name.clone()), Box::new(rest.clone())]))
    } else {
        None
    }
}

pub fn lookup_empty(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "lookup" && a.len() == 2) && matches!(get_arg(t, 1), Term::Con(ref n, ref a) if n == "Nil" && a.is_empty()) {
    let name = get_arg(t, 0).clone();
        Some(Term::Con("Var".to_string(), vec![Box::new(name.clone())]))
    } else {
        None
    }
}

pub fn ast_var(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "astVar" && a.len() == 2) && matches!(get_arg(t, 0), Term::Con(ref n, ref a) if n == "MkAST" && a.len() == 3) {
    let var = get_arg(get_arg(t, 0), 0).clone();
    let lit = get_arg(get_arg(t, 0), 1).clone();
    let con = get_arg(get_arg(t, 0), 2).clone();
    let s = get_arg(t, 1).clone();
        Some(Term::Con("App".to_string(), vec![Box::new(var.clone()), Box::new(s.clone())]))
    } else {
        None
    }
}

pub fn ast_lit(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "astLit" && a.len() == 2) && matches!(get_arg(t, 0), Term::Con(ref n, ref a) if n == "MkAST" && a.len() == 3) {
    let var = get_arg(get_arg(t, 0), 0).clone();
    let lit = get_arg(get_arg(t, 0), 1).clone();
    let con = get_arg(get_arg(t, 0), 2).clone();
    let s = get_arg(t, 1).clone();
        Some(Term::Con("App".to_string(), vec![Box::new(lit.clone()), Box::new(s.clone())]))
    } else {
        None
    }
}

pub fn ast_con(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "astCon" && a.len() == 3) && matches!(get_arg(t, 0), Term::Con(ref n, ref a) if n == "MkAST" && a.len() == 3) {
    let var = get_arg(get_arg(t, 0), 0).clone();
    let lit = get_arg(get_arg(t, 0), 1).clone();
    let con = get_arg(get_arg(t, 0), 2).clone();
    let name = get_arg(t, 1).clone();
    let args = get_arg(t, 2).clone();
        Some(Term::Con("App".to_string(), vec![Box::new(Term::Con("App".to_string(), vec![Box::new(con.clone()), Box::new(name.clone())])), Box::new(args.clone())]))
    } else {
        None
    }
}

pub fn default_a_s_t(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "defaultAST" && a.is_empty()) {
        Some(Term::Con("MkAST".to_string(), vec![Box::new(Term::Con("Var".to_string(), vec![])), Box::new(Term::Con("Lit".to_string(), vec![])), Box::new(Term::Con("Con".to_string(), vec![]))]))
    } else {
        None
    }
}

pub fn language_name(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "languageName" && a.len() == 1) && matches!(get_arg(t, 0), Term::Con(ref n, ref a) if n == "MkLanguage" && a.len() == 2) {
    let name = get_arg(get_arg(t, 0), 0).clone();
    let pieces = get_arg(get_arg(t, 0), 1).clone();
        Some(name.clone())
    } else {
        None
    }
}

pub fn language_pieces(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "languagePieces" && a.len() == 1) && matches!(get_arg(t, 0), Term::Con(ref n, ref a) if n == "MkLanguage" && a.len() == 2) {
    let name = get_arg(get_arg(t, 0), 0).clone();
    let pieces = get_arg(get_arg(t, 0), 1).clone();
        Some(pieces.clone())
    } else {
        None
    }
}

pub fn language_all_grammar(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "languageAllGrammar" && a.len() == 1) && matches!(get_arg(t, 0), Term::Con(ref n, ref a) if n == "MkLanguage" && a.len() == 2) {
    let name = get_arg(get_arg(t, 0), 0).clone();
    let pieces = get_arg(get_arg(t, 0), 1).clone();
        Some(Term::Con("flatMap".to_string(), vec![Box::new(Term::Con("pieceGrammar".to_string(), vec![])), Box::new(pieces.clone())]))
    } else {
        None
    }
}

pub fn language_all_rules(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "languageAllRules" && a.len() == 1) && matches!(get_arg(t, 0), Term::Con(ref n, ref a) if n == "MkLanguage" && a.len() == 2) {
    let name = get_arg(get_arg(t, 0), 0).clone();
    let pieces = get_arg(get_arg(t, 0), 1).clone();
        Some(Term::Con("flatMap".to_string(), vec![Box::new(Term::Con("pieceRules".to_string(), vec![])), Box::new(pieces.clone())]))
    } else {
        None
    }
}

pub fn piece_name(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "pieceName" && a.len() == 1) && matches!(get_arg(t, 0), Term::Con(ref n, ref a) if n == "MkPiece" && a.len() == 5) {
    let name = get_arg(get_arg(t, 0), 0).clone();
    let level = get_arg(get_arg(t, 0), 1).clone();
    let grammar = get_arg(get_arg(t, 0), 2).clone();
    let rules = get_arg(get_arg(t, 0), 3).clone();
    let typeRules = get_arg(get_arg(t, 0), 4).clone();
        Some(name.clone())
    } else {
        None
    }
}

pub fn piece_level(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "pieceLevel" && a.len() == 1) && matches!(get_arg(t, 0), Term::Con(ref n, ref a) if n == "MkPiece" && a.len() == 5) {
    let name = get_arg(get_arg(t, 0), 0).clone();
    let level = get_arg(get_arg(t, 0), 1).clone();
    let grammar = get_arg(get_arg(t, 0), 2).clone();
    let rules = get_arg(get_arg(t, 0), 3).clone();
    let typeRules = get_arg(get_arg(t, 0), 4).clone();
        Some(level.clone())
    } else {
        None
    }
}

pub fn piece_grammar(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "pieceGrammar" && a.len() == 1) && matches!(get_arg(t, 0), Term::Con(ref n, ref a) if n == "MkPiece" && a.len() == 5) {
    let name = get_arg(get_arg(t, 0), 0).clone();
    let level = get_arg(get_arg(t, 0), 1).clone();
    let grammar = get_arg(get_arg(t, 0), 2).clone();
    let rules = get_arg(get_arg(t, 0), 3).clone();
    let typeRules = get_arg(get_arg(t, 0), 4).clone();
        Some(grammar.clone())
    } else {
        None
    }
}

pub fn piece_rules(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "pieceRules" && a.len() == 1) && matches!(get_arg(t, 0), Term::Con(ref n, ref a) if n == "MkPiece" && a.len() == 5) {
    let name = get_arg(get_arg(t, 0), 0).clone();
    let level = get_arg(get_arg(t, 0), 1).clone();
    let grammar = get_arg(get_arg(t, 0), 2).clone();
    let rules = get_arg(get_arg(t, 0), 3).clone();
    let typeRules = get_arg(get_arg(t, 0), 4).clone();
        Some(rules.clone())
    } else {
        None
    }
}

pub fn piece_type_rules(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "pieceTypeRules" && a.len() == 1) && matches!(get_arg(t, 0), Term::Con(ref n, ref a) if n == "MkPiece" && a.len() == 5) {
    let name = get_arg(get_arg(t, 0), 0).clone();
    let level = get_arg(get_arg(t, 0), 1).clone();
    let grammar = get_arg(get_arg(t, 0), 2).clone();
    let rules = get_arg(get_arg(t, 0), 3).clone();
    let typeRules = get_arg(get_arg(t, 0), 4).clone();
        Some(typeRules.clone())
    } else {
        None
    }
}

pub fn rule_name(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "ruleName" && a.len() == 1) && matches!(get_arg(t, 0), Term::Con(ref n, ref a) if n == "MkRule" && a.len() == 3) {
    let name = get_arg(get_arg(t, 0), 0).clone();
    let pattern = get_arg(get_arg(t, 0), 1).clone();
    let template = get_arg(get_arg(t, 0), 2).clone();
        Some(name.clone())
    } else {
        None
    }
}

pub fn rule_pattern(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "rulePattern" && a.len() == 1) && matches!(get_arg(t, 0), Term::Con(ref n, ref a) if n == "MkRule" && a.len() == 3) {
    let name = get_arg(get_arg(t, 0), 0).clone();
    let pattern = get_arg(get_arg(t, 0), 1).clone();
    let template = get_arg(get_arg(t, 0), 2).clone();
        Some(pattern.clone())
    } else {
        None
    }
}

pub fn rule_template(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "ruleTemplate" && a.len() == 1) && matches!(get_arg(t, 0), Term::Con(ref n, ref a) if n == "MkRule" && a.len() == 3) {
    let name = get_arg(get_arg(t, 0), 0).clone();
    let pattern = get_arg(get_arg(t, 0), 1).clone();
    let template = get_arg(get_arg(t, 0), 2).clone();
        Some(template.clone())
    } else {
        None
    }
}

pub fn source_loc_to_string(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "sourceLocToString" && a.len() == 1) && matches!(get_arg(t, 0), Term::Con(ref n, ref a) if n == "MkSourceLoc" && a.len() == 4) {
    let file = get_arg(get_arg(t, 0), 0).clone();
    let line = get_arg(get_arg(t, 0), 1).clone();
    let col = get_arg(get_arg(t, 0), 2).clone();
    let span = get_arg(get_arg(t, 0), 3).clone();
        Some(Term::Con("concat".to_string(), vec![Box::new(Term::Con("concat".to_string(), vec![Box::new(Term::Con("concat".to_string(), vec![Box::new(Term::Con("concat".to_string(), vec![Box::new(file.clone()), Box::new(Term::Lit("\":\"".to_string()))])), Box::new(Term::Con("toString".to_string(), vec![Box::new(line.clone())]))])), Box::new(Term::Lit("\":\"".to_string()))])), Box::new(Term::Con("toString".to_string(), vec![Box::new(col.clone())]))]))
    } else {
        None
    }
}

pub fn source_loc_to_string_unknown(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "sourceLocToString" && a.len() == 1) && matches!(get_arg(t, 0), Term::Con(ref n, ref a) if n == "UnknownLoc" && a.is_empty()) {
        Some(Term::Lit("\"<unknown>:0:0\"".to_string()))
    } else {
        None
    }
}

pub fn type_error_simple(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "typeErrorSimple" && a.len() == 2) {
    let msg = get_arg(t, 0).clone();
    let loc = get_arg(t, 1).clone();
        Some(Term::Con("MkTypeError".to_string(), vec![Box::new(msg.clone()), Box::new(loc.clone()), Box::new(Term::Con("SevError".to_string(), vec![])), Box::new(Term::Con("None".to_string(), vec![])), Box::new(Term::Con("None".to_string(), vec![])), Box::new(Term::Con("Nil".to_string(), vec![]))]))
    } else {
        None
    }
}

pub fn type_error_mismatch(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "typeErrorMismatch" && a.len() == 3) {
    let expected = get_arg(t, 0).clone();
    let actual = get_arg(t, 1).clone();
    let loc = get_arg(t, 2).clone();
        Some(Term::Con("MkTypeError".to_string(), vec![Box::new(Term::Lit("\"type mismatch\"".to_string())), Box::new(loc.clone()), Box::new(Term::Con("SevError".to_string(), vec![])), Box::new(Term::Con("Some".to_string(), vec![Box::new(expected.clone())])), Box::new(Term::Con("Some".to_string(), vec![Box::new(actual.clone())])), Box::new(Term::Con("Nil".to_string(), vec![]))]))
    } else {
        None
    }
}

pub fn type_error_undefined(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "typeErrorUndefined" && a.len() == 2) {
    let name = get_arg(t, 0).clone();
    let loc = get_arg(t, 1).clone();
        Some(Term::Con("MkTypeError".to_string(), vec![Box::new(Term::Con("concat".to_string(), vec![Box::new(Term::Lit("\"undefined: \"".to_string())), Box::new(name.clone())])), Box::new(loc.clone()), Box::new(Term::Con("SevError".to_string(), vec![])), Box::new(Term::Con("None".to_string(), vec![])), Box::new(Term::Con("None".to_string(), vec![])), Box::new(Term::Con("Nil".to_string(), vec![]))]))
    } else {
        None
    }
}

pub fn type_error_to_string(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "typeErrorToString" && a.len() == 1) && matches!(get_arg(t, 0), Term::Con(ref n, ref a) if n == "MkTypeError" && a.len() == 6) {
    let msg = get_arg(get_arg(t, 0), 0).clone();
    let loc = get_arg(get_arg(t, 0), 1).clone();
    let sev = get_arg(get_arg(t, 0), 2).clone();
    let exp = get_arg(get_arg(t, 0), 3).clone();
    let act = get_arg(get_arg(t, 0), 4).clone();
    let ctx = get_arg(get_arg(t, 0), 5).clone();
        Some(Term::Con("let".to_string(), vec![Box::new(Term::Var("sevStr".to_string())), Box::new(Term::Con("match".to_string(), vec![Box::new(sev.clone()), Box::new(Term::Con("SevError".to_string(), vec![])), Box::new(Term::Lit("\"error\"".to_string())), Box::new(Term::Con("SevWarning".to_string(), vec![])), Box::new(Term::Lit("\"warning\"".to_string())), Box::new(Term::Con("SevInfo".to_string(), vec![])), Box::new(Term::Lit("\"info\"".to_string()))])), Box::new(Term::Con("let".to_string(), vec![Box::new(Term::Var("locStr".to_string())), Box::new(Term::Con("sourceLocToString".to_string(), vec![Box::new(loc.clone())])), Box::new(Term::Con("let".to_string(), vec![Box::new(Term::Var("base".to_string())), Box::new(Term::Con("concat".to_string(), vec![Box::new(Term::Con("concat".to_string(), vec![Box::new(Term::Con("concat".to_string(), vec![Box::new(Term::Var("locStr".to_string())), Box::new(Term::Lit("\": \"".to_string()))])), Box::new(Term::Var("sevStr".to_string()))])), Box::new(Term::Con("concat".to_string(), vec![Box::new(Term::Lit("\": \"".to_string())), Box::new(msg.clone())]))])), Box::new(Term::Con("match".to_string(), vec![Box::new(exp.clone()), Box::new(Term::Con("Some".to_string(), vec![Box::new(Term::Var("e".to_string()))])), Box::new(Term::Con("match".to_string(), vec![Box::new(act.clone()), Box::new(Term::Con("Some".to_string(), vec![Box::new(Term::Var("a".to_string()))])), Box::new(Term::Con("concat".to_string(), vec![Box::new(Term::Con("concat".to_string(), vec![Box::new(Term::Con("concat".to_string(), vec![Box::new(Term::Var("base".to_string())), Box::new(Term::Lit("\"\\n  expected: \"".to_string()))])), Box::new(Term::Con("termToString".to_string(), vec![Box::new(Term::Var("e".to_string()))]))])), Box::new(Term::Con("concat".to_string(), vec![Box::new(Term::Lit("\"\\n  actual: \"".to_string())), Box::new(Term::Con("termToString".to_string(), vec![Box::new(Term::Var("a".to_string()))]))]))])), Box::new(Term::Con("None".to_string(), vec![])), Box::new(Term::Var("base".to_string()))])), Box::new(Term::Con("None".to_string(), vec![])), Box::new(Term::Var("base".to_string()))]))]))]))]))
    } else {
        None
    }
}

pub fn eval_result_pure(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "evalResultPure" && a.len() == 1) {
    let a = get_arg(t, 0).clone();
        Some(Term::Con("EvalOk".to_string(), vec![Box::new(a.clone()), Box::new(Term::Con("Nil".to_string(), vec![]))]))
    } else {
        None
    }
}

pub fn eval_result_map_ok(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "evalResultMap" && a.len() == 2) && matches!(get_arg(t, 1), Term::Con(ref n, ref a) if n == "EvalOk" && a.len() == 2) {
    let f = get_arg(t, 0).clone();
    let a = get_arg(get_arg(t, 1), 0).clone();
    let errs = get_arg(get_arg(t, 1), 1).clone();
        Some(Term::Con("EvalOk".to_string(), vec![Box::new(Term::Con("app".to_string(), vec![Box::new(a.clone())])), Box::new(errs.clone())]))
    } else {
        None
    }
}

pub fn eval_result_map_failed(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "evalResultMap" && a.len() == 2) && matches!(get_arg(t, 1), Term::Con(ref n, ref a) if n == "EvalFailed" && a.len() == 1) {
    let f = get_arg(t, 0).clone();
    let errs = get_arg(get_arg(t, 1), 0).clone();
        Some(Term::Con("EvalFailed".to_string(), vec![Box::new(errs.clone())]))
    } else {
        None
    }
}

pub fn eval_result_bind_ok(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "evalResultBind" && a.len() == 2) && matches!(get_arg(t, 0), Term::Con(ref n, ref a) if n == "EvalOk" && a.len() == 2) {
    let a = get_arg(get_arg(t, 0), 0).clone();
    let errs = get_arg(get_arg(t, 0), 1).clone();
    let f = get_arg(t, 1).clone();
        Some(Term::Con("match".to_string(), vec![Box::new(Term::Con("app".to_string(), vec![Box::new(a.clone())])), Box::new(Term::Con("EvalOk".to_string(), vec![Box::new(Term::Var("b".to_string())), Box::new(Term::Var("errs2".to_string()))])), Box::new(Term::Con("EvalOk".to_string(), vec![Box::new(Term::Var("b".to_string())), Box::new(Term::Con("append".to_string(), vec![Box::new(errs.clone()), Box::new(Term::Var("errs2".to_string()))]))])), Box::new(Term::Con("EvalFailed".to_string(), vec![Box::new(Term::Var("errs2".to_string()))])), Box::new(Term::Con("EvalFailed".to_string(), vec![Box::new(Term::Con("append".to_string(), vec![Box::new(errs.clone()), Box::new(Term::Var("errs2".to_string()))]))]))]))
    } else {
        None
    }
}

pub fn eval_result_bind_failed(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "evalResultBind" && a.len() == 2) && matches!(get_arg(t, 0), Term::Con(ref n, ref a) if n == "EvalFailed" && a.len() == 1) {
    let errs = get_arg(get_arg(t, 0), 0).clone();
    let f = get_arg(t, 1).clone();
        Some(Term::Con("EvalFailed".to_string(), vec![Box::new(errs.clone())]))
    } else {
        None
    }
}

pub fn eval_result_add_error(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "evalResultAddError" && a.len() == 2) && matches!(get_arg(t, 1), Term::Con(ref n, ref a) if n == "EvalOk" && a.len() == 2) {
    let e = get_arg(t, 0).clone();
    let a = get_arg(get_arg(t, 1), 0).clone();
    let errs = get_arg(get_arg(t, 1), 1).clone();
        Some(Term::Con("EvalOk".to_string(), vec![Box::new(a.clone()), Box::new(Term::Con("Cons".to_string(), vec![Box::new(e.clone()), Box::new(errs.clone())]))]))
    } else {
        None
    }
}

pub fn eval_result_add_error_failed(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "evalResultAddError" && a.len() == 2) && matches!(get_arg(t, 1), Term::Con(ref n, ref a) if n == "EvalFailed" && a.len() == 1) {
    let e = get_arg(t, 0).clone();
    let errs = get_arg(get_arg(t, 1), 0).clone();
        Some(Term::Con("EvalFailed".to_string(), vec![Box::new(Term::Con("Cons".to_string(), vec![Box::new(e.clone()), Box::new(errs.clone())]))]))
    } else {
        None
    }
}

pub fn eval_result_is_ok(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "evalResultIsOk" && a.len() == 1) && matches!(get_arg(t, 0), Term::Con(ref n, ref a) if n == "EvalOk" && a.len() == 2) {
    let a = get_arg(get_arg(t, 0), 0).clone();
    let errs = get_arg(get_arg(t, 0), 1).clone();
        Some(Term::Con("True".to_string(), vec![]))
    } else {
        None
    }
}

pub fn eval_result_is_ok_failed(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "evalResultIsOk" && a.len() == 1) && matches!(get_arg(t, 0), Term::Con(ref n, ref a) if n == "EvalFailed" && a.len() == 1) {
    let errs = get_arg(get_arg(t, 0), 0).clone();
        Some(Term::Con("False".to_string(), vec![]))
    } else {
        None
    }
}

pub fn eval_result_get_errors(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "evalResultGetErrors" && a.len() == 1) && matches!(get_arg(t, 0), Term::Con(ref n, ref a) if n == "EvalOk" && a.len() == 2) {
    let a = get_arg(get_arg(t, 0), 0).clone();
    let errs = get_arg(get_arg(t, 0), 1).clone();
        Some(errs.clone())
    } else {
        None
    }
}

pub fn eval_result_get_errors_failed(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "evalResultGetErrors" && a.len() == 1) && matches!(get_arg(t, 0), Term::Con(ref n, ref a) if n == "EvalFailed" && a.len() == 1) {
    let errs = get_arg(get_arg(t, 0), 0).clone();
        Some(errs.clone())
    } else {
        None
    }
}

pub fn context_extend(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "contextExtend" && a.len() == 4) {
    let ctx = get_arg(t, 0).clone();
    let name = get_arg(t, 1).clone();
    let ty = get_arg(t, 2).clone();
    let loc = get_arg(t, 3).clone();
        Some(Term::Con("ContextCons".to_string(), vec![Box::new(Term::Con("MkBinding".to_string(), vec![Box::new(name.clone()), Box::new(ty.clone()), Box::new(Term::Con("None".to_string(), vec![])), Box::new(loc.clone())])), Box::new(ctx.clone())]))
    } else {
        None
    }
}

pub fn context_extend_let(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "contextExtendLet" && a.len() == 5) {
    let ctx = get_arg(t, 0).clone();
    let name = get_arg(t, 1).clone();
    let ty = get_arg(t, 2).clone();
    let val = get_arg(t, 3).clone();
    let loc = get_arg(t, 4).clone();
        Some(Term::Con("ContextCons".to_string(), vec![Box::new(Term::Con("MkBinding".to_string(), vec![Box::new(name.clone()), Box::new(ty.clone()), Box::new(Term::Con("Some".to_string(), vec![Box::new(val.clone())])), Box::new(loc.clone())])), Box::new(ctx.clone())]))
    } else {
        None
    }
}

pub fn context_lookup_empty(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "contextLookup" && a.len() == 2) && matches!(get_arg(t, 0), Term::Con(ref n, ref a) if n == "EmptyContext" && a.is_empty()) {
    let name = get_arg(t, 1).clone();
        Some(Term::Con("None".to_string(), vec![]))
    } else {
        None
    }
}

pub fn context_lookup_found(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "contextLookup" && a.len() == 2) && matches!(get_arg(t, 0), Term::Con(ref n, ref a) if n == "ContextCons" && a.len() == 2) && matches!(get_arg(get_arg(t, 0), 0), Term::Con(ref n, ref a) if n == "MkBinding" && a.len() == 4) {
    let name = get_arg(get_arg(get_arg(t, 0), 0), 0).clone();
    let ty = get_arg(get_arg(get_arg(t, 0), 0), 1).clone();
    let val = get_arg(get_arg(get_arg(t, 0), 0), 2).clone();
    let loc = get_arg(get_arg(get_arg(t, 0), 0), 3).clone();
    let rest = get_arg(get_arg(t, 0), 1).clone();
        Some(Term::Con("Some".to_string(), vec![Box::new(Term::Con("MkBinding".to_string(), vec![Box::new(name.clone()), Box::new(ty.clone()), Box::new(val.clone()), Box::new(loc.clone())]))]))
    } else {
        None
    }
}

pub fn context_lookup_miss(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "contextLookup" && a.len() == 2) && matches!(get_arg(t, 0), Term::Con(ref n, ref a) if n == "ContextCons" && a.len() == 2) && matches!(get_arg(get_arg(t, 0), 0), Term::Con(ref n, ref a) if n == "MkBinding" && a.len() == 4) {
    let n1 = get_arg(get_arg(get_arg(t, 0), 0), 0).clone();
    let ty = get_arg(get_arg(get_arg(t, 0), 0), 1).clone();
    let val = get_arg(get_arg(get_arg(t, 0), 0), 2).clone();
    let loc = get_arg(get_arg(get_arg(t, 0), 0), 3).clone();
    let rest = get_arg(get_arg(t, 0), 1).clone();
    let n2 = get_arg(t, 1).clone();
        Some(Term::Con("contextLookup".to_string(), vec![Box::new(rest.clone()), Box::new(n2.clone())]))
    } else {
        None
    }
}

pub fn context_lookup_type(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "contextLookupType" && a.len() == 2) {
    let ctx = get_arg(t, 0).clone();
    let name = get_arg(t, 1).clone();
        Some(Term::Con("match".to_string(), vec![Box::new(Term::Con("contextLookup".to_string(), vec![Box::new(ctx.clone()), Box::new(name.clone())])), Box::new(Term::Con("Some".to_string(), vec![Box::new(Term::Con("MkBinding".to_string(), vec![Box::new(Term::Var("n".to_string())), Box::new(Term::Var("ty".to_string())), Box::new(Term::Var("v".to_string())), Box::new(Term::Var("l".to_string()))]))])), Box::new(Term::Con("Some".to_string(), vec![Box::new(Term::Var("ty".to_string()))])), Box::new(Term::Con("None".to_string(), vec![])), Box::new(Term::Con("None".to_string(), vec![]))]))
    } else {
        None
    }
}

pub fn context_names(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "contextNames" && a.len() == 1) && matches!(get_arg(t, 0), Term::Con(ref n, ref a) if n == "EmptyContext" && a.is_empty()) {
        Some(Term::Con("Nil".to_string(), vec![]))
    } else {
        None
    }
}

pub fn context_names_cons(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "contextNames" && a.len() == 1) && matches!(get_arg(t, 0), Term::Con(ref n, ref a) if n == "ContextCons" && a.len() == 2) && matches!(get_arg(get_arg(t, 0), 0), Term::Con(ref n, ref a) if n == "MkBinding" && a.len() == 4) {
    let name = get_arg(get_arg(get_arg(t, 0), 0), 0).clone();
    let ty = get_arg(get_arg(get_arg(t, 0), 0), 1).clone();
    let val = get_arg(get_arg(get_arg(t, 0), 0), 2).clone();
    let loc = get_arg(get_arg(get_arg(t, 0), 0), 3).clone();
    let rest = get_arg(get_arg(t, 0), 1).clone();
        Some(Term::Con("Cons".to_string(), vec![Box::new(name.clone()), Box::new(Term::Con("contextNames".to_string(), vec![Box::new(rest.clone())]))]))
    } else {
        None
    }
}

pub fn var_context_extend(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "varContextExtend" && a.len() == 2) {
    let ctx = get_arg(t, 0).clone();
    let name = get_arg(t, 1).clone();
        Some(Term::Con("VarContextCons".to_string(), vec![Box::new(name.clone()), Box::new(ctx.clone())]))
    } else {
        None
    }
}

pub fn var_context_contains_empty(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "varContextContains" && a.len() == 2) && matches!(get_arg(t, 0), Term::Con(ref n, ref a) if n == "EmptyVarContext" && a.is_empty()) {
    let name = get_arg(t, 1).clone();
        Some(Term::Con("False".to_string(), vec![]))
    } else {
        None
    }
}

pub fn var_context_contains_found(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "varContextContains" && a.len() == 2) && matches!(get_arg(t, 0), Term::Con(ref n, ref a) if n == "VarContextCons" && a.len() == 2) {
    let name = get_arg(get_arg(t, 0), 0).clone();
    let rest = get_arg(get_arg(t, 0), 1).clone();
        Some(Term::Con("True".to_string(), vec![]))
    } else {
        None
    }
}

pub fn var_context_contains_miss(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "varContextContains" && a.len() == 2) && matches!(get_arg(t, 0), Term::Con(ref n, ref a) if n == "VarContextCons" && a.len() == 2) {
    let n1 = get_arg(get_arg(t, 0), 0).clone();
    let rest = get_arg(get_arg(t, 0), 1).clone();
    let n2 = get_arg(t, 1).clone();
        Some(Term::Con("varContextContains".to_string(), vec![Box::new(rest.clone()), Box::new(n2.clone())]))
    } else {
        None
    }
}

pub fn eval_env_empty(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "evalEnvEmpty" && a.is_empty()) {
        Some(Term::Con("MkEvalEnv".to_string(), vec![Box::new(Term::Con("EmptyAttrEnv".to_string(), vec![])), Box::new(Term::Con("EmptyContext".to_string(), vec![])), Box::new(Term::Con("EmptyVarContext".to_string(), vec![])), Box::new(Term::Con("Nil".to_string(), vec![])), Box::new(Term::Con("UnknownLoc".to_string(), vec![]))]))
    } else {
        None
    }
}

pub fn eval_env_with_ctx(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "evalEnvWithCtx" && a.len() == 2) && matches!(get_arg(t, 0), Term::Con(ref n, ref a) if n == "MkEvalEnv" && a.len() == 5) {
    let attrs = get_arg(get_arg(t, 0), 0).clone();
    let oldCtx = get_arg(get_arg(t, 0), 1).clone();
    let vars = get_arg(get_arg(t, 0), 2).clone();
    let errs = get_arg(get_arg(t, 0), 3).clone();
    let loc = get_arg(get_arg(t, 0), 4).clone();
    let ctx = get_arg(t, 1).clone();
        Some(Term::Con("MkEvalEnv".to_string(), vec![Box::new(attrs.clone()), Box::new(ctx.clone()), Box::new(vars.clone()), Box::new(errs.clone()), Box::new(loc.clone())]))
    } else {
        None
    }
}

pub fn eval_env_with_loc(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "evalEnvWithLoc" && a.len() == 2) && matches!(get_arg(t, 0), Term::Con(ref n, ref a) if n == "MkEvalEnv" && a.len() == 5) {
    let attrs = get_arg(get_arg(t, 0), 0).clone();
    let ctx = get_arg(get_arg(t, 0), 1).clone();
    let vars = get_arg(get_arg(t, 0), 2).clone();
    let errs = get_arg(get_arg(t, 0), 3).clone();
    let oldLoc = get_arg(get_arg(t, 0), 4).clone();
    let loc = get_arg(t, 1).clone();
        Some(Term::Con("MkEvalEnv".to_string(), vec![Box::new(attrs.clone()), Box::new(ctx.clone()), Box::new(vars.clone()), Box::new(errs.clone()), Box::new(loc.clone())]))
    } else {
        None
    }
}

pub fn eval_env_add_binding(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "evalEnvAddBinding" && a.len() == 3) && matches!(get_arg(t, 0), Term::Con(ref n, ref a) if n == "MkEvalEnv" && a.len() == 5) {
    let attrs = get_arg(get_arg(t, 0), 0).clone();
    let ctx = get_arg(get_arg(t, 0), 1).clone();
    let vars = get_arg(get_arg(t, 0), 2).clone();
    let errs = get_arg(get_arg(t, 0), 3).clone();
    let loc = get_arg(get_arg(t, 0), 4).clone();
    let name = get_arg(t, 1).clone();
    let ty = get_arg(t, 2).clone();
        Some(Term::Con("MkEvalEnv".to_string(), vec![Box::new(attrs.clone()), Box::new(Term::Con("contextExtend".to_string(), vec![Box::new(ctx.clone()), Box::new(name.clone()), Box::new(ty.clone()), Box::new(loc.clone())])), Box::new(vars.clone()), Box::new(errs.clone()), Box::new(loc.clone())]))
    } else {
        None
    }
}

pub fn eval_env_add_var(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "evalEnvAddVar" && a.len() == 2) && matches!(get_arg(t, 0), Term::Con(ref n, ref a) if n == "MkEvalEnv" && a.len() == 5) {
    let attrs = get_arg(get_arg(t, 0), 0).clone();
    let ctx = get_arg(get_arg(t, 0), 1).clone();
    let vars = get_arg(get_arg(t, 0), 2).clone();
    let errs = get_arg(get_arg(t, 0), 3).clone();
    let loc = get_arg(get_arg(t, 0), 4).clone();
    let name = get_arg(t, 1).clone();
        Some(Term::Con("MkEvalEnv".to_string(), vec![Box::new(attrs.clone()), Box::new(ctx.clone()), Box::new(Term::Con("varContextExtend".to_string(), vec![Box::new(vars.clone()), Box::new(name.clone())])), Box::new(errs.clone()), Box::new(loc.clone())]))
    } else {
        None
    }
}

pub fn eval_env_add_error(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "evalEnvAddError" && a.len() == 2) && matches!(get_arg(t, 0), Term::Con(ref n, ref a) if n == "MkEvalEnv" && a.len() == 5) {
    let attrs = get_arg(get_arg(t, 0), 0).clone();
    let ctx = get_arg(get_arg(t, 0), 1).clone();
    let vars = get_arg(get_arg(t, 0), 2).clone();
    let errs = get_arg(get_arg(t, 0), 3).clone();
    let loc = get_arg(get_arg(t, 0), 4).clone();
    let e = get_arg(t, 1).clone();
        Some(Term::Con("MkEvalEnv".to_string(), vec![Box::new(attrs.clone()), Box::new(ctx.clone()), Box::new(vars.clone()), Box::new(Term::Con("Cons".to_string(), vec![Box::new(e.clone()), Box::new(errs.clone())])), Box::new(loc.clone())]))
    } else {
        None
    }
}

pub fn eval_env_add_type_error(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "evalEnvAddTypeError" && a.len() == 2) && matches!(get_arg(t, 0), Term::Con(ref n, ref a) if n == "MkEvalEnv" && a.len() == 5) {
    let attrs = get_arg(get_arg(t, 0), 0).clone();
    let ctx = get_arg(get_arg(t, 0), 1).clone();
    let vars = get_arg(get_arg(t, 0), 2).clone();
    let errs = get_arg(get_arg(t, 0), 3).clone();
    let loc = get_arg(get_arg(t, 0), 4).clone();
    let msg = get_arg(t, 1).clone();
        Some(Term::Con("MkEvalEnv".to_string(), vec![Box::new(attrs.clone()), Box::new(ctx.clone()), Box::new(vars.clone()), Box::new(Term::Con("Cons".to_string(), vec![Box::new(Term::Con("typeErrorSimple".to_string(), vec![Box::new(msg.clone()), Box::new(loc.clone())])), Box::new(errs.clone())])), Box::new(loc.clone())]))
    } else {
        None
    }
}

pub fn eval_env_add_mismatch(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "evalEnvAddMismatch" && a.len() == 3) && matches!(get_arg(t, 0), Term::Con(ref n, ref a) if n == "MkEvalEnv" && a.len() == 5) {
    let attrs = get_arg(get_arg(t, 0), 0).clone();
    let ctx = get_arg(get_arg(t, 0), 1).clone();
    let vars = get_arg(get_arg(t, 0), 2).clone();
    let errs = get_arg(get_arg(t, 0), 3).clone();
    let loc = get_arg(get_arg(t, 0), 4).clone();
    let expected = get_arg(t, 1).clone();
    let actual = get_arg(t, 2).clone();
        Some(Term::Con("MkEvalEnv".to_string(), vec![Box::new(attrs.clone()), Box::new(ctx.clone()), Box::new(vars.clone()), Box::new(Term::Con("Cons".to_string(), vec![Box::new(Term::Con("typeErrorMismatch".to_string(), vec![Box::new(expected.clone()), Box::new(actual.clone()), Box::new(loc.clone())])), Box::new(errs.clone())])), Box::new(loc.clone())]))
    } else {
        None
    }
}

pub fn eval_env_set_attr(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "evalEnvSetAttr" && a.len() == 4) && matches!(get_arg(t, 0), Term::Con(ref n, ref a) if n == "MkEvalEnv" && a.len() == 5) {
    let attrs = get_arg(get_arg(t, 0), 0).clone();
    let ctx = get_arg(get_arg(t, 0), 1).clone();
    let vars = get_arg(get_arg(t, 0), 2).clone();
    let errs = get_arg(get_arg(t, 0), 3).clone();
    let loc = get_arg(get_arg(t, 0), 4).clone();
    let path = get_arg(t, 1).clone();
    let name = get_arg(t, 2).clone();
    let val = get_arg(t, 3).clone();
        Some(Term::Con("MkEvalEnv".to_string(), vec![Box::new(Term::Con("attrEnvInsert".to_string(), vec![Box::new(attrs.clone()), Box::new(path.clone()), Box::new(name.clone()), Box::new(val.clone())])), Box::new(ctx.clone()), Box::new(vars.clone()), Box::new(errs.clone()), Box::new(loc.clone())]))
    } else {
        None
    }
}

pub fn eval_env_get_attr(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "evalEnvGetAttr" && a.len() == 3) && matches!(get_arg(t, 0), Term::Con(ref n, ref a) if n == "MkEvalEnv" && a.len() == 5) {
    let attrs = get_arg(get_arg(t, 0), 0).clone();
    let ctx = get_arg(get_arg(t, 0), 1).clone();
    let vars = get_arg(get_arg(t, 0), 2).clone();
    let errs = get_arg(get_arg(t, 0), 3).clone();
    let loc = get_arg(get_arg(t, 0), 4).clone();
    let path = get_arg(t, 1).clone();
    let name = get_arg(t, 2).clone();
        Some(Term::Con("attrEnvLookup".to_string(), vec![Box::new(attrs.clone()), Box::new(path.clone()), Box::new(name.clone())]))
    } else {
        None
    }
}

pub fn eval_env_has_errors(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "evalEnvHasErrors" && a.len() == 1) && matches!(get_arg(t, 0), Term::Con(ref n, ref a) if n == "MkEvalEnv" && a.len() == 5) {
    let attrs = get_arg(get_arg(t, 0), 0).clone();
    let ctx = get_arg(get_arg(t, 0), 1).clone();
    let vars = get_arg(get_arg(t, 0), 2).clone();
    let errs = get_arg(get_arg(t, 0), 3).clone();
    let loc = get_arg(get_arg(t, 0), 4).clone();
        Some(Term::Con("not".to_string(), vec![Box::new(Term::Con("null".to_string(), vec![Box::new(errs.clone())]))]))
    } else {
        None
    }
}

pub fn free_vars_var(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "freeVars" && a.len() == 1) && matches!(get_arg(t, 0), Term::Con(ref n, ref a) if n == "Var" && a.len() == 1) {
    let n = get_arg(get_arg(t, 0), 0).clone();
        Some(Term::Con("Cons".to_string(), vec![Box::new(n.clone()), Box::new(Term::Con("Nil".to_string(), vec![]))]))
    } else {
        None
    }
}

pub fn free_vars_lit(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "freeVars" && a.len() == 1) && matches!(get_arg(t, 0), Term::Con(ref n, ref a) if n == "Lit" && a.len() == 1) {
    let s = get_arg(get_arg(t, 0), 0).clone();
        Some(Term::Con("Nil".to_string(), vec![]))
    } else {
        None
    }
}

pub fn free_vars_lam(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "freeVars" && a.len() == 1) && matches!(get_arg(t, 0), Term::Con(ref n, ref a) if n == "Con" && a.len() == 2) && matches!(get_arg(get_arg(t, 0), 0), Term::Lit(ref s) if s == "\"lam\"") && matches!(get_arg(get_arg(t, 0), 1), Term::Con(ref n, ref a) if n == "Cons" && a.len() == 2) && matches!(get_arg(get_arg(get_arg(t, 0), 1), 0), Term::Con(ref n, ref a) if n == "Var" && a.len() == 1) && matches!(get_arg(get_arg(get_arg(t, 0), 1), 1), Term::Con(ref n, ref a) if n == "Cons" && a.len() == 2) && matches!(get_arg(get_arg(get_arg(get_arg(t, 0), 1), 1), 1), Term::Con(ref n, ref a) if n == "Cons" && a.len() == 2) && matches!(get_arg(get_arg(get_arg(get_arg(get_arg(t, 0), 1), 1), 1), 1), Term::Con(ref n, ref a) if n == "Nil" && a.is_empty()) {
    let x = get_arg(get_arg(get_arg(get_arg(t, 0), 1), 0), 0).clone();
    let ty = get_arg(get_arg(get_arg(get_arg(t, 0), 1), 1), 0).clone();
    let body = get_arg(get_arg(get_arg(get_arg(get_arg(t, 0), 1), 1), 1), 0).clone();
        Some(Term::Con("append".to_string(), vec![Box::new(Term::Con("freeVars".to_string(), vec![Box::new(ty.clone())])), Box::new(Term::Con("filter".to_string(), vec![Box::new(Term::Con("binder".to_string(), vec![Box::new(Term::Lit("v".to_string())), Box::new(Term::Con("not".to_string(), vec![Box::new(Term::Con("eq".to_string(), vec![Box::new(Term::Var("v".to_string())), Box::new(x.clone())]))]))])), Box::new(Term::Con("freeVars".to_string(), vec![Box::new(body.clone())]))]))]))
    } else {
        None
    }
}

pub fn free_vars_pi(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "freeVars" && a.len() == 1) && matches!(get_arg(t, 0), Term::Con(ref n, ref a) if n == "Con" && a.len() == 2) && matches!(get_arg(get_arg(t, 0), 0), Term::Lit(ref s) if s == "\"Pi\"") && matches!(get_arg(get_arg(t, 0), 1), Term::Con(ref n, ref a) if n == "Cons" && a.len() == 2) && matches!(get_arg(get_arg(get_arg(t, 0), 1), 0), Term::Con(ref n, ref a) if n == "Var" && a.len() == 1) && matches!(get_arg(get_arg(get_arg(t, 0), 1), 1), Term::Con(ref n, ref a) if n == "Cons" && a.len() == 2) && matches!(get_arg(get_arg(get_arg(get_arg(t, 0), 1), 1), 1), Term::Con(ref n, ref a) if n == "Cons" && a.len() == 2) && matches!(get_arg(get_arg(get_arg(get_arg(get_arg(t, 0), 1), 1), 1), 1), Term::Con(ref n, ref a) if n == "Nil" && a.is_empty()) {
    let x = get_arg(get_arg(get_arg(get_arg(t, 0), 1), 0), 0).clone();
    let dom = get_arg(get_arg(get_arg(get_arg(t, 0), 1), 1), 0).clone();
    let cod = get_arg(get_arg(get_arg(get_arg(get_arg(t, 0), 1), 1), 1), 0).clone();
        Some(Term::Con("append".to_string(), vec![Box::new(Term::Con("freeVars".to_string(), vec![Box::new(dom.clone())])), Box::new(Term::Con("filter".to_string(), vec![Box::new(Term::Con("binder".to_string(), vec![Box::new(Term::Lit("v".to_string())), Box::new(Term::Con("not".to_string(), vec![Box::new(Term::Con("eq".to_string(), vec![Box::new(Term::Var("v".to_string())), Box::new(x.clone())]))]))])), Box::new(Term::Con("freeVars".to_string(), vec![Box::new(cod.clone())]))]))]))
    } else {
        None
    }
}

pub fn free_vars_con(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "freeVars" && a.len() == 1) && matches!(get_arg(t, 0), Term::Con(ref n, ref a) if n == "Con" && a.len() == 2) {
    let c = get_arg(get_arg(t, 0), 0).clone();
    let args = get_arg(get_arg(t, 0), 1).clone();
        Some(Term::Con("flatMap".to_string(), vec![Box::new(Term::Con("freeVars".to_string(), vec![])), Box::new(args.clone())]))
    } else {
        None
    }
}

pub fn fresh_name(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "freshName" && a.len() == 2) {
    let base = get_arg(t, 0).clone();
    let avoid = get_arg(t, 1).clone();
        Some(Term::Con("freshNameHelper".to_string(), vec![Box::new(base.clone()), Box::new(avoid.clone()), Box::new(Term::Lit("0".to_string()))]))
    } else {
        None
    }
}

pub fn fresh_name_helper(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "freshNameHelper" && a.len() == 3) {
    let base = get_arg(t, 0).clone();
    let avoid = get_arg(t, 1).clone();
    let i = get_arg(t, 2).clone();
        Some(Term::Con("let".to_string(), vec![Box::new(Term::Var("candidate".to_string())), Box::new(Term::Con("if".to_string(), vec![Box::new(Term::Con("eq".to_string(), vec![Box::new(i.clone()), Box::new(Term::Lit("0".to_string()))])), Box::new(base.clone()), Box::new(Term::Con("concat".to_string(), vec![Box::new(base.clone()), Box::new(Term::Con("toString".to_string(), vec![Box::new(i.clone())]))]))])), Box::new(Term::Con("if".to_string(), vec![Box::new(Term::Con("contains".to_string(), vec![Box::new(avoid.clone()), Box::new(Term::Var("candidate".to_string()))])), Box::new(Term::Con("freshNameHelper".to_string(), vec![Box::new(base.clone()), Box::new(avoid.clone()), Box::new(Term::Con("add".to_string(), vec![Box::new(i.clone()), Box::new(Term::Lit("1".to_string()))]))])), Box::new(Term::Var("candidate".to_string()))]))]))
    } else {
        None
    }
}

pub fn subst_avoid_var(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "substAvoid" && a.len() == 4) && matches!(get_arg(t, 3), Term::Con(ref n, ref a) if n == "Var" && a.len() == 1) {
    let name = get_arg(t, 0).clone();
    let repl = get_arg(t, 1).clone();
    let fv = get_arg(t, 2).clone();
    let n = get_arg(get_arg(t, 3), 0).clone();
        Some(Term::Con("if".to_string(), vec![Box::new(Term::Con("eq".to_string(), vec![Box::new(n.clone()), Box::new(name.clone())])), Box::new(repl.clone()), Box::new(Term::Con("Var".to_string(), vec![Box::new(n.clone())]))]))
    } else {
        None
    }
}

pub fn subst_avoid_lit(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "substAvoid" && a.len() == 4) && matches!(get_arg(t, 3), Term::Con(ref n, ref a) if n == "Lit" && a.len() == 1) {
    let name = get_arg(t, 0).clone();
    let repl = get_arg(t, 1).clone();
    let fv = get_arg(t, 2).clone();
    let s = get_arg(get_arg(t, 3), 0).clone();
        Some(Term::Con("Lit".to_string(), vec![Box::new(s.clone())]))
    } else {
        None
    }
}

pub fn subst_avoid_lam(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "substAvoid" && a.len() == 4) && matches!(get_arg(t, 3), Term::Con(ref n, ref a) if n == "Con" && a.len() == 2) && matches!(get_arg(get_arg(t, 3), 0), Term::Lit(ref s) if s == "\"lam\"") && matches!(get_arg(get_arg(t, 3), 1), Term::Con(ref n, ref a) if n == "Cons" && a.len() == 2) && matches!(get_arg(get_arg(get_arg(t, 3), 1), 0), Term::Con(ref n, ref a) if n == "Var" && a.len() == 1) && matches!(get_arg(get_arg(get_arg(t, 3), 1), 1), Term::Con(ref n, ref a) if n == "Cons" && a.len() == 2) && matches!(get_arg(get_arg(get_arg(get_arg(t, 3), 1), 1), 1), Term::Con(ref n, ref a) if n == "Cons" && a.len() == 2) && matches!(get_arg(get_arg(get_arg(get_arg(get_arg(t, 3), 1), 1), 1), 1), Term::Con(ref n, ref a) if n == "Nil" && a.is_empty()) {
    let name = get_arg(t, 0).clone();
    let repl = get_arg(t, 1).clone();
    let fv = get_arg(t, 2).clone();
    let x = get_arg(get_arg(get_arg(get_arg(t, 3), 1), 0), 0).clone();
    let ty = get_arg(get_arg(get_arg(get_arg(t, 3), 1), 1), 0).clone();
    let body = get_arg(get_arg(get_arg(get_arg(get_arg(t, 3), 1), 1), 1), 0).clone();
        Some(Term::Con("if".to_string(), vec![Box::new(Term::Con("eq".to_string(), vec![Box::new(x.clone()), Box::new(name.clone())])), Box::new(Term::Con("Con".to_string(), vec![Box::new(Term::Lit("\"lam\"".to_string())), Box::new(Term::Con("Cons".to_string(), vec![Box::new(Term::Con("Var".to_string(), vec![Box::new(x.clone())])), Box::new(Term::Con("Cons".to_string(), vec![Box::new(Term::Con("substAvoid".to_string(), vec![Box::new(name.clone()), Box::new(repl.clone()), Box::new(fv.clone()), Box::new(ty.clone())])), Box::new(Term::Con("Cons".to_string(), vec![Box::new(body.clone()), Box::new(Term::Con("Nil".to_string(), vec![]))]))]))]))])), Box::new(Term::Con("if".to_string(), vec![Box::new(Term::Con("contains".to_string(), vec![Box::new(fv.clone()), Box::new(x.clone())])), Box::new(Term::Con("let".to_string(), vec![Box::new(Term::Var("x2".to_string())), Box::new(Term::Con("freshName".to_string(), vec![Box::new(x.clone()), Box::new(fv.clone())])), Box::new(Term::Con("let".to_string(), vec![Box::new(Term::Var("body2".to_string())), Box::new(Term::Con("subst".to_string(), vec![Box::new(x.clone()), Box::new(Term::Con("Var".to_string(), vec![Box::new(Term::Var("x2".to_string()))])), Box::new(body.clone())])), Box::new(Term::Con("Con".to_string(), vec![Box::new(Term::Lit("\"lam\"".to_string())), Box::new(Term::Con("Cons".to_string(), vec![Box::new(Term::Con("Var".to_string(), vec![Box::new(Term::Var("x2".to_string()))])), Box::new(Term::Con("Cons".to_string(), vec![Box::new(Term::Con("substAvoid".to_string(), vec![Box::new(name.clone()), Box::new(repl.clone()), Box::new(fv.clone()), Box::new(ty.clone())])), Box::new(Term::Con("Cons".to_string(), vec![Box::new(Term::Con("substAvoid".to_string(), vec![Box::new(name.clone()), Box::new(repl.clone()), Box::new(Term::Con("Cons".to_string(), vec![Box::new(Term::Var("x2".to_string())), Box::new(fv.clone())])), Box::new(Term::Var("body2".to_string()))])), Box::new(Term::Con("Nil".to_string(), vec![]))]))]))]))]))]))])), Box::new(Term::Con("Con".to_string(), vec![Box::new(Term::Lit("\"lam\"".to_string())), Box::new(Term::Con("Cons".to_string(), vec![Box::new(Term::Con("Var".to_string(), vec![Box::new(x.clone())])), Box::new(Term::Con("Cons".to_string(), vec![Box::new(Term::Con("substAvoid".to_string(), vec![Box::new(name.clone()), Box::new(repl.clone()), Box::new(fv.clone()), Box::new(ty.clone())])), Box::new(Term::Con("Cons".to_string(), vec![Box::new(Term::Con("substAvoid".to_string(), vec![Box::new(name.clone()), Box::new(repl.clone()), Box::new(fv.clone()), Box::new(body.clone())])), Box::new(Term::Con("Nil".to_string(), vec![]))]))]))]))]))]))]))
    } else {
        None
    }
}

pub fn subst_avoid_pi(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "substAvoid" && a.len() == 4) && matches!(get_arg(t, 3), Term::Con(ref n, ref a) if n == "Con" && a.len() == 2) && matches!(get_arg(get_arg(t, 3), 0), Term::Lit(ref s) if s == "\"Pi\"") && matches!(get_arg(get_arg(t, 3), 1), Term::Con(ref n, ref a) if n == "Cons" && a.len() == 2) && matches!(get_arg(get_arg(get_arg(t, 3), 1), 0), Term::Con(ref n, ref a) if n == "Var" && a.len() == 1) && matches!(get_arg(get_arg(get_arg(t, 3), 1), 1), Term::Con(ref n, ref a) if n == "Cons" && a.len() == 2) && matches!(get_arg(get_arg(get_arg(get_arg(t, 3), 1), 1), 1), Term::Con(ref n, ref a) if n == "Cons" && a.len() == 2) && matches!(get_arg(get_arg(get_arg(get_arg(get_arg(t, 3), 1), 1), 1), 1), Term::Con(ref n, ref a) if n == "Nil" && a.is_empty()) {
    let name = get_arg(t, 0).clone();
    let repl = get_arg(t, 1).clone();
    let fv = get_arg(t, 2).clone();
    let x = get_arg(get_arg(get_arg(get_arg(t, 3), 1), 0), 0).clone();
    let dom = get_arg(get_arg(get_arg(get_arg(t, 3), 1), 1), 0).clone();
    let cod = get_arg(get_arg(get_arg(get_arg(get_arg(t, 3), 1), 1), 1), 0).clone();
        Some(Term::Con("if".to_string(), vec![Box::new(Term::Con("eq".to_string(), vec![Box::new(x.clone()), Box::new(name.clone())])), Box::new(Term::Con("Con".to_string(), vec![Box::new(Term::Lit("\"Pi\"".to_string())), Box::new(Term::Con("Cons".to_string(), vec![Box::new(Term::Con("Var".to_string(), vec![Box::new(x.clone())])), Box::new(Term::Con("Cons".to_string(), vec![Box::new(Term::Con("substAvoid".to_string(), vec![Box::new(name.clone()), Box::new(repl.clone()), Box::new(fv.clone()), Box::new(dom.clone())])), Box::new(Term::Con("Cons".to_string(), vec![Box::new(cod.clone()), Box::new(Term::Con("Nil".to_string(), vec![]))]))]))]))])), Box::new(Term::Con("if".to_string(), vec![Box::new(Term::Con("contains".to_string(), vec![Box::new(fv.clone()), Box::new(x.clone())])), Box::new(Term::Con("let".to_string(), vec![Box::new(Term::Var("x2".to_string())), Box::new(Term::Con("freshName".to_string(), vec![Box::new(x.clone()), Box::new(fv.clone())])), Box::new(Term::Con("let".to_string(), vec![Box::new(Term::Var("cod2".to_string())), Box::new(Term::Con("subst".to_string(), vec![Box::new(x.clone()), Box::new(Term::Con("Var".to_string(), vec![Box::new(Term::Var("x2".to_string()))])), Box::new(cod.clone())])), Box::new(Term::Con("Con".to_string(), vec![Box::new(Term::Lit("\"Pi\"".to_string())), Box::new(Term::Con("Cons".to_string(), vec![Box::new(Term::Con("Var".to_string(), vec![Box::new(Term::Var("x2".to_string()))])), Box::new(Term::Con("Cons".to_string(), vec![Box::new(Term::Con("substAvoid".to_string(), vec![Box::new(name.clone()), Box::new(repl.clone()), Box::new(fv.clone()), Box::new(dom.clone())])), Box::new(Term::Con("Cons".to_string(), vec![Box::new(Term::Con("substAvoid".to_string(), vec![Box::new(name.clone()), Box::new(repl.clone()), Box::new(Term::Con("Cons".to_string(), vec![Box::new(Term::Var("x2".to_string())), Box::new(fv.clone())])), Box::new(Term::Var("cod2".to_string()))])), Box::new(Term::Con("Nil".to_string(), vec![]))]))]))]))]))]))])), Box::new(Term::Con("Con".to_string(), vec![Box::new(Term::Lit("\"Pi\"".to_string())), Box::new(Term::Con("Cons".to_string(), vec![Box::new(Term::Con("Var".to_string(), vec![Box::new(x.clone())])), Box::new(Term::Con("Cons".to_string(), vec![Box::new(Term::Con("substAvoid".to_string(), vec![Box::new(name.clone()), Box::new(repl.clone()), Box::new(fv.clone()), Box::new(dom.clone())])), Box::new(Term::Con("Cons".to_string(), vec![Box::new(Term::Con("substAvoid".to_string(), vec![Box::new(name.clone()), Box::new(repl.clone()), Box::new(fv.clone()), Box::new(cod.clone())])), Box::new(Term::Con("Nil".to_string(), vec![]))]))]))]))]))]))]))
    } else {
        None
    }
}

pub fn subst_avoid_con(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "substAvoid" && a.len() == 4) && matches!(get_arg(t, 3), Term::Con(ref n, ref a) if n == "Con" && a.len() == 2) {
    let name = get_arg(t, 0).clone();
    let repl = get_arg(t, 1).clone();
    let fv = get_arg(t, 2).clone();
    let c = get_arg(get_arg(t, 3), 0).clone();
    let args = get_arg(get_arg(t, 3), 1).clone();
        Some(Term::Con("Con".to_string(), vec![Box::new(c.clone()), Box::new(Term::Con("map".to_string(), vec![Box::new(Term::Con("binder".to_string(), vec![Box::new(Term::Lit("a".to_string())), Box::new(Term::Con("substAvoid".to_string(), vec![Box::new(name.clone()), Box::new(repl.clone()), Box::new(fv.clone()), Box::new(Term::Var("a".to_string()))]))])), Box::new(args.clone())]))]))
    } else {
        None
    }
}

pub fn attr_ref_self(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "attrRefSelf" && a.len() == 1) {
    let name = get_arg(t, 0).clone();
        Some(Term::Con("MkAttrRef".to_string(), vec![Box::new(Term::Con("Empty".to_string(), vec![])), Box::new(name.clone())]))
    } else {
        None
    }
}

pub fn attr_ref_child(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "attrRefChild" && a.len() == 2) {
    let child = get_arg(t, 0).clone();
    let name = get_arg(t, 1).clone();
        Some(Term::Con("MkAttrRef".to_string(), vec![Box::new(Term::Con("PathCon".to_string(), vec![Box::new(child.clone()), Box::new(Term::Con("Empty".to_string(), vec![]))])), Box::new(name.clone())]))
    } else {
        None
    }
}

pub fn empty_attr_def(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "emptyAttrDef" && a.len() == 2) {
    let name = get_arg(t, 0).clone();
    let flow = get_arg(t, 1).clone();
        Some(Term::Con("MkAttrDef".to_string(), vec![Box::new(name.clone()), Box::new(flow.clone()), Box::new(Term::Con("None".to_string(), vec![])), Box::new(Term::Con("Nil".to_string(), vec![]))]))
    } else {
        None
    }
}

pub fn add_attr_rule(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "addAttrRule" && a.len() == 2) && matches!(get_arg(t, 0), Term::Con(ref n, ref a) if n == "MkAttrDef" && a.len() == 4) {
    let name = get_arg(get_arg(t, 0), 0).clone();
    let flow = get_arg(get_arg(t, 0), 1).clone();
    let ty = get_arg(get_arg(t, 0), 2).clone();
    let rules = get_arg(get_arg(t, 0), 3).clone();
    let rule = get_arg(t, 1).clone();
        Some(Term::Con("MkAttrDef".to_string(), vec![Box::new(name.clone()), Box::new(flow.clone()), Box::new(ty.clone()), Box::new(Term::Con("append".to_string(), vec![Box::new(rules.clone()), Box::new(Term::Con("Cons".to_string(), vec![Box::new(rule.clone()), Box::new(Term::Con("Nil".to_string(), vec![]))]))]))]))
    } else {
        None
    }
}

pub fn attr_env_lookup_empty(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "attrEnvLookup" && a.len() == 3) && matches!(get_arg(t, 0), Term::Con(ref n, ref a) if n == "Empty" && a.is_empty()) {
    let path = get_arg(t, 1).clone();
    let name = get_arg(t, 2).clone();
        Some(Term::Con("None".to_string(), vec![]))
    } else {
        None
    }
}

pub fn attr_env_lookup_found(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "attrEnvLookup" && a.len() == 3) && matches!(get_arg(t, 0), Term::Con(ref n, ref a) if n == "AttrEnvCons" && a.len() == 4) {
    let path = get_arg(get_arg(t, 0), 0).clone();
    let name = get_arg(get_arg(t, 0), 1).clone();
    let val = get_arg(get_arg(t, 0), 2).clone();
    let rest = get_arg(get_arg(t, 0), 3).clone();
        Some(Term::Con("Some".to_string(), vec![Box::new(val.clone())]))
    } else {
        None
    }
}

pub fn attr_env_lookup_miss(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "attrEnvLookup" && a.len() == 3) && matches!(get_arg(t, 0), Term::Con(ref n, ref a) if n == "AttrEnvCons" && a.len() == 4) {
    let p1 = get_arg(get_arg(t, 0), 0).clone();
    let n1 = get_arg(get_arg(t, 0), 1).clone();
    let val = get_arg(get_arg(t, 0), 2).clone();
    let rest = get_arg(get_arg(t, 0), 3).clone();
    let p2 = get_arg(t, 1).clone();
    let n2 = get_arg(t, 2).clone();
        Some(Term::Con("attrEnvLookup".to_string(), vec![Box::new(rest.clone()), Box::new(p2.clone()), Box::new(n2.clone())]))
    } else {
        None
    }
}

pub fn attr_env_insert(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "attrEnvInsert" && a.len() == 4) {
    let env = get_arg(t, 0).clone();
    let path = get_arg(t, 1).clone();
    let name = get_arg(t, 2).clone();
    let val = get_arg(t, 3).clone();
        Some(Term::Con("AttrEnvCons".to_string(), vec![Box::new(path.clone()), Box::new(name.clone()), Box::new(val.clone()), Box::new(env.clone())]))
    } else {
        None
    }
}

pub fn attr_env_get_local(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "attrEnvGetLocal" && a.len() == 2) {
    let env = get_arg(t, 0).clone();
    let name = get_arg(t, 1).clone();
        Some(Term::Con("attrEnvLookup".to_string(), vec![Box::new(env.clone()), Box::new(Term::Con("Empty".to_string(), vec![])), Box::new(name.clone())]))
    } else {
        None
    }
}

pub fn attr_env_get_child(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "attrEnvGetChild" && a.len() == 3) {
    let env = get_arg(t, 0).clone();
    let child = get_arg(t, 1).clone();
    let name = get_arg(t, 2).clone();
        Some(Term::Con("attrEnvLookup".to_string(), vec![Box::new(env.clone()), Box::new(Term::Con("PathCon".to_string(), vec![Box::new(child.clone()), Box::new(Term::Con("Empty".to_string(), vec![]))])), Box::new(name.clone())]))
    } else {
        None
    }
}

pub fn attr_env_merge_empty(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "attrEnvMerge" && a.len() == 2) && matches!(get_arg(t, 1), Term::Con(ref n, ref a) if n == "EmptyAttrEnv" && a.is_empty()) {
    let env1 = get_arg(t, 0).clone();
        Some(env1.clone())
    } else {
        None
    }
}

pub fn attr_env_merge_cons(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "attrEnvMerge" && a.len() == 2) && matches!(get_arg(t, 1), Term::Con(ref n, ref a) if n == "AttrEnvCons" && a.len() == 4) {
    let env1 = get_arg(t, 0).clone();
    let path = get_arg(get_arg(t, 1), 0).clone();
    let name = get_arg(get_arg(t, 1), 1).clone();
    let val = get_arg(get_arg(t, 1), 2).clone();
    let rest = get_arg(get_arg(t, 1), 3).clone();
        Some(Term::Con("attrEnvMerge".to_string(), vec![Box::new(Term::Con("AttrEnvCons".to_string(), vec![Box::new(path.clone()), Box::new(name.clone()), Box::new(val.clone()), Box::new(env1.clone())])), Box::new(rest.clone())]))
    } else {
        None
    }
}

pub fn eval_attr_expr_var(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "evalAttrExpr" && a.len() == 2) && matches!(get_arg(t, 0), Term::Con(ref n, ref a) if n == "Var" && a.len() == 1) {
    let name = get_arg(get_arg(t, 0), 0).clone();
    let env = get_arg(t, 1).clone();
        Some(Term::Con("if".to_string(), vec![Box::new(Term::Con("startsWith".to_string(), vec![Box::new(name.clone()), Box::new(Term::Lit("\"$\"".to_string()))])), Box::new(Term::Con("match".to_string(), vec![Box::new(Term::Con("attrEnvLookup".to_string(), vec![Box::new(env.clone()), Box::new(Term::Con("Empty".to_string(), vec![])), Box::new(Term::Con("drop".to_string(), vec![Box::new(Term::Lit("1".to_string())), Box::new(name.clone())]))])), Box::new(Term::Con("Some".to_string(), vec![Box::new(Term::Var("v".to_string()))])), Box::new(Term::Var("v".to_string())), Box::new(Term::Con("None".to_string(), vec![])), Box::new(Term::Con("Con".to_string(), vec![Box::new(Term::Lit("\"error\"".to_string())), Box::new(Term::Con("Cons".to_string(), vec![Box::new(Term::Con("Lit".to_string(), vec![Box::new(Term::Con("concat".to_string(), vec![Box::new(Term::Lit("\"undefined: \"".to_string())), Box::new(name.clone())]))])), Box::new(Term::Con("Nil".to_string(), vec![]))]))]))])), Box::new(Term::Con("Var".to_string(), vec![Box::new(name.clone())]))]))
    } else {
        None
    }
}

pub fn eval_attr_expr_con(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "evalAttrExpr" && a.len() == 2) && matches!(get_arg(t, 0), Term::Con(ref n, ref a) if n == "Con" && a.len() == 2) {
    let c = get_arg(get_arg(t, 0), 0).clone();
    let args = get_arg(get_arg(t, 0), 1).clone();
    let env = get_arg(t, 1).clone();
        Some(Term::Con("Con".to_string(), vec![Box::new(c.clone()), Box::new(Term::Con("map".to_string(), vec![Box::new(Term::Con("binder".to_string(), vec![Box::new(Term::Lit("x".to_string())), Box::new(Term::Con("evalAttrExpr".to_string(), vec![Box::new(Term::Var("x".to_string())), Box::new(env.clone())]))])), Box::new(args.clone())]))]))
    } else {
        None
    }
}

pub fn eval_attr_expr_lit(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "evalAttrExpr" && a.len() == 2) && matches!(get_arg(t, 0), Term::Con(ref n, ref a) if n == "Lit" && a.len() == 1) {
    let s = get_arg(get_arg(t, 0), 0).clone();
    let env = get_arg(t, 1).clone();
        Some(Term::Con("Lit".to_string(), vec![Box::new(s.clone())]))
    } else {
        None
    }
}

pub fn find_rule_empty(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "findRule" && a.len() == 3) && matches!(get_arg(t, 2), Term::Con(ref n, ref a) if n == "Nil" && a.is_empty()) {
    let prod = get_arg(t, 0).clone();
    let target = get_arg(t, 1).clone();
        Some(Term::Con("None".to_string(), vec![]))
    } else {
        None
    }
}

pub fn find_rule_found(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "findRule" && a.len() == 3) && matches!(get_arg(t, 2), Term::Con(ref n, ref a) if n == "Cons" && a.len() == 2) && matches!(get_arg(get_arg(t, 2), 0), Term::Con(ref n, ref a) if n == "MkAttrRule" && a.len() == 3) {
    let prod = get_arg(t, 0).clone();
    let target = get_arg(t, 1).clone();
    let expr = get_arg(get_arg(get_arg(t, 2), 0), 2).clone();
    let rest = get_arg(get_arg(t, 2), 1).clone();
        Some(Term::Con("Some".to_string(), vec![Box::new(Term::Con("MkAttrRule".to_string(), vec![Box::new(prod.clone()), Box::new(target.clone()), Box::new(expr.clone())]))]))
    } else {
        None
    }
}

pub fn find_rule_miss(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "findRule" && a.len() == 3) && matches!(get_arg(t, 2), Term::Con(ref n, ref a) if n == "Cons" && a.len() == 2) && matches!(get_arg(get_arg(t, 2), 0), Term::Con(ref n, ref a) if n == "MkAttrRule" && a.len() == 3) {
    let prod = get_arg(t, 0).clone();
    let target = get_arg(t, 1).clone();
    let p2 = get_arg(get_arg(get_arg(t, 2), 0), 0).clone();
    let t2 = get_arg(get_arg(get_arg(t, 2), 0), 1).clone();
    let e = get_arg(get_arg(get_arg(t, 2), 0), 2).clone();
    let rest = get_arg(get_arg(t, 2), 1).clone();
        Some(Term::Con("findRule".to_string(), vec![Box::new(prod.clone()), Box::new(target.clone()), Box::new(rest.clone())]))
    } else {
        None
    }
}

pub fn eval_syn_var(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "evalSyn" && a.len() == 2) && matches!(get_arg(t, 1), Term::Con(ref n, ref a) if n == "Var" && a.len() == 1) {
    let def = get_arg(t, 0).clone();
    let x = get_arg(get_arg(t, 1), 0).clone();
        Some(Term::Con("EmptyAttrEnv".to_string(), vec![]))
    } else {
        None
    }
}

pub fn eval_syn_lit(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "evalSyn" && a.len() == 2) && matches!(get_arg(t, 1), Term::Con(ref n, ref a) if n == "Lit" && a.len() == 1) {
    let def = get_arg(t, 0).clone();
    let s = get_arg(get_arg(t, 1), 0).clone();
        Some(Term::Con("EmptyAttrEnv".to_string(), vec![]))
    } else {
        None
    }
}

pub fn eval_syn_con(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "evalSyn" && a.len() == 2) && matches!(get_arg(t, 0), Term::Con(ref n, ref a) if n == "MkAttrDef" && a.len() == 4) && matches!(get_arg(t, 1), Term::Con(ref n, ref a) if n == "Con" && a.len() == 2) {
    let attrName = get_arg(get_arg(t, 0), 0).clone();
    let flow = get_arg(get_arg(t, 0), 1).clone();
    let ty = get_arg(get_arg(t, 0), 2).clone();
    let rules = get_arg(get_arg(t, 0), 3).clone();
    let prod = get_arg(get_arg(t, 1), 0).clone();
    let children = get_arg(get_arg(t, 1), 1).clone();
        Some(Term::Con("evalSynConHelper".to_string(), vec![Box::new(attrName.clone()), Box::new(flow.clone()), Box::new(ty.clone()), Box::new(rules.clone()), Box::new(prod.clone()), Box::new(children.clone()), Box::new(Term::Lit("0".to_string()))]))
    } else {
        None
    }
}

pub fn eval_syn_con_helper(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "evalSynConHelper" && a.len() == 7) {
    let attrName = get_arg(t, 0).clone();
    let flow = get_arg(t, 1).clone();
    let ty = get_arg(t, 2).clone();
    let rules = get_arg(t, 3).clone();
    let prod = get_arg(t, 4).clone();
    let children = get_arg(t, 5).clone();
    let idx = get_arg(t, 6).clone();
        Some(Term::Con("let".to_string(), vec![Box::new(Term::Var("childEnvs".to_string())), Box::new(Term::Con("mapWithIndex".to_string(), vec![Box::new(Term::Con("i".to_string(), vec![Box::new(Term::Con("binder".to_string(), vec![Box::new(Term::Lit("child".to_string())), Box::new(Term::Con("prefixEnv".to_string(), vec![Box::new(Term::Con("concat".to_string(), vec![Box::new(Term::Lit("\"child\"".to_string())), Box::new(Term::Con("toString".to_string(), vec![Box::new(Term::Var("i".to_string()))]))])), Box::new(Term::Con("evalSyn".to_string(), vec![Box::new(Term::Con("MkAttrDef".to_string(), vec![Box::new(attrName.clone()), Box::new(flow.clone()), Box::new(ty.clone()), Box::new(rules.clone())])), Box::new(Term::Var("child".to_string()))]))]))]))])), Box::new(children.clone())])), Box::new(Term::Con("let".to_string(), vec![Box::new(Term::Var("env".to_string())), Box::new(Term::Con("foldl".to_string(), vec![Box::new(Term::Con("attrEnvMerge".to_string(), vec![])), Box::new(Term::Con("EmptyAttrEnv".to_string(), vec![])), Box::new(Term::Var("childEnvs".to_string()))])), Box::new(Term::Con("match".to_string(), vec![Box::new(Term::Con("findRule".to_string(), vec![Box::new(prod.clone()), Box::new(Term::Con("Empty".to_string(), vec![])), Box::new(rules.clone())])), Box::new(Term::Con("Some".to_string(), vec![Box::new(Term::Con("MkAttrRule".to_string(), vec![Box::new(Term::Var("p".to_string())), Box::new(Term::Var("t".to_string())), Box::new(Term::Var("expr".to_string()))]))])), Box::new(Term::Con("attrEnvInsert".to_string(), vec![Box::new(Term::Var("env".to_string())), Box::new(Term::Con("Empty".to_string(), vec![])), Box::new(attrName.clone()), Box::new(Term::Con("evalAttrExpr".to_string(), vec![Box::new(Term::Var("expr".to_string())), Box::new(Term::Var("env".to_string()))]))])), Box::new(Term::Con("None".to_string(), vec![])), Box::new(Term::Var("env".to_string()))]))]))]))
    } else {
        None
    }
}

pub fn eval_inh_var(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "evalInh" && a.len() == 3) && matches!(get_arg(t, 1), Term::Con(ref n, ref a) if n == "Var" && a.len() == 1) {
    let def = get_arg(t, 0).clone();
    let x = get_arg(get_arg(t, 1), 0).clone();
    let parentEnv = get_arg(t, 2).clone();
        Some(parentEnv.clone())
    } else {
        None
    }
}

pub fn eval_inh_lit(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "evalInh" && a.len() == 3) && matches!(get_arg(t, 1), Term::Con(ref n, ref a) if n == "Lit" && a.len() == 1) {
    let def = get_arg(t, 0).clone();
    let s = get_arg(get_arg(t, 1), 0).clone();
    let parentEnv = get_arg(t, 2).clone();
        Some(parentEnv.clone())
    } else {
        None
    }
}

pub fn eval_inh_con(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "evalInh" && a.len() == 3) && matches!(get_arg(t, 0), Term::Con(ref n, ref a) if n == "MkAttrDef" && a.len() == 4) && matches!(get_arg(t, 1), Term::Con(ref n, ref a) if n == "Con" && a.len() == 2) {
    let attrName = get_arg(get_arg(t, 0), 0).clone();
    let flow = get_arg(get_arg(t, 0), 1).clone();
    let ty = get_arg(get_arg(t, 0), 2).clone();
    let rules = get_arg(get_arg(t, 0), 3).clone();
    let prod = get_arg(get_arg(t, 1), 0).clone();
    let children = get_arg(get_arg(t, 1), 1).clone();
    let parentEnv = get_arg(t, 2).clone();
        Some(Term::Con("evalInhConHelper".to_string(), vec![Box::new(attrName.clone()), Box::new(flow.clone()), Box::new(ty.clone()), Box::new(rules.clone()), Box::new(prod.clone()), Box::new(children.clone()), Box::new(parentEnv.clone()), Box::new(Term::Lit("0".to_string()))]))
    } else {
        None
    }
}

pub fn eval_attrs(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "evalAttrs" && a.len() == 2) {
    let defs = get_arg(t, 0).clone();
    let term = get_arg(t, 1).clone();
        Some(Term::Con("let".to_string(), vec![Box::new(Term::Var("synDefs".to_string())), Box::new(Term::Con("filter".to_string(), vec![Box::new(Term::Con("binder".to_string(), vec![Box::new(Term::Lit("d".to_string())), Box::new(Term::Con("eq".to_string(), vec![Box::new(Term::Con("attrDefFlow".to_string(), vec![Box::new(Term::Var("d".to_string()))])), Box::new(Term::Con("Syn".to_string(), vec![]))]))])), Box::new(defs.clone())])), Box::new(Term::Con("let".to_string(), vec![Box::new(Term::Var("inhDefs".to_string())), Box::new(Term::Con("filter".to_string(), vec![Box::new(Term::Con("binder".to_string(), vec![Box::new(Term::Lit("d".to_string())), Box::new(Term::Con("eq".to_string(), vec![Box::new(Term::Con("attrDefFlow".to_string(), vec![Box::new(Term::Var("d".to_string()))])), Box::new(Term::Con("Inh".to_string(), vec![]))]))])), Box::new(defs.clone())])), Box::new(Term::Con("let".to_string(), vec![Box::new(Term::Var("inhEnv".to_string())), Box::new(Term::Con("foldl".to_string(), vec![Box::new(Term::Con("env".to_string(), vec![Box::new(Term::Con("binder".to_string(), vec![Box::new(Term::Lit("def".to_string())), Box::new(Term::Con("evalInh".to_string(), vec![Box::new(Term::Var("def".to_string())), Box::new(term.clone()), Box::new(Term::Var("env".to_string()))]))]))])), Box::new(Term::Con("EmptyAttrEnv".to_string(), vec![])), Box::new(Term::Var("inhDefs".to_string()))])), Box::new(Term::Con("foldl".to_string(), vec![Box::new(Term::Con("env".to_string(), vec![Box::new(Term::Con("binder".to_string(), vec![Box::new(Term::Lit("def".to_string())), Box::new(Term::Con("attrEnvMerge".to_string(), vec![Box::new(Term::Var("env".to_string())), Box::new(Term::Con("evalSyn".to_string(), vec![Box::new(Term::Var("def".to_string())), Box::new(term.clone())]))]))]))])), Box::new(Term::Var("inhEnv".to_string())), Box::new(Term::Var("synDefs".to_string()))]))]))]))]))
    } else {
        None
    }
}

pub fn cata_term_var(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "cataTerm" && a.len() == 2) && matches!(get_arg(t, 1), Term::Con(ref n, ref a) if n == "Var" && a.len() == 1) {
    let alg = get_arg(t, 0).clone();
    let x = get_arg(get_arg(t, 1), 0).clone();
        Some(Term::Con("app".to_string(), vec![Box::new(x.clone()), Box::new(Term::Con("Nil".to_string(), vec![]))]))
    } else {
        None
    }
}

pub fn cata_term_lit(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "cataTerm" && a.len() == 2) && matches!(get_arg(t, 1), Term::Con(ref n, ref a) if n == "Lit" && a.len() == 1) {
    let alg = get_arg(t, 0).clone();
    let s = get_arg(get_arg(t, 1), 0).clone();
        Some(Term::Con("app".to_string(), vec![Box::new(s.clone()), Box::new(Term::Con("Nil".to_string(), vec![]))]))
    } else {
        None
    }
}

pub fn cata_term_con(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "cataTerm" && a.len() == 2) && matches!(get_arg(t, 1), Term::Con(ref n, ref a) if n == "Con" && a.len() == 2) {
    let alg = get_arg(t, 0).clone();
    let c = get_arg(get_arg(t, 1), 0).clone();
    let args = get_arg(get_arg(t, 1), 1).clone();
        Some(Term::Con("app".to_string(), vec![Box::new(c.clone()), Box::new(Term::Con("map".to_string(), vec![Box::new(Term::Con("binder".to_string(), vec![Box::new(Term::Lit("a".to_string())), Box::new(Term::Con("cataTerm".to_string(), vec![Box::new(alg.clone()), Box::new(Term::Var("a".to_string()))]))])), Box::new(args.clone())]))]))
    } else {
        None
    }
}

pub fn para_term_var(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "paraTerm" && a.len() == 2) && matches!(get_arg(t, 1), Term::Con(ref n, ref a) if n == "Var" && a.len() == 1) {
    let coalg = get_arg(t, 0).clone();
    let x = get_arg(get_arg(t, 1), 0).clone();
        Some(Term::Con("app".to_string(), vec![Box::new(x.clone()), Box::new(Term::Con("Nil".to_string(), vec![]))]))
    } else {
        None
    }
}

pub fn para_term_lit(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "paraTerm" && a.len() == 2) && matches!(get_arg(t, 1), Term::Con(ref n, ref a) if n == "Lit" && a.len() == 1) {
    let coalg = get_arg(t, 0).clone();
    let s = get_arg(get_arg(t, 1), 0).clone();
        Some(Term::Con("app".to_string(), vec![Box::new(s.clone()), Box::new(Term::Con("Nil".to_string(), vec![]))]))
    } else {
        None
    }
}

pub fn para_term_con(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "paraTerm" && a.len() == 2) && matches!(get_arg(t, 1), Term::Con(ref n, ref a) if n == "Con" && a.len() == 2) {
    let coalg = get_arg(t, 0).clone();
    let c = get_arg(get_arg(t, 1), 0).clone();
    let args = get_arg(get_arg(t, 1), 1).clone();
        Some(Term::Con("app".to_string(), vec![Box::new(c.clone()), Box::new(Term::Con("map".to_string(), vec![Box::new(Term::Con("binder".to_string(), vec![Box::new(Term::Lit("a".to_string())), Box::new(Term::Con("Pair".to_string(), vec![Box::new(Term::Var("a".to_string())), Box::new(Term::Con("paraTerm".to_string(), vec![Box::new(coalg.clone()), Box::new(Term::Var("a".to_string()))]))]))])), Box::new(args.clone())]))]))
    } else {
        None
    }
}

pub fn attr_lang_syn_attrs(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "attrLangSynAttrs" && a.len() == 1) && matches!(get_arg(t, 0), Term::Con(ref n, ref a) if n == "MkAttrLanguage" && a.len() == 3) {
    let name = get_arg(get_arg(t, 0), 0).clone();
    let pieces = get_arg(get_arg(t, 0), 1).clone();
    let attrs = get_arg(get_arg(t, 0), 2).clone();
        Some(Term::Con("filter".to_string(), vec![Box::new(Term::Con("binder".to_string(), vec![Box::new(Term::Lit("d".to_string())), Box::new(Term::Con("eq".to_string(), vec![Box::new(Term::Con("attrDefFlow".to_string(), vec![Box::new(Term::Var("d".to_string()))])), Box::new(Term::Con("Syn".to_string(), vec![]))]))])), Box::new(attrs.clone())]))
    } else {
        None
    }
}

pub fn attr_lang_inh_attrs(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "attrLangInhAttrs" && a.len() == 1) && matches!(get_arg(t, 0), Term::Con(ref n, ref a) if n == "MkAttrLanguage" && a.len() == 3) {
    let name = get_arg(get_arg(t, 0), 0).clone();
    let pieces = get_arg(get_arg(t, 0), 1).clone();
    let attrs = get_arg(get_arg(t, 0), 2).clone();
        Some(Term::Con("filter".to_string(), vec![Box::new(Term::Con("binder".to_string(), vec![Box::new(Term::Lit("d".to_string())), Box::new(Term::Con("eq".to_string(), vec![Box::new(Term::Con("attrDefFlow".to_string(), vec![Box::new(Term::Var("d".to_string()))])), Box::new(Term::Con("Inh".to_string(), vec![]))]))])), Box::new(attrs.clone())]))
    } else {
        None
    }
}

pub fn attr_lang_eval(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "attrLangEval" && a.len() == 2) && matches!(get_arg(t, 0), Term::Con(ref n, ref a) if n == "MkAttrLanguage" && a.len() == 3) {
    let name = get_arg(get_arg(t, 0), 0).clone();
    let pieces = get_arg(get_arg(t, 0), 1).clone();
    let attrs = get_arg(get_arg(t, 0), 2).clone();
    let term = get_arg(t, 1).clone();
        Some(Term::Con("evalAttrs".to_string(), vec![Box::new(attrs.clone()), Box::new(term.clone())]))
    } else {
        None
    }
}

pub fn attr_lang_pushout(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "attrLangPushout" && a.len() == 2) && matches!(get_arg(t, 0), Term::Con(ref n, ref a) if n == "MkAttrLanguage" && a.len() == 3) && matches!(get_arg(t, 1), Term::Con(ref n, ref a) if n == "MkAttrLanguage" && a.len() == 3) {
    let n1 = get_arg(get_arg(t, 0), 0).clone();
    let p1 = get_arg(get_arg(t, 0), 1).clone();
    let a1 = get_arg(get_arg(t, 0), 2).clone();
    let n2 = get_arg(get_arg(t, 1), 0).clone();
    let p2 = get_arg(get_arg(t, 1), 1).clone();
    let a2 = get_arg(get_arg(t, 1), 2).clone();
        Some(Term::Con("MkAttrLanguage".to_string(), vec![Box::new(Term::Con("concat".to_string(), vec![Box::new(Term::Con("concat".to_string(), vec![Box::new(n1.clone()), Box::new(Term::Lit("\"_\"".to_string()))])), Box::new(n2.clone())])), Box::new(Term::Con("append".to_string(), vec![Box::new(p1.clone()), Box::new(p2.clone())])), Box::new(Term::Con("append".to_string(), vec![Box::new(a1.clone()), Box::new(a2.clone())]))]))
    } else {
        None
    }
}

pub fn tok_eq(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "tokEq" && a.len() == 2) && matches!(get_arg(t, 0), Term::Con(ref n, ref a) if n == "TokIdent" && a.len() == 1) && matches!(get_arg(t, 1), Term::Con(ref n, ref a) if n == "TokIdent" && a.len() == 1) {
    let a = get_arg(get_arg(t, 0), 0).clone();
    let b = get_arg(get_arg(t, 1), 0).clone();
        Some(Term::Con("strEq".to_string(), vec![Box::new(a.clone()), Box::new(b.clone())]))
    } else {
        None
    }
}

pub fn tok_eq_string(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "tokEq" && a.len() == 2) && matches!(get_arg(t, 0), Term::Con(ref n, ref a) if n == "TokString" && a.len() == 1) && matches!(get_arg(t, 1), Term::Con(ref n, ref a) if n == "TokString" && a.len() == 1) {
    let a = get_arg(get_arg(t, 0), 0).clone();
    let b = get_arg(get_arg(t, 1), 0).clone();
        Some(Term::Con("strEq".to_string(), vec![Box::new(a.clone()), Box::new(b.clone())]))
    } else {
        None
    }
}

pub fn tok_eq_sym(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "tokEq" && a.len() == 2) && matches!(get_arg(t, 0), Term::Con(ref n, ref a) if n == "TokSym" && a.len() == 1) && matches!(get_arg(t, 1), Term::Con(ref n, ref a) if n == "TokSym" && a.len() == 1) {
    let a = get_arg(get_arg(t, 0), 0).clone();
    let b = get_arg(get_arg(t, 1), 0).clone();
        Some(Term::Con("strEq".to_string(), vec![Box::new(a.clone()), Box::new(b.clone())]))
    } else {
        None
    }
}

pub fn tok_eq_mismatch(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "tokEq" && a.len() == 2) {
    let a = get_arg(t, 0).clone();
    let b = get_arg(t, 1).clone();
        Some(Term::Con("false".to_string(), vec![]))
    } else {
        None
    }
}

pub fn state_tokens(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "stateTokens" && a.len() == 1) && matches!(get_arg(t, 0), Term::Con(ref n, ref a) if n == "MkState" && a.len() == 2) {
    let toks = get_arg(get_arg(t, 0), 0).clone();
    let pos = get_arg(get_arg(t, 0), 1).clone();
        Some(toks.clone())
    } else {
        None
    }
}

pub fn state_pos(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "statePos" && a.len() == 1) && matches!(get_arg(t, 0), Term::Con(ref n, ref a) if n == "MkState" && a.len() == 2) {
    let toks = get_arg(get_arg(t, 0), 0).clone();
    let pos = get_arg(get_arg(t, 0), 1).clone();
        Some(pos.clone())
    } else {
        None
    }
}

pub fn state_advance(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "stateAdvance" && a.len() == 1) && matches!(get_arg(t, 0), Term::Con(ref n, ref a) if n == "MkState" && a.len() == 2) && matches!(get_arg(get_arg(t, 0), 0), Term::Con(ref n, ref a) if n == "Cons" && a.len() == 2) {
    let v_t = get_arg(get_arg(get_arg(t, 0), 0), 0).clone();
    let ts = get_arg(get_arg(get_arg(t, 0), 0), 1).clone();
    let pos = get_arg(get_arg(t, 0), 1).clone();
        Some(Term::Con("MkState".to_string(), vec![Box::new(ts.clone()), Box::new(Term::Con("add".to_string(), vec![Box::new(pos.clone()), Box::new(Term::Lit("1".to_string()))]))]))
    } else {
        None
    }
}

pub fn parse_lit(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "parseLit" && a.len() == 2) && matches!(get_arg(t, 1), Term::Con(ref n, ref a) if n == "MkState" && a.len() == 2) && matches!(get_arg(get_arg(t, 1), 0), Term::Con(ref n, ref a) if n == "Cons" && a.len() == 2) && matches!(get_arg(get_arg(get_arg(t, 1), 0), 0), Term::Con(ref n, ref a) if n == "TokSym" && a.len() == 1) {
    let s = get_arg(t, 0).clone();
    let rest = get_arg(get_arg(get_arg(t, 1), 0), 1).clone();
    let pos = get_arg(get_arg(t, 1), 1).clone();
        Some(Term::Con("ParseOk".to_string(), vec![Box::new(Term::Con("Lit".to_string(), vec![Box::new(s.clone())])), Box::new(Term::Con("MkState".to_string(), vec![Box::new(rest.clone()), Box::new(Term::Con("add".to_string(), vec![Box::new(pos.clone()), Box::new(Term::Lit("1".to_string()))]))]))]))
    } else {
        None
    }
}

pub fn parse_lit_fail(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "parseLit" && a.len() == 2) && matches!(get_arg(t, 1), Term::Con(ref n, ref a) if n == "MkState" && a.len() == 2) && matches!(get_arg(get_arg(t, 1), 0), Term::Con(ref n, ref a) if n == "Cons" && a.len() == 2) {
    let s = get_arg(t, 0).clone();
    let v_t = get_arg(get_arg(get_arg(t, 1), 0), 0).clone();
    let rest = get_arg(get_arg(get_arg(t, 1), 0), 1).clone();
    let pos = get_arg(get_arg(t, 1), 1).clone();
        Some(Term::Con("ParseFail".to_string(), vec![Box::new(Term::Con("concat".to_string(), vec![Box::new(Term::Lit("\"expected \"".to_string())), Box::new(s.clone())])), Box::new(Term::Con("MkState".to_string(), vec![Box::new(Term::Con("Cons".to_string(), vec![Box::new(v_t.clone()), Box::new(rest.clone())])), Box::new(pos.clone())]))]))
    } else {
        None
    }
}

pub fn parse_ident(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "parseIdent" && a.len() == 1) && matches!(get_arg(t, 0), Term::Con(ref n, ref a) if n == "MkState" && a.len() == 2) && matches!(get_arg(get_arg(t, 0), 0), Term::Con(ref n, ref a) if n == "Cons" && a.len() == 2) && matches!(get_arg(get_arg(get_arg(t, 0), 0), 0), Term::Con(ref n, ref a) if n == "TokIdent" && a.len() == 1) {
    let name = get_arg(get_arg(get_arg(get_arg(t, 0), 0), 0), 0).clone();
    let rest = get_arg(get_arg(get_arg(t, 0), 0), 1).clone();
    let pos = get_arg(get_arg(t, 0), 1).clone();
        Some(Term::Con("ParseOk".to_string(), vec![Box::new(Term::Con("Var".to_string(), vec![Box::new(name.clone())])), Box::new(Term::Con("MkState".to_string(), vec![Box::new(rest.clone()), Box::new(Term::Con("add".to_string(), vec![Box::new(pos.clone()), Box::new(Term::Lit("1".to_string()))]))]))]))
    } else {
        None
    }
}

pub fn parse_ident_fail(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "parseIdent" && a.len() == 1) && matches!(get_arg(t, 0), Term::Con(ref n, ref a) if n == "MkState" && a.len() == 2) && matches!(get_arg(get_arg(t, 0), 0), Term::Con(ref n, ref a) if n == "Cons" && a.len() == 2) {
    let v_t = get_arg(get_arg(get_arg(t, 0), 0), 0).clone();
    let rest = get_arg(get_arg(get_arg(t, 0), 0), 1).clone();
    let pos = get_arg(get_arg(t, 0), 1).clone();
        Some(Term::Con("ParseFail".to_string(), vec![Box::new(Term::Lit("\"expected identifier\"".to_string())), Box::new(Term::Con("MkState".to_string(), vec![Box::new(Term::Con("Cons".to_string(), vec![Box::new(v_t.clone()), Box::new(rest.clone())])), Box::new(pos.clone())]))]))
    } else {
        None
    }
}

pub fn parse_seq(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "parseSeq" && a.len() == 3) {
    let p1 = get_arg(t, 0).clone();
    let p2 = get_arg(t, 1).clone();
    let state = get_arg(t, 2).clone();
        Some(Term::Con("case".to_string(), vec![Box::new(Term::Con("parse".to_string(), vec![Box::new(p1.clone()), Box::new(state.clone())])), Box::new(Term::Con("ParseOk".to_string(), vec![Box::new(Term::Var("t1".to_string())), Box::new(Term::Var("s1".to_string()))])), Box::new(Term::Con("case".to_string(), vec![Box::new(Term::Con("parse".to_string(), vec![Box::new(p2.clone()), Box::new(Term::Var("s1".to_string()))])), Box::new(Term::Con("ParseOk".to_string(), vec![Box::new(Term::Var("t2".to_string())), Box::new(Term::Var("s2".to_string()))])), Box::new(Term::Con("ParseOk".to_string(), vec![Box::new(Term::Con("Con".to_string(), vec![Box::new(Term::Lit("\"seq\"".to_string())), Box::new(Term::Con("Cons".to_string(), vec![Box::new(Term::Var("t1".to_string())), Box::new(Term::Con("Cons".to_string(), vec![Box::new(Term::Var("t2".to_string())), Box::new(Term::Con("Nil".to_string(), vec![]))]))]))])), Box::new(Term::Var("s2".to_string()))])), Box::new(Term::Con("ParseFail".to_string(), vec![Box::new(Term::Var("msg".to_string())), Box::new(Term::Var("s".to_string()))])), Box::new(Term::Con("ParseFail".to_string(), vec![Box::new(Term::Var("msg".to_string())), Box::new(Term::Var("s".to_string()))]))])), Box::new(Term::Con("ParseFail".to_string(), vec![Box::new(Term::Var("msg".to_string())), Box::new(Term::Var("s".to_string()))])), Box::new(Term::Con("ParseFail".to_string(), vec![Box::new(Term::Var("msg".to_string())), Box::new(Term::Var("s".to_string()))]))]))
    } else {
        None
    }
}

pub fn parse_alt(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "parseAlt" && a.len() == 3) {
    let p1 = get_arg(t, 0).clone();
    let p2 = get_arg(t, 1).clone();
    let state = get_arg(t, 2).clone();
        Some(Term::Con("case".to_string(), vec![Box::new(Term::Con("parse".to_string(), vec![Box::new(p1.clone()), Box::new(state.clone())])), Box::new(Term::Con("ParseOk".to_string(), vec![Box::new(Term::Var("t".to_string())), Box::new(Term::Var("s".to_string()))])), Box::new(Term::Con("ParseOk".to_string(), vec![Box::new(Term::Var("t".to_string())), Box::new(Term::Var("s".to_string()))])), Box::new(Term::Con("ParseFail".to_string(), vec![Box::new(Term::Var("msg1".to_string())), Box::new(Term::Var("s1".to_string()))])), Box::new(Term::Con("case".to_string(), vec![Box::new(Term::Con("parse".to_string(), vec![Box::new(p2.clone()), Box::new(state.clone())])), Box::new(Term::Con("ParseOk".to_string(), vec![Box::new(Term::Var("t".to_string())), Box::new(Term::Var("s".to_string()))])), Box::new(Term::Con("ParseOk".to_string(), vec![Box::new(Term::Var("t".to_string())), Box::new(Term::Var("s".to_string()))])), Box::new(Term::Con("ParseFail".to_string(), vec![Box::new(Term::Var("msg2".to_string())), Box::new(Term::Var("s2".to_string()))])), Box::new(Term::Con("ParseFail".to_string(), vec![Box::new(Term::Con("concat".to_string(), vec![Box::new(Term::Var("msg1".to_string())), Box::new(Term::Con("concat".to_string(), vec![Box::new(Term::Lit("\" or \"".to_string())), Box::new(Term::Var("msg2".to_string()))]))])), Box::new(state.clone())]))]))]))
    } else {
        None
    }
}

pub fn parse_star(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "parseStar" && a.len() == 2) {
    let p = get_arg(t, 0).clone();
    let state = get_arg(t, 1).clone();
        Some(Term::Con("case".to_string(), vec![Box::new(Term::Con("parse".to_string(), vec![Box::new(p.clone()), Box::new(state.clone())])), Box::new(Term::Con("ParseOk".to_string(), vec![Box::new(Term::Var("t".to_string())), Box::new(Term::Var("s".to_string()))])), Box::new(Term::Con("case".to_string(), vec![Box::new(Term::Con("parseStar".to_string(), vec![Box::new(p.clone()), Box::new(Term::Var("s".to_string()))])), Box::new(Term::Con("ParseOk".to_string(), vec![Box::new(Term::Con("Con".to_string(), vec![Box::new(Term::Lit("\"list\"".to_string())), Box::new(Term::Var("ts".to_string()))])), Box::new(Term::Var("s2".to_string()))])), Box::new(Term::Con("ParseOk".to_string(), vec![Box::new(Term::Con("Con".to_string(), vec![Box::new(Term::Lit("\"list\"".to_string())), Box::new(Term::Con("Cons".to_string(), vec![Box::new(Term::Var("t".to_string())), Box::new(Term::Var("ts".to_string()))]))])), Box::new(Term::Var("s2".to_string()))])), Box::new(Term::Con("ParseFail".to_string(), vec![Box::new(Term::Var("msg".to_string())), Box::new(Term::Var("s2".to_string()))])), Box::new(Term::Con("ParseOk".to_string(), vec![Box::new(Term::Con("Con".to_string(), vec![Box::new(Term::Lit("\"list\"".to_string())), Box::new(Term::Con("Cons".to_string(), vec![Box::new(Term::Var("t".to_string())), Box::new(Term::Con("Nil".to_string(), vec![]))]))])), Box::new(Term::Var("s".to_string()))]))])), Box::new(Term::Con("ParseFail".to_string(), vec![Box::new(Term::Var("msg".to_string())), Box::new(Term::Var("s".to_string()))])), Box::new(Term::Con("ParseOk".to_string(), vec![Box::new(Term::Con("Con".to_string(), vec![Box::new(Term::Lit("\"list\"".to_string())), Box::new(Term::Con("Nil".to_string(), vec![]))])), Box::new(state.clone())]))]))
    } else {
        None
    }
}

pub fn parse_opt(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "parseOpt" && a.len() == 2) {
    let p = get_arg(t, 0).clone();
    let state = get_arg(t, 1).clone();
        Some(Term::Con("case".to_string(), vec![Box::new(Term::Con("parse".to_string(), vec![Box::new(p.clone()), Box::new(state.clone())])), Box::new(Term::Con("ParseOk".to_string(), vec![Box::new(Term::Var("t".to_string())), Box::new(Term::Var("s".to_string()))])), Box::new(Term::Con("ParseOk".to_string(), vec![Box::new(Term::Con("Con".to_string(), vec![Box::new(Term::Lit("\"some\"".to_string())), Box::new(Term::Con("Cons".to_string(), vec![Box::new(Term::Var("t".to_string())), Box::new(Term::Con("Nil".to_string(), vec![]))]))])), Box::new(Term::Var("s".to_string()))])), Box::new(Term::Con("ParseFail".to_string(), vec![Box::new(Term::Var("msg".to_string())), Box::new(Term::Var("s".to_string()))])), Box::new(Term::Con("ParseOk".to_string(), vec![Box::new(Term::Con("Con".to_string(), vec![Box::new(Term::Lit("\"none\"".to_string())), Box::new(Term::Con("Nil".to_string(), vec![]))])), Box::new(state.clone())]))]))
    } else {
        None
    }
}

pub fn parse_con(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "parseCon" && a.len() == 3) {
    let name = get_arg(t, 0).clone();
    let p = get_arg(t, 1).clone();
    let state = get_arg(t, 2).clone();
        Some(Term::Con("case".to_string(), vec![Box::new(Term::Con("parse".to_string(), vec![Box::new(p.clone()), Box::new(state.clone())])), Box::new(Term::Con("ParseOk".to_string(), vec![Box::new(Term::Var("t".to_string())), Box::new(Term::Var("s".to_string()))])), Box::new(Term::Con("ParseOk".to_string(), vec![Box::new(Term::Con("Con".to_string(), vec![Box::new(name.clone()), Box::new(Term::Con("Cons".to_string(), vec![Box::new(Term::Var("t".to_string())), Box::new(Term::Con("Nil".to_string(), vec![]))]))])), Box::new(Term::Var("s".to_string()))])), Box::new(Term::Con("ParseFail".to_string(), vec![Box::new(Term::Var("msg".to_string())), Box::new(Term::Var("s".to_string()))])), Box::new(Term::Con("ParseFail".to_string(), vec![Box::new(Term::Var("msg".to_string())), Box::new(Term::Var("s".to_string()))]))]))
    } else {
        None
    }
}

pub fn parse_g_empty(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "parse" && a.len() == 2) && matches!(get_arg(t, 0), Term::Con(ref n, ref a) if n == "GEmpty" && a.is_empty()) {
    let state = get_arg(t, 1).clone();
        Some(Term::Con("ParseOk".to_string(), vec![Box::new(Term::Con("Con".to_string(), vec![Box::new(Term::Lit("\"unit\"".to_string())), Box::new(Term::Con("Nil".to_string(), vec![]))])), Box::new(state.clone())]))
    } else {
        None
    }
}

pub fn parse_g_lit(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "parse" && a.len() == 2) && matches!(get_arg(t, 0), Term::Con(ref n, ref a) if n == "GLit" && a.len() == 1) {
    let s = get_arg(get_arg(t, 0), 0).clone();
    let state = get_arg(t, 1).clone();
        Some(Term::Con("parseLit".to_string(), vec![Box::new(s.clone()), Box::new(state.clone())]))
    } else {
        None
    }
}

pub fn parse_g_ref(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "parse" && a.len() == 2) && matches!(get_arg(t, 0), Term::Con(ref n, ref a) if n == "GRef" && a.len() == 1) && matches!(get_arg(get_arg(t, 0), 0), Term::Lit(ref s) if s == "\"ident\"") {
    let state = get_arg(t, 1).clone();
        Some(Term::Con("parseIdent".to_string(), vec![Box::new(state.clone())]))
    } else {
        None
    }
}

pub fn parse_g_seq(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "parse" && a.len() == 2) && matches!(get_arg(t, 0), Term::Con(ref n, ref a) if n == "GSeq" && a.len() == 2) {
    let g1 = get_arg(get_arg(t, 0), 0).clone();
    let g2 = get_arg(get_arg(t, 0), 1).clone();
    let state = get_arg(t, 1).clone();
        Some(Term::Con("parseSeq".to_string(), vec![Box::new(g1.clone()), Box::new(g2.clone()), Box::new(state.clone())]))
    } else {
        None
    }
}

pub fn parse_g_alt(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "parse" && a.len() == 2) && matches!(get_arg(t, 0), Term::Con(ref n, ref a) if n == "GAlt" && a.len() == 2) {
    let g1 = get_arg(get_arg(t, 0), 0).clone();
    let g2 = get_arg(get_arg(t, 0), 1).clone();
    let state = get_arg(t, 1).clone();
        Some(Term::Con("parseAlt".to_string(), vec![Box::new(g1.clone()), Box::new(g2.clone()), Box::new(state.clone())]))
    } else {
        None
    }
}

pub fn parse_g_star(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "parse" && a.len() == 2) && matches!(get_arg(t, 0), Term::Con(ref n, ref a) if n == "GStar" && a.len() == 1) {
    let g = get_arg(get_arg(t, 0), 0).clone();
    let state = get_arg(t, 1).clone();
        Some(Term::Con("parseStar".to_string(), vec![Box::new(g.clone()), Box::new(state.clone())]))
    } else {
        None
    }
}

pub fn parse_g_opt(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "parse" && a.len() == 2) && matches!(get_arg(t, 0), Term::Con(ref n, ref a) if n == "GOpt" && a.len() == 1) {
    let g = get_arg(get_arg(t, 0), 0).clone();
    let state = get_arg(t, 1).clone();
        Some(Term::Con("parseOpt".to_string(), vec![Box::new(g.clone()), Box::new(state.clone())]))
    } else {
        None
    }
}

pub fn parse_g_con(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "parse" && a.len() == 2) && matches!(get_arg(t, 0), Term::Con(ref n, ref a) if n == "GCon" && a.len() == 2) {
    let name = get_arg(get_arg(t, 0), 0).clone();
    let g = get_arg(get_arg(t, 0), 1).clone();
    let state = get_arg(t, 1).clone();
        Some(Term::Con("parseCon".to_string(), vec![Box::new(name.clone()), Box::new(g.clone()), Box::new(state.clone())]))
    } else {
        None
    }
}

pub fn print_lit(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "print" && a.len() == 2) && matches!(get_arg(t, 0), Term::Con(ref n, ref a) if n == "GLit" && a.len() == 1) && matches!(get_arg(t, 1), Term::Con(ref n, ref a) if n == "Lit" && a.len() == 1) {
    let s = get_arg(get_arg(t, 0), 0).clone();
        Some(Term::Con("PrintOk".to_string(), vec![Box::new(Term::Con("Cons".to_string(), vec![Box::new(Term::Con("TokSym".to_string(), vec![Box::new(s.clone())])), Box::new(Term::Con("Nil".to_string(), vec![]))]))]))
    } else {
        None
    }
}

pub fn print_ident(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "print" && a.len() == 2) && matches!(get_arg(t, 0), Term::Con(ref n, ref a) if n == "GRef" && a.len() == 1) && matches!(get_arg(get_arg(t, 0), 0), Term::Lit(ref s) if s == "\"ident\"") && matches!(get_arg(t, 1), Term::Con(ref n, ref a) if n == "Var" && a.len() == 1) {
    let name = get_arg(get_arg(t, 1), 0).clone();
        Some(Term::Con("PrintOk".to_string(), vec![Box::new(Term::Con("Cons".to_string(), vec![Box::new(Term::Con("TokIdent".to_string(), vec![Box::new(name.clone())])), Box::new(Term::Con("Nil".to_string(), vec![]))]))]))
    } else {
        None
    }
}

pub fn print_seq(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "print" && a.len() == 2) && matches!(get_arg(t, 0), Term::Con(ref n, ref a) if n == "GSeq" && a.len() == 2) && matches!(get_arg(t, 1), Term::Con(ref n, ref a) if n == "Con" && a.len() == 2) && matches!(get_arg(get_arg(t, 1), 0), Term::Lit(ref s) if s == "\"seq\"") && matches!(get_arg(get_arg(t, 1), 1), Term::Con(ref n, ref a) if n == "Cons" && a.len() == 2) && matches!(get_arg(get_arg(get_arg(t, 1), 1), 1), Term::Con(ref n, ref a) if n == "Cons" && a.len() == 2) && matches!(get_arg(get_arg(get_arg(get_arg(t, 1), 1), 1), 1), Term::Con(ref n, ref a) if n == "Nil" && a.is_empty()) {
    let g1 = get_arg(get_arg(t, 0), 0).clone();
    let g2 = get_arg(get_arg(t, 0), 1).clone();
    let t1 = get_arg(get_arg(get_arg(t, 1), 1), 0).clone();
    let t2 = get_arg(get_arg(get_arg(get_arg(t, 1), 1), 1), 0).clone();
        Some(Term::Con("case".to_string(), vec![Box::new(Term::Con("print".to_string(), vec![Box::new(g1.clone()), Box::new(t1.clone())])), Box::new(Term::Con("PrintOk".to_string(), vec![Box::new(Term::Var("toks1".to_string()))])), Box::new(Term::Con("case".to_string(), vec![Box::new(Term::Con("print".to_string(), vec![Box::new(g2.clone()), Box::new(t2.clone())])), Box::new(Term::Con("PrintOk".to_string(), vec![Box::new(Term::Var("toks2".to_string()))])), Box::new(Term::Con("PrintOk".to_string(), vec![Box::new(Term::Con("append".to_string(), vec![Box::new(Term::Var("toks1".to_string())), Box::new(Term::Var("toks2".to_string()))]))])), Box::new(Term::Con("PrintFail".to_string(), vec![Box::new(Term::Var("msg".to_string()))])), Box::new(Term::Con("PrintFail".to_string(), vec![Box::new(Term::Var("msg".to_string()))]))])), Box::new(Term::Con("PrintFail".to_string(), vec![Box::new(Term::Var("msg".to_string()))])), Box::new(Term::Con("PrintFail".to_string(), vec![Box::new(Term::Var("msg".to_string()))]))]))
    } else {
        None
    }
}

pub fn print_con(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "print" && a.len() == 2) && matches!(get_arg(t, 0), Term::Con(ref n, ref a) if n == "GCon" && a.len() == 2) && matches!(get_arg(t, 1), Term::Con(ref n, ref a) if n == "Con" && a.len() == 2) && matches!(get_arg(get_arg(t, 1), 1), Term::Con(ref n, ref a) if n == "Cons" && a.len() == 2) && matches!(get_arg(get_arg(get_arg(t, 1), 1), 1), Term::Con(ref n, ref a) if n == "Nil" && a.is_empty()) {
    let name = get_arg(get_arg(t, 0), 0).clone();
    let g = get_arg(get_arg(t, 0), 1).clone();
    let v_t = get_arg(get_arg(get_arg(t, 1), 1), 0).clone();
        Some(Term::Con("print".to_string(), vec![Box::new(g.clone()), Box::new(v_t.clone())]))
    } else {
        None
    }
}

pub fn grammar_iso(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "grammarIso" && a.len() == 1) {
    let g = get_arg(t, 0).clone();
        Some(Term::Con("MkIso".to_string(), vec![Box::new(Term::Con("Lam".to_string(), vec![Box::new(Term::Con("binder".to_string(), vec![Box::new(Term::Lit("input".to_string())), Box::new(Term::Con("case".to_string(), vec![Box::new(Term::Con("parse".to_string(), vec![Box::new(g.clone()), Box::new(Term::Con("tokenize".to_string(), vec![Box::new(Term::Con("input".to_string(), vec![]))]))])), Box::new(Term::Con("ParseOk".to_string(), vec![Box::new(Term::Var("t".to_string())), Box::new(Term::Var("s".to_string()))])), Box::new(Term::Con("Some".to_string(), vec![Box::new(Term::Var("t".to_string()))])), Box::new(Term::Con("ParseFail".to_string(), vec![Box::new(Term::Var("msg".to_string())), Box::new(Term::Var("s".to_string()))])), Box::new(Term::Con("None".to_string(), vec![]))]))]))])), Box::new(Term::Con("Lam".to_string(), vec![Box::new(Term::Con("binder".to_string(), vec![Box::new(Term::Lit("term".to_string())), Box::new(Term::Con("case".to_string(), vec![Box::new(Term::Con("print".to_string(), vec![Box::new(g.clone()), Box::new(Term::Var("term".to_string()))])), Box::new(Term::Con("PrintOk".to_string(), vec![Box::new(Term::Var("toks".to_string()))])), Box::new(Term::Con("Some".to_string(), vec![Box::new(Term::Con("detokenize".to_string(), vec![Box::new(Term::Var("toks".to_string()))]))])), Box::new(Term::Con("PrintFail".to_string(), vec![Box::new(Term::Var("msg".to_string()))])), Box::new(Term::Con("None".to_string(), vec![]))]))]))]))]))
    } else {
        None
    }
}

pub fn match_var_meta(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "match" && a.len() == 2) && matches!(get_arg(t, 0), Term::Con(ref n, ref a) if n == "Var" && a.len() == 1) {
    let name = get_arg(get_arg(t, 0), 0).clone();
    let v_t = get_arg(t, 1).clone();
        Some(Term::Con("Some".to_string(), vec![Box::new(Term::Con("Bind".to_string(), vec![Box::new(name.clone()), Box::new(v_t.clone()), Box::new(Term::Con("Empty".to_string(), vec![]))]))]))
    } else {
        None
    }
}

pub fn match_list_nil(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "matchList" && a.len() == 2) && matches!(get_arg(t, 0), Term::Con(ref n, ref a) if n == "Nil" && a.is_empty()) && matches!(get_arg(t, 1), Term::Con(ref n, ref a) if n == "Nil" && a.is_empty()) {
        Some(Term::Con("Some".to_string(), vec![Box::new(Term::Con("Empty".to_string(), vec![]))]))
    } else {
        None
    }
}

pub fn match_list_cons(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "matchList" && a.len() == 2) && matches!(get_arg(t, 0), Term::Con(ref n, ref a) if n == "Cons" && a.len() == 2) && matches!(get_arg(t, 1), Term::Con(ref n, ref a) if n == "Cons" && a.len() == 2) {
    let p = get_arg(get_arg(t, 0), 0).clone();
    let ps = get_arg(get_arg(t, 0), 1).clone();
    let v_t = get_arg(get_arg(t, 1), 0).clone();
    let ts = get_arg(get_arg(t, 1), 1).clone();
        Some(Term::Con("merge".to_string(), vec![Box::new(Term::Con("match".to_string(), vec![Box::new(p.clone()), Box::new(v_t.clone())])), Box::new(Term::Con("matchList".to_string(), vec![Box::new(ps.clone()), Box::new(ts.clone())]))]))
    } else {
        None
    }
}

pub fn merge_envs(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "merge" && a.len() == 2) && matches!(get_arg(t, 0), Term::Con(ref n, ref a) if n == "Some" && a.len() == 1) && matches!(get_arg(t, 1), Term::Con(ref n, ref a) if n == "Some" && a.len() == 1) {
    let e1 = get_arg(get_arg(t, 0), 0).clone();
    let e2 = get_arg(get_arg(t, 1), 0).clone();
        Some(Term::Con("Some".to_string(), vec![Box::new(Term::Con("append".to_string(), vec![Box::new(e1.clone()), Box::new(e2.clone())]))]))
    } else {
        None
    }
}

pub fn subst_var_hit(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "subst" && a.len() == 2) && matches!(get_arg(t, 0), Term::Con(ref n, ref a) if n == "Var" && a.len() == 1) && matches!(get_arg(t, 1), Term::Con(ref n, ref a) if n == "Bind" && a.len() == 3) {
    let name = get_arg(get_arg(t, 0), 0).clone();
    let val = get_arg(get_arg(t, 1), 1).clone();
    let rest = get_arg(get_arg(t, 1), 2).clone();
        Some(val.clone())
    } else {
        None
    }
}

pub fn subst_var_miss(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "subst" && a.len() == 2) && matches!(get_arg(t, 0), Term::Con(ref n, ref a) if n == "Var" && a.len() == 1) && matches!(get_arg(t, 1), Term::Con(ref n, ref a) if n == "Bind" && a.len() == 3) {
    let name = get_arg(get_arg(t, 0), 0).clone();
    let other = get_arg(get_arg(t, 1), 0).clone();
    let val = get_arg(get_arg(t, 1), 1).clone();
    let rest = get_arg(get_arg(t, 1), 2).clone();
        Some(Term::Con("subst".to_string(), vec![Box::new(Term::Con("Var".to_string(), vec![Box::new(name.clone())])), Box::new(rest.clone())]))
    } else {
        None
    }
}

pub fn subst_var_empty(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "subst" && a.len() == 2) && matches!(get_arg(t, 0), Term::Con(ref n, ref a) if n == "Var" && a.len() == 1) && matches!(get_arg(t, 1), Term::Con(ref n, ref a) if n == "Empty" && a.is_empty()) {
    let name = get_arg(get_arg(t, 0), 0).clone();
        Some(Term::Con("Var".to_string(), vec![Box::new(name.clone())]))
    } else {
        None
    }
}

pub fn apply_rule(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "apply" && a.len() == 2) && matches!(get_arg(t, 0), Term::Con(ref n, ref a) if n == "MkRule" && a.len() == 3) {
    let name = get_arg(get_arg(t, 0), 0).clone();
    let pat = get_arg(get_arg(t, 0), 1).clone();
    let tmpl = get_arg(get_arg(t, 0), 2).clone();
    let v_t = get_arg(t, 1).clone();
        Some(Term::Con("case".to_string(), vec![Box::new(Term::Con("match".to_string(), vec![Box::new(pat.clone()), Box::new(v_t.clone())])), Box::new(Term::Con("Some".to_string(), vec![Box::new(Term::Var("env".to_string()))])), Box::new(Term::Con("subst".to_string(), vec![Box::new(tmpl.clone()), Box::new(Term::Var("env".to_string()))])), Box::new(Term::Con("None".to_string(), vec![])), Box::new(Term::Con("None".to_string(), vec![]))]))
    } else {
        None
    }
}

pub fn try_rules_first(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "tryRules" && a.len() == 2) && matches!(get_arg(t, 0), Term::Con(ref n, ref a) if n == "Cons" && a.len() == 2) {
    let r = get_arg(get_arg(t, 0), 0).clone();
    let rs = get_arg(get_arg(t, 0), 1).clone();
    let v_t = get_arg(t, 1).clone();
        Some(Term::Con("case".to_string(), vec![Box::new(Term::Con("apply".to_string(), vec![Box::new(r.clone()), Box::new(v_t.clone())])), Box::new(Term::Con("Some".to_string(), vec![Box::new(Term::Var("result".to_string()))])), Box::new(Term::Con("Some".to_string(), vec![Box::new(Term::Var("result".to_string()))])), Box::new(Term::Con("None".to_string(), vec![])), Box::new(Term::Con("tryRules".to_string(), vec![Box::new(rs.clone()), Box::new(v_t.clone())]))]))
    } else {
        None
    }
}

pub fn try_rules_empty(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "tryRules" && a.len() == 2) && matches!(get_arg(t, 0), Term::Con(ref n, ref a) if n == "Nil" && a.is_empty()) {
    let v_t = get_arg(t, 1).clone();
        Some(Term::Con("None".to_string(), vec![]))
    } else {
        None
    }
}

pub fn normalize_step(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "normalize" && a.len() == 2) {
    let rules = get_arg(t, 0).clone();
    let v_t = get_arg(t, 1).clone();
        Some(Term::Con("let".to_string(), vec![Box::new(Term::Var("t'".to_string())), Box::new(Term::Con("normalizeOnce".to_string(), vec![Box::new(rules.clone()), Box::new(v_t.clone())])), Box::new(Term::Con("if".to_string(), vec![Box::new(Term::Con("eq".to_string(), vec![Box::new(v_t.clone()), Box::new(Term::Var("t'".to_string()))])), Box::new(v_t.clone()), Box::new(Term::Con("normalize".to_string(), vec![Box::new(rules.clone()), Box::new(Term::Var("t'".to_string()))]))]))]))
    } else {
        None
    }
}

pub fn normalize_once_top(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "normalizeOnce" && a.len() == 2) {
    let rules = get_arg(t, 0).clone();
    let v_t = get_arg(t, 1).clone();
        Some(Term::Con("case".to_string(), vec![Box::new(Term::Con("tryRules".to_string(), vec![Box::new(rules.clone()), Box::new(v_t.clone())])), Box::new(Term::Con("Some".to_string(), vec![Box::new(Term::Var("result".to_string()))])), Box::new(Term::Var("result".to_string())), Box::new(Term::Con("None".to_string(), vec![])), Box::new(Term::Con("normalizeChildren".to_string(), vec![Box::new(rules.clone()), Box::new(v_t.clone())]))]))
    } else {
        None
    }
}

pub fn normalize_children_var(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "normalizeChildren" && a.len() == 2) && matches!(get_arg(t, 1), Term::Con(ref n, ref a) if n == "Var" && a.len() == 1) {
    let rules = get_arg(t, 0).clone();
    let x = get_arg(get_arg(t, 1), 0).clone();
        Some(Term::Con("Var".to_string(), vec![Box::new(x.clone())]))
    } else {
        None
    }
}

pub fn normalize_children_lit(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "normalizeChildren" && a.len() == 2) && matches!(get_arg(t, 1), Term::Con(ref n, ref a) if n == "Lit" && a.len() == 1) {
    let rules = get_arg(t, 0).clone();
    let s = get_arg(get_arg(t, 1), 0).clone();
        Some(Term::Con("Lit".to_string(), vec![Box::new(s.clone())]))
    } else {
        None
    }
}

pub fn normalize_children_con(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "normalizeChildren" && a.len() == 2) && matches!(get_arg(t, 1), Term::Con(ref n, ref a) if n == "Con" && a.len() == 2) {
    let rules = get_arg(t, 0).clone();
    let name = get_arg(get_arg(t, 1), 0).clone();
    let args = get_arg(get_arg(t, 1), 1).clone();
        Some(Term::Con("Con".to_string(), vec![Box::new(name.clone()), Box::new(Term::Con("map".to_string(), vec![Box::new(Term::Con("normalizeOnce".to_string(), vec![Box::new(rules.clone())])), Box::new(args.clone())]))]))
    } else {
        None
    }
}

pub fn rosetta_translate(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "translate" && a.len() == 3) && matches!(get_arg(t, 0), Term::Con(ref n, ref a) if n == "MkLang" && a.len() == 3) && matches!(get_arg(t, 1), Term::Con(ref n, ref a) if n == "MkLang" && a.len() == 3) {
    let n1 = get_arg(get_arg(t, 0), 0).clone();
    let g1 = get_arg(get_arg(t, 0), 1).clone();
    let iso1 = get_arg(get_arg(t, 0), 2).clone();
    let n2 = get_arg(get_arg(t, 1), 0).clone();
    let g2 = get_arg(get_arg(t, 1), 1).clone();
    let iso2 = get_arg(get_arg(t, 1), 2).clone();
    let src = get_arg(t, 2).clone();
        Some(Term::Con("forward".to_string(), vec![Box::new(iso2.clone()), Box::new(Term::Con("backward".to_string(), vec![Box::new(iso1.clone()), Box::new(src.clone())]))]))
    } else {
        None
    }
}

pub fn round_trip(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "roundtrip" && a.len() == 2) && matches!(get_arg(t, 0), Term::Con(ref n, ref a) if n == "MkLang" && a.len() == 3) && matches!(get_arg(get_arg(t, 0), 2), Term::Con(ref n, ref a) if n == "MkIso" && a.len() == 2) {
    let n = get_arg(get_arg(t, 0), 0).clone();
    let g = get_arg(get_arg(t, 0), 1).clone();
    let parse = get_arg(get_arg(get_arg(t, 0), 2), 0).clone();
    let print = get_arg(get_arg(get_arg(t, 0), 2), 1).clone();
    let src = get_arg(t, 1).clone();
        Some(Term::Con("bind".to_string(), vec![Box::new(Term::Con("App".to_string(), vec![Box::new(parse.clone()), Box::new(src.clone())])), Box::new(Term::Var("ast".to_string())), Box::new(Term::Con("App".to_string(), vec![Box::new(print.clone()), Box::new(Term::Var("ast".to_string()))]))]))
    } else {
        None
    }
}

pub fn map_nil(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "map" && a.len() == 2) && matches!(get_arg(t, 1), Term::Con(ref n, ref a) if n == "Nil" && a.is_empty()) {
    let f = get_arg(t, 0).clone();
        Some(Term::Con("Nil".to_string(), vec![]))
    } else {
        None
    }
}

pub fn map_cons(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "map" && a.len() == 2) && matches!(get_arg(t, 1), Term::Con(ref n, ref a) if n == "Cons" && a.len() == 2) {
    let f = get_arg(t, 0).clone();
    let x = get_arg(get_arg(t, 1), 0).clone();
    let xs = get_arg(get_arg(t, 1), 1).clone();
        Some(Term::Con("Cons".to_string(), vec![Box::new(Term::Con("App".to_string(), vec![Box::new(f.clone()), Box::new(x.clone())])), Box::new(Term::Con("map".to_string(), vec![Box::new(f.clone()), Box::new(xs.clone())]))]))
    } else {
        None
    }
}

pub fn fold_nil(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "fold" && a.len() == 3) && matches!(get_arg(t, 2), Term::Con(ref n, ref a) if n == "Nil" && a.is_empty()) {
    let f = get_arg(t, 0).clone();
    let acc = get_arg(t, 1).clone();
        Some(acc.clone())
    } else {
        None
    }
}

pub fn fold_cons(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "fold" && a.len() == 3) && matches!(get_arg(t, 2), Term::Con(ref n, ref a) if n == "Cons" && a.len() == 2) {
    let f = get_arg(t, 0).clone();
    let acc = get_arg(t, 1).clone();
    let x = get_arg(get_arg(t, 2), 0).clone();
    let xs = get_arg(get_arg(t, 2), 1).clone();
        Some(Term::Con("fold".to_string(), vec![Box::new(f.clone()), Box::new(Term::Con("App".to_string(), vec![Box::new(f.clone()), Box::new(acc.clone()), Box::new(x.clone())])), Box::new(xs.clone())]))
    } else {
        None
    }
}

pub fn append_nil(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "append" && a.len() == 2) && matches!(get_arg(t, 0), Term::Con(ref n, ref a) if n == "Nil" && a.is_empty()) {
    let ys = get_arg(t, 1).clone();
        Some(ys.clone())
    } else {
        None
    }
}

pub fn append_cons(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "append" && a.len() == 2) && matches!(get_arg(t, 0), Term::Con(ref n, ref a) if n == "Cons" && a.len() == 2) {
    let x = get_arg(get_arg(t, 0), 0).clone();
    let xs = get_arg(get_arg(t, 0), 1).clone();
    let ys = get_arg(t, 1).clone();
        Some(Term::Con("Cons".to_string(), vec![Box::new(x.clone()), Box::new(Term::Con("append".to_string(), vec![Box::new(xs.clone()), Box::new(ys.clone())]))]))
    } else {
        None
    }
}

pub fn if_true(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "if" && a.len() == 3) && matches!(get_arg(t, 0), Term::Con(ref n, ref a) if n == "true" && a.is_empty()) {
    let then = get_arg(t, 1).clone();
    let v_else = get_arg(t, 2).clone();
        Some(then.clone())
    } else {
        None
    }
}

pub fn if_false(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "if" && a.len() == 3) && matches!(get_arg(t, 0), Term::Con(ref n, ref a) if n == "false" && a.is_empty()) {
    let then = get_arg(t, 1).clone();
    let v_else = get_arg(t, 2).clone();
        Some(v_else.clone())
    } else {
        None
    }
}

pub fn eq_same(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "eq" && a.len() == 2) {
    let x = get_arg(t, 0).clone();
        Some(Term::Con("true".to_string(), vec![]))
    } else {
        None
    }
}

pub fn bind_some(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "bind" && a.len() == 3) && matches!(get_arg(t, 0), Term::Con(ref n, ref a) if n == "Some" && a.len() == 1) {
    let x = get_arg(get_arg(t, 0), 0).clone();
    let var = get_arg(t, 1).clone();
    let body = get_arg(t, 2).clone();
        Some(Term::Con("subst".to_string(), vec![Box::new(body.clone()), Box::new(Term::Con("Bind".to_string(), vec![Box::new(var.clone()), Box::new(x.clone()), Box::new(Term::Con("Empty".to_string(), vec![]))]))]))
    } else {
        None
    }
}

pub fn bind_none(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "bind" && a.len() == 3) && matches!(get_arg(t, 0), Term::Con(ref n, ref a) if n == "None" && a.is_empty()) {
    let var = get_arg(t, 1).clone();
    let body = get_arg(t, 2).clone();
        Some(Term::Con("None".to_string(), vec![]))
    } else {
        None
    }
}

pub fn prod_name(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "prodName" && a.len() == 1) && matches!(get_arg(t, 0), Term::Con(ref n, ref a) if n == "MkProd" && a.len() == 3) {
    let name = get_arg(get_arg(t, 0), 0).clone();
    let expr = get_arg(get_arg(t, 0), 1).clone();
    let con = get_arg(get_arg(t, 0), 2).clone();
        Some(name.clone())
    } else {
        None
    }
}

pub fn prod_grammar(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "prodGrammar" && a.len() == 1) && matches!(get_arg(t, 0), Term::Con(ref n, ref a) if n == "MkProd" && a.len() == 3) {
    let name = get_arg(get_arg(t, 0), 0).clone();
    let expr = get_arg(get_arg(t, 0), 1).clone();
    let con = get_arg(get_arg(t, 0), 2).clone();
        Some(expr.clone())
    } else {
        None
    }
}

pub fn prod_con(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "prodCon" && a.len() == 1) && matches!(get_arg(t, 0), Term::Con(ref n, ref a) if n == "MkProd" && a.len() == 3) {
    let name = get_arg(get_arg(t, 0), 0).clone();
    let expr = get_arg(get_arg(t, 0), 1).clone();
    let con = get_arg(get_arg(t, 0), 2).clone();
        Some(con.clone())
    } else {
        None
    }
}

pub fn ast_to_grammar_lit(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "astToGrammar" && a.len() == 1) && matches!(get_arg(t, 0), Term::Con(ref n, ref a) if n == "Con" && a.len() == 2) && matches!(get_arg(get_arg(t, 0), 0), Term::Lit(ref s) if s == "\"lit\"") && matches!(get_arg(get_arg(t, 0), 1), Term::Con(ref n, ref a) if n == "Cons" && a.len() == 2) && matches!(get_arg(get_arg(get_arg(t, 0), 1), 0), Term::Con(ref n, ref a) if n == "Con" && a.len() == 2) && matches!(get_arg(get_arg(get_arg(get_arg(t, 0), 1), 0), 0), Term::Lit(ref s) if s == "\"string\"") && matches!(get_arg(get_arg(get_arg(get_arg(t, 0), 1), 0), 1), Term::Con(ref n, ref a) if n == "Cons" && a.len() == 2) && matches!(get_arg(get_arg(get_arg(get_arg(get_arg(t, 0), 1), 0), 1), 0), Term::Con(ref n, ref a) if n == "Lit" && a.len() == 1) && matches!(get_arg(get_arg(get_arg(get_arg(get_arg(t, 0), 1), 0), 1), 1), Term::Con(ref n, ref a) if n == "Nil" && a.is_empty()) && matches!(get_arg(get_arg(get_arg(t, 0), 1), 1), Term::Con(ref n, ref a) if n == "Nil" && a.is_empty()) {
    let s = get_arg(get_arg(get_arg(get_arg(get_arg(get_arg(t, 0), 1), 0), 1), 0), 0).clone();
        Some(Term::Con("GLit".to_string(), vec![Box::new(Term::Con("stripQuotes".to_string(), vec![Box::new(s.clone())]))]))
    } else {
        None
    }
}

pub fn ast_to_grammar_ref(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "astToGrammar" && a.len() == 1) && matches!(get_arg(t, 0), Term::Con(ref n, ref a) if n == "Con" && a.len() == 2) && matches!(get_arg(get_arg(t, 0), 0), Term::Lit(ref s) if s == "\"ref\"") && matches!(get_arg(get_arg(t, 0), 1), Term::Con(ref n, ref a) if n == "Cons" && a.len() == 2) && matches!(get_arg(get_arg(get_arg(t, 0), 1), 0), Term::Con(ref n, ref a) if n == "Con" && a.len() == 2) && matches!(get_arg(get_arg(get_arg(get_arg(t, 0), 1), 0), 0), Term::Lit(ref s) if s == "\"ident\"") && matches!(get_arg(get_arg(get_arg(get_arg(t, 0), 1), 0), 1), Term::Con(ref n, ref a) if n == "Cons" && a.len() == 2) && matches!(get_arg(get_arg(get_arg(get_arg(get_arg(t, 0), 1), 0), 1), 0), Term::Con(ref n, ref a) if n == "Var" && a.len() == 1) && matches!(get_arg(get_arg(get_arg(get_arg(get_arg(t, 0), 1), 0), 1), 1), Term::Con(ref n, ref a) if n == "Nil" && a.is_empty()) && matches!(get_arg(get_arg(get_arg(t, 0), 1), 1), Term::Con(ref n, ref a) if n == "Nil" && a.is_empty()) {
    let name = get_arg(get_arg(get_arg(get_arg(get_arg(get_arg(t, 0), 1), 0), 1), 0), 0).clone();
        Some(Term::Con("GRef".to_string(), vec![Box::new(name.clone())]))
    } else {
        None
    }
}

pub fn ast_to_grammar_special(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "astToGrammar" && a.len() == 1) && matches!(get_arg(t, 0), Term::Con(ref n, ref a) if n == "Con" && a.len() == 2) && matches!(get_arg(get_arg(t, 0), 0), Term::Lit(ref s) if s == "\"special\"") && matches!(get_arg(get_arg(t, 0), 1), Term::Con(ref n, ref a) if n == "Cons" && a.len() == 2) && matches!(get_arg(get_arg(get_arg(t, 0), 1), 0), Term::Con(ref n, ref a) if n == "Var" && a.len() == 1) && matches!(get_arg(get_arg(get_arg(t, 0), 1), 1), Term::Con(ref n, ref a) if n == "Nil" && a.is_empty()) {
    let s = get_arg(get_arg(get_arg(get_arg(t, 0), 1), 0), 0).clone();
        Some(Term::Con("GRef".to_string(), vec![Box::new(Term::Con("concat".to_string(), vec![Box::new(Term::Lit("\"TOKEN.\"".to_string())), Box::new(Term::Con("stripAngleBrackets".to_string(), vec![Box::new(s.clone())]))]))]))
    } else {
        None
    }
}

pub fn ast_to_grammar_seq(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "astToGrammar" && a.len() == 1) && matches!(get_arg(t, 0), Term::Con(ref n, ref a) if n == "Con" && a.len() == 2) && matches!(get_arg(get_arg(t, 0), 0), Term::Lit(ref s) if s == "\"seq\"") {
    let args = get_arg(get_arg(t, 0), 1).clone();
        Some(Term::Con("foldr".to_string(), vec![Box::new(Term::Con("GSeq".to_string(), vec![])), Box::new(Term::Con("GEmpty".to_string(), vec![])), Box::new(Term::Con("map".to_string(), vec![Box::new(Term::Con("astToGrammar".to_string(), vec![])), Box::new(args.clone())]))]))
    } else {
        None
    }
}

pub fn ast_to_grammar_alt(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "astToGrammar" && a.len() == 1) && matches!(get_arg(t, 0), Term::Con(ref n, ref a) if n == "Con" && a.len() == 2) && matches!(get_arg(get_arg(t, 0), 0), Term::Lit(ref s) if s == "\"alt\"") {
    let args = get_arg(get_arg(t, 0), 1).clone();
        Some(Term::Con("let".to_string(), vec![Box::new(Term::Var("parts".to_string())), Box::new(Term::Con("splitByPipe".to_string(), vec![Box::new(args.clone())])), Box::new(Term::Con("foldr1".to_string(), vec![Box::new(Term::Con("GAlt".to_string(), vec![])), Box::new(Term::Con("map".to_string(), vec![Box::new(Term::Con("astToGrammar".to_string(), vec![])), Box::new(Term::Var("parts".to_string()))]))]))]))
    } else {
        None
    }
}

pub fn ast_to_grammar_star(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "astToGrammar" && a.len() == 1) && matches!(get_arg(t, 0), Term::Con(ref n, ref a) if n == "Con" && a.len() == 2) && matches!(get_arg(get_arg(t, 0), 0), Term::Lit(ref s) if s == "\"star\"") && matches!(get_arg(get_arg(t, 0), 1), Term::Con(ref n, ref a) if n == "Cons" && a.len() == 2) && matches!(get_arg(get_arg(get_arg(t, 0), 1), 1), Term::Con(ref n, ref a) if n == "Nil" && a.is_empty()) {
    let g = get_arg(get_arg(get_arg(t, 0), 1), 0).clone();
        Some(Term::Con("GStar".to_string(), vec![Box::new(Term::Con("astToGrammar".to_string(), vec![Box::new(g.clone())]))]))
    } else {
        None
    }
}

pub fn ast_to_grammar_plus(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "astToGrammar" && a.len() == 1) && matches!(get_arg(t, 0), Term::Con(ref n, ref a) if n == "Con" && a.len() == 2) && matches!(get_arg(get_arg(t, 0), 0), Term::Lit(ref s) if s == "\"plus\"") && matches!(get_arg(get_arg(t, 0), 1), Term::Con(ref n, ref a) if n == "Cons" && a.len() == 2) && matches!(get_arg(get_arg(get_arg(t, 0), 1), 1), Term::Con(ref n, ref a) if n == "Nil" && a.is_empty()) {
    let g = get_arg(get_arg(get_arg(t, 0), 1), 0).clone();
        Some(Term::Con("GPlus".to_string(), vec![Box::new(Term::Con("astToGrammar".to_string(), vec![Box::new(g.clone())]))]))
    } else {
        None
    }
}

pub fn ast_to_grammar_opt(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "astToGrammar" && a.len() == 1) && matches!(get_arg(t, 0), Term::Con(ref n, ref a) if n == "Con" && a.len() == 2) && matches!(get_arg(get_arg(t, 0), 0), Term::Lit(ref s) if s == "\"opt\"") && matches!(get_arg(get_arg(t, 0), 1), Term::Con(ref n, ref a) if n == "Cons" && a.len() == 2) && matches!(get_arg(get_arg(get_arg(t, 0), 1), 1), Term::Con(ref n, ref a) if n == "Nil" && a.is_empty()) {
    let g = get_arg(get_arg(get_arg(t, 0), 1), 0).clone();
        Some(Term::Con("GOpt".to_string(), vec![Box::new(Term::Con("astToGrammar".to_string(), vec![Box::new(g.clone())]))]))
    } else {
        None
    }
}

pub fn ast_to_grammar_not(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "astToGrammar" && a.len() == 1) && matches!(get_arg(t, 0), Term::Con(ref n, ref a) if n == "Con" && a.len() == 2) && matches!(get_arg(get_arg(t, 0), 0), Term::Lit(ref s) if s == "\"not\"") && matches!(get_arg(get_arg(t, 0), 1), Term::Con(ref n, ref a) if n == "Cons" && a.len() == 2) && matches!(get_arg(get_arg(get_arg(t, 0), 1), 1), Term::Con(ref n, ref a) if n == "Nil" && a.is_empty()) {
    let g = get_arg(get_arg(get_arg(t, 0), 1), 0).clone();
        Some(Term::Con("GNot".to_string(), vec![Box::new(Term::Con("astToGrammar".to_string(), vec![Box::new(g.clone())]))]))
    } else {
        None
    }
}

pub fn ast_to_grammar_and(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "astToGrammar" && a.len() == 1) && matches!(get_arg(t, 0), Term::Con(ref n, ref a) if n == "Con" && a.len() == 2) && matches!(get_arg(get_arg(t, 0), 0), Term::Lit(ref s) if s == "\"and\"") && matches!(get_arg(get_arg(t, 0), 1), Term::Con(ref n, ref a) if n == "Cons" && a.len() == 2) && matches!(get_arg(get_arg(get_arg(t, 0), 1), 1), Term::Con(ref n, ref a) if n == "Nil" && a.is_empty()) {
    let g = get_arg(get_arg(get_arg(t, 0), 1), 0).clone();
        Some(Term::Con("GAnd".to_string(), vec![Box::new(Term::Con("astToGrammar".to_string(), vec![Box::new(g.clone())]))]))
    } else {
        None
    }
}

pub fn extract_parent_names(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "extractParentNames" && a.len() == 1) && matches!(get_arg(t, 0), Term::Con(ref n, ref a) if n == "Con" && a.len() == 2) && matches!(get_arg(get_arg(t, 0), 0), Term::Lit(ref s) if s == "\"DLang\"") {
    let args = get_arg(get_arg(t, 0), 1).clone();
        Some(Term::Con("filterMap".to_string(), vec![Box::new(Term::Con("extractParentFromArg".to_string(), vec![])), Box::new(args.clone())]))
    } else {
        None
    }
}

pub fn extract_parent_names_other(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "extractParentNames" && a.len() == 1) {
    let other = get_arg(t, 0).clone();
        Some(Term::Con("Nil".to_string(), vec![]))
    } else {
        None
    }
}

pub fn extract_parent_from_arg(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "extractParentFromArg" && a.len() == 1) && matches!(get_arg(t, 0), Term::Con(ref n, ref a) if n == "Con" && a.len() == 2) && matches!(get_arg(get_arg(t, 0), 0), Term::Lit(ref s) if s == "\"DImports\"") {
    let imports = get_arg(get_arg(t, 0), 1).clone();
        Some(Term::Con("Some".to_string(), vec![Box::new(Term::Con("filterMap".to_string(), vec![Box::new(Term::Con("extractIdentName".to_string(), vec![])), Box::new(imports.clone())]))]))
    } else {
        None
    }
}

pub fn extract_parent_from_arg_other(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "extractParentFromArg" && a.len() == 1) {
    let other = get_arg(t, 0).clone();
        Some(Term::Con("None".to_string(), vec![]))
    } else {
        None
    }
}

pub fn extract_ident_name(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "extractIdentName" && a.len() == 1) && matches!(get_arg(t, 0), Term::Con(ref n, ref a) if n == "Con" && a.len() == 2) && matches!(get_arg(get_arg(t, 0), 0), Term::Lit(ref s) if s == "\"ident\"") && matches!(get_arg(get_arg(t, 0), 1), Term::Con(ref n, ref a) if n == "Cons" && a.len() == 2) && matches!(get_arg(get_arg(get_arg(t, 0), 1), 0), Term::Con(ref n, ref a) if n == "Var" && a.len() == 1) && matches!(get_arg(get_arg(get_arg(t, 0), 1), 1), Term::Con(ref n, ref a) if n == "Nil" && a.is_empty()) {
    let name = get_arg(get_arg(get_arg(get_arg(t, 0), 1), 0), 0).clone();
        Some(Term::Con("Some".to_string(), vec![Box::new(name.clone())]))
    } else {
        None
    }
}

pub fn extract_ident_name_other(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "extractIdentName" && a.len() == 1) {
    let other = get_arg(t, 0).clone();
        Some(Term::Con("None".to_string(), vec![]))
    } else {
        None
    }
}

pub fn extract_productions(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "extractProductions" && a.len() == 1) && matches!(get_arg(t, 0), Term::Con(ref n, ref a) if n == "Con" && a.len() == 2) && matches!(get_arg(get_arg(t, 0), 0), Term::Lit(ref s) if s == "\"DGrammar\"") && matches!(get_arg(get_arg(t, 0), 1), Term::Con(ref n, ref a) if n == "Cons" && a.len() == 2) && matches!(get_arg(get_arg(get_arg(t, 0), 1), 0), Term::Con(ref n, ref a) if n == "Con" && a.len() == 2) && matches!(get_arg(get_arg(get_arg(get_arg(t, 0), 1), 0), 0), Term::Lit(ref s) if s == "\"ident\"") && matches!(get_arg(get_arg(get_arg(get_arg(t, 0), 1), 0), 1), Term::Con(ref n, ref a) if n == "Cons" && a.len() == 2) && matches!(get_arg(get_arg(get_arg(get_arg(get_arg(t, 0), 1), 0), 1), 0), Term::Con(ref n, ref a) if n == "Var" && a.len() == 1) && matches!(get_arg(get_arg(get_arg(get_arg(get_arg(t, 0), 1), 0), 1), 1), Term::Con(ref n, ref a) if n == "Nil" && a.is_empty()) && matches!(get_arg(get_arg(get_arg(t, 0), 1), 1), Term::Con(ref n, ref a) if n == "Cons" && a.len() == 2) && matches!(get_arg(get_arg(get_arg(get_arg(t, 0), 1), 1), 1), Term::Con(ref n, ref a) if n == "Nil" && a.is_empty()) {
    let lang = get_arg(get_arg(get_arg(get_arg(get_arg(get_arg(t, 0), 1), 0), 1), 0), 0).clone();
    let pieces = get_arg(get_arg(get_arg(get_arg(t, 0), 1), 1), 0).clone();
        Some(Term::Con("concatMap".to_string(), vec![Box::new(Term::Con("extractPieceProductions".to_string(), vec![])), Box::new(Term::Con("getList".to_string(), vec![Box::new(pieces.clone())]))]))
    } else {
        None
    }
}

pub fn extract_piece_productions(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "extractPieceProductions" && a.len() == 1) && matches!(get_arg(t, 0), Term::Con(ref n, ref a) if n == "Con" && a.len() == 2) && matches!(get_arg(get_arg(t, 0), 0), Term::Lit(ref s) if s == "\"DPiece\"") && matches!(get_arg(get_arg(t, 0), 1), Term::Con(ref n, ref a) if n == "Cons" && a.len() == 2) && matches!(get_arg(get_arg(get_arg(t, 0), 1), 0), Term::Con(ref n, ref a) if n == "Con" && a.len() == 2) && matches!(get_arg(get_arg(get_arg(get_arg(t, 0), 1), 0), 0), Term::Lit(ref s) if s == "\"ident\"") && matches!(get_arg(get_arg(get_arg(get_arg(t, 0), 1), 0), 1), Term::Con(ref n, ref a) if n == "Cons" && a.len() == 2) && matches!(get_arg(get_arg(get_arg(get_arg(get_arg(t, 0), 1), 0), 1), 0), Term::Con(ref n, ref a) if n == "Var" && a.len() == 1) && matches!(get_arg(get_arg(get_arg(get_arg(get_arg(t, 0), 1), 0), 1), 1), Term::Con(ref n, ref a) if n == "Nil" && a.is_empty()) && matches!(get_arg(get_arg(get_arg(t, 0), 1), 1), Term::Con(ref n, ref a) if n == "Cons" && a.len() == 2) && matches!(get_arg(get_arg(get_arg(get_arg(t, 0), 1), 1), 1), Term::Con(ref n, ref a) if n == "Nil" && a.is_empty()) {
    let pieceName = get_arg(get_arg(get_arg(get_arg(get_arg(get_arg(t, 0), 1), 0), 1), 0), 0).clone();
    let members = get_arg(get_arg(get_arg(get_arg(t, 0), 1), 1), 0).clone();
        Some(Term::Con("concatMap".to_string(), vec![Box::new(Term::Con("extractMemberProd".to_string(), vec![Box::new(pieceName.clone())])), Box::new(Term::Con("getList".to_string(), vec![Box::new(members.clone())]))]))
    } else {
        None
    }
}

pub fn extract_member_prod_syntax(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "extractMemberProd" && a.len() == 2) && matches!(get_arg(t, 1), Term::Con(ref n, ref a) if n == "Con" && a.len() == 2) && matches!(get_arg(get_arg(t, 1), 0), Term::Lit(ref s) if s == "\"DSyntax\"") && matches!(get_arg(get_arg(t, 1), 1), Term::Con(ref n, ref a) if n == "Cons" && a.len() == 2) && matches!(get_arg(get_arg(get_arg(t, 1), 1), 0), Term::Con(ref n, ref a) if n == "Con" && a.len() == 2) && matches!(get_arg(get_arg(get_arg(get_arg(t, 1), 1), 0), 0), Term::Lit(ref s) if s == "\"ident\"") && matches!(get_arg(get_arg(get_arg(get_arg(t, 1), 1), 0), 1), Term::Con(ref n, ref a) if n == "Cons" && a.len() == 2) && matches!(get_arg(get_arg(get_arg(get_arg(get_arg(t, 1), 1), 0), 1), 0), Term::Con(ref n, ref a) if n == "Var" && a.len() == 1) && matches!(get_arg(get_arg(get_arg(get_arg(get_arg(t, 1), 1), 0), 1), 1), Term::Con(ref n, ref a) if n == "Nil" && a.is_empty()) && matches!(get_arg(get_arg(get_arg(t, 1), 1), 1), Term::Con(ref n, ref a) if n == "Cons" && a.len() == 2) && matches!(get_arg(get_arg(get_arg(get_arg(t, 1), 1), 1), 1), Term::Con(ref n, ref a) if n == "Nil" && a.is_empty()) {
    let piece = get_arg(t, 0).clone();
    let cat = get_arg(get_arg(get_arg(get_arg(get_arg(get_arg(t, 1), 1), 0), 1), 0), 0).clone();
    let alts = get_arg(get_arg(get_arg(get_arg(t, 1), 1), 1), 0).clone();
        Some(Term::Con("map".to_string(), vec![Box::new(Term::Con("mkProduction".to_string(), vec![Box::new(piece.clone()), Box::new(cat.clone())])), Box::new(Term::Con("splitByPipe".to_string(), vec![Box::new(Term::Con("getList".to_string(), vec![Box::new(alts.clone())]))]))]))
    } else {
        None
    }
}

pub fn mk_production(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "mkProduction" && a.len() == 3) {
    let piece = get_arg(t, 0).clone();
    let cat = get_arg(t, 1).clone();
    let alt = get_arg(t, 2).clone();
        Some(Term::Con("let".to_string(), vec![Box::new(Term::Var("conName".to_string())), Box::new(Term::Con("extractConName".to_string(), vec![Box::new(alt.clone())])), Box::new(Term::Con("MkProd".to_string(), vec![Box::new(Term::Con("concat".to_string(), vec![Box::new(piece.clone()), Box::new(Term::Con("concat".to_string(), vec![Box::new(Term::Lit("\".\"".to_string())), Box::new(cat.clone())]))])), Box::new(Term::Con("astToGrammar".to_string(), vec![Box::new(alt.clone())])), Box::new(Term::Var("conName".to_string()))]))]))
    } else {
        None
    }
}

pub fn extract_con_name(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "extractConName" && a.len() == 1) {
    let alt = get_arg(t, 0).clone();
        Some(Term::Con("case".to_string(), vec![Box::new(Term::Con("findArrow".to_string(), vec![Box::new(alt.clone())])), Box::new(Term::Con("Some".to_string(), vec![Box::new(Term::Var("name".to_string()))])), Box::new(Term::Var("name".to_string())), Box::new(Term::Con("None".to_string(), vec![])), Box::new(Term::Lit("\"node\"".to_string()))]))
    } else {
        None
    }
}

pub fn extract_rules(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "extractRules" && a.len() == 1) && matches!(get_arg(t, 0), Term::Con(ref n, ref a) if n == "Con" && a.len() == 2) && matches!(get_arg(get_arg(t, 0), 0), Term::Lit(ref s) if s == "\"DGrammar\"") && matches!(get_arg(get_arg(t, 0), 1), Term::Con(ref n, ref a) if n == "Cons" && a.len() == 2) && matches!(get_arg(get_arg(get_arg(t, 0), 1), 1), Term::Con(ref n, ref a) if n == "Cons" && a.len() == 2) && matches!(get_arg(get_arg(get_arg(get_arg(t, 0), 1), 1), 1), Term::Con(ref n, ref a) if n == "Nil" && a.is_empty()) {
    let lang = get_arg(get_arg(get_arg(t, 0), 1), 0).clone();
    let pieces = get_arg(get_arg(get_arg(get_arg(t, 0), 1), 1), 0).clone();
        Some(Term::Con("concatMap".to_string(), vec![Box::new(Term::Con("extractPieceRules".to_string(), vec![])), Box::new(Term::Con("getList".to_string(), vec![Box::new(pieces.clone())]))]))
    } else {
        None
    }
}

pub fn extract_piece_rules(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "extractPieceRules" && a.len() == 1) && matches!(get_arg(t, 0), Term::Con(ref n, ref a) if n == "Con" && a.len() == 2) && matches!(get_arg(get_arg(t, 0), 0), Term::Lit(ref s) if s == "\"DPiece\"") && matches!(get_arg(get_arg(t, 0), 1), Term::Con(ref n, ref a) if n == "Cons" && a.len() == 2) && matches!(get_arg(get_arg(get_arg(t, 0), 1), 1), Term::Con(ref n, ref a) if n == "Cons" && a.len() == 2) && matches!(get_arg(get_arg(get_arg(get_arg(t, 0), 1), 1), 1), Term::Con(ref n, ref a) if n == "Nil" && a.is_empty()) {
    let name = get_arg(get_arg(get_arg(t, 0), 1), 0).clone();
    let members = get_arg(get_arg(get_arg(get_arg(t, 0), 1), 1), 0).clone();
        Some(Term::Con("filterMap".to_string(), vec![Box::new(Term::Con("extractRule".to_string(), vec![])), Box::new(Term::Con("getList".to_string(), vec![Box::new(members.clone())]))]))
    } else {
        None
    }
}

pub fn extract_rule(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "extractRule" && a.len() == 1) && matches!(get_arg(t, 0), Term::Con(ref n, ref a) if n == "Con" && a.len() == 2) && matches!(get_arg(get_arg(t, 0), 0), Term::Lit(ref s) if s == "\"DRule\"") && matches!(get_arg(get_arg(t, 0), 1), Term::Con(ref n, ref a) if n == "Cons" && a.len() == 2) && matches!(get_arg(get_arg(get_arg(t, 0), 1), 0), Term::Con(ref n, ref a) if n == "Con" && a.len() == 2) && matches!(get_arg(get_arg(get_arg(get_arg(t, 0), 1), 0), 0), Term::Lit(ref s) if s == "\"ident\"") && matches!(get_arg(get_arg(get_arg(get_arg(t, 0), 1), 0), 1), Term::Con(ref n, ref a) if n == "Cons" && a.len() == 2) && matches!(get_arg(get_arg(get_arg(get_arg(get_arg(t, 0), 1), 0), 1), 0), Term::Con(ref n, ref a) if n == "Var" && a.len() == 1) && matches!(get_arg(get_arg(get_arg(get_arg(get_arg(t, 0), 1), 0), 1), 1), Term::Con(ref n, ref a) if n == "Nil" && a.is_empty()) && matches!(get_arg(get_arg(get_arg(t, 0), 1), 1), Term::Con(ref n, ref a) if n == "Cons" && a.len() == 2) && matches!(get_arg(get_arg(get_arg(get_arg(t, 0), 1), 1), 1), Term::Con(ref n, ref a) if n == "Cons" && a.len() == 2) && matches!(get_arg(get_arg(get_arg(get_arg(get_arg(t, 0), 1), 1), 1), 1), Term::Con(ref n, ref a) if n == "Nil" && a.is_empty()) {
    let name = get_arg(get_arg(get_arg(get_arg(get_arg(get_arg(t, 0), 1), 0), 1), 0), 0).clone();
    let pat = get_arg(get_arg(get_arg(get_arg(t, 0), 1), 1), 0).clone();
    let template = get_arg(get_arg(get_arg(get_arg(get_arg(t, 0), 1), 1), 1), 0).clone();
        Some(Term::Con("Some".to_string(), vec![Box::new(Term::Con("MkRule".to_string(), vec![Box::new(name.clone()), Box::new(pat.clone()), Box::new(template.clone())]))]))
    } else {
        None
    }
}

pub fn extract_rule_none(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "extractRule" && a.len() == 1) {
    let other = get_arg(t, 0).clone();
        Some(Term::Con("None".to_string(), vec![]))
    } else {
        None
    }
}

pub fn parse_with_grammar(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "parseWithGrammar" && a.len() == 2) && matches!(get_arg(t, 0), Term::Con(ref n, ref a) if n == "MkGrammar" && a.len() == 4) {
    let prods = get_arg(get_arg(t, 0), 0).clone();
    let tokProds = get_arg(get_arg(t, 0), 1).clone();
    let syms = get_arg(get_arg(t, 0), 2).clone();
    let start = get_arg(get_arg(t, 0), 3).clone();
    let input = get_arg(t, 1).clone();
        Some(Term::Con("let".to_string(), vec![Box::new(Term::Var("tokens".to_string())), Box::new(Term::Con("tokenize".to_string(), vec![Box::new(input.clone())])), Box::new(Term::Con("let".to_string(), vec![Box::new(Term::Var("state".to_string())), Box::new(Term::Con("MkState".to_string(), vec![Box::new(Term::Var("tokens".to_string())), Box::new(Term::Lit("0".to_string()))])), Box::new(Term::Con("parseProduction".to_string(), vec![Box::new(start.clone()), Box::new(prods.clone()), Box::new(Term::Var("state".to_string()))]))]))]))
    } else {
        None
    }
}

pub fn parse_production(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "parseProduction" && a.len() == 3) {
    let name = get_arg(t, 0).clone();
    let prods = get_arg(t, 1).clone();
    let state = get_arg(t, 2).clone();
        Some(Term::Con("case".to_string(), vec![Box::new(Term::Con("findProd".to_string(), vec![Box::new(name.clone()), Box::new(prods.clone())])), Box::new(Term::Con("Some".to_string(), vec![Box::new(Term::Con("MkProd".to_string(), vec![Box::new(Term::Var("n".to_string())), Box::new(Term::Var("g".to_string())), Box::new(Term::Var("c".to_string()))]))])), Box::new(Term::Con("parse".to_string(), vec![Box::new(Term::Var("g".to_string())), Box::new(state.clone())])), Box::new(Term::Con("None".to_string(), vec![])), Box::new(Term::Con("ParseFail".to_string(), vec![Box::new(Term::Con("concat".to_string(), vec![Box::new(Term::Lit("\"unknown production: \"".to_string())), Box::new(name.clone())])), Box::new(state.clone())]))]))
    } else {
        None
    }
}

pub fn find_prod_hit(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "findProd" && a.len() == 2) && matches!(get_arg(t, 1), Term::Con(ref n, ref a) if n == "Cons" && a.len() == 2) && matches!(get_arg(get_arg(t, 1), 0), Term::Con(ref n, ref a) if n == "MkProd" && a.len() == 3) {
    let name = get_arg(t, 0).clone();
    let g = get_arg(get_arg(get_arg(t, 1), 0), 1).clone();
    let c = get_arg(get_arg(get_arg(t, 1), 0), 2).clone();
    let rest = get_arg(get_arg(t, 1), 1).clone();
        Some(Term::Con("Some".to_string(), vec![Box::new(Term::Con("MkProd".to_string(), vec![Box::new(name.clone()), Box::new(g.clone()), Box::new(c.clone())]))]))
    } else {
        None
    }
}

pub fn find_prod_miss(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "findProd" && a.len() == 2) && matches!(get_arg(t, 1), Term::Con(ref n, ref a) if n == "Cons" && a.len() == 2) && matches!(get_arg(get_arg(t, 1), 0), Term::Con(ref n, ref a) if n == "MkProd" && a.len() == 3) {
    let name = get_arg(t, 0).clone();
    let other = get_arg(get_arg(get_arg(t, 1), 0), 0).clone();
    let g = get_arg(get_arg(get_arg(t, 1), 0), 1).clone();
    let c = get_arg(get_arg(get_arg(t, 1), 0), 2).clone();
    let rest = get_arg(get_arg(t, 1), 1).clone();
        Some(Term::Con("findProd".to_string(), vec![Box::new(name.clone()), Box::new(rest.clone())]))
    } else {
        None
    }
}

pub fn find_prod_empty(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "findProd" && a.len() == 2) && matches!(get_arg(t, 1), Term::Con(ref n, ref a) if n == "Nil" && a.is_empty()) {
    let name = get_arg(t, 0).clone();
        Some(Term::Con("None".to_string(), vec![]))
    } else {
        None
    }
}

pub fn print_with_grammar(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "printWithGrammar" && a.len() == 3) && matches!(get_arg(t, 0), Term::Con(ref n, ref a) if n == "MkGrammar" && a.len() == 4) {
    let prods = get_arg(get_arg(t, 0), 0).clone();
    let tokProds = get_arg(get_arg(t, 0), 1).clone();
    let syms = get_arg(get_arg(t, 0), 2).clone();
    let start = get_arg(get_arg(t, 0), 3).clone();
    let prodName = get_arg(t, 1).clone();
    let term = get_arg(t, 2).clone();
        Some(Term::Con("case".to_string(), vec![Box::new(Term::Con("findProd".to_string(), vec![Box::new(prodName.clone()), Box::new(prods.clone())])), Box::new(Term::Con("Some".to_string(), vec![Box::new(Term::Con("MkProd".to_string(), vec![Box::new(Term::Var("n".to_string())), Box::new(Term::Var("g".to_string())), Box::new(Term::Var("c".to_string()))]))])), Box::new(Term::Con("print".to_string(), vec![Box::new(Term::Var("g".to_string())), Box::new(term.clone())])), Box::new(Term::Con("None".to_string(), vec![])), Box::new(Term::Con("PrintFail".to_string(), vec![Box::new(Term::Con("concat".to_string(), vec![Box::new(Term::Lit("\"unknown production: \"".to_string())), Box::new(prodName.clone())]))]))]))
    } else {
        None
    }
}

pub fn strip_quotes(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "stripQuotes" && a.len() == 1) {
    let s = get_arg(t, 0).clone();
        Some(Term::Con("if".to_string(), vec![Box::new(Term::Con("and".to_string(), vec![Box::new(Term::Con("startsWith".to_string(), vec![Box::new(s.clone()), Box::new(Term::Lit("\"\\\"\"".to_string()))])), Box::new(Term::Con("endsWith".to_string(), vec![Box::new(s.clone()), Box::new(Term::Lit("\"\\\"\"".to_string()))]))])), Box::new(Term::Con("drop".to_string(), vec![Box::new(Term::Lit("1".to_string())), Box::new(Term::Con("dropRight".to_string(), vec![Box::new(Term::Lit("1".to_string())), Box::new(s.clone())]))])), Box::new(s.clone())]))
    } else {
        None
    }
}

pub fn strip_angle_brackets(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "stripAngleBrackets" && a.len() == 1) {
    let s = get_arg(t, 0).clone();
        Some(Term::Con("if".to_string(), vec![Box::new(Term::Con("and".to_string(), vec![Box::new(Term::Con("startsWith".to_string(), vec![Box::new(s.clone()), Box::new(Term::Lit("\"<\"".to_string()))])), Box::new(Term::Con("endsWith".to_string(), vec![Box::new(s.clone()), Box::new(Term::Lit("\">\"".to_string()))]))])), Box::new(Term::Con("drop".to_string(), vec![Box::new(Term::Lit("1".to_string())), Box::new(Term::Con("dropRight".to_string(), vec![Box::new(Term::Lit("1".to_string())), Box::new(s.clone())]))])), Box::new(s.clone())]))
    } else {
        None
    }
}

pub fn split_by_pipe(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "splitByPipe" && a.len() == 1) {
    let ts = get_arg(t, 0).clone();
        Some(Term::Con("splitBy".to_string(), vec![Box::new(Term::Con("Lit".to_string(), vec![Box::new(Term::Lit("\"|\"".to_string()))])), Box::new(ts.clone())]))
    } else {
        None
    }
}

pub fn get_list(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "getList" && a.len() == 1) && matches!(get_arg(t, 0), Term::Con(ref n, ref a) if n == "Con" && a.len() == 2) && matches!(get_arg(get_arg(t, 0), 0), Term::Lit(ref s) if s == "\"list\"") {
    let xs = get_arg(get_arg(t, 0), 1).clone();
        Some(xs.clone())
    } else {
        None
    }
}

pub fn get_list_other(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "getList" && a.len() == 1) {
    let v_t = get_arg(t, 0).clone();
        Some(Term::Con("Cons".to_string(), vec![Box::new(v_t.clone()), Box::new(Term::Con("Nil".to_string(), vec![]))]))
    } else {
        None
    }
}

pub fn rt_grammar(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "rtGrammar" && a.len() == 1) && matches!(get_arg(t, 0), Term::Con(ref n, ref a) if n == "MkRuntime" && a.len() == 2) {
    let grammar = get_arg(get_arg(t, 0), 0).clone();
    let rules = get_arg(get_arg(t, 0), 1).clone();
        Some(grammar.clone())
    } else {
        None
    }
}

pub fn rt_rules(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "rtRules" && a.len() == 1) && matches!(get_arg(t, 0), Term::Con(ref n, ref a) if n == "MkRuntime" && a.len() == 2) {
    let grammar = get_arg(get_arg(t, 0), 0).clone();
    let rules = get_arg(get_arg(t, 0), 1).clone();
        Some(rules.clone())
    } else {
        None
    }
}

pub fn load_bootstrap(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "loadBootstrap" && a.len() == 1) {
    let content = get_arg(t, 0).clone();
        Some(Term::Con("case".to_string(), vec![Box::new(Term::Con("parseBootstrap".to_string(), vec![Box::new(content.clone())])), Box::new(Term::Con("Some".to_string(), vec![Box::new(Term::Var("ast".to_string()))])), Box::new(Term::Con("let".to_string(), vec![Box::new(Term::Var("prods".to_string())), Box::new(Term::Con("extractProductions".to_string(), vec![Box::new(Term::Var("ast".to_string()))])), Box::new(Term::Con("let".to_string(), vec![Box::new(Term::Var("rules".to_string())), Box::new(Term::Con("extractRules".to_string(), vec![Box::new(Term::Var("ast".to_string()))])), Box::new(Term::Con("Some".to_string(), vec![Box::new(Term::Con("MkRuntime".to_string(), vec![Box::new(Term::Con("MkGrammar".to_string(), vec![Box::new(Term::Var("prods".to_string())), Box::new(Term::Con("Nil".to_string(), vec![])), Box::new(Term::Con("Nil".to_string(), vec![])), Box::new(Term::Lit("\"File.legoFile\"".to_string()))])), Box::new(Term::Var("rules".to_string()))]))]))]))])), Box::new(Term::Con("None".to_string(), vec![])), Box::new(Term::Con("None".to_string(), vec![]))]))
    } else {
        None
    }
}

pub fn parse_bootstrap(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "parseBootstrap" && a.len() == 1) {
    let content = get_arg(t, 0).clone();
        Some(Term::Con("hardcodedParse".to_string(), vec![Box::new(content.clone())]))
    } else {
        None
    }
}

pub fn load_lego(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "loadLego" && a.len() == 2) {
    let bootstrapRt = get_arg(t, 0).clone();
    let content = get_arg(t, 1).clone();
        Some(Term::Con("case".to_string(), vec![Box::new(Term::Con("parseLegoFile".to_string(), vec![Box::new(bootstrapRt.clone()), Box::new(content.clone())])), Box::new(Term::Con("Some".to_string(), vec![Box::new(Term::Var("ast".to_string()))])), Box::new(Term::Con("let".to_string(), vec![Box::new(Term::Var("prods".to_string())), Box::new(Term::Con("extractProductions".to_string(), vec![Box::new(Term::Var("ast".to_string()))])), Box::new(Term::Con("let".to_string(), vec![Box::new(Term::Var("rules".to_string())), Box::new(Term::Con("extractRules".to_string(), vec![Box::new(Term::Var("ast".to_string()))])), Box::new(Term::Con("let".to_string(), vec![Box::new(Term::Var("bootstrapProds".to_string())), Box::new(Term::Con("rtGrammar".to_string(), vec![Box::new(bootstrapRt.clone())])), Box::new(Term::Con("Some".to_string(), vec![Box::new(Term::Con("MkRuntime".to_string(), vec![Box::new(Term::Con("MkGrammar".to_string(), vec![Box::new(Term::Con("append".to_string(), vec![Box::new(Term::Var("prods".to_string())), Box::new(Term::Con("grammarProds".to_string(), vec![Box::new(Term::Var("bootstrapProds".to_string()))]))])), Box::new(Term::Con("Nil".to_string(), vec![])), Box::new(Term::Con("Nil".to_string(), vec![])), Box::new(Term::Lit("\"File.legoFile\"".to_string()))])), Box::new(Term::Con("append".to_string(), vec![Box::new(Term::Var("rules".to_string())), Box::new(Term::Con("rtRules".to_string(), vec![Box::new(bootstrapRt.clone())]))]))]))]))]))]))])), Box::new(Term::Con("None".to_string(), vec![])), Box::new(Term::Con("None".to_string(), vec![]))]))
    } else {
        None
    }
}

pub fn parse_lego_file(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "parseLegoFile" && a.len() == 2) {
    let rt = get_arg(t, 0).clone();
    let content = get_arg(t, 1).clone();
        Some(Term::Con("parseWithGrammar".to_string(), vec![Box::new(Term::Con("rtGrammar".to_string(), vec![Box::new(rt.clone())])), Box::new(content.clone())]))
    } else {
        None
    }
}

pub fn parse_lego_file_e(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "parseLegoFileE" && a.len() == 2) {
    let rt = get_arg(t, 0).clone();
    let content = get_arg(t, 1).clone();
        Some(Term::Con("case".to_string(), vec![Box::new(Term::Con("parseWithGrammar".to_string(), vec![Box::new(Term::Con("rtGrammar".to_string(), vec![Box::new(rt.clone())])), Box::new(content.clone())])), Box::new(Term::Con("ParseOk".to_string(), vec![Box::new(Term::Var("t".to_string())), Box::new(Term::Var("s".to_string()))])), Box::new(Term::Con("Ok".to_string(), vec![Box::new(Term::Var("t".to_string()))])), Box::new(Term::Con("ParseFail".to_string(), vec![Box::new(Term::Var("msg".to_string())), Box::new(Term::Var("s".to_string()))])), Box::new(Term::Con("Err".to_string(), vec![Box::new(Term::Var("msg".to_string()))]))]))
    } else {
        None
    }
}

pub fn load_language(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "loadLanguage" && a.len() == 2) {
    let rt = get_arg(t, 0).clone();
    let path = get_arg(t, 1).clone();
        Some(Term::Con("loadLanguageWithParents".to_string(), vec![Box::new(rt.clone()), Box::new(path.clone()), Box::new(Term::Con("Nil".to_string(), vec![]))]))
    } else {
        None
    }
}

pub fn load_language_with_parents(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "loadLanguageWithParents" && a.len() == 3) {
    let rt = get_arg(t, 0).clone();
    let path = get_arg(t, 1).clone();
    let visited = get_arg(t, 2).clone();
        Some(Term::Con("if".to_string(), vec![Box::new(Term::Con("elem".to_string(), vec![Box::new(path.clone()), Box::new(visited.clone())])), Box::new(Term::Con("Err".to_string(), vec![Box::new(Term::Con("concat".to_string(), vec![Box::new(Term::Lit("\"Circular language inheritance: \"".to_string())), Box::new(path.clone())]))])), Box::new(Term::Con("case".to_string(), vec![Box::new(Term::Con("readFile".to_string(), vec![Box::new(path.clone())])), Box::new(Term::Con("Some".to_string(), vec![Box::new(Term::Var("content".to_string()))])), Box::new(Term::Con("loadLanguageContent".to_string(), vec![Box::new(rt.clone()), Box::new(path.clone()), Box::new(Term::Var("content".to_string())), Box::new(Term::Con("Cons".to_string(), vec![Box::new(path.clone()), Box::new(visited.clone())]))])), Box::new(Term::Con("None".to_string(), vec![])), Box::new(Term::Con("Err".to_string(), vec![Box::new(Term::Con("concat".to_string(), vec![Box::new(Term::Lit("\"Cannot read file: \"".to_string())), Box::new(path.clone())]))]))]))]))
    } else {
        None
    }
}

pub fn load_language_content(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "loadLanguageContent" && a.len() == 4) {
    let rt = get_arg(t, 0).clone();
    let path = get_arg(t, 1).clone();
    let content = get_arg(t, 2).clone();
    let visited = get_arg(t, 3).clone();
        Some(Term::Con("case".to_string(), vec![Box::new(Term::Con("parseLegoFile".to_string(), vec![Box::new(rt.clone()), Box::new(content.clone())])), Box::new(Term::Con("Some".to_string(), vec![Box::new(Term::Var("ast".to_string()))])), Box::new(Term::Con("let".to_string(), vec![Box::new(Term::Var("parentNames".to_string())), Box::new(Term::Con("extractParentNames".to_string(), vec![Box::new(Term::Var("ast".to_string()))])), Box::new(Term::Con("loadWithParents".to_string(), vec![Box::new(rt.clone()), Box::new(path.clone()), Box::new(Term::Var("ast".to_string())), Box::new(Term::Var("parentNames".to_string())), Box::new(visited.clone())]))])), Box::new(Term::Con("None".to_string(), vec![])), Box::new(Term::Con("Err".to_string(), vec![Box::new(Term::Lit("\"parse failed\"".to_string()))]))]))
    } else {
        None
    }
}

pub fn load_with_parents(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "loadWithParents" && a.len() == 5) {
    let rt = get_arg(t, 0).clone();
    let path = get_arg(t, 1).clone();
    let ast = get_arg(t, 2).clone();
    let parentNames = get_arg(t, 3).clone();
    let visited = get_arg(t, 4).clone();
        Some(Term::Con("case".to_string(), vec![Box::new(Term::Con("loadParentGrammars".to_string(), vec![Box::new(rt.clone()), Box::new(path.clone()), Box::new(parentNames.clone()), Box::new(visited.clone())])), Box::new(Term::Con("Ok".to_string(), vec![Box::new(Term::Var("inheritedProds".to_string())), Box::new(Term::Var("inheritedTokProds".to_string()))])), Box::new(Term::Con("let".to_string(), vec![Box::new(Term::Var("childProds".to_string())), Box::new(Term::Con("extractProductions".to_string(), vec![Box::new(ast.clone())])), Box::new(Term::Con("let".to_string(), vec![Box::new(Term::Var("childTokProds".to_string())), Box::new(Term::Con("extractTokenProductions".to_string(), vec![Box::new(ast.clone())])), Box::new(Term::Con("let".to_string(), vec![Box::new(Term::Var("mergedProds".to_string())), Box::new(Term::Con("append".to_string(), vec![Box::new(Term::Var("inheritedProds".to_string())), Box::new(Term::Var("childProds".to_string()))])), Box::new(Term::Con("let".to_string(), vec![Box::new(Term::Var("mergedTokProds".to_string())), Box::new(Term::Con("append".to_string(), vec![Box::new(Term::Var("inheritedTokProds".to_string())), Box::new(Term::Var("childTokProds".to_string()))])), Box::new(Term::Con("let".to_string(), vec![Box::new(Term::Var("syms".to_string())), Box::new(Term::Con("extractSymbols".to_string(), vec![Box::new(Term::Var("mergedProds".to_string()))])), Box::new(Term::Con("let".to_string(), vec![Box::new(Term::Var("start".to_string())), Box::new(Term::Con("findStartProd".to_string(), vec![Box::new(Term::Var("childProds".to_string()))])), Box::new(Term::Con("Ok".to_string(), vec![Box::new(Term::Con("MkGrammar".to_string(), vec![Box::new(Term::Var("mergedProds".to_string())), Box::new(Term::Var("mergedTokProds".to_string())), Box::new(Term::Var("syms".to_string())), Box::new(Term::Var("start".to_string()))]))]))]))]))]))]))]))])), Box::new(Term::Con("Err".to_string(), vec![Box::new(Term::Var("e".to_string()))])), Box::new(Term::Con("Err".to_string(), vec![Box::new(Term::Var("e".to_string()))]))]))
    } else {
        None
    }
}

pub fn load_parent_grammars(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "loadParentGrammars" && a.len() == 4) && matches!(get_arg(t, 2), Term::Con(ref n, ref a) if n == "Nil" && a.is_empty()) {
    let rt = get_arg(t, 0).clone();
    let childPath = get_arg(t, 1).clone();
    let visited = get_arg(t, 3).clone();
        Some(Term::Con("Ok".to_string(), vec![Box::new(Term::Con("Nil".to_string(), vec![])), Box::new(Term::Con("Nil".to_string(), vec![]))]))
    } else {
        None
    }
}

pub fn load_parent_grammars_non_empty(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "loadParentGrammars" && a.len() == 4) && matches!(get_arg(t, 2), Term::Con(ref n, ref a) if n == "Cons" && a.len() == 2) {
    let rt = get_arg(t, 0).clone();
    let childPath = get_arg(t, 1).clone();
    let parent = get_arg(get_arg(t, 2), 0).clone();
    let rest = get_arg(get_arg(t, 2), 1).clone();
    let visited = get_arg(t, 3).clone();
        Some(Term::Con("case".to_string(), vec![Box::new(Term::Con("resolveParentPath".to_string(), vec![Box::new(parent.clone()), Box::new(childPath.clone())])), Box::new(Term::Con("Some".to_string(), vec![Box::new(Term::Var("parentPath".to_string()))])), Box::new(Term::Con("case".to_string(), vec![Box::new(Term::Con("loadLanguageWithParents".to_string(), vec![Box::new(rt.clone()), Box::new(Term::Var("parentPath".to_string())), Box::new(visited.clone())])), Box::new(Term::Con("Ok".to_string(), vec![Box::new(Term::Var("parentGrammar".to_string()))])), Box::new(Term::Con("case".to_string(), vec![Box::new(Term::Con("loadParentGrammars".to_string(), vec![Box::new(rt.clone()), Box::new(childPath.clone()), Box::new(rest.clone()), Box::new(visited.clone())])), Box::new(Term::Con("Ok".to_string(), vec![Box::new(Term::Var("restProds".to_string())), Box::new(Term::Var("restTokProds".to_string()))])), Box::new(Term::Con("Ok".to_string(), vec![Box::new(Term::Con("append".to_string(), vec![Box::new(Term::Con("grammarProds".to_string(), vec![Box::new(Term::Var("parentGrammar".to_string()))])), Box::new(Term::Var("restProds".to_string()))])), Box::new(Term::Con("append".to_string(), vec![Box::new(Term::Con("grammarTokProds".to_string(), vec![Box::new(Term::Var("parentGrammar".to_string()))])), Box::new(Term::Var("restTokProds".to_string()))]))])), Box::new(Term::Con("Err".to_string(), vec![Box::new(Term::Var("e".to_string()))])), Box::new(Term::Con("Err".to_string(), vec![Box::new(Term::Var("e".to_string()))]))])), Box::new(Term::Con("Err".to_string(), vec![Box::new(Term::Var("e".to_string()))])), Box::new(Term::Con("Err".to_string(), vec![Box::new(Term::Con("concat".to_string(), vec![Box::new(Term::Lit("\"Failed to load parent \"".to_string())), Box::new(Term::Con("concat".to_string(), vec![Box::new(parent.clone()), Box::new(Term::Con("concat".to_string(), vec![Box::new(Term::Lit("\": \"".to_string())), Box::new(Term::Var("e".to_string()))]))]))]))]))])), Box::new(Term::Con("None".to_string(), vec![])), Box::new(Term::Con("if".to_string(), vec![Box::new(Term::Con("eq".to_string(), vec![Box::new(parent.clone()), Box::new(Term::Lit("\"Bootstrap\"".to_string()))])), Box::new(Term::Con("case".to_string(), vec![Box::new(Term::Con("loadParentGrammars".to_string(), vec![Box::new(rt.clone()), Box::new(childPath.clone()), Box::new(rest.clone()), Box::new(visited.clone())])), Box::new(Term::Con("Ok".to_string(), vec![Box::new(Term::Var("restProds".to_string())), Box::new(Term::Var("restTokProds".to_string()))])), Box::new(Term::Con("Ok".to_string(), vec![Box::new(Term::Con("append".to_string(), vec![Box::new(Term::Con("grammarProds".to_string(), vec![Box::new(Term::Con("rtGrammar".to_string(), vec![Box::new(rt.clone())]))])), Box::new(Term::Var("restProds".to_string()))])), Box::new(Term::Con("append".to_string(), vec![Box::new(Term::Con("grammarTokProds".to_string(), vec![Box::new(Term::Con("rtGrammar".to_string(), vec![Box::new(rt.clone())]))])), Box::new(Term::Var("restTokProds".to_string()))]))])), Box::new(Term::Con("Err".to_string(), vec![Box::new(Term::Var("e".to_string()))])), Box::new(Term::Con("Err".to_string(), vec![Box::new(Term::Var("e".to_string()))]))])), Box::new(Term::Con("Err".to_string(), vec![Box::new(Term::Con("concat".to_string(), vec![Box::new(Term::Lit("\"Cannot find parent language: \"".to_string())), Box::new(parent.clone())]))]))]))]))
    } else {
        None
    }
}

pub fn resolve_parent_path(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "resolveParentPath" && a.len() == 2) {
    let parentName = get_arg(t, 0).clone();
    let childPath = get_arg(t, 1).clone();
        Some(Term::Con("findFirst".to_string(), vec![Box::new(Term::Con("fileExists".to_string(), vec![])), Box::new(Term::Con("Cons".to_string(), vec![Box::new(Term::Con("concat".to_string(), vec![Box::new(Term::Con("dirname".to_string(), vec![Box::new(childPath.clone())])), Box::new(Term::Con("concat".to_string(), vec![Box::new(Term::Lit("\"/\"".to_string())), Box::new(Term::Con("concat".to_string(), vec![Box::new(parentName.clone()), Box::new(Term::Lit("\".lego\"".to_string()))]))]))])), Box::new(Term::Con("Cons".to_string(), vec![Box::new(Term::Con("concat".to_string(), vec![Box::new(Term::Lit("\"test/\"".to_string())), Box::new(Term::Con("concat".to_string(), vec![Box::new(parentName.clone()), Box::new(Term::Lit("\".lego\"".to_string()))]))])), Box::new(Term::Con("Cons".to_string(), vec![Box::new(Term::Con("concat".to_string(), vec![Box::new(Term::Lit("\"src/Lego/\"".to_string())), Box::new(Term::Con("concat".to_string(), vec![Box::new(parentName.clone()), Box::new(Term::Lit("\".lego\"".to_string()))]))])), Box::new(Term::Con("Cons".to_string(), vec![Box::new(Term::Con("concat".to_string(), vec![Box::new(Term::Lit("\"src/Rosetta/\"".to_string())), Box::new(Term::Con("concat".to_string(), vec![Box::new(parentName.clone()), Box::new(Term::Lit("\".lego\"".to_string()))]))])), Box::new(Term::Con("Nil".to_string(), vec![]))]))]))]))]))]))
    } else {
        None
    }
}

pub fn grammar_prods(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "grammarProds" && a.len() == 1) && matches!(get_arg(t, 0), Term::Con(ref n, ref a) if n == "MkGrammar" && a.len() == 4) {
    let prods = get_arg(get_arg(t, 0), 0).clone();
    let tokProds = get_arg(get_arg(t, 0), 1).clone();
    let syms = get_arg(get_arg(t, 0), 2).clone();
    let start = get_arg(get_arg(t, 0), 3).clone();
        Some(prods.clone())
    } else {
        None
    }
}

pub fn grammar_tok_prods(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "grammarTokProds" && a.len() == 1) && matches!(get_arg(t, 0), Term::Con(ref n, ref a) if n == "MkGrammar" && a.len() == 4) {
    let prods = get_arg(get_arg(t, 0), 0).clone();
    let tokProds = get_arg(get_arg(t, 0), 1).clone();
    let syms = get_arg(get_arg(t, 0), 2).clone();
    let start = get_arg(get_arg(t, 0), 3).clone();
        Some(tokProds.clone())
    } else {
        None
    }
}

pub fn extract_token_productions(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "extractTokenProductions" && a.len() == 1) {
    let ast = get_arg(t, 0).clone();
        Some(Term::Con("filter".to_string(), vec![Box::new(Term::Con("isTokenProd".to_string(), vec![])), Box::new(Term::Con("extractProductions".to_string(), vec![Box::new(ast.clone())]))]))
    } else {
        None
    }
}

pub fn is_token_prod(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "isTokenProd" && a.len() == 1) && matches!(get_arg(t, 0), Term::Con(ref n, ref a) if n == "MkProd" && a.len() == 3) {
    let name = get_arg(get_arg(t, 0), 0).clone();
    let g = get_arg(get_arg(t, 0), 1).clone();
    let c = get_arg(get_arg(t, 0), 2).clone();
        Some(Term::Con("startsWith".to_string(), vec![Box::new(name.clone()), Box::new(Term::Lit("\"TOKEN.\"".to_string()))]))
    } else {
        None
    }
}

pub fn extract_symbols(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "extractSymbols" && a.len() == 1) {
    let prods = get_arg(t, 0).clone();
        Some(Term::Con("nub".to_string(), vec![Box::new(Term::Con("concatMap".to_string(), vec![Box::new(Term::Con("prodSymbols".to_string(), vec![])), Box::new(prods.clone())]))]))
    } else {
        None
    }
}

pub fn prod_symbols(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "prodSymbols" && a.len() == 1) && matches!(get_arg(t, 0), Term::Con(ref n, ref a) if n == "MkProd" && a.len() == 3) {
    let name = get_arg(get_arg(t, 0), 0).clone();
    let g = get_arg(get_arg(t, 0), 1).clone();
    let c = get_arg(get_arg(t, 0), 2).clone();
        Some(Term::Con("grammarSymbols".to_string(), vec![Box::new(g.clone())]))
    } else {
        None
    }
}

pub fn grammar_symbols_ref(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "grammarSymbols" && a.len() == 1) && matches!(get_arg(t, 0), Term::Con(ref n, ref a) if n == "GRef" && a.len() == 1) {
    let name = get_arg(get_arg(t, 0), 0).clone();
        Some(Term::Con("Cons".to_string(), vec![Box::new(name.clone()), Box::new(Term::Con("Nil".to_string(), vec![]))]))
    } else {
        None
    }
}

pub fn grammar_symbols_seq(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "grammarSymbols" && a.len() == 1) && matches!(get_arg(t, 0), Term::Con(ref n, ref a) if n == "GSeq" && a.len() == 2) {
    let g1 = get_arg(get_arg(t, 0), 0).clone();
    let g2 = get_arg(get_arg(t, 0), 1).clone();
        Some(Term::Con("append".to_string(), vec![Box::new(Term::Con("grammarSymbols".to_string(), vec![Box::new(g1.clone())])), Box::new(Term::Con("grammarSymbols".to_string(), vec![Box::new(g2.clone())]))]))
    } else {
        None
    }
}

pub fn grammar_symbols_alt(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "grammarSymbols" && a.len() == 1) && matches!(get_arg(t, 0), Term::Con(ref n, ref a) if n == "GAlt" && a.len() == 2) {
    let g1 = get_arg(get_arg(t, 0), 0).clone();
    let g2 = get_arg(get_arg(t, 0), 1).clone();
        Some(Term::Con("append".to_string(), vec![Box::new(Term::Con("grammarSymbols".to_string(), vec![Box::new(g1.clone())])), Box::new(Term::Con("grammarSymbols".to_string(), vec![Box::new(g2.clone())]))]))
    } else {
        None
    }
}

pub fn grammar_symbols_star(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "grammarSymbols" && a.len() == 1) && matches!(get_arg(t, 0), Term::Con(ref n, ref a) if n == "GStar" && a.len() == 1) {
    let g = get_arg(get_arg(t, 0), 0).clone();
        Some(Term::Con("grammarSymbols".to_string(), vec![Box::new(g.clone())]))
    } else {
        None
    }
}

pub fn grammar_symbols_other(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "grammarSymbols" && a.len() == 1) {
    let g = get_arg(t, 0).clone();
        Some(Term::Con("Nil".to_string(), vec![]))
    } else {
        None
    }
}

pub fn find_start_prod(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "findStartProd" && a.len() == 1) && matches!(get_arg(t, 0), Term::Con(ref n, ref a) if n == "Cons" && a.len() == 2) && matches!(get_arg(get_arg(t, 0), 0), Term::Con(ref n, ref a) if n == "MkProd" && a.len() == 3) {
    let name = get_arg(get_arg(get_arg(t, 0), 0), 0).clone();
    let g = get_arg(get_arg(get_arg(t, 0), 0), 1).clone();
    let c = get_arg(get_arg(get_arg(t, 0), 0), 2).clone();
    let rest = get_arg(get_arg(t, 0), 1).clone();
        Some(name.clone())
    } else {
        None
    }
}

pub fn find_start_prod_empty(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "findStartProd" && a.len() == 1) && matches!(get_arg(t, 0), Term::Con(ref n, ref a) if n == "Nil" && a.is_empty()) {
        Some(Term::Lit("\"File.legoFile\"".to_string()))
    } else {
        None
    }
}

pub fn normalize(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "normalize" && a.len() == 2) {
    let rt = get_arg(t, 0).clone();
    let term = get_arg(t, 1).clone();
        Some(Term::Con("normalizeWith".to_string(), vec![Box::new(Term::Lit("1000".to_string())), Box::new(Term::Con("rtRules".to_string(), vec![Box::new(rt.clone())])), Box::new(term.clone())]))
    } else {
        None
    }
}

pub fn normalize_with(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "normalizeWith" && a.len() == 3) && matches!(get_arg(t, 0), Term::Lit(ref s) if s == "0") {
    let rules = get_arg(t, 1).clone();
    let v_t = get_arg(t, 2).clone();
        Some(v_t.clone())
    } else {
        None
    }
}

pub fn normalize_with_fuel(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "normalizeWith" && a.len() == 3) {
    let n = get_arg(t, 0).clone();
    let rules = get_arg(t, 1).clone();
    let v_t = get_arg(t, 2).clone();
        Some(Term::Con("case".to_string(), vec![Box::new(Term::Con("tryApplyRules".to_string(), vec![Box::new(rules.clone()), Box::new(v_t.clone())])), Box::new(Term::Con("Some".to_string(), vec![Box::new(Term::Var("t'".to_string()))])), Box::new(Term::Con("normalizeWith".to_string(), vec![Box::new(Term::Con("sub".to_string(), vec![Box::new(n.clone()), Box::new(Term::Lit("1".to_string()))])), Box::new(rules.clone()), Box::new(Term::Var("t'".to_string()))])), Box::new(Term::Con("None".to_string(), vec![])), Box::new(Term::Con("normalizeChildren".to_string(), vec![Box::new(n.clone()), Box::new(rules.clone()), Box::new(v_t.clone())]))]))
    } else {
        None
    }
}

pub fn try_apply_rules(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "tryApplyRules" && a.len() == 2) && matches!(get_arg(t, 0), Term::Con(ref n, ref a) if n == "Cons" && a.len() == 2) && matches!(get_arg(get_arg(t, 0), 0), Term::Con(ref n, ref a) if n == "MkRule" && a.len() == 3) {
    let name = get_arg(get_arg(get_arg(t, 0), 0), 0).clone();
    let pat = get_arg(get_arg(get_arg(t, 0), 0), 1).clone();
    let tmpl = get_arg(get_arg(get_arg(t, 0), 0), 2).clone();
    let rest = get_arg(get_arg(t, 0), 1).clone();
    let v_t = get_arg(t, 1).clone();
        Some(Term::Con("case".to_string(), vec![Box::new(Term::Con("matchPat".to_string(), vec![Box::new(pat.clone()), Box::new(v_t.clone())])), Box::new(Term::Con("Some".to_string(), vec![Box::new(Term::Var("bindings".to_string()))])), Box::new(Term::Con("Some".to_string(), vec![Box::new(Term::Con("subst".to_string(), vec![Box::new(tmpl.clone()), Box::new(Term::Var("bindings".to_string()))]))])), Box::new(Term::Con("None".to_string(), vec![])), Box::new(Term::Con("tryApplyRules".to_string(), vec![Box::new(rest.clone()), Box::new(v_t.clone())]))]))
    } else {
        None
    }
}

pub fn try_apply_rules_empty(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "tryApplyRules" && a.len() == 2) && matches!(get_arg(t, 0), Term::Con(ref n, ref a) if n == "Nil" && a.is_empty()) {
    let v_t = get_arg(t, 1).clone();
        Some(Term::Con("None".to_string(), vec![]))
    } else {
        None
    }
}

pub fn normalize_children(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "normalizeChildren" && a.len() == 3) && matches!(get_arg(t, 2), Term::Con(ref n, ref a) if n == "Var" && a.len() == 1) {
    let n = get_arg(t, 0).clone();
    let rules = get_arg(t, 1).clone();
    let x = get_arg(get_arg(t, 2), 0).clone();
        Some(Term::Con("Var".to_string(), vec![Box::new(x.clone())]))
    } else {
        None
    }
}

pub fn print_term(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "printTerm" && a.len() == 3) {
    let rt = get_arg(t, 0).clone();
    let term = get_arg(t, 1).clone();
    let prodName = get_arg(t, 2).clone();
        Some(Term::Con("case".to_string(), vec![Box::new(Term::Con("printWithGrammar".to_string(), vec![Box::new(Term::Con("rtGrammar".to_string(), vec![Box::new(rt.clone())])), Box::new(prodName.clone()), Box::new(term.clone())])), Box::new(Term::Con("PrintOk".to_string(), vec![Box::new(Term::Var("tokens".to_string()))])), Box::new(Term::Con("Some".to_string(), vec![Box::new(Term::Con("joinTokens".to_string(), vec![Box::new(Term::Var("tokens".to_string()))]))])), Box::new(Term::Con("PrintFail".to_string(), vec![Box::new(Term::Var("msg".to_string()))])), Box::new(Term::Con("None".to_string(), vec![]))]))
    } else {
        None
    }
}

pub fn join_tokens(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "joinTokens" && a.len() == 1) {
    let tokens = get_arg(t, 0).clone();
        Some(Term::Con("intercalate".to_string(), vec![Box::new(Term::Lit("\" \"".to_string())), Box::new(Term::Con("map".to_string(), vec![Box::new(Term::Con("tokenToString".to_string(), vec![])), Box::new(tokens.clone())]))]))
    } else {
        None
    }
}

pub fn token_to_string(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "tokenToString" && a.len() == 1) && matches!(get_arg(t, 0), Term::Con(ref n, ref a) if n == "TokIdent" && a.len() == 1) {
    let s = get_arg(get_arg(t, 0), 0).clone();
        Some(s.clone())
    } else {
        None
    }
}

pub fn token_to_string_str(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "tokenToString" && a.len() == 1) && matches!(get_arg(t, 0), Term::Con(ref n, ref a) if n == "TokString" && a.len() == 1) {
    let s = get_arg(get_arg(t, 0), 0).clone();
        Some(Term::Con("concat".to_string(), vec![Box::new(Term::Lit("\"\\\"\"".to_string())), Box::new(Term::Con("concat".to_string(), vec![Box::new(s.clone()), Box::new(Term::Lit("\"\\\"\"".to_string()))]))]))
    } else {
        None
    }
}

pub fn token_to_string_sym(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "tokenToString" && a.len() == 1) && matches!(get_arg(t, 0), Term::Con(ref n, ref a) if n == "TokSym" && a.len() == 1) {
    let s = get_arg(get_arg(t, 0), 0).clone();
        Some(s.clone())
    } else {
        None
    }
}

pub fn init_runtime(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "initRuntime" && a.len() == 2) {
    let bootstrapContent = get_arg(t, 0).clone();
    let legoContent = get_arg(t, 1).clone();
        Some(Term::Con("case".to_string(), vec![Box::new(Term::Con("loadBootstrap".to_string(), vec![Box::new(bootstrapContent.clone())])), Box::new(Term::Con("Some".to_string(), vec![Box::new(Term::Var("bootstrapRt".to_string()))])), Box::new(Term::Con("case".to_string(), vec![Box::new(Term::Con("loadLego".to_string(), vec![Box::new(Term::Var("bootstrapRt".to_string())), Box::new(legoContent.clone())])), Box::new(Term::Con("Some".to_string(), vec![Box::new(Term::Var("legoRt".to_string()))])), Box::new(Term::Con("Ok".to_string(), vec![Box::new(Term::Var("legoRt".to_string()))])), Box::new(Term::Con("None".to_string(), vec![])), Box::new(Term::Con("Err".to_string(), vec![Box::new(Term::Lit("\"failed to load Lego.lego\"".to_string()))]))])), Box::new(Term::Con("None".to_string(), vec![])), Box::new(Term::Con("Err".to_string(), vec![Box::new(Term::Lit("\"failed to load Bootstrap.lego\"".to_string()))]))]))
    } else {
        None
    }
}

pub fn val_error_format(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "valErrorFormat" && a.len() == 1) && matches!(get_arg(t, 0), Term::Con(ref n, ref a) if n == "UndefinedProduction" && a.len() == 2) {
    let v_ref = get_arg(get_arg(t, 0), 0).clone();
    let source = get_arg(get_arg(t, 0), 1).clone();
        Some(Term::Con("concat".to_string(), vec![Box::new(Term::Con("concat".to_string(), vec![Box::new(Term::Con("concat".to_string(), vec![Box::new(Term::Lit("\"ERROR: Undefined production '\"".to_string())), Box::new(v_ref.clone())])), Box::new(Term::Lit("\"' referenced from '\"".to_string()))])), Box::new(Term::Con("concat".to_string(), vec![Box::new(source.clone()), Box::new(Term::Lit("\"'\"".to_string()))]))]))
    } else {
        None
    }
}

pub fn val_error_format_dup(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "valErrorFormat" && a.len() == 1) && matches!(get_arg(t, 0), Term::Con(ref n, ref a) if n == "DuplicateProduction" && a.len() == 1) {
    let name = get_arg(get_arg(t, 0), 0).clone();
        Some(Term::Con("concat".to_string(), vec![Box::new(Term::Con("concat".to_string(), vec![Box::new(Term::Lit("\"ERROR: Duplicate production '\"".to_string())), Box::new(name.clone())])), Box::new(Term::Lit("\"'\"".to_string()))]))
    } else {
        None
    }
}

pub fn val_error_format_unbound(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "valErrorFormat" && a.len() == 1) && matches!(get_arg(t, 0), Term::Con(ref n, ref a) if n == "UnboundVariable" && a.len() == 2) {
    let var = get_arg(get_arg(t, 0), 0).clone();
    let rule = get_arg(get_arg(t, 0), 1).clone();
        Some(Term::Con("concat".to_string(), vec![Box::new(Term::Con("concat".to_string(), vec![Box::new(Term::Con("concat".to_string(), vec![Box::new(Term::Con("concat".to_string(), vec![Box::new(Term::Lit("\"ERROR: Unbound variable '\"".to_string())), Box::new(var.clone())])), Box::new(Term::Lit("\"' in rule '\"".to_string()))])), Box::new(rule.clone())])), Box::new(Term::Lit("\"'\"".to_string()))]))
    } else {
        None
    }
}

pub fn val_error_format_circular(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "valErrorFormat" && a.len() == 1) && matches!(get_arg(t, 0), Term::Con(ref n, ref a) if n == "CircularImport" && a.len() == 1) {
    let v_mod = get_arg(get_arg(t, 0), 0).clone();
        Some(Term::Con("concat".to_string(), vec![Box::new(Term::Con("concat".to_string(), vec![Box::new(Term::Lit("\"ERROR: Circular import of '\"".to_string())), Box::new(v_mod.clone())])), Box::new(Term::Lit("\"'\"".to_string()))]))
    } else {
        None
    }
}

pub fn val_error_format_invalid(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "valErrorFormat" && a.len() == 1) && matches!(get_arg(t, 0), Term::Con(ref n, ref a) if n == "InvalidSyntax" && a.len() == 2) {
    let ctx = get_arg(get_arg(t, 0), 0).clone();
    let msg = get_arg(get_arg(t, 0), 1).clone();
        Some(Term::Con("concat".to_string(), vec![Box::new(Term::Con("concat".to_string(), vec![Box::new(Term::Con("concat".to_string(), vec![Box::new(Term::Lit("\"ERROR: Invalid syntax in \"".to_string())), Box::new(ctx.clone())])), Box::new(Term::Lit("\": \"".to_string()))])), Box::new(msg.clone())]))
    } else {
        None
    }
}

pub fn val_warn_format_conflict(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "valWarnFormat" && a.len() == 1) && matches!(get_arg(t, 0), Term::Con(ref n, ref a) if n == "ConflictingRules" && a.len() == 3) {
    let r1 = get_arg(get_arg(t, 0), 0).clone();
    let r2 = get_arg(get_arg(t, 0), 1).clone();
    let reason = get_arg(get_arg(t, 0), 2).clone();
        Some(Term::Con("concat".to_string(), vec![Box::new(Term::Con("concat".to_string(), vec![Box::new(Term::Con("concat".to_string(), vec![Box::new(Term::Con("concat".to_string(), vec![Box::new(Term::Con("concat".to_string(), vec![Box::new(Term::Lit("\"WARNING: Conflicting rules '\"".to_string())), Box::new(r1.clone())])), Box::new(Term::Lit("\"' and '\"".to_string()))])), Box::new(r2.clone())])), Box::new(Term::Lit("\"': \"".to_string()))])), Box::new(reason.clone())]))
    } else {
        None
    }
}

pub fn val_warn_format_direct_l_r(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "valWarnFormat" && a.len() == 1) && matches!(get_arg(t, 0), Term::Con(ref n, ref a) if n == "DirectLeftRecursion" && a.len() == 1) {
    let name = get_arg(get_arg(t, 0), 0).clone();
        Some(Term::Con("concat".to_string(), vec![Box::new(Term::Con("concat".to_string(), vec![Box::new(Term::Lit("\"WARNING: Direct left recursion in production '\"".to_string())), Box::new(name.clone())])), Box::new(Term::Lit("\"'\"".to_string()))]))
    } else {
        None
    }
}

pub fn val_warn_format_indirect_l_r(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "valWarnFormat" && a.len() == 1) && matches!(get_arg(t, 0), Term::Con(ref n, ref a) if n == "IndirectLeftRecursion" && a.len() == 1) {
    let path = get_arg(get_arg(t, 0), 0).clone();
        Some(Term::Con("concat".to_string(), vec![Box::new(Term::Lit("\"WARNING: Indirect left recursion: \"".to_string())), Box::new(Term::Con("intercalate".to_string(), vec![Box::new(Term::Lit("\" -> \"".to_string())), Box::new(path.clone())]))]))
    } else {
        None
    }
}

pub fn val_warn_format_unused(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "valWarnFormat" && a.len() == 1) && matches!(get_arg(t, 0), Term::Con(ref n, ref a) if n == "UnusedProduction" && a.len() == 1) {
    let name = get_arg(get_arg(t, 0), 0).clone();
        Some(Term::Con("concat".to_string(), vec![Box::new(Term::Con("concat".to_string(), vec![Box::new(Term::Lit("\"WARNING: Unused production '\"".to_string())), Box::new(name.clone())])), Box::new(Term::Lit("\"'\"".to_string()))]))
    } else {
        None
    }
}

pub fn val_warn_format_shadow(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "valWarnFormat" && a.len() == 1) && matches!(get_arg(t, 0), Term::Con(ref n, ref a) if n == "ShadowedProduction" && a.len() == 2) {
    let name = get_arg(get_arg(t, 0), 0).clone();
    let by = get_arg(get_arg(t, 0), 1).clone();
        Some(Term::Con("concat".to_string(), vec![Box::new(Term::Con("concat".to_string(), vec![Box::new(Term::Con("concat".to_string(), vec![Box::new(Term::Con("concat".to_string(), vec![Box::new(Term::Lit("\"WARNING: Production '\"".to_string())), Box::new(name.clone())])), Box::new(Term::Lit("\"' shadowed by '\"".to_string()))])), Box::new(by.clone())])), Box::new(Term::Lit("\"'\"".to_string()))]))
    } else {
        None
    }
}

pub fn val_warn_format_ambig(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "valWarnFormat" && a.len() == 1) && matches!(get_arg(t, 0), Term::Con(ref n, ref a) if n == "AmbiguousGrammar" && a.len() == 2) {
    let name = get_arg(get_arg(t, 0), 0).clone();
    let reason = get_arg(get_arg(t, 0), 1).clone();
        Some(Term::Con("concat".to_string(), vec![Box::new(Term::Con("concat".to_string(), vec![Box::new(Term::Con("concat".to_string(), vec![Box::new(Term::Con("concat".to_string(), vec![Box::new(Term::Lit("\"WARNING: Ambiguous grammar for '\"".to_string())), Box::new(name.clone())])), Box::new(Term::Lit("\"': \"".to_string()))])), Box::new(reason.clone())])), Box::new(Term::Lit("\"\"".to_string()))]))
    } else {
        None
    }
}

pub fn val_warn_format_missing_cut(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "valWarnFormat" && a.len() == 1) && matches!(get_arg(t, 0), Term::Con(ref n, ref a) if n == "MissingCut" && a.len() == 2) {
    let prod = get_arg(get_arg(t, 0), 0).clone();
    let kw = get_arg(get_arg(t, 0), 1).clone();
        Some(Term::Con("concat".to_string(), vec![Box::new(Term::Con("concat".to_string(), vec![Box::new(Term::Con("concat".to_string(), vec![Box::new(Term::Con("concat".to_string(), vec![Box::new(Term::Lit("\"OPTIMIZE: Production '\"".to_string())), Box::new(prod.clone())])), Box::new(Term::Lit("\"' could add cut after '\"".to_string()))])), Box::new(kw.clone())])), Box::new(Term::Lit("\"' for better errors\"".to_string()))]))
    } else {
        None
    }
}

pub fn val_warn_format_cycle(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "valWarnFormat" && a.len() == 1) && matches!(get_arg(t, 0), Term::Con(ref n, ref a) if n == "RuleCycle" && a.len() == 1) {
    let cycle = get_arg(get_arg(t, 0), 0).clone();
        Some(Term::Con("concat".to_string(), vec![Box::new(Term::Lit("\"WARNING: Potential non-terminating rule cycle: \"".to_string())), Box::new(Term::Con("intercalate".to_string(), vec![Box::new(Term::Lit("\" -> \"".to_string())), Box::new(cycle.clone())]))]))
    } else {
        None
    }
}

pub fn val_warn_format_unreachable(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "valWarnFormat" && a.len() == 1) && matches!(get_arg(t, 0), Term::Con(ref n, ref a) if n == "UnreachableAlt" && a.len() == 2) {
    let prod = get_arg(get_arg(t, 0), 0).clone();
    let idx = get_arg(get_arg(t, 0), 1).clone();
        Some(Term::Con("concat".to_string(), vec![Box::new(Term::Con("concat".to_string(), vec![Box::new(Term::Con("concat".to_string(), vec![Box::new(Term::Lit("\"WARNING: Alternative \"".to_string())), Box::new(Term::Con("toString".to_string(), vec![Box::new(idx.clone())]))])), Box::new(Term::Lit("\" in '\"".to_string()))])), Box::new(Term::Con("concat".to_string(), vec![Box::new(prod.clone()), Box::new(Term::Lit("\"' is unreachable\"".to_string()))]))]))
    } else {
        None
    }
}

pub fn val_warn_format_redundant(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "valWarnFormat" && a.len() == 1) && matches!(get_arg(t, 0), Term::Con(ref n, ref a) if n == "RedundantAlt" && a.len() == 3) {
    let prod = get_arg(get_arg(t, 0), 0).clone();
    let i = get_arg(get_arg(t, 0), 1).clone();
    let j = get_arg(get_arg(t, 0), 2).clone();
        Some(Term::Con("concat".to_string(), vec![Box::new(Term::Con("concat".to_string(), vec![Box::new(Term::Con("concat".to_string(), vec![Box::new(Term::Con("concat".to_string(), vec![Box::new(Term::Con("concat".to_string(), vec![Box::new(Term::Lit("\"WARNING: Alternatives \"".to_string())), Box::new(Term::Con("toString".to_string(), vec![Box::new(i.clone())]))])), Box::new(Term::Lit("\" and \"".to_string()))])), Box::new(Term::Con("toString".to_string(), vec![Box::new(j.clone())]))])), Box::new(Term::Lit("\" in '\"".to_string()))])), Box::new(Term::Con("concat".to_string(), vec![Box::new(prod.clone()), Box::new(Term::Lit("\"' are redundant\"".to_string()))]))]))
    } else {
        None
    }
}

pub fn val_result_empty(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "valResultEmpty" && a.is_empty()) {
        Some(Term::Con("MkValidationResult".to_string(), vec![Box::new(Term::Con("Nil".to_string(), vec![])), Box::new(Term::Con("Nil".to_string(), vec![]))]))
    } else {
        None
    }
}

pub fn val_result_append(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "valResultAppend" && a.len() == 2) && matches!(get_arg(t, 0), Term::Con(ref n, ref a) if n == "MkValidationResult" && a.len() == 2) && matches!(get_arg(t, 1), Term::Con(ref n, ref a) if n == "MkValidationResult" && a.len() == 2) {
    let e1 = get_arg(get_arg(t, 0), 0).clone();
    let w1 = get_arg(get_arg(t, 0), 1).clone();
    let e2 = get_arg(get_arg(t, 1), 0).clone();
    let w2 = get_arg(get_arg(t, 1), 1).clone();
        Some(Term::Con("MkValidationResult".to_string(), vec![Box::new(Term::Con("append".to_string(), vec![Box::new(e1.clone()), Box::new(e2.clone())])), Box::new(Term::Con("append".to_string(), vec![Box::new(w1.clone()), Box::new(w2.clone())]))]))
    } else {
        None
    }
}

pub fn val_result_add_error(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "valResultAddError" && a.len() == 2) && matches!(get_arg(t, 0), Term::Con(ref n, ref a) if n == "MkValidationResult" && a.len() == 2) {
    let errs = get_arg(get_arg(t, 0), 0).clone();
    let warns = get_arg(get_arg(t, 0), 1).clone();
    let e = get_arg(t, 1).clone();
        Some(Term::Con("MkValidationResult".to_string(), vec![Box::new(Term::Con("Cons".to_string(), vec![Box::new(e.clone()), Box::new(errs.clone())])), Box::new(warns.clone())]))
    } else {
        None
    }
}

pub fn val_result_add_warning(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "valResultAddWarning" && a.len() == 2) && matches!(get_arg(t, 0), Term::Con(ref n, ref a) if n == "MkValidationResult" && a.len() == 2) {
    let errs = get_arg(get_arg(t, 0), 0).clone();
    let warns = get_arg(get_arg(t, 0), 1).clone();
    let w = get_arg(t, 1).clone();
        Some(Term::Con("MkValidationResult".to_string(), vec![Box::new(errs.clone()), Box::new(Term::Con("Cons".to_string(), vec![Box::new(w.clone()), Box::new(warns.clone())]))]))
    } else {
        None
    }
}

pub fn val_result_has_errors(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "valResultHasErrors" && a.len() == 1) && matches!(get_arg(t, 0), Term::Con(ref n, ref a) if n == "MkValidationResult" && a.len() == 2) {
    let errs = get_arg(get_arg(t, 0), 0).clone();
    let warns = get_arg(get_arg(t, 0), 1).clone();
        Some(Term::Con("not".to_string(), vec![Box::new(Term::Con("null".to_string(), vec![Box::new(errs.clone())]))]))
    } else {
        None
    }
}

pub fn val_result_format(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "valResultFormat" && a.len() == 1) && matches!(get_arg(t, 0), Term::Con(ref n, ref a) if n == "MkValidationResult" && a.len() == 2) {
    let errs = get_arg(get_arg(t, 0), 0).clone();
    let warns = get_arg(get_arg(t, 0), 1).clone();
        Some(Term::Con("append".to_string(), vec![Box::new(Term::Con("map".to_string(), vec![Box::new(Term::Con("valErrorFormat".to_string(), vec![])), Box::new(errs.clone())])), Box::new(Term::Con("map".to_string(), vec![Box::new(Term::Con("valWarnFormat".to_string(), vec![])), Box::new(warns.clone())]))]))
    } else {
        None
    }
}

pub fn builtin_productions(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "builtinProductions" && a.is_empty()) {
        Some(Term::Con("Cons".to_string(), vec![Box::new(Term::Lit("\"nat\"".to_string())), Box::new(Term::Con("Cons".to_string(), vec![Box::new(Term::Lit("\"int\"".to_string())), Box::new(Term::Con("Cons".to_string(), vec![Box::new(Term::Lit("\"str\"".to_string())), Box::new(Term::Con("Cons".to_string(), vec![Box::new(Term::Lit("\"string\"".to_string())), Box::new(Term::Con("Cons".to_string(), vec![Box::new(Term::Lit("\"ident\"".to_string())), Box::new(Term::Con("Cons".to_string(), vec![Box::new(Term::Lit("\"char\"".to_string())), Box::new(Term::Con("Cons".to_string(), vec![Box::new(Term::Lit("\"float\"".to_string())), Box::new(Term::Con("Cons".to_string(), vec![Box::new(Term::Lit("\"bool\"".to_string())), Box::new(Term::Con("Nil".to_string(), vec![]))]))]))]))]))]))]))]))]))
    } else {
        None
    }
}

pub fn extract_refs_empty(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "extractRefs" && a.len() == 1) && matches!(get_arg(t, 0), Term::Con(ref n, ref a) if n == "GEmpty" && a.is_empty()) {
        Some(Term::Con("Nil".to_string(), vec![]))
    } else {
        None
    }
}

pub fn extract_refs_lit(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "extractRefs" && a.len() == 1) && matches!(get_arg(t, 0), Term::Con(ref n, ref a) if n == "GLit" && a.len() == 1) {
    let s = get_arg(get_arg(t, 0), 0).clone();
        Some(Term::Con("Nil".to_string(), vec![]))
    } else {
        None
    }
}

pub fn extract_refs_ref(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "extractRefs" && a.len() == 1) && matches!(get_arg(t, 0), Term::Con(ref n, ref a) if n == "GRef" && a.len() == 1) {
    let name = get_arg(get_arg(t, 0), 0).clone();
        Some(Term::Con("Cons".to_string(), vec![Box::new(name.clone()), Box::new(Term::Con("Nil".to_string(), vec![]))]))
    } else {
        None
    }
}

pub fn extract_refs_seq(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "extractRefs" && a.len() == 1) && matches!(get_arg(t, 0), Term::Con(ref n, ref a) if n == "GSeq" && a.len() == 2) {
    let g1 = get_arg(get_arg(t, 0), 0).clone();
    let g2 = get_arg(get_arg(t, 0), 1).clone();
        Some(Term::Con("append".to_string(), vec![Box::new(Term::Con("extractRefs".to_string(), vec![Box::new(g1.clone())])), Box::new(Term::Con("extractRefs".to_string(), vec![Box::new(g2.clone())]))]))
    } else {
        None
    }
}

pub fn extract_refs_alt(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "extractRefs" && a.len() == 1) && matches!(get_arg(t, 0), Term::Con(ref n, ref a) if n == "GAlt" && a.len() == 2) {
    let g1 = get_arg(get_arg(t, 0), 0).clone();
    let g2 = get_arg(get_arg(t, 0), 1).clone();
        Some(Term::Con("append".to_string(), vec![Box::new(Term::Con("extractRefs".to_string(), vec![Box::new(g1.clone())])), Box::new(Term::Con("extractRefs".to_string(), vec![Box::new(g2.clone())]))]))
    } else {
        None
    }
}

pub fn extract_refs_star(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "extractRefs" && a.len() == 1) && matches!(get_arg(t, 0), Term::Con(ref n, ref a) if n == "GStar" && a.len() == 1) {
    let g = get_arg(get_arg(t, 0), 0).clone();
        Some(Term::Con("extractRefs".to_string(), vec![Box::new(g.clone())]))
    } else {
        None
    }
}

pub fn extract_refs_plus(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "extractRefs" && a.len() == 1) && matches!(get_arg(t, 0), Term::Con(ref n, ref a) if n == "GPlus" && a.len() == 1) {
    let g = get_arg(get_arg(t, 0), 0).clone();
        Some(Term::Con("extractRefs".to_string(), vec![Box::new(g.clone())]))
    } else {
        None
    }
}

pub fn extract_refs_opt(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "extractRefs" && a.len() == 1) && matches!(get_arg(t, 0), Term::Con(ref n, ref a) if n == "GOpt" && a.len() == 1) {
    let g = get_arg(get_arg(t, 0), 0).clone();
        Some(Term::Con("extractRefs".to_string(), vec![Box::new(g.clone())]))
    } else {
        None
    }
}

pub fn extract_refs_not(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "extractRefs" && a.len() == 1) && matches!(get_arg(t, 0), Term::Con(ref n, ref a) if n == "GNot" && a.len() == 1) {
    let g = get_arg(get_arg(t, 0), 0).clone();
        Some(Term::Con("extractRefs".to_string(), vec![Box::new(g.clone())]))
    } else {
        None
    }
}

pub fn extract_refs_and(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "extractRefs" && a.len() == 1) && matches!(get_arg(t, 0), Term::Con(ref n, ref a) if n == "GAnd" && a.len() == 1) {
    let g = get_arg(get_arg(t, 0), 0).clone();
        Some(Term::Con("extractRefs".to_string(), vec![Box::new(g.clone())]))
    } else {
        None
    }
}

pub fn extract_refs_con(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "extractRefs" && a.len() == 1) && matches!(get_arg(t, 0), Term::Con(ref n, ref a) if n == "GCon" && a.len() == 2) {
    let name = get_arg(get_arg(t, 0), 0).clone();
    let g = get_arg(get_arg(t, 0), 1).clone();
        Some(Term::Con("extractRefs".to_string(), vec![Box::new(g.clone())]))
    } else {
        None
    }
}

pub fn check_undefined_refs(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "checkUndefinedRefs" && a.len() == 1) {
    let grammar = get_arg(t, 0).clone();
        Some(Term::Con("let".to_string(), vec![Box::new(Term::Var("defined".to_string())), Box::new(Term::Con("grammarDefinedNames".to_string(), vec![Box::new(grammar.clone())])), Box::new(Term::Con("let".to_string(), vec![Box::new(Term::Var("builtins".to_string())), Box::new(Term::Con("builtinProductions".to_string(), vec![])), Box::new(Term::Con("foldl".to_string(), vec![Box::new(Term::Con("acc".to_string(), vec![Box::new(Term::Con("binder".to_string(), vec![Box::new(Term::Lit("prod".to_string())), Box::new(Term::Con("let".to_string(), vec![Box::new(Term::Var("refs".to_string())), Box::new(Term::Con("extractRefs".to_string(), vec![Box::new(Term::Con("grammarLookup".to_string(), vec![Box::new(grammar.clone()), Box::new(Term::Var("prod".to_string()))]))])), Box::new(Term::Con("foldl".to_string(), vec![Box::new(Term::Con("acc2".to_string(), vec![Box::new(Term::Con("binder".to_string(), vec![Box::new(Term::Lit("ref".to_string())), Box::new(Term::Con("if".to_string(), vec![Box::new(Term::Con("or".to_string(), vec![Box::new(Term::Con("contains".to_string(), vec![Box::new(Term::Var("defined".to_string())), Box::new(Term::Var("ref".to_string()))])), Box::new(Term::Con("contains".to_string(), vec![Box::new(Term::Var("builtins".to_string())), Box::new(Term::Con("baseName".to_string(), vec![Box::new(Term::Var("ref".to_string()))]))]))])), Box::new(Term::Var("acc2".to_string())), Box::new(Term::Con("valResultAddError".to_string(), vec![Box::new(Term::Var("acc2".to_string())), Box::new(Term::Con("UndefinedProduction".to_string(), vec![Box::new(Term::Var("ref".to_string())), Box::new(Term::Var("prod".to_string()))]))]))]))]))])), Box::new(Term::Var("acc".to_string())), Box::new(Term::Var("refs".to_string()))]))]))]))])), Box::new(Term::Con("valResultEmpty".to_string(), vec![])), Box::new(Term::Con("grammarProductions".to_string(), vec![Box::new(grammar.clone())]))]))]))]))
    } else {
        None
    }
}

pub fn is_direct_left_rec_empty(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "isDirectLeftRec" && a.len() == 2) && matches!(get_arg(t, 1), Term::Con(ref n, ref a) if n == "GEmpty" && a.is_empty()) {
    let name = get_arg(t, 0).clone();
        Some(Term::Con("False".to_string(), vec![]))
    } else {
        None
    }
}

pub fn is_direct_left_rec_lit(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "isDirectLeftRec" && a.len() == 2) && matches!(get_arg(t, 1), Term::Con(ref n, ref a) if n == "GLit" && a.len() == 1) {
    let name = get_arg(t, 0).clone();
    let s = get_arg(get_arg(t, 1), 0).clone();
        Some(Term::Con("False".to_string(), vec![]))
    } else {
        None
    }
}

pub fn is_direct_left_rec_ref(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "isDirectLeftRec" && a.len() == 2) && matches!(get_arg(t, 1), Term::Con(ref n, ref a) if n == "GRef" && a.len() == 1) {
    let name = get_arg(t, 0).clone();
    let v_ref = get_arg(get_arg(t, 1), 0).clone();
        Some(Term::Con("eq".to_string(), vec![Box::new(v_ref.clone()), Box::new(name.clone())]))
    } else {
        None
    }
}

pub fn is_direct_left_rec_seq(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "isDirectLeftRec" && a.len() == 2) && matches!(get_arg(t, 1), Term::Con(ref n, ref a) if n == "GSeq" && a.len() == 2) {
    let name = get_arg(t, 0).clone();
    let g1 = get_arg(get_arg(t, 1), 0).clone();
    let g2 = get_arg(get_arg(t, 1), 1).clone();
        Some(Term::Con("isDirectLeftRec".to_string(), vec![Box::new(name.clone()), Box::new(g1.clone())]))
    } else {
        None
    }
}

pub fn is_direct_left_rec_alt(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "isDirectLeftRec" && a.len() == 2) && matches!(get_arg(t, 1), Term::Con(ref n, ref a) if n == "GAlt" && a.len() == 2) {
    let name = get_arg(t, 0).clone();
    let g1 = get_arg(get_arg(t, 1), 0).clone();
    let g2 = get_arg(get_arg(t, 1), 1).clone();
        Some(Term::Con("or".to_string(), vec![Box::new(Term::Con("isDirectLeftRec".to_string(), vec![Box::new(name.clone()), Box::new(g1.clone())])), Box::new(Term::Con("isDirectLeftRec".to_string(), vec![Box::new(name.clone()), Box::new(g2.clone())]))]))
    } else {
        None
    }
}

pub fn is_direct_left_rec_star(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "isDirectLeftRec" && a.len() == 2) && matches!(get_arg(t, 1), Term::Con(ref n, ref a) if n == "GStar" && a.len() == 1) {
    let name = get_arg(t, 0).clone();
    let g = get_arg(get_arg(t, 1), 0).clone();
        Some(Term::Con("isDirectLeftRec".to_string(), vec![Box::new(name.clone()), Box::new(g.clone())]))
    } else {
        None
    }
}

pub fn is_direct_left_rec_plus(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "isDirectLeftRec" && a.len() == 2) && matches!(get_arg(t, 1), Term::Con(ref n, ref a) if n == "GPlus" && a.len() == 1) {
    let name = get_arg(t, 0).clone();
    let g = get_arg(get_arg(t, 1), 0).clone();
        Some(Term::Con("isDirectLeftRec".to_string(), vec![Box::new(name.clone()), Box::new(g.clone())]))
    } else {
        None
    }
}

pub fn is_direct_left_rec_opt(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "isDirectLeftRec" && a.len() == 2) && matches!(get_arg(t, 1), Term::Con(ref n, ref a) if n == "GOpt" && a.len() == 1) {
    let name = get_arg(t, 0).clone();
    let g = get_arg(get_arg(t, 1), 0).clone();
        Some(Term::Con("isDirectLeftRec".to_string(), vec![Box::new(name.clone()), Box::new(g.clone())]))
    } else {
        None
    }
}

pub fn is_direct_left_rec_con(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "isDirectLeftRec" && a.len() == 2) && matches!(get_arg(t, 1), Term::Con(ref n, ref a) if n == "GCon" && a.len() == 2) {
    let name = get_arg(t, 0).clone();
    let c = get_arg(get_arg(t, 1), 0).clone();
    let g = get_arg(get_arg(t, 1), 1).clone();
        Some(Term::Con("isDirectLeftRec".to_string(), vec![Box::new(name.clone()), Box::new(g.clone())]))
    } else {
        None
    }
}

pub fn check_left_recursion(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "checkLeftRecursion" && a.len() == 1) {
    let grammar = get_arg(t, 0).clone();
        Some(Term::Con("foldl".to_string(), vec![Box::new(Term::Con("acc".to_string(), vec![Box::new(Term::Con("binder".to_string(), vec![Box::new(Term::Lit("prod".to_string())), Box::new(Term::Con("if".to_string(), vec![Box::new(Term::Con("isDirectLeftRec".to_string(), vec![Box::new(Term::Var("prod".to_string())), Box::new(Term::Con("grammarLookup".to_string(), vec![Box::new(grammar.clone()), Box::new(Term::Var("prod".to_string()))]))])), Box::new(Term::Con("valResultAddWarning".to_string(), vec![Box::new(Term::Var("acc".to_string())), Box::new(Term::Con("DirectLeftRecursion".to_string(), vec![Box::new(Term::Var("prod".to_string()))]))])), Box::new(Term::Var("acc".to_string()))]))]))])), Box::new(Term::Con("valResultEmpty".to_string(), vec![])), Box::new(Term::Con("grammarProductions".to_string(), vec![Box::new(grammar.clone())]))]))
    } else {
        None
    }
}

pub fn vars_in_var(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "varsIn" && a.len() == 1) && matches!(get_arg(t, 0), Term::Con(ref n, ref a) if n == "Var" && a.len() == 1) {
    let v = get_arg(get_arg(t, 0), 0).clone();
        Some(Term::Con("Cons".to_string(), vec![Box::new(v.clone()), Box::new(Term::Con("Nil".to_string(), vec![]))]))
    } else {
        None
    }
}

pub fn vars_in_lit(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "varsIn" && a.len() == 1) && matches!(get_arg(t, 0), Term::Con(ref n, ref a) if n == "Lit" && a.len() == 1) {
    let s = get_arg(get_arg(t, 0), 0).clone();
        Some(Term::Con("Nil".to_string(), vec![]))
    } else {
        None
    }
}

pub fn vars_in_con(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "varsIn" && a.len() == 1) && matches!(get_arg(t, 0), Term::Con(ref n, ref a) if n == "Con" && a.len() == 2) {
    let c = get_arg(get_arg(t, 0), 0).clone();
    let args = get_arg(get_arg(t, 0), 1).clone();
        Some(Term::Con("flatMap".to_string(), vec![Box::new(Term::Con("varsIn".to_string(), vec![])), Box::new(args.clone())]))
    } else {
        None
    }
}

pub fn pattern_vars_var(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "patternVars" && a.len() == 1) && matches!(get_arg(t, 0), Term::Con(ref n, ref a) if n == "Var" && a.len() == 1) {
    let v = get_arg(get_arg(t, 0), 0).clone();
        Some(Term::Con("if".to_string(), vec![Box::new(Term::Con("startsWith".to_string(), vec![Box::new(v.clone()), Box::new(Term::Lit("\"$\"".to_string()))])), Box::new(Term::Con("Cons".to_string(), vec![Box::new(v.clone()), Box::new(Term::Con("Nil".to_string(), vec![]))])), Box::new(Term::Con("Nil".to_string(), vec![]))]))
    } else {
        None
    }
}

pub fn pattern_vars_lit(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "patternVars" && a.len() == 1) && matches!(get_arg(t, 0), Term::Con(ref n, ref a) if n == "Lit" && a.len() == 1) {
    let s = get_arg(get_arg(t, 0), 0).clone();
        Some(Term::Con("Nil".to_string(), vec![]))
    } else {
        None
    }
}

pub fn pattern_vars_con(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "patternVars" && a.len() == 1) && matches!(get_arg(t, 0), Term::Con(ref n, ref a) if n == "Con" && a.len() == 2) {
    let c = get_arg(get_arg(t, 0), 0).clone();
    let args = get_arg(get_arg(t, 0), 1).clone();
        Some(Term::Con("flatMap".to_string(), vec![Box::new(Term::Con("patternVars".to_string(), vec![])), Box::new(args.clone())]))
    } else {
        None
    }
}

pub fn check_unbound_vars(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "checkUnboundVars" && a.len() == 1) {
    let rules = get_arg(t, 0).clone();
        Some(Term::Con("foldl".to_string(), vec![Box::new(Term::Con("acc".to_string(), vec![Box::new(Term::Con("binder".to_string(), vec![Box::new(Term::Lit("rule".to_string())), Box::new(Term::Con("let".to_string(), vec![Box::new(Term::Var("patVars".to_string())), Box::new(Term::Con("patternVars".to_string(), vec![Box::new(Term::Con("rulePattern".to_string(), vec![Box::new(Term::Var("rule".to_string()))]))])), Box::new(Term::Con("let".to_string(), vec![Box::new(Term::Var("tplVars".to_string())), Box::new(Term::Con("filter".to_string(), vec![Box::new(Term::Con("binder".to_string(), vec![Box::new(Term::Lit("v".to_string())), Box::new(Term::Con("startsWith".to_string(), vec![Box::new(Term::Var("v".to_string())), Box::new(Term::Lit("\"$\"".to_string()))]))])), Box::new(Term::Con("varsIn".to_string(), vec![Box::new(Term::Con("ruleTemplate".to_string(), vec![Box::new(Term::Var("rule".to_string()))]))]))])), Box::new(Term::Con("let".to_string(), vec![Box::new(Term::Var("unbound".to_string())), Box::new(Term::Con("filter".to_string(), vec![Box::new(Term::Con("binder".to_string(), vec![Box::new(Term::Lit("v".to_string())), Box::new(Term::Con("not".to_string(), vec![Box::new(Term::Con("contains".to_string(), vec![Box::new(Term::Var("patVars".to_string())), Box::new(Term::Var("v".to_string()))]))]))])), Box::new(Term::Var("tplVars".to_string()))])), Box::new(Term::Con("foldl".to_string(), vec![Box::new(Term::Con("acc2".to_string(), vec![Box::new(Term::Con("binder".to_string(), vec![Box::new(Term::Lit("v".to_string())), Box::new(Term::Con("valResultAddError".to_string(), vec![Box::new(Term::Var("acc2".to_string())), Box::new(Term::Con("UnboundVariable".to_string(), vec![Box::new(Term::Var("v".to_string())), Box::new(Term::Con("ruleName".to_string(), vec![Box::new(Term::Var("rule".to_string()))]))]))]))]))])), Box::new(Term::Var("acc".to_string())), Box::new(Term::Var("unbound".to_string()))]))]))]))]))]))])), Box::new(Term::Con("valResultEmpty".to_string(), vec![])), Box::new(rules.clone())]))
    } else {
        None
    }
}

pub fn pattern_key_var(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "patternKey" && a.len() == 1) && matches!(get_arg(t, 0), Term::Con(ref n, ref a) if n == "Var" && a.len() == 1) {
    let v = get_arg(get_arg(t, 0), 0).clone();
        Some(Term::Lit("\"_\"".to_string()))
    } else {
        None
    }
}

pub fn pattern_key_lit(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "patternKey" && a.len() == 1) && matches!(get_arg(t, 0), Term::Con(ref n, ref a) if n == "Lit" && a.len() == 1) {
    let s = get_arg(get_arg(t, 0), 0).clone();
        Some(Term::Con("concat".to_string(), vec![Box::new(Term::Con("concat".to_string(), vec![Box::new(Term::Lit("\"\\\"\"".to_string())), Box::new(s.clone())])), Box::new(Term::Lit("\"\\\"\"".to_string()))]))
    } else {
        None
    }
}

pub fn pattern_key_con(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "patternKey" && a.len() == 1) && matches!(get_arg(t, 0), Term::Con(ref n, ref a) if n == "Con" && a.len() == 2) {
    let name = get_arg(get_arg(t, 0), 0).clone();
    let args = get_arg(get_arg(t, 0), 1).clone();
        Some(Term::Con("concat".to_string(), vec![Box::new(Term::Con("concat".to_string(), vec![Box::new(Term::Con("concat".to_string(), vec![Box::new(Term::Lit("\"(\"".to_string())), Box::new(name.clone())])), Box::new(Term::Con("concat".to_string(), vec![Box::new(Term::Lit("\" \"".to_string())), Box::new(Term::Con("intercalate".to_string(), vec![Box::new(Term::Lit("\" \"".to_string())), Box::new(Term::Con("map".to_string(), vec![Box::new(Term::Con("patternKey".to_string(), vec![])), Box::new(args.clone())]))]))]))])), Box::new(Term::Lit("\")\"".to_string()))]))
    } else {
        None
    }
}

pub fn check_conflicting_rules(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "checkConflictingRules" && a.len() == 1) {
    let rules = get_arg(t, 0).clone();
        Some(Term::Con("let".to_string(), vec![Box::new(Term::Var("grouped".to_string())), Box::new(Term::Con("groupBy".to_string(), vec![Box::new(Term::Con("binder".to_string(), vec![Box::new(Term::Lit("r".to_string())), Box::new(Term::Con("patternKey".to_string(), vec![Box::new(Term::Con("rulePattern".to_string(), vec![Box::new(Term::Var("r".to_string()))]))]))])), Box::new(rules.clone())])), Box::new(Term::Con("foldl".to_string(), vec![Box::new(Term::Con("acc".to_string(), vec![Box::new(Term::Con("binder".to_string(), vec![Box::new(Term::Lit("group".to_string())), Box::new(Term::Con("if".to_string(), vec![Box::new(Term::Con("gt".to_string(), vec![Box::new(Term::Con("length".to_string(), vec![Box::new(Term::Var("group".to_string()))])), Box::new(Term::Lit("1".to_string()))])), Box::new(Term::Con("let".to_string(), vec![Box::new(Term::Var("names".to_string())), Box::new(Term::Con("map".to_string(), vec![Box::new(Term::Con("ruleName".to_string(), vec![])), Box::new(Term::Var("group".to_string()))])), Box::new(Term::Con("valResultAddWarning".to_string(), vec![Box::new(Term::Var("acc".to_string())), Box::new(Term::Con("ConflictingRules".to_string(), vec![Box::new(Term::Con("head".to_string(), vec![Box::new(Term::Var("names".to_string()))])), Box::new(Term::Con("head".to_string(), vec![Box::new(Term::Con("tail".to_string(), vec![Box::new(Term::Var("names".to_string()))]))])), Box::new(Term::Lit("\"same pattern structure\"".to_string()))]))]))])), Box::new(Term::Var("acc".to_string()))]))]))])), Box::new(Term::Con("valResultEmpty".to_string(), vec![])), Box::new(Term::Con("mapValues".to_string(), vec![Box::new(Term::Var("grouped".to_string()))]))]))]))
    } else {
        None
    }
}

pub fn validate_grammar(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "validateGrammar" && a.len() == 2) {
    let grammar = get_arg(t, 0).clone();
    let rules = get_arg(t, 1).clone();
        Some(Term::Con("valResultAppend".to_string(), vec![Box::new(Term::Con("valResultAppend".to_string(), vec![Box::new(Term::Con("checkUndefinedRefs".to_string(), vec![Box::new(grammar.clone())])), Box::new(Term::Con("checkLeftRecursion".to_string(), vec![Box::new(grammar.clone())]))])), Box::new(Term::Con("valResultAppend".to_string(), vec![Box::new(Term::Con("checkUnboundVars".to_string(), vec![Box::new(rules.clone())])), Box::new(Term::Con("checkConflictingRules".to_string(), vec![Box::new(rules.clone())]))]))]))
    } else {
        None
    }
}

pub fn format_validation_result(t: &Term) -> Option<Term> {
    if matches!(t, Term::Con(ref n, ref a) if n == "formatValidationResult" && a.len() == 1) {
    let result = get_arg(t, 0).clone();
        Some(Term::Con("let".to_string(), vec![Box::new(Term::Var("lines".to_string())), Box::new(Term::Con("valResultFormat".to_string(), vec![Box::new(result.clone())])), Box::new(Term::Con("intercalate".to_string(), vec![Box::new(Term::Lit("\"\\n\"".to_string())), Box::new(Term::Var("lines".to_string()))]))]))
    } else {
        None
    }
}

