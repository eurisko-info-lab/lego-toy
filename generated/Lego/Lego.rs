// Generated from Rosetta IR
// Module: Lego

#[derive(Debug, Clone, PartialEq)]
pub enum term {

}

#[derive(Debug, Clone, PartialEq)]
pub enum env {

}

#[derive(Debug, Clone, PartialEq)]
pub enum binding {

}

#[derive(Debug, Clone, PartialEq)]
pub enum rule {

}

#[derive(Debug, Clone, PartialEq)]
pub enum iso {

}

#[derive(Debug, Clone, PartialEq)]
pub enum symbol {

}

#[derive(Debug, Clone, PartialEq)]
pub enum production {

}

#[derive(Debug, Clone, PartialEq)]
pub enum grammar {

}

pub fn atomExpand(e: &Expr) -> Option<Expr> {
    match e {
        Expr::Atom { arg1: name } => Some(Expr::Con { arg1: Box::new(name.clone()) }),
        _ => None,
    }
}

pub fn matchVar(e: &Expr) -> Option<Expr> {
    match e {
        Expr::Match { arg1: Expr::Var { arg1: name }, arg2: t } => Some(Expr::If { arg1: Box::new(Expr::StartsWith { arg1: Box::new(name.clone()), arg2: Box::new(Expr::Lit { arg1: Box::new(Expr::String { arg1: Box::new("$") }) }) }), arg2: Box::new(Expr::Env { arg1: Box::new(Expr::Con { arg1: Box::new((), arg2: Box::new(Expr::Var { arg1: Box::new($), arg2: Box::new(name.clone()) }), arg3: Box::new(Expr::Var { arg1: Box::new($), arg2: Box::new(t.clone()) }), arg4: Box::new()) }) }), arg3: Box::new(Expr::If { arg1: Box::new(Expr::Eq { arg1: Box::new(Expr::Var { arg1: Box::new(name.clone()) }), arg2: Box::new(t.clone()) }), arg2: Box::new(Expr::Env), arg3: Box::new(Expr::Fail) }) }),
        _ => None,
    }
}

pub fn matchLit(e: &Expr) -> Option<Expr> {
    match e {
        Expr::Match { arg1: Expr::Lit { arg1: a }, arg2: Expr::Lit { arg1: b } } => Some(Expr::If { arg1: Box::new(Expr::Eq { arg1: Box::new(a.clone()), arg2: Box::new(b.clone()) }), arg2: Box::new(Expr::Env), arg3: Box::new(Expr::Fail) }),
        _ => None,
    }
}

pub fn matchCon(e: &Expr) -> Option<Expr> {
    match e {
        Expr::Match { arg1: Expr::Con { arg1: n1, arg2: args1 }, arg2: Expr::Con { arg1: n2, arg2: args2 } } => Some(Expr::If { arg1: Box::new(Expr::Eq { arg1: Box::new(n1.clone()), arg2: Box::new(n2.clone()) }), arg2: Box::new(Expr::MatchList { arg1: Box::new(args1.clone()), arg2: Box::new(args2.clone()) }), arg3: Box::new(Expr::Fail) }),
        _ => None,
    }
}

pub fn matchFail(e: &Expr) -> Option<Expr> {
    match e {
        Expr::Match { arg1: p, arg2: t } => Some(Expr::Fail),
        _ => None,
    }
}

pub fn matchListNil(e: &Expr) -> Option<Expr> {
    match e {
        Expr::MatchList { arg1: Expr::Unit { arg1: (, arg2: ) }, arg2: Expr::Unit { arg1: (, arg2: ) } } => Some(Expr::Env),
        _ => None,
    }
}

pub fn matchListCons(e: &Expr) -> Option<Expr> {
    match e {
        Expr::MatchList { arg1: Expr::Con { arg1: (, arg2: Expr::Var { arg1: $, arg2: p }, arg3: Expr::Var { arg1: $, arg2: ps }, arg4: ) }, arg2: Expr::Con { arg1: (, arg2: Expr::Var { arg1: $, arg2: t }, arg3: Expr::Var { arg1: $, arg2: ts }, arg4: ) } } => Some(Expr::Merge { arg1: Box::new(Expr::Match { arg1: Box::new(p.clone()), arg2: Box::new(t.clone()) }), arg2: Box::new(Expr::MatchList { arg1: Box::new(ps.clone()), arg2: Box::new(ts.clone()) }) }),
        _ => None,
    }
}

pub fn mergeEnvs(e: &Expr) -> Option<Expr> {
    match e {
        Expr::Merge { arg1: Expr::Env { arg1: bs1 }, arg2: Expr::Env { arg1: bs2 } } => Some(Expr::Env { arg1: Box::new(bs1.clone()), arg2: Box::new(bs2.clone()) }),
        _ => None,
    }
}

pub fn mergeFail(e: &Expr) -> Option<Expr> {
    match e {
        Expr::Merge { arg1: Expr::Fail, arg2: e } => Some(Expr::Fail),
        _ => None,
    }
}

pub fn substVar(e: &Expr) -> Option<Expr> {
    match e {
        Expr::Subst { arg1: Expr::Var { arg1: name }, arg2: Expr::Env { arg1: bindings } } => Some(Expr::Lookup { arg1: Box::new(name.clone()), arg2: Box::new(bindings.clone()) }),
        _ => None,
    }
}

pub fn substLit(e: &Expr) -> Option<Expr> {
    match e {
        Expr::Subst { arg1: Expr::Lit { arg1: s }, arg2: env } => Some(Expr::Lit { arg1: Box::new(s.clone()) }),
        _ => None,
    }
}

pub fn substCon(e: &Expr) -> Option<Expr> {
    match e {
        Expr::Subst { arg1: Expr::Con { arg1: name, arg2: args }, arg2: env } => Some(Expr::Con { arg1: Box::new(name.clone()), arg2: Box::new(Expr::MapSubst { arg1: Box::new(args.clone()), arg2: Box::new(env.clone()) }) }),
        _ => None,
    }
}

pub fn mapSubstNil(e: &Expr) -> Option<Expr> {
    match e {
        Expr::MapSubst { arg1: Expr::Unit { arg1: (, arg2: ) }, arg2: env } => Some(Expr::Unit { arg1: Box::new((), arg2: Box::new()) }),
        _ => None,
    }
}

pub fn mapSubstCons(e: &Expr) -> Option<Expr> {
    match e {
        Expr::MapSubst { arg1: Expr::Con { arg1: (, arg2: Expr::Var { arg1: $, arg2: t }, arg3: Expr::Var { arg1: $, arg2: ts }, arg4: ) }, arg2: env } => Some(Expr::Con { arg1: Box::new((), arg2: Box::new(Expr::App { arg1: Box::new((), arg2: Box::new(Expr::Con { arg1: Box::new(subst.clone()) }), arg3: Box::new(Expr::Var { arg1: Box::new($), arg2: Box::new(t.clone()) }), arg4: Box::new(Expr::Var { arg1: Box::new($), arg2: Box::new(env.clone()) }), arg5: Box::new()) }), arg3: Box::new(Expr::Con { arg1: Box::new((), arg2: Box::new(mapSubst.clone()), arg3: Box::new(Expr::Var { arg1: Box::new($), arg2: Box::new(ts.clone()) }), arg4: Box::new(Expr::Var { arg1: Box::new($), arg2: Box::new(env.clone()) }), arg5: Box::new()) }), arg4: Box::new()) }),
        _ => None,
    }
}

pub fn lookupHit(e: &Expr) -> Option<Expr> {
    match e {
        Expr::Lookup { arg1: name, arg2: Expr::App { arg1: (, arg2: (, arg3: name, arg4: val, arg5: ), arg6: rest, arg7: ) } } => Some(val.clone()),
        _ => None,
    }
}

pub fn lookupMiss(e: &Expr) -> Option<Expr> {
    match e {
        Expr::Lookup { arg1: name, arg2: Expr::App { arg1: (, arg2: (, arg3: other, arg4: val, arg5: ), arg6: rest, arg7: ) } } => Some(Expr::Lookup { arg1: Box::new(name.clone()), arg2: Box::new(rest.clone()) }),
        _ => None,
    }
}

pub fn lookupFail(e: &Expr) -> Option<Expr> {
    match e {
        Expr::Lookup { arg1: name, arg2: Expr::Unit { arg1: (, arg2: ) } } => Some(Expr::Var { arg1: Box::new(name.clone()) }),
        _ => None,
    }
}

pub fn applyRule(e: &Expr) -> Option<Expr> {
    match e {
        Expr::Apply { arg1: Expr::Rule { arg1: name, arg2: pat, arg3: tmpl }, arg2: t } => Some(Expr::Case { arg1: Box::new(Expr::Match { arg1: Box::new(pat.clone()), arg2: Box::new(t.clone()) }), arg2: Box::new(Expr::Env { arg1: Box::new(bs.clone()) }), arg3: Box::new(Expr::Subst { arg1: Box::new(tmpl.clone()), arg2: Box::new(Expr::Env { arg1: Box::new(bs.clone()) }) }), arg4: Box::new(Expr::Fail), arg5: Box::new(Expr::Fail) }),
        _ => None,
    }
}

pub fn tryFirst(e: &Expr) -> Option<Expr> {
    match e {
        Expr::TryRules { arg1: Expr::App { arg1: (, arg2: (, arg3: rule, arg4: n, arg5: p, arg6: t, arg7: ), arg8: rest, arg9: ) }, arg2: term } => Some(Expr::Case { arg1: Box::new(Expr::Apply { arg1: Box::new(Expr::Rule { arg1: Box::new(n.clone()), arg2: Box::new(p.clone()), arg3: Box::new(t.clone()) }), arg2: Box::new(term.clone()) }), arg2: Box::new(Expr::Fail), arg3: Box::new(Expr::TryRules { arg1: Box::new(rest.clone()), arg2: Box::new(term.clone()) }), arg4: Box::new(result.clone()), arg5: Box::new(result.clone()) }),
        _ => None,
    }
}

pub fn tryEmpty(e: &Expr) -> Option<Expr> {
    match e {
        Expr::TryRules { arg1: Expr::Unit { arg1: (, arg2: ) }, arg2: term } => Some(Expr::Fail),
        _ => None,
    }
}

pub fn normalizeStep(e: &Expr) -> Option<Expr> {
    match e {
        Expr::Normalize { arg1: rules, arg2: t } => Some(Expr::LetIn { arg1: Box::new((), arg2: Box::new(let), arg3: Box::new($), arg4: Box::new(t'.clone()), arg5: Box::new(=), arg6: Box::new(Expr::NormalizeOnce { arg1: Box::new(rules.clone()), arg2: Box::new(t.clone()) }), arg7: Box::new(in), arg8: Box::new(Expr::If { arg1: Box::new(Expr::Eq { arg1: Box::new(t.clone()), arg2: Box::new(t'.clone()) }), arg2: Box::new(t.clone()), arg3: Box::new(Expr::Normalize { arg1: Box::new(rules.clone()), arg2: Box::new(t'.clone()) }) }), arg9: Box::new()) }),
        _ => None,
    }
}

pub fn normalizeOnce(e: &Expr) -> Option<Expr> {
    match e {
        Expr::NormalizeOnce { arg1: rules, arg2: t } => Some(Expr::Case { arg1: Box::new(Expr::TryRules { arg1: Box::new(rules.clone()), arg2: Box::new(t.clone()) }), arg2: Box::new(Expr::Fail), arg3: Box::new(Expr::NormalizeChildren { arg1: Box::new(rules.clone()), arg2: Box::new(t.clone()) }), arg4: Box::new(result.clone()), arg5: Box::new(result.clone()) }),
        _ => None,
    }
}

pub fn normalizeChildrenVar(e: &Expr) -> Option<Expr> {
    match e {
        Expr::NormalizeChildren { arg1: rules, arg2: Expr::Var { arg1: x } } => Some(Expr::Var { arg1: Box::new(x.clone()) }),
        _ => None,
    }
}

pub fn normalizeChildrenLit(e: &Expr) -> Option<Expr> {
    match e {
        Expr::NormalizeChildren { arg1: rules, arg2: Expr::Lit { arg1: s } } => Some(Expr::Lit { arg1: Box::new(s.clone()) }),
        _ => None,
    }
}

pub fn normalizeChildrenCon(e: &Expr) -> Option<Expr> {
    match e {
        Expr::NormalizeChildren { arg1: rules, arg2: Expr::Con { arg1: name, arg2: args } } => Some(Expr::Con { arg1: Box::new(name.clone()), arg2: Box::new(Expr::MapNormalize { arg1: Box::new(rules.clone()), arg2: Box::new(args.clone()) }) }),
        _ => None,
    }
}

pub fn mapNormalizeNil(e: &Expr) -> Option<Expr> {
    match e {
        Expr::MapNormalize { arg1: rules, arg2: Expr::Unit { arg1: (, arg2: ) } } => Some(Expr::Unit { arg1: Box::new((), arg2: Box::new()) }),
        _ => None,
    }
}

pub fn mapNormalizeCons(e: &Expr) -> Option<Expr> {
    match e {
        Expr::MapNormalize { arg1: rules, arg2: Expr::Con { arg1: (, arg2: Expr::Var { arg1: $, arg2: t }, arg3: Expr::Var { arg1: $, arg2: ts }, arg4: ) } } => Some(Expr::Con { arg1: Box::new((), arg2: Box::new(Expr::App { arg1: Box::new((), arg2: Box::new(Expr::Con { arg1: Box::new(normalizeOnce.clone()) }), arg3: Box::new(Expr::Var { arg1: Box::new($), arg2: Box::new(rules.clone()) }), arg4: Box::new(Expr::Var { arg1: Box::new($), arg2: Box::new(t.clone()) }), arg5: Box::new()) }), arg3: Box::new(Expr::Con { arg1: Box::new((), arg2: Box::new(mapNormalize.clone()), arg3: Box::new(Expr::Var { arg1: Box::new($), arg2: Box::new(rules.clone()) }), arg4: Box::new(Expr::Var { arg1: Box::new($), arg2: Box::new(ts.clone()) }), arg5: Box::new()) }), arg4: Box::new()) }),
        _ => None,
    }
}

pub fn isoId(e: &Expr) -> Option<Expr> {
    match e {
        Expr::IsoId => Some(Expr::Iso { arg1: Box::new(Expr::Con { arg1: Box::new((), arg2: Box::new(Expr::Var { arg1: Box::new($), arg2: Box::new(x.clone()) }), arg3: Box::new(Expr::Con { arg1: Box::new((), arg2: Box::new(some.clone()), arg3: Box::new(Expr::Var { arg1: Box::new($), arg2: Box::new(x.clone()) }), arg4: Box::new()) }), arg4: Box::new()) }), arg2: Box::new(Expr::Con { arg1: Box::new((), arg2: Box::new(Expr::Var { arg1: Box::new($), arg2: Box::new(x.clone()) }), arg3: Box::new(Expr::Con { arg1: Box::new((), arg2: Box::new(some.clone()), arg3: Box::new(Expr::Var { arg1: Box::new($), arg2: Box::new(x.clone()) }), arg4: Box::new()) }), arg4: Box::new()) }) }),
        _ => None,
    }
}

pub fn isoComp(e: &Expr) -> Option<Expr> {
    match e {
        Expr::IsoComp { arg1: Expr::Iso { arg1: fwd1, arg2: bwd1 }, arg2: Expr::Iso { arg1: fwd2, arg2: bwd2 } } => Some(Expr::Iso { arg1: Box::new(Expr::Con { arg1: Box::new((), arg2: Box::new(Expr::Var { arg1: Box::new($), arg2: Box::new(a.clone()) }), arg3: Box::new(Expr::Con { arg1: Box::new((), arg2: Box::new(bind.clone()), arg3: Box::new(Expr::Con { arg1: Box::new((), arg2: Box::new(apply.clone()), arg3: Box::new(Expr::Var { arg1: Box::new($), arg2: Box::new(fwd1.clone()) }), arg4: Box::new(Expr::Var { arg1: Box::new($), arg2: Box::new(a.clone()) }), arg5: Box::new()) }), arg4: Box::new(Expr::Var { arg1: Box::new($), arg2: Box::new(b.clone()) }), arg5: Box::new(Expr::Con { arg1: Box::new((), arg2: Box::new(apply.clone()), arg3: Box::new(Expr::Var { arg1: Box::new($), arg2: Box::new(fwd2.clone()) }), arg4: Box::new(Expr::Var { arg1: Box::new($), arg2: Box::new(b.clone()) }), arg5: Box::new()) }), arg6: Box::new()) }), arg4: Box::new()) }), arg2: Box::new(Expr::Con { arg1: Box::new((), arg2: Box::new(Expr::Var { arg1: Box::new($), arg2: Box::new(c.clone()) }), arg3: Box::new(Expr::Con { arg1: Box::new((), arg2: Box::new(bind.clone()), arg3: Box::new(Expr::Con { arg1: Box::new((), arg2: Box::new(apply.clone()), arg3: Box::new(Expr::Var { arg1: Box::new($), arg2: Box::new(bwd2.clone()) }), arg4: Box::new(Expr::Var { arg1: Box::new($), arg2: Box::new(c.clone()) }), arg5: Box::new()) }), arg4: Box::new(Expr::Var { arg1: Box::new($), arg2: Box::new(b.clone()) }), arg5: Box::new(Expr::Con { arg1: Box::new((), arg2: Box::new(apply.clone()), arg3: Box::new(Expr::Var { arg1: Box::new($), arg2: Box::new(bwd1.clone()) }), arg4: Box::new(Expr::Var { arg1: Box::new($), arg2: Box::new(b.clone()) }), arg5: Box::new()) }), arg6: Box::new()) }), arg4: Box::new()) }) }),
        _ => None,
    }
}

pub fn isoSym(e: &Expr) -> Option<Expr> {
    match e {
        Expr::IsoSym { arg1: Expr::Iso { arg1: fwd, arg2: bwd } } => Some(Expr::Iso { arg1: Box::new(bwd.clone()), arg2: Box::new(fwd.clone()) }),
        _ => None,
    }
}

pub fn stringEq(e: &Expr) -> Option<Expr> {
    match e {
        Expr::Eq { arg1: Expr::Lit { arg1: a }, arg2: Expr::Lit { arg1: b } } => Some(Expr::EqStrings { arg1: Box::new(a.clone()), arg2: Box::new(b.clone()) }),
        _ => None,
    }
}

pub fn startsWith(e: &Expr) -> Option<Expr> {
    match e {
        Expr::StartsWith { arg1: s, arg2: prefix } => Some(Expr::StartsWithBuiltin { arg1: Box::new(s.clone()), arg2: Box::new(prefix.clone()) }),
        _ => None,
    }
}

pub fn ifTrue(e: &Expr) -> Option<Expr> {
    match e {
        Expr::If { arg1: Expr::True, arg2: then, arg3: else_ } => Some(then.clone()),
        _ => None,
    }
}

pub fn ifFalse(e: &Expr) -> Option<Expr> {
    match e {
        Expr::If { arg1: Expr::False, arg2: then, arg3: else_ } => Some(else_.clone()),
        _ => None,
    }
}

pub fn bindSome(e: &Expr) -> Option<Expr> {
    match e {
        Expr::Bind { arg1: Expr::Some { arg1: x }, arg2: var, arg3: body } => Some(Expr::Subst { arg1: Box::new(body.clone()), arg2: Box::new(Expr::Env { arg1: Box::new(Expr::Con { arg1: Box::new((), arg2: Box::new(Expr::Var { arg1: Box::new($), arg2: Box::new(var.clone()) }), arg3: Box::new(Expr::Var { arg1: Box::new($), arg2: Box::new(x.clone()) }), arg4: Box::new()) }) }) }),
        _ => None,
    }
}

pub fn bindNone(e: &Expr) -> Option<Expr> {
    match e {
        Expr::Bind { arg1: Expr::None, arg2: var, arg3: body } => Some(Expr::None),
        _ => None,
    }
}

pub fn caseMatch(e: &Expr) -> Option<Expr> {
    match e {
        Expr::Case { arg1: scrutinee, arg2: pat1, arg3: body1, arg4: rest } => Some(Expr::Case { arg1: Box::new(Expr::Match { arg1: Box::new(pat1.clone()), arg2: Box::new(scrutinee.clone()) }), arg2: Box::new(Expr::Env { arg1: Box::new(bs.clone()) }), arg3: Box::new(Expr::Subst { arg1: Box::new(body1.clone()), arg2: Box::new(Expr::Env { arg1: Box::new(bs.clone()) }) }), arg4: Box::new(Expr::Fail), arg5: Box::new(Expr::Case { arg1: Box::new(scrutinee.clone()), arg2: Box::new(rest.clone()) }) }),
        _ => None,
    }
}

pub fn caseEmpty(e: &Expr) -> Option<Expr> {
    match e {
        Expr::Case { arg1: scrutinee } => Some(Expr::Stuck { arg1: Box::new(scrutinee.clone()) }),
        _ => None,
    }
}

pub fn mapNil(e: &Expr) -> Option<Expr> {
    match e {
        Expr::Map { arg1: f, arg2: Expr::Unit { arg1: (, arg2: ) } } => Some(Expr::Unit { arg1: Box::new((), arg2: Box::new()) }),
        _ => None,
    }
}

pub fn mapCons(e: &Expr) -> Option<Expr> {
    match e {
        Expr::Map { arg1: f, arg2: Expr::Con { arg1: (, arg2: Expr::Var { arg1: $, arg2: x }, arg3: Expr::Var { arg1: $, arg2: xs }, arg4: ) } } => Some(Expr::Con { arg1: Box::new((), arg2: Box::new(Expr::App { arg1: Box::new((), arg2: Box::new(Expr::Con { arg1: Box::new(apply.clone()) }), arg3: Box::new(Expr::Var { arg1: Box::new($), arg2: Box::new(f.clone()) }), arg4: Box::new(Expr::Var { arg1: Box::new($), arg2: Box::new(x.clone()) }), arg5: Box::new()) }), arg3: Box::new(Expr::Con { arg1: Box::new((), arg2: Box::new(map.clone()), arg3: Box::new(Expr::Var { arg1: Box::new($), arg2: Box::new(f.clone()) }), arg4: Box::new(Expr::Var { arg1: Box::new($), arg2: Box::new(xs.clone()) }), arg5: Box::new()) }), arg4: Box::new()) }),
        _ => None,
    }
}

pub fn foldNil(e: &Expr) -> Option<Expr> {
    match e {
        Expr::Fold { arg1: f, arg2: acc, arg3: Expr::Unit { arg1: (, arg2: ) } } => Some(acc.clone()),
        _ => None,
    }
}

pub fn foldCons(e: &Expr) -> Option<Expr> {
    match e {
        Expr::Fold { arg1: f, arg2: acc, arg3: Expr::Con { arg1: (, arg2: Expr::Var { arg1: $, arg2: x }, arg3: Expr::Var { arg1: $, arg2: xs }, arg4: ) } } => Some(Expr::Fold { arg1: Box::new(f.clone()), arg2: Box::new(Expr::Apply { arg1: Box::new(f.clone()), arg2: Box::new(acc.clone()), arg3: Box::new(x.clone()) }), arg3: Box::new(xs.clone()) }),
        _ => None,
    }
}

pub fn appendNil(e: &Expr) -> Option<Expr> {
    match e {
        Expr::Append { arg1: Expr::Unit { arg1: (, arg2: ) }, arg2: ys } => Some(ys.clone()),
        _ => None,
    }
}

pub fn appendCons(e: &Expr) -> Option<Expr> {
    match e {
        Expr::Append { arg1: Expr::Con { arg1: (, arg2: Expr::Var { arg1: $, arg2: x }, arg3: Expr::Var { arg1: $, arg2: xs }, arg4: ) }, arg2: ys } => Some(Expr::Con { arg1: Box::new((), arg2: Box::new(Expr::Var { arg1: Box::new($), arg2: Box::new(x.clone()) }), arg3: Box::new(Expr::Con { arg1: Box::new((), arg2: Box::new(append.clone()), arg3: Box::new(Expr::Var { arg1: Box::new($), arg2: Box::new(xs.clone()) }), arg4: Box::new(Expr::Var { arg1: Box::new($), arg2: Box::new(ys.clone()) }), arg5: Box::new()) }), arg4: Box::new()) }),
        _ => None,
    }
}

pub fn lengthNil(e: &Expr) -> Option<Expr> {
    match e {
        Expr::Length { arg1: Expr::Unit { arg1: (, arg2: ) } } => Some(Expr::Zero),
        _ => None,
    }
}

pub fn lengthCons(e: &Expr) -> Option<Expr> {
    match e {
        Expr::Length { arg1: Expr::Con { arg1: (, arg2: Expr::Var { arg1: $, arg2: x }, arg3: Expr::Var { arg1: $, arg2: xs }, arg4: ) } } => Some(Expr::Succ { arg1: Box::new(Expr::Length { arg1: Box::new(xs.clone()) }) }),
        _ => None,
    }
}
