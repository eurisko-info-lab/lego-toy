// Generated from Rosetta IR
// Module: Lego

package generated

enum term:


enum env:


enum binding:


enum rule:


enum iso:


enum symbol:


enum production:


enum grammar:


def atomExpand(e: Expr): Option[Expr] = e match
  case Atom(name) => Some(Con(name))
  case _ => None

def matchVar(e: Expr): Option[Expr] = e match
  case Match(Var(name), t) => Some(If(StartsWith(name, Lit(String("$"))), Env(Con((, Var($, name), Var($, t), ))), If(Eq(Var(name), t), Env(), Fail())))
  case _ => None

def matchLit(e: Expr): Option[Expr] = e match
  case Match(Lit(a), Lit(b)) => Some(If(Eq(a, b), Env(), Fail()))
  case _ => None

def matchCon(e: Expr): Option[Expr] = e match
  case Match(Con(n1, args1), Con(n2, args2)) => Some(If(Eq(n1, n2), MatchList(args1, args2), Fail()))
  case _ => None

def matchFail(e: Expr): Option[Expr] = e match
  case Match(p, t) => Some(Fail())
  case _ => None

def matchListNil(e: Expr): Option[Expr] = e match
  case MatchList(Unit((, )), Unit((, ))) => Some(Env())
  case _ => None

def matchListCons(e: Expr): Option[Expr] = e match
  case MatchList(Con((, Var($, p), Var($, ps), )), Con((, Var($, t), Var($, ts), ))) => Some(Merge(Match(p, t), MatchList(ps, ts)))
  case _ => None

def mergeEnvs(e: Expr): Option[Expr] = e match
  case Merge(Env(bs1), Env(bs2)) => Some(Env(bs1, bs2))
  case _ => None

def mergeFail(e: Expr): Option[Expr] = e match
  case Merge(Fail(), e) => Some(Fail())
  case _ => None

def substVar(e: Expr): Option[Expr] = e match
  case Subst(Var(name), Env(bindings)) => Some(Lookup(name, bindings))
  case _ => None

def substLit(e: Expr): Option[Expr] = e match
  case Subst(Lit(s), env) => Some(Lit(s))
  case _ => None

def substCon(e: Expr): Option[Expr] = e match
  case Subst(Con(name, args), env) => Some(Con(name, MapSubst(args, env)))
  case _ => None

def mapSubstNil(e: Expr): Option[Expr] = e match
  case MapSubst(Unit((, )), env) => Some(Unit((, )))
  case _ => None

def mapSubstCons(e: Expr): Option[Expr] = e match
  case MapSubst(Con((, Var($, t), Var($, ts), )), env) => Some(Con((, App((, Con(subst), Var($, t), Var($, env), )), Con((, mapSubst, Var($, ts), Var($, env), )), )))
  case _ => None

def lookupHit(e: Expr): Option[Expr] = e match
  case Lookup(name, App((, (, name, val_, ), rest, ))) => Some(val_)
  case _ => None

def lookupMiss(e: Expr): Option[Expr] = e match
  case Lookup(name, App((, (, other, val_, ), rest, ))) => Some(Lookup(name, rest))
  case _ => None

def lookupFail(e: Expr): Option[Expr] = e match
  case Lookup(name, Unit((, ))) => Some(Var(name))
  case _ => None

def applyRule(e: Expr): Option[Expr] = e match
  case Apply(Rule(name, pat, tmpl), t) => Some(Case(Match(pat, t), Env(bs), Subst(tmpl, Env(bs)), Fail(), Fail()))
  case _ => None

def tryFirst(e: Expr): Option[Expr] = e match
  case TryRules(App((, (, rule, n, p, t, ), rest, )), term) => Some(Case(Apply(Rule(n, p, t), term), Fail(), TryRules(rest, term), result, result))
  case _ => None

def tryEmpty(e: Expr): Option[Expr] = e match
  case TryRules(Unit((, )), term) => Some(Fail())
  case _ => None

def normalizeStep(e: Expr): Option[Expr] = e match
  case Normalize(rules, t) => Some(LetIn((, let, $, t', =, NormalizeOnce(rules, t), in, If(Eq(t, t'), t, Normalize(rules, t')), )))
  case _ => None

def normalizeOnce(e: Expr): Option[Expr] = e match
  case NormalizeOnce(rules, t) => Some(Case(TryRules(rules, t), Fail(), NormalizeChildren(rules, t), result, result))
  case _ => None

def normalizeChildrenVar(e: Expr): Option[Expr] = e match
  case NormalizeChildren(rules, Var(x)) => Some(Var(x))
  case _ => None

def normalizeChildrenLit(e: Expr): Option[Expr] = e match
  case NormalizeChildren(rules, Lit(s)) => Some(Lit(s))
  case _ => None

def normalizeChildrenCon(e: Expr): Option[Expr] = e match
  case NormalizeChildren(rules, Con(name, args)) => Some(Con(name, MapNormalize(rules, args)))
  case _ => None

def mapNormalizeNil(e: Expr): Option[Expr] = e match
  case MapNormalize(rules, Unit((, ))) => Some(Unit((, )))
  case _ => None

def mapNormalizeCons(e: Expr): Option[Expr] = e match
  case MapNormalize(rules, Con((, Var($, t), Var($, ts), ))) => Some(Con((, App((, Con(normalizeOnce), Var($, rules), Var($, t), )), Con((, mapNormalize, Var($, rules), Var($, ts), )), )))
  case _ => None

def isoId(e: Expr): Option[Expr] = e match
  case IsoId() => Some(Iso(Con((, Var($, x), Con((, some, Var($, x), )), )), Con((, Var($, x), Con((, some, Var($, x), )), ))))
  case _ => None

def isoComp(e: Expr): Option[Expr] = e match
  case IsoComp(Iso(fwd1, bwd1), Iso(fwd2, bwd2)) => Some(Iso(Con((, Var($, a), Con((, bind, Con((, apply, Var($, fwd1), Var($, a), )), Var($, b), Con((, apply, Var($, fwd2), Var($, b), )), )), )), Con((, Var($, c), Con((, bind, Con((, apply, Var($, bwd2), Var($, c), )), Var($, b), Con((, apply, Var($, bwd1), Var($, b), )), )), ))))
  case _ => None

def isoSym(e: Expr): Option[Expr] = e match
  case IsoSym(Iso(fwd, bwd)) => Some(Iso(bwd, fwd))
  case _ => None

def stringEq(e: Expr): Option[Expr] = e match
  case Eq(Lit(a), Lit(b)) => Some(EqStrings(a, b))
  case _ => None

def startsWith(e: Expr): Option[Expr] = e match
  case StartsWith(s, prefix) => Some(StartsWithBuiltin(s, prefix))
  case _ => None

def ifTrue(e: Expr): Option[Expr] = e match
  case If(True(), then_, else_) => Some(then_)
  case _ => None

def ifFalse(e: Expr): Option[Expr] = e match
  case If(False(), then_, else_) => Some(else_)
  case _ => None

def bindSome(e: Expr): Option[Expr] = e match
  case Bind(Some(x), var_, body) => Some(Subst(body, Env(Con((, Var($, var_), Var($, x), )))))
  case _ => None

def bindNone(e: Expr): Option[Expr] = e match
  case Bind(None(), var_, body) => Some(None())
  case _ => None

def caseMatch(e: Expr): Option[Expr] = e match
  case Case(scrutinee, pat1, body1, rest) => Some(Case(Match(pat1, scrutinee), Env(bs), Subst(body1, Env(bs)), Fail(), Case(scrutinee, rest)))
  case _ => None

def caseEmpty(e: Expr): Option[Expr] = e match
  case Case(scrutinee) => Some(Stuck(scrutinee))
  case _ => None

def mapNil(e: Expr): Option[Expr] = e match
  case Map(f, Unit((, ))) => Some(Unit((, )))
  case _ => None

def mapCons(e: Expr): Option[Expr] = e match
  case Map(f, Con((, Var($, x), Var($, xs), ))) => Some(Con((, App((, Con(apply), Var($, f), Var($, x), )), Con((, map, Var($, f), Var($, xs), )), )))
  case _ => None

def foldNil(e: Expr): Option[Expr] = e match
  case Fold(f, acc, Unit((, ))) => Some(acc)
  case _ => None

def foldCons(e: Expr): Option[Expr] = e match
  case Fold(f, acc, Con((, Var($, x), Var($, xs), ))) => Some(Fold(f, Apply(f, acc, x), xs))
  case _ => None

def appendNil(e: Expr): Option[Expr] = e match
  case Append(Unit((, )), ys) => Some(ys)
  case _ => None

def appendCons(e: Expr): Option[Expr] = e match
  case Append(Con((, Var($, x), Var($, xs), )), ys) => Some(Con((, Var($, x), Con((, append, Var($, xs), Var($, ys), )), )))
  case _ => None

def lengthNil(e: Expr): Option[Expr] = e match
  case Length(Unit((, ))) => Some(Zero())
  case _ => None

def lengthCons(e: Expr): Option[Expr] = e match
  case Length(Con((, Var($, x), Var($, xs), ))) => Some(Succ(Length(xs)))
  case _ => None
