package generated

sealed trait Iso[a, b]

case class MkIso[a, b]( v0: (a) => Option[b] ,  v1: (b) => Option[a]) extends Iso[a, b]

sealed trait Term

case class Var( v0: String) extends Term
case class Lit( v0: String) extends Term
case class Con( v0: String ,  v1: List[Term]) extends Term

sealed trait AST[a]

case class MkAST[a]( v0: (String) => a ,  v1: (String) => a ,  v2: (String) => (List[a]) => a) extends AST[a]

sealed trait PieceLevel

case class TokenLevel() extends PieceLevel
case class SyntaxLevel() extends PieceLevel

sealed trait Rule

case class MkRule( v0: String ,  v1: Term ,  v2: Term) extends Rule

sealed trait TypeRule

case class MkTypeRule( v0: String ,  v1: Term ,  v2: Term) extends TypeRule

sealed trait GrammarExpr

case class GEmpty() extends GrammarExpr
case class GLit( v0: String) extends GrammarExpr
case class GRef( v0: String) extends GrammarExpr
case class GSeq( v0: GrammarExpr ,  v1: GrammarExpr) extends GrammarExpr
case class GAlt( v0: GrammarExpr ,  v1: GrammarExpr) extends GrammarExpr
case class GStar( v0: GrammarExpr) extends GrammarExpr
case class GPlus( v0: GrammarExpr) extends GrammarExpr
case class GOpt( v0: GrammarExpr) extends GrammarExpr
case class GNot( v0: GrammarExpr) extends GrammarExpr
case class GAnd( v0: GrammarExpr) extends GrammarExpr
case class GCon( v0: String ,  v1: GrammarExpr) extends GrammarExpr

sealed trait GrammarProduction

case class MkGrammarProduction( v0: String ,  v1: GrammarExpr ,  v2: String) extends GrammarProduction

sealed trait Piece

case class MkPiece( v0: String ,  v1: PieceLevel ,  v2: List[GrammarProduction] ,  v3: List[Rule] ,  v4: List[TypeRule]) extends Piece

sealed trait Language

case class MkLanguage( v0: String ,  v1: List[Piece]) extends Language

sealed trait SourceLoc

case class MkSourceLoc( v0: String ,  v1: Int ,  v2: Int ,  v3: Int) extends SourceLoc
case class UnknownLoc() extends SourceLoc

sealed trait Severity

case class SevError() extends Severity
case class SevWarning() extends Severity
case class SevInfo() extends Severity

sealed trait Binding

case class MkBinding( v0: String ,  v1: Term ,  v2: Option[Term] ,  v3: SourceLoc) extends Binding

sealed trait TypeError

case class MkTypeError( v0: String ,  v1: SourceLoc ,  v2: Severity ,  v3: Option[Term] ,  v4: Option[Term] ,  v5: List[Binding]) extends TypeError

sealed trait EvalResult

case class EvalOk( v0: Term ,  v1: List[TypeError]) extends EvalResult
case class EvalFailed( v0: List[TypeError]) extends EvalResult

sealed trait Context

case class EmptyContext() extends Context
case class ContextCons( v0: Binding ,  v1: Context) extends Context

sealed trait VarContext

case class EmptyVarContext() extends VarContext
case class VarContextCons( v0: String ,  v1: VarContext) extends VarContext

sealed trait EvalEnv

case class MkEvalEnv( v0: AttrEnv ,  v1: Context ,  v2: VarContext ,  v3: List[TypeError] ,  v4: SourceLoc) extends EvalEnv

sealed trait Mode

case class Infer() extends Mode
case class Check() extends Mode

sealed trait AttrFlow

case class Syn() extends AttrFlow
case class Inh() extends AttrFlow
case class SynInh() extends AttrFlow

sealed trait AttrPath

case class Empty() extends AttrPath
case class PathCon( v0: String ,  v1: AttrPath) extends AttrPath

sealed trait AttrRef

case class MkAttrRef( v0: AttrPath ,  v1: String) extends AttrRef

sealed trait AttrRule

case class MkAttrRule( v0: String ,  v1: AttrPath ,  v2: Term) extends AttrRule

sealed trait AttrDef

case class MkAttrDef( v0: String ,  v1: AttrFlow ,  v2: Option[Term] ,  v3: List[AttrRule]) extends AttrDef

sealed trait AttrEnv

case class EmptyAttrEnv() extends AttrEnv
case class AttrEnvCons( v0: AttrPath ,  v1: String ,  v2: Term ,  v3: AttrEnv) extends AttrEnv

sealed trait AttrLanguage

case class MkAttrLanguage( v0: String ,  v1: List[GrammarProduction] ,  v2: List[AttrDef]) extends AttrLanguage

sealed trait Token

case class TokIdent( v0: String) extends Token
case class TokString( v0: String) extends Token
case class TokInt( v0: Int) extends Token
case class TokSym( v0: String) extends Token
case class TokEOF() extends Token

sealed trait ParseState

case class MkState( v0: List[Token] ,  v1: Int) extends ParseState

sealed trait ParseResult

case class ParseOk( v0: Term ,  v1: ParseState) extends ParseResult
case class ParseFail( v0: String ,  v1: ParseState) extends ParseResult

sealed trait PrintResult

case class PrintOk( v0: List[Token]) extends PrintResult
case class PrintFail( v0: String) extends PrintResult

sealed trait Env

case class EnvEmpty() extends Env
case class Bind( v0: String ,  v1: Term ,  v2: Env) extends Env

sealed trait Symbol

case class Terminal( v0: String) extends Symbol
case class NonTerminal( v0: String) extends Symbol
case class Epsilon() extends Symbol

sealed trait Production

case class MkProd( v0: String ,  v1: List[Symbol] ,  v2: String) extends Production

sealed trait Grammar

case class MkGrammar( v0: List[Production]) extends Grammar

sealed trait Parser

case class MkParser( v0: Grammar ,  v1: (String) => Option[Term]) extends Parser

sealed trait Printer

case class MkPrinter( v0: Grammar ,  v1: (Term) => Option[String]) extends Printer

sealed trait LoadedGrammar

case class LoadedGrammarMkGrammar( v0: List[Production] ,  v1: List[Production] ,  v2: List[String] ,  v3: String) extends LoadedGrammar

sealed trait Runtime

case class MkRuntime( v0: LoadedGrammar ,  v1: List[Rule]) extends Runtime

sealed trait ValidationSeverity

case class ValError() extends ValidationSeverity
case class ValWarning() extends ValidationSeverity
case class ValInfo() extends ValidationSeverity

sealed trait ValidationError

case class UndefinedProduction( v0: String ,  v1: String) extends ValidationError
case class DuplicateProduction( v0: String) extends ValidationError
case class UnboundVariable( v0: String ,  v1: String) extends ValidationError
case class CircularImport( v0: String) extends ValidationError
case class InvalidSyntax( v0: String ,  v1: String) extends ValidationError

sealed trait ValidationWarning

case class ConflictingRules( v0: String ,  v1: String ,  v2: String) extends ValidationWarning
case class DirectLeftRecursion( v0: String) extends ValidationWarning
case class IndirectLeftRecursion( v0: List[String]) extends ValidationWarning
case class UnusedProduction( v0: String) extends ValidationWarning
case class ShadowedProduction( v0: String ,  v1: String) extends ValidationWarning
case class AmbiguousGrammar( v0: String ,  v1: String) extends ValidationWarning
case class MissingCut( v0: String ,  v1: String) extends ValidationWarning
case class RuleCycle( v0: List[String]) extends ValidationWarning
case class UnreachableAlt( v0: String ,  v1: Int) extends ValidationWarning
case class RedundantAlt( v0: String ,  v1: Int ,  v2: Int) extends ValidationWarning

sealed trait ValidationResult

case class MkValidationResult( v0: List[ValidationError] ,  v1: List[ValidationWarning]) extends ValidationResult

def isoId(t: Term): Option[Term] = t match {
  case Con("isoId", Nil) => Some(Con("MkIso", List(Con("Lam", List(Con("binder", List(Lit("x"), Con("Some", List(Con("x", Nil))))))), Con("Lam", List(Con("binder", List(Lit("x"), Con("Some", List(Con("x", Nil))))))))))
  case _ => None
}

def isoComp(t: Term): Option[Term] = t match {
  case Con("comp", List(Con("MkIso", List(f1, b1)), Con("MkIso", List(f2, b2)))) => Some(Con("MkIso", List(Con("Lam", List(Con("binder", List(Lit("a"), Con("bind", List(Con("App", List(f1, Con("a", Nil))), Con("b", Nil), Con("App", List(f2, Con("b", Nil))))))))), Con("Lam", List(Con("binder", List(Lit("c"), Con("bind", List(Con("App", List(b2, Con("c", Nil))), Con("b", Nil), Con("App", List(b1, Con("b", Nil))))))))))))
  case _ => None
}

def isoSym(t: Term): Option[Term] = t match {
  case Con("sym", List(Con("MkIso", List(fwd, bwd)))) => Some(Con("MkIso", List(bwd, fwd)))
  case _ => None
}

def isoForward(t: Term): Option[Term] = t match {
  case Con("forward", List(Con("MkIso", List(fwd, bwd)), x)) => Some(Con("App", List(fwd, x)))
  case _ => None
}

def isoBackward(t: Term): Option[Term] = t match {
  case Con("backward", List(Con("MkIso", List(fwd, bwd)), x)) => Some(Con("App", List(bwd, x)))
  case _ => None
}

def isoPar(t: Term): Option[Term] = t match {
  case Con("par", List(Con("MkIso", List(f1, b1)), Con("MkIso", List(f2, b2)))) => Some(Con("MkIso", List(Con("Lam", List(Con("binder", List(Lit("p"), Con("bind", List(Con("App", List(f1, Con("Fst", List(Con("p", Nil))))), Con("x", Nil), Con("bind", List(Con("App", List(f2, Con("Snd", List(Con("p", Nil))))), Con("y", Nil), Con("Some", List(Con("Pair", List(Con("x", Nil), Con("y", Nil))))))))))))), Con("Lam", List(Con("binder", List(Lit("p"), Con("bind", List(Con("App", List(b1, Con("Fst", List(Con("p", Nil))))), Con("x", Nil), Con("bind", List(Con("App", List(b2, Con("Snd", List(Con("p", Nil))))), Con("y", Nil), Con("Some", List(Con("Pair", List(Con("x", Nil), Con("y", Nil))))))))))))))))
  case _ => None
}

def isoOrElse(t: Term): Option[Term] = t match {
  case Con("orElse", List(Con("MkIso", List(f1, b1)), Con("MkIso", List(f2, b2)))) => Some(Con("MkIso", List(Con("Lam", List(Con("binder", List(Lit("a"), Con("case", List(Con("App", List(f1, Con("a", Nil))), Con("Some", List(Var("x"))), Con("Some", List(Var("x"))), Con("None", Nil), Con("App", List(f2, Con("a", Nil))))))))), Con("Lam", List(Con("binder", List(Lit("b"), Con("case", List(Con("App", List(b1, Con("b", Nil))), Con("Some", List(Var("x"))), Con("Some", List(Var("x"))), Con("None", Nil), Con("App", List(b2, Con("b", Nil))))))))))))
  case _ => None
}

def termAtom(t: Term): Option[Term] = t match {
  case Con("atom", List(s)) => Some(Con("Con", List(s, Con("Nil", Nil))))
  case _ => None
}

def termApp(t: Term): Option[Term] = t match {
  case Con("app", List(f, args)) => Some(Con("Con", List(f, args)))
  case _ => None
}

def matchMeta(t: Term): Option[Term] = t match {
  case Con("matchPat", List(Con("Var", List(name)), v_t)) => Some(Con("Some", List(Con("Cons", List(Con("Pair", List(name, v_t)), Con("Nil", Nil))))))
  case _ => None
}

def matchVarSame(t: Term): Option[Term] = t match {
  case Con("matchPat", List(Con("Var", List(name)), Con("Var", List(name0)))) if name0 == name => Some(Con("Some", List(Con("Nil", Nil))))
  case _ => None
}

def matchVarDiff(t: Term): Option[Term] = t match {
  case Con("matchPat", List(Con("Var", List(a)), Con("Var", List(b)))) => Some(Con("None", Nil))
  case _ => None
}

def matchLitSame(t: Term): Option[Term] = t match {
  case Con("matchPat", List(Con("Lit", List(s)), Con("Lit", List(s0)))) if s0 == s => Some(Con("Some", List(Con("Nil", Nil))))
  case _ => None
}

def matchLitDiff(t: Term): Option[Term] = t match {
  case Con("matchPat", List(Con("Lit", List(a)), Con("Lit", List(b)))) => Some(Con("None", Nil))
  case _ => None
}

def matchConSame(t: Term): Option[Term] = t match {
  case Con("matchPat", List(Con("Con", List(n, pats)), Con("Con", List(n0, args)))) if n0 == n => Some(Con("matchArgs", List(pats, args)))
  case _ => None
}

def matchConDiff(t: Term): Option[Term] = t match {
  case Con("matchPat", List(Con("Con", List(n1, pats)), Con("Con", List(n2, args)))) => Some(Con("None", Nil))
  case _ => None
}

def matchArgsNil(t: Term): Option[Term] = t match {
  case Con("matchArgs", List(Con("Nil", Nil), Con("Nil", Nil))) => Some(Con("Some", List(Con("Nil", Nil))))
  case _ => None
}

def matchArgsCons(t: Term): Option[Term] = t match {
  case Con("matchArgs", List(Con("Cons", List(p, ps)), Con("Cons", List(a, as)))) => Some(Con("merge", List(Con("matchPat", List(p, a)), Con("matchArgs", List(ps, as)))))
  case _ => None
}

def matchArgsMismatch(t: Term): Option[Term] = t match {
  case Con("matchArgs", List(ps, as)) => Some(Con("None", Nil))
  case _ => None
}

def mergeBindings(t: Term): Option[Term] = t match {
  case Con("merge", List(Con("Some", List(bs1)), Con("Some", List(bs2)))) => Some(Con("Some", List(Con("append", List(bs1, bs2)))))
  case _ => None
}

def mergeFail(t: Term): Option[Term] = t match {
  case Con("merge", List(Con("None", Nil), x)) => Some(Con("None", Nil))
  case _ => None
}

def substVar(t: Term): Option[Term] = t match {
  case Con("subst", List(Con("Var", List(name)), bindings)) => Some(Con("lookup", List(name, bindings)))
  case _ => None
}

def substLit(t: Term): Option[Term] = t match {
  case Con("subst", List(Con("Lit", List(s)), bindings)) => Some(Con("Lit", List(s)))
  case _ => None
}

def substCon(t: Term): Option[Term] = t match {
  case Con("subst", List(Con("Con", List(n, args)), bindings)) => Some(Con("Con", List(n, Con("map", List(Con("Lam", List(Con("binder", List(Lit("t"), Con("subst", List(Con("t", Nil), bindings)))))), args)))))
  case _ => None
}

def lookupHit(t: Term): Option[Term] = t match {
  case Con("lookup", List(name, Con("Cons", List(Con("Pair", List(name0, v_val)), rest)))) if name0 == name => Some(v_val)
  case _ => None
}

def lookupMiss(t: Term): Option[Term] = t match {
  case Con("lookup", List(name, Con("Cons", List(Con("Pair", List(other, v_val)), rest)))) => Some(Con("lookup", List(name, rest)))
  case _ => None
}

def lookupEmpty(t: Term): Option[Term] = t match {
  case Con("lookup", List(name, Con("Nil", Nil))) => Some(Con("Var", List(name)))
  case _ => None
}

def astVar(t: Term): Option[Term] = t match {
  case Con("astVar", List(Con("MkAST", List(v_var, lit, con)), s)) => Some(Con("App", List(v_var, s)))
  case _ => None
}

def astLit(t: Term): Option[Term] = t match {
  case Con("astLit", List(Con("MkAST", List(v_var, lit, con)), s)) => Some(Con("App", List(lit, s)))
  case _ => None
}

def astCon(t: Term): Option[Term] = t match {
  case Con("astCon", List(Con("MkAST", List(v_var, lit, con)), name, args)) => Some(Con("App", List(Con("App", List(con, name)), args)))
  case _ => None
}

def defaultAST(t: Term): Option[Term] = t match {
  case Con("defaultAST", Nil) => Some(Con("MkAST", List(Con("Var", Nil), Con("Lit", Nil), Con("Con", Nil))))
  case _ => None
}

def languageName(t: Term): Option[Term] = t match {
  case Con("languageName", List(Con("MkLanguage", List(name, pieces)))) => Some(name)
  case _ => None
}

def languagePieces(t: Term): Option[Term] = t match {
  case Con("languagePieces", List(Con("MkLanguage", List(name, pieces)))) => Some(pieces)
  case _ => None
}

def languageAllGrammar(t: Term): Option[Term] = t match {
  case Con("languageAllGrammar", List(Con("MkLanguage", List(name, pieces)))) => Some(Con("flatMap", List(Con("pieceGrammar", Nil), pieces)))
  case _ => None
}

def languageAllRules(t: Term): Option[Term] = t match {
  case Con("languageAllRules", List(Con("MkLanguage", List(name, pieces)))) => Some(Con("flatMap", List(Con("pieceRules", Nil), pieces)))
  case _ => None
}

def pieceName(t: Term): Option[Term] = t match {
  case Con("pieceName", List(Con("MkPiece", List(name, level, grammar, rules, typeRules)))) => Some(name)
  case _ => None
}

def pieceLevel(t: Term): Option[Term] = t match {
  case Con("pieceLevel", List(Con("MkPiece", List(name, level, grammar, rules, typeRules)))) => Some(level)
  case _ => None
}

def pieceGrammar(t: Term): Option[Term] = t match {
  case Con("pieceGrammar", List(Con("MkPiece", List(name, level, grammar, rules, typeRules)))) => Some(grammar)
  case _ => None
}

def pieceRules(t: Term): Option[Term] = t match {
  case Con("pieceRules", List(Con("MkPiece", List(name, level, grammar, rules, typeRules)))) => Some(rules)
  case _ => None
}

def pieceTypeRules(t: Term): Option[Term] = t match {
  case Con("pieceTypeRules", List(Con("MkPiece", List(name, level, grammar, rules, typeRules)))) => Some(typeRules)
  case _ => None
}

def ruleName(t: Term): Option[Term] = t match {
  case Con("ruleName", List(Con("MkRule", List(name, pattern, template)))) => Some(name)
  case _ => None
}

def rulePattern(t: Term): Option[Term] = t match {
  case Con("rulePattern", List(Con("MkRule", List(name, pattern, template)))) => Some(pattern)
  case _ => None
}

def ruleTemplate(t: Term): Option[Term] = t match {
  case Con("ruleTemplate", List(Con("MkRule", List(name, pattern, template)))) => Some(template)
  case _ => None
}

def sourceLocToString(t: Term): Option[Term] = t match {
  case Con("sourceLocToString", List(Con("MkSourceLoc", List(file, line, col, span)))) => Some(Con("concat", List(Con("concat", List(Con("concat", List(Con("concat", List(file, Lit("\":\""))), Con("toString", List(line)))), Lit("\":\""))), Con("toString", List(col)))))
  case _ => None
}

def sourceLocToStringUnknown(t: Term): Option[Term] = t match {
  case Con("sourceLocToString", List(Con("UnknownLoc", Nil))) => Some(Lit("\"<unknown>:0:0\""))
  case _ => None
}

def typeErrorSimple(t: Term): Option[Term] = t match {
  case Con("typeErrorSimple", List(msg, loc)) => Some(Con("MkTypeError", List(msg, loc, Con("SevError", Nil), Con("None", Nil), Con("None", Nil), Con("Nil", Nil))))
  case _ => None
}

def typeErrorMismatch(t: Term): Option[Term] = t match {
  case Con("typeErrorMismatch", List(expected, actual, loc)) => Some(Con("MkTypeError", List(Lit("\"type mismatch\""), loc, Con("SevError", Nil), Con("Some", List(expected)), Con("Some", List(actual)), Con("Nil", Nil))))
  case _ => None
}

def typeErrorUndefined(t: Term): Option[Term] = t match {
  case Con("typeErrorUndefined", List(name, loc)) => Some(Con("MkTypeError", List(Con("concat", List(Lit("\"undefined: \""), name)), loc, Con("SevError", Nil), Con("None", Nil), Con("None", Nil), Con("Nil", Nil))))
  case _ => None
}

def typeErrorToString(t: Term): Option[Term] = t match {
  case Con("typeErrorToString", List(Con("MkTypeError", List(msg, loc, sev, exp, act, ctx)))) => Some(Con("let", List(Var("sevStr"), Con("match", List(sev, Con("SevError", Nil), Lit("\"error\""), Con("SevWarning", Nil), Lit("\"warning\""), Con("SevInfo", Nil), Lit("\"info\""))), Con("let", List(Var("locStr"), Con("sourceLocToString", List(loc)), Con("let", List(Var("base"), Con("concat", List(Con("concat", List(Con("concat", List(Var("locStr"), Lit("\": \""))), Var("sevStr"))), Con("concat", List(Lit("\": \""), msg)))), Con("match", List(exp, Con("Some", List(Var("e"))), Con("match", List(act, Con("Some", List(Var("a"))), Con("concat", List(Con("concat", List(Con("concat", List(Var("base"), Lit("\"\\n  expected: \""))), Con("termToString", List(Var("e"))))), Con("concat", List(Lit("\"\\n  actual: \""), Con("termToString", List(Var("a"))))))), Con("None", Nil), Var("base"))), Con("None", Nil), Var("base"))))))))))
  case _ => None
}

def evalResultPure(t: Term): Option[Term] = t match {
  case Con("evalResultPure", List(a)) => Some(Con("EvalOk", List(a, Con("Nil", Nil))))
  case _ => None
}

def evalResultMapOk(t: Term): Option[Term] = t match {
  case Con("evalResultMap", List(f, Con("EvalOk", List(a, errs)))) => Some(Con("EvalOk", List(Con("app", List(a)), errs)))
  case _ => None
}

def evalResultMapFailed(t: Term): Option[Term] = t match {
  case Con("evalResultMap", List(f, Con("EvalFailed", List(errs)))) => Some(Con("EvalFailed", List(errs)))
  case _ => None
}

def evalResultBindOk(t: Term): Option[Term] = t match {
  case Con("evalResultBind", List(Con("EvalOk", List(a, errs)), f)) => Some(Con("match", List(Con("app", List(a)), Con("EvalOk", List(Var("b"), Var("errs2"))), Con("EvalOk", List(Var("b"), Con("append", List(errs, Var("errs2"))))), Con("EvalFailed", List(Var("errs2"))), Con("EvalFailed", List(Con("append", List(errs, Var("errs2"))))))))
  case _ => None
}

def evalResultBindFailed(t: Term): Option[Term] = t match {
  case Con("evalResultBind", List(Con("EvalFailed", List(errs)), f)) => Some(Con("EvalFailed", List(errs)))
  case _ => None
}

def evalResultAddError(t: Term): Option[Term] = t match {
  case Con("evalResultAddError", List(e, Con("EvalOk", List(a, errs)))) => Some(Con("EvalOk", List(a, Con("Cons", List(e, errs)))))
  case _ => None
}

def evalResultAddErrorFailed(t: Term): Option[Term] = t match {
  case Con("evalResultAddError", List(e, Con("EvalFailed", List(errs)))) => Some(Con("EvalFailed", List(Con("Cons", List(e, errs)))))
  case _ => None
}

def evalResultIsOk(t: Term): Option[Term] = t match {
  case Con("evalResultIsOk", List(Con("EvalOk", List(a, errs)))) => Some(Con("True", Nil))
  case _ => None
}

def evalResultIsOkFailed(t: Term): Option[Term] = t match {
  case Con("evalResultIsOk", List(Con("EvalFailed", List(errs)))) => Some(Con("False", Nil))
  case _ => None
}

def evalResultGetErrors(t: Term): Option[Term] = t match {
  case Con("evalResultGetErrors", List(Con("EvalOk", List(a, errs)))) => Some(errs)
  case _ => None
}

def evalResultGetErrorsFailed(t: Term): Option[Term] = t match {
  case Con("evalResultGetErrors", List(Con("EvalFailed", List(errs)))) => Some(errs)
  case _ => None
}

def contextExtend(t: Term): Option[Term] = t match {
  case Con("contextExtend", List(ctx, name, ty, loc)) => Some(Con("ContextCons", List(Con("MkBinding", List(name, ty, Con("None", Nil), loc)), ctx)))
  case _ => None
}

def contextExtendLet(t: Term): Option[Term] = t match {
  case Con("contextExtendLet", List(ctx, name, ty, v_val, loc)) => Some(Con("ContextCons", List(Con("MkBinding", List(name, ty, Con("Some", List(v_val)), loc)), ctx)))
  case _ => None
}

def contextLookupEmpty(t: Term): Option[Term] = t match {
  case Con("contextLookup", List(Con("EmptyContext", Nil), name)) => Some(Con("None", Nil))
  case _ => None
}

def contextLookupFound(t: Term): Option[Term] = t match {
  case Con("contextLookup", List(Con("ContextCons", List(Con("MkBinding", List(name, ty, v_val, loc)), rest)), name0)) if name0 == name => Some(Con("Some", List(Con("MkBinding", List(name, ty, v_val, loc)))))
  case _ => None
}

def contextLookupMiss(t: Term): Option[Term] = t match {
  case Con("contextLookup", List(Con("ContextCons", List(Con("MkBinding", List(n1, ty, v_val, loc)), rest)), n2)) => Some(Con("contextLookup", List(rest, n2)))
  case _ => None
}

def contextLookupType(t: Term): Option[Term] = t match {
  case Con("contextLookupType", List(ctx, name)) => Some(Con("match", List(Con("contextLookup", List(ctx, name)), Con("Some", List(Con("MkBinding", List(Var("n"), Var("ty"), Var("v"), Var("l"))))), Con("Some", List(Var("ty"))), Con("None", Nil), Con("None", Nil))))
  case _ => None
}

def contextNames(t: Term): Option[Term] = t match {
  case Con("contextNames", List(Con("EmptyContext", Nil))) => Some(Con("Nil", Nil))
  case _ => None
}

def contextNamesCons(t: Term): Option[Term] = t match {
  case Con("contextNames", List(Con("ContextCons", List(Con("MkBinding", List(name, ty, v_val, loc)), rest)))) => Some(Con("Cons", List(name, Con("contextNames", List(rest)))))
  case _ => None
}

def varContextExtend(t: Term): Option[Term] = t match {
  case Con("varContextExtend", List(ctx, name)) => Some(Con("VarContextCons", List(name, ctx)))
  case _ => None
}

def varContextContainsEmpty(t: Term): Option[Term] = t match {
  case Con("varContextContains", List(Con("EmptyVarContext", Nil), name)) => Some(Con("False", Nil))
  case _ => None
}

def varContextContainsFound(t: Term): Option[Term] = t match {
  case Con("varContextContains", List(Con("VarContextCons", List(name, rest)), name0)) if name0 == name => Some(Con("True", Nil))
  case _ => None
}

def varContextContainsMiss(t: Term): Option[Term] = t match {
  case Con("varContextContains", List(Con("VarContextCons", List(n1, rest)), n2)) => Some(Con("varContextContains", List(rest, n2)))
  case _ => None
}

def evalEnvEmpty(t: Term): Option[Term] = t match {
  case Con("evalEnvEmpty", Nil) => Some(Con("MkEvalEnv", List(Con("EmptyAttrEnv", Nil), Con("EmptyContext", Nil), Con("EmptyVarContext", Nil), Con("Nil", Nil), Con("UnknownLoc", Nil))))
  case _ => None
}

def evalEnvWithCtx(t: Term): Option[Term] = t match {
  case Con("evalEnvWithCtx", List(Con("MkEvalEnv", List(attrs, oldCtx, vars, errs, loc)), ctx)) => Some(Con("MkEvalEnv", List(attrs, ctx, vars, errs, loc)))
  case _ => None
}

def evalEnvWithLoc(t: Term): Option[Term] = t match {
  case Con("evalEnvWithLoc", List(Con("MkEvalEnv", List(attrs, ctx, vars, errs, oldLoc)), loc)) => Some(Con("MkEvalEnv", List(attrs, ctx, vars, errs, loc)))
  case _ => None
}

def evalEnvAddBinding(t: Term): Option[Term] = t match {
  case Con("evalEnvAddBinding", List(Con("MkEvalEnv", List(attrs, ctx, vars, errs, loc)), name, ty)) => Some(Con("MkEvalEnv", List(attrs, Con("contextExtend", List(ctx, name, ty, loc)), vars, errs, loc)))
  case _ => None
}

def evalEnvAddVar(t: Term): Option[Term] = t match {
  case Con("evalEnvAddVar", List(Con("MkEvalEnv", List(attrs, ctx, vars, errs, loc)), name)) => Some(Con("MkEvalEnv", List(attrs, ctx, Con("varContextExtend", List(vars, name)), errs, loc)))
  case _ => None
}

def evalEnvAddError(t: Term): Option[Term] = t match {
  case Con("evalEnvAddError", List(Con("MkEvalEnv", List(attrs, ctx, vars, errs, loc)), e)) => Some(Con("MkEvalEnv", List(attrs, ctx, vars, Con("Cons", List(e, errs)), loc)))
  case _ => None
}

def evalEnvAddTypeError(t: Term): Option[Term] = t match {
  case Con("evalEnvAddTypeError", List(Con("MkEvalEnv", List(attrs, ctx, vars, errs, loc)), msg)) => Some(Con("MkEvalEnv", List(attrs, ctx, vars, Con("Cons", List(Con("typeErrorSimple", List(msg, loc)), errs)), loc)))
  case _ => None
}

def evalEnvAddMismatch(t: Term): Option[Term] = t match {
  case Con("evalEnvAddMismatch", List(Con("MkEvalEnv", List(attrs, ctx, vars, errs, loc)), expected, actual)) => Some(Con("MkEvalEnv", List(attrs, ctx, vars, Con("Cons", List(Con("typeErrorMismatch", List(expected, actual, loc)), errs)), loc)))
  case _ => None
}

def evalEnvSetAttr(t: Term): Option[Term] = t match {
  case Con("evalEnvSetAttr", List(Con("MkEvalEnv", List(attrs, ctx, vars, errs, loc)), path, name, v_val)) => Some(Con("MkEvalEnv", List(Con("attrEnvInsert", List(attrs, path, name, v_val)), ctx, vars, errs, loc)))
  case _ => None
}

def evalEnvGetAttr(t: Term): Option[Term] = t match {
  case Con("evalEnvGetAttr", List(Con("MkEvalEnv", List(attrs, ctx, vars, errs, loc)), path, name)) => Some(Con("attrEnvLookup", List(attrs, path, name)))
  case _ => None
}

def evalEnvHasErrors(t: Term): Option[Term] = t match {
  case Con("evalEnvHasErrors", List(Con("MkEvalEnv", List(attrs, ctx, vars, errs, loc)))) => Some(Con("not", List(Con("null", List(errs)))))
  case _ => None
}

def freeVarsVar(t: Term): Option[Term] = t match {
  case Con("freeVars", List(Con("Var", List(n)))) => Some(Con("Cons", List(n, Con("Nil", Nil))))
  case _ => None
}

def freeVarsLit(t: Term): Option[Term] = t match {
  case Con("freeVars", List(Con("Lit", List(s)))) => Some(Con("Nil", Nil))
  case _ => None
}

def freeVarsLam(t: Term): Option[Term] = t match {
  case Con("freeVars", List(Con("Con", List(Lit("\"lam\""), Con("Cons", List(Con("Var", List(x)), Con("Cons", List(ty, Con("Cons", List(body, Con("Nil", Nil))))))))))) => Some(Con("append", List(Con("freeVars", List(ty)), Con("filter", List(Con("binder", List(Lit("v"), Con("not", List(Con("eq", List(Var("v"), x)))))), Con("freeVars", List(body)))))))
  case _ => None
}

def freeVarsPi(t: Term): Option[Term] = t match {
  case Con("freeVars", List(Con("Con", List(Lit("\"Pi\""), Con("Cons", List(Con("Var", List(x)), Con("Cons", List(dom, Con("Cons", List(cod, Con("Nil", Nil))))))))))) => Some(Con("append", List(Con("freeVars", List(dom)), Con("filter", List(Con("binder", List(Lit("v"), Con("not", List(Con("eq", List(Var("v"), x)))))), Con("freeVars", List(cod)))))))
  case _ => None
}

def freeVarsCon(t: Term): Option[Term] = t match {
  case Con("freeVars", List(Con("Con", List(c, args)))) => Some(Con("flatMap", List(Con("freeVars", Nil), args)))
  case _ => None
}

def freshName(t: Term): Option[Term] = t match {
  case Con("freshName", List(base, avoid)) => Some(Con("freshNameHelper", List(base, avoid, Lit("0"))))
  case _ => None
}

def freshNameHelper(t: Term): Option[Term] = t match {
  case Con("freshNameHelper", List(base, avoid, i)) => Some(Con("let", List(Var("candidate"), Con("if", List(Con("eq", List(i, Lit("0"))), base, Con("concat", List(base, Con("toString", List(i)))))), Con("if", List(Con("contains", List(avoid, Var("candidate"))), Con("freshNameHelper", List(base, avoid, Con("add", List(i, Lit("1"))))), Var("candidate"))))))
  case _ => None
}

def substAvoidVar(t: Term): Option[Term] = t match {
  case Con("substAvoid", List(name, repl, fv, Con("Var", List(n)))) => Some(Con("if", List(Con("eq", List(n, name)), repl, Con("Var", List(n)))))
  case _ => None
}

def substAvoidLit(t: Term): Option[Term] = t match {
  case Con("substAvoid", List(name, repl, fv, Con("Lit", List(s)))) => Some(Con("Lit", List(s)))
  case _ => None
}

def substAvoidLam(t: Term): Option[Term] = t match {
  case Con("substAvoid", List(name, repl, fv, Con("Con", List(Lit("\"lam\""), Con("Cons", List(Con("Var", List(x)), Con("Cons", List(ty, Con("Cons", List(body, Con("Nil", Nil))))))))))) => Some(Con("if", List(Con("eq", List(x, name)), Con("Con", List(Lit("\"lam\""), Con("Cons", List(Con("Var", List(x)), Con("Cons", List(Con("substAvoid", List(name, repl, fv, ty)), Con("Cons", List(body, Con("Nil", Nil))))))))), Con("if", List(Con("contains", List(fv, x)), Con("let", List(Var("x2"), Con("freshName", List(x, fv)), Con("let", List(Var("body2"), Con("subst", List(x, Con("Var", List(Var("x2"))), body)), Con("Con", List(Lit("\"lam\""), Con("Cons", List(Con("Var", List(Var("x2"))), Con("Cons", List(Con("substAvoid", List(name, repl, fv, ty)), Con("Cons", List(Con("substAvoid", List(name, repl, Con("Cons", List(Var("x2"), fv)), Var("body2"))), Con("Nil", Nil))))))))))))), Con("Con", List(Lit("\"lam\""), Con("Cons", List(Con("Var", List(x)), Con("Cons", List(Con("substAvoid", List(name, repl, fv, ty)), Con("Cons", List(Con("substAvoid", List(name, repl, fv, body)), Con("Nil", Nil))))))))))))))
  case _ => None
}

def substAvoidPi(t: Term): Option[Term] = t match {
  case Con("substAvoid", List(name, repl, fv, Con("Con", List(Lit("\"Pi\""), Con("Cons", List(Con("Var", List(x)), Con("Cons", List(dom, Con("Cons", List(cod, Con("Nil", Nil))))))))))) => Some(Con("if", List(Con("eq", List(x, name)), Con("Con", List(Lit("\"Pi\""), Con("Cons", List(Con("Var", List(x)), Con("Cons", List(Con("substAvoid", List(name, repl, fv, dom)), Con("Cons", List(cod, Con("Nil", Nil))))))))), Con("if", List(Con("contains", List(fv, x)), Con("let", List(Var("x2"), Con("freshName", List(x, fv)), Con("let", List(Var("cod2"), Con("subst", List(x, Con("Var", List(Var("x2"))), cod)), Con("Con", List(Lit("\"Pi\""), Con("Cons", List(Con("Var", List(Var("x2"))), Con("Cons", List(Con("substAvoid", List(name, repl, fv, dom)), Con("Cons", List(Con("substAvoid", List(name, repl, Con("Cons", List(Var("x2"), fv)), Var("cod2"))), Con("Nil", Nil))))))))))))), Con("Con", List(Lit("\"Pi\""), Con("Cons", List(Con("Var", List(x)), Con("Cons", List(Con("substAvoid", List(name, repl, fv, dom)), Con("Cons", List(Con("substAvoid", List(name, repl, fv, cod)), Con("Nil", Nil))))))))))))))
  case _ => None
}

def substAvoidCon(t: Term): Option[Term] = t match {
  case Con("substAvoid", List(name, repl, fv, Con("Con", List(c, args)))) => Some(Con("Con", List(c, Con("map", List(Con("binder", List(Lit("a"), Con("substAvoid", List(name, repl, fv, Var("a"))))), args)))))
  case _ => None
}

def attrRefSelf(t: Term): Option[Term] = t match {
  case Con("attrRefSelf", List(name)) => Some(Con("MkAttrRef", List(Con("Empty", Nil), name)))
  case _ => None
}

def attrRefChild(t: Term): Option[Term] = t match {
  case Con("attrRefChild", List(child, name)) => Some(Con("MkAttrRef", List(Con("PathCon", List(child, Con("Empty", Nil))), name)))
  case _ => None
}

def emptyAttrDef(t: Term): Option[Term] = t match {
  case Con("emptyAttrDef", List(name, flow)) => Some(Con("MkAttrDef", List(name, flow, Con("None", Nil), Con("Nil", Nil))))
  case _ => None
}

def addAttrRule(t: Term): Option[Term] = t match {
  case Con("addAttrRule", List(Con("MkAttrDef", List(name, flow, ty, rules)), rule)) => Some(Con("MkAttrDef", List(name, flow, ty, Con("append", List(rules, Con("Cons", List(rule, Con("Nil", Nil))))))))
  case _ => None
}

def attrEnvLookupEmpty(t: Term): Option[Term] = t match {
  case Con("attrEnvLookup", List(Con("Empty", Nil), path, name)) => Some(Con("None", Nil))
  case _ => None
}

def attrEnvLookupFound(t: Term): Option[Term] = t match {
  case Con("attrEnvLookup", List(Con("AttrEnvCons", List(path, name, v_val, rest)), path0, name1)) if name1 == name && path0 == path => Some(Con("Some", List(v_val)))
  case _ => None
}

def attrEnvLookupMiss(t: Term): Option[Term] = t match {
  case Con("attrEnvLookup", List(Con("AttrEnvCons", List(p1, n1, v_val, rest)), p2, n2)) => Some(Con("attrEnvLookup", List(rest, p2, n2)))
  case _ => None
}

def attrEnvInsert(t: Term): Option[Term] = t match {
  case Con("attrEnvInsert", List(env, path, name, v_val)) => Some(Con("AttrEnvCons", List(path, name, v_val, env)))
  case _ => None
}

def attrEnvGetLocal(t: Term): Option[Term] = t match {
  case Con("attrEnvGetLocal", List(env, name)) => Some(Con("attrEnvLookup", List(env, Con("Empty", Nil), name)))
  case _ => None
}

def attrEnvGetChild(t: Term): Option[Term] = t match {
  case Con("attrEnvGetChild", List(env, child, name)) => Some(Con("attrEnvLookup", List(env, Con("PathCon", List(child, Con("Empty", Nil))), name)))
  case _ => None
}

def attrEnvMergeEmpty(t: Term): Option[Term] = t match {
  case Con("attrEnvMerge", List(env1, Con("EmptyAttrEnv", Nil))) => Some(env1)
  case _ => None
}

def attrEnvMergeCons(t: Term): Option[Term] = t match {
  case Con("attrEnvMerge", List(env1, Con("AttrEnvCons", List(path, name, v_val, rest)))) => Some(Con("attrEnvMerge", List(Con("AttrEnvCons", List(path, name, v_val, env1)), rest)))
  case _ => None
}

def evalAttrExprVar(t: Term): Option[Term] = t match {
  case Con("evalAttrExpr", List(Con("Var", List(name)), env)) => Some(Con("if", List(Con("startsWith", List(name, Lit("\"$\""))), Con("match", List(Con("attrEnvLookup", List(env, Con("Empty", Nil), Con("drop", List(Lit("1"), name)))), Con("Some", List(Var("v"))), Var("v"), Con("None", Nil), Con("Con", List(Lit("\"error\""), Con("Cons", List(Con("Lit", List(Con("concat", List(Lit("\"undefined: \""), name)))), Con("Nil", Nil))))))), Con("Var", List(name)))))
  case _ => None
}

def evalAttrExprCon(t: Term): Option[Term] = t match {
  case Con("evalAttrExpr", List(Con("Con", List(c, args)), env)) => Some(Con("Con", List(c, Con("map", List(Con("binder", List(Lit("x"), Con("evalAttrExpr", List(Var("x"), env)))), args)))))
  case _ => None
}

def evalAttrExprLit(t: Term): Option[Term] = t match {
  case Con("evalAttrExpr", List(Con("Lit", List(s)), env)) => Some(Con("Lit", List(s)))
  case _ => None
}

def findRuleEmpty(t: Term): Option[Term] = t match {
  case Con("findRule", List(prod, target, Con("Nil", Nil))) => Some(Con("None", Nil))
  case _ => None
}

def findRuleFound(t: Term): Option[Term] = t match {
  case Con("findRule", List(prod, target, Con("Cons", List(Con("MkAttrRule", List(prod0, target1, expr)), rest)))) if target1 == target && prod0 == prod => Some(Con("Some", List(Con("MkAttrRule", List(prod, target, expr)))))
  case _ => None
}

def findRuleMiss(t: Term): Option[Term] = t match {
  case Con("findRule", List(prod, target, Con("Cons", List(Con("MkAttrRule", List(p2, t2, e)), rest)))) => Some(Con("findRule", List(prod, target, rest)))
  case _ => None
}

def evalSynVar(t: Term): Option[Term] = t match {
  case Con("evalSyn", List(v_def, Con("Var", List(x)))) => Some(Con("EmptyAttrEnv", Nil))
  case _ => None
}

def evalSynLit(t: Term): Option[Term] = t match {
  case Con("evalSyn", List(v_def, Con("Lit", List(s)))) => Some(Con("EmptyAttrEnv", Nil))
  case _ => None
}

def evalSynCon(t: Term): Option[Term] = t match {
  case Con("evalSyn", List(Con("MkAttrDef", List(attrName, flow, ty, rules)), Con("Con", List(prod, children)))) => Some(Con("evalSynConHelper", List(attrName, flow, ty, rules, prod, children, Lit("0"))))
  case _ => None
}

def evalSynConHelper(t: Term): Option[Term] = t match {
  case Con("evalSynConHelper", List(attrName, flow, ty, rules, prod, children, idx)) => Some(Con("let", List(Var("childEnvs"), Con("mapWithIndex", List(Con("i", List(Con("binder", List(Lit("child"), Con("prefixEnv", List(Con("concat", List(Lit("\"child\""), Con("toString", List(Var("i"))))), Con("evalSyn", List(Con("MkAttrDef", List(attrName, flow, ty, rules)), Var("child"))))))))), children)), Con("let", List(Var("env"), Con("foldl", List(Con("attrEnvMerge", Nil), Con("EmptyAttrEnv", Nil), Var("childEnvs"))), Con("match", List(Con("findRule", List(prod, Con("Empty", Nil), rules)), Con("Some", List(Con("MkAttrRule", List(Var("p"), Var("t"), Var("expr"))))), Con("attrEnvInsert", List(Var("env"), Con("Empty", Nil), attrName, Con("evalAttrExpr", List(Var("expr"), Var("env"))))), Con("None", Nil), Var("env"))))))))
  case _ => None
}

def evalInhVar(t: Term): Option[Term] = t match {
  case Con("evalInh", List(v_def, Con("Var", List(x)), parentEnv)) => Some(parentEnv)
  case _ => None
}

def evalInhLit(t: Term): Option[Term] = t match {
  case Con("evalInh", List(v_def, Con("Lit", List(s)), parentEnv)) => Some(parentEnv)
  case _ => None
}

def evalInhCon(t: Term): Option[Term] = t match {
  case Con("evalInh", List(Con("MkAttrDef", List(attrName, flow, ty, rules)), Con("Con", List(prod, children)), parentEnv)) => Some(Con("evalInhConHelper", List(attrName, flow, ty, rules, prod, children, parentEnv, Lit("0"))))
  case _ => None
}

def evalAttrs(t: Term): Option[Term] = t match {
  case Con("evalAttrs", List(defs, term)) => Some(Con("let", List(Var("synDefs"), Con("filter", List(Con("binder", List(Lit("d"), Con("eq", List(Con("attrDefFlow", List(Var("d"))), Con("Syn", Nil))))), defs)), Con("let", List(Var("inhDefs"), Con("filter", List(Con("binder", List(Lit("d"), Con("eq", List(Con("attrDefFlow", List(Var("d"))), Con("Inh", Nil))))), defs)), Con("let", List(Var("inhEnv"), Con("foldl", List(Con("env", List(Con("binder", List(Lit("def"), Con("evalInh", List(Var("def"), term, Var("env"))))))), Con("EmptyAttrEnv", Nil), Var("inhDefs"))), Con("foldl", List(Con("env", List(Con("binder", List(Lit("def"), Con("attrEnvMerge", List(Var("env"), Con("evalSyn", List(Var("def"), term)))))))), Var("inhEnv"), Var("synDefs"))))))))))
  case _ => None
}

def cataTermVar(t: Term): Option[Term] = t match {
  case Con("cataTerm", List(alg, Con("Var", List(x)))) => Some(Con("app", List(x, Con("Nil", Nil))))
  case _ => None
}

def cataTermLit(t: Term): Option[Term] = t match {
  case Con("cataTerm", List(alg, Con("Lit", List(s)))) => Some(Con("app", List(s, Con("Nil", Nil))))
  case _ => None
}

def cataTermCon(t: Term): Option[Term] = t match {
  case Con("cataTerm", List(alg, Con("Con", List(c, args)))) => Some(Con("app", List(c, Con("map", List(Con("binder", List(Lit("a"), Con("cataTerm", List(alg, Var("a"))))), args)))))
  case _ => None
}

def paraTermVar(t: Term): Option[Term] = t match {
  case Con("paraTerm", List(coalg, Con("Var", List(x)))) => Some(Con("app", List(x, Con("Nil", Nil))))
  case _ => None
}

def paraTermLit(t: Term): Option[Term] = t match {
  case Con("paraTerm", List(coalg, Con("Lit", List(s)))) => Some(Con("app", List(s, Con("Nil", Nil))))
  case _ => None
}

def paraTermCon(t: Term): Option[Term] = t match {
  case Con("paraTerm", List(coalg, Con("Con", List(c, args)))) => Some(Con("app", List(c, Con("map", List(Con("binder", List(Lit("a"), Con("Pair", List(Var("a"), Con("paraTerm", List(coalg, Var("a"))))))), args)))))
  case _ => None
}

def attrLangSynAttrs(t: Term): Option[Term] = t match {
  case Con("attrLangSynAttrs", List(Con("MkAttrLanguage", List(name, pieces, attrs)))) => Some(Con("filter", List(Con("binder", List(Lit("d"), Con("eq", List(Con("attrDefFlow", List(Var("d"))), Con("Syn", Nil))))), attrs)))
  case _ => None
}

def attrLangInhAttrs(t: Term): Option[Term] = t match {
  case Con("attrLangInhAttrs", List(Con("MkAttrLanguage", List(name, pieces, attrs)))) => Some(Con("filter", List(Con("binder", List(Lit("d"), Con("eq", List(Con("attrDefFlow", List(Var("d"))), Con("Inh", Nil))))), attrs)))
  case _ => None
}

def attrLangEval(t: Term): Option[Term] = t match {
  case Con("attrLangEval", List(Con("MkAttrLanguage", List(name, pieces, attrs)), term)) => Some(Con("evalAttrs", List(attrs, term)))
  case _ => None
}

def attrLangPushout(t: Term): Option[Term] = t match {
  case Con("attrLangPushout", List(Con("MkAttrLanguage", List(n1, p1, a1)), Con("MkAttrLanguage", List(n2, p2, a2)))) => Some(Con("MkAttrLanguage", List(Con("concat", List(Con("concat", List(n1, Lit("\"_\""))), n2)), Con("append", List(p1, p2)), Con("append", List(a1, a2)))))
  case _ => None
}

def tokEq(t: Term): Option[Term] = t match {
  case Con("tokEq", List(Con("TokIdent", List(a)), Con("TokIdent", List(b)))) => Some(Con("strEq", List(a, b)))
  case _ => None
}

def tokEqString(t: Term): Option[Term] = t match {
  case Con("tokEq", List(Con("TokString", List(a)), Con("TokString", List(b)))) => Some(Con("strEq", List(a, b)))
  case _ => None
}

def tokEqSym(t: Term): Option[Term] = t match {
  case Con("tokEq", List(Con("TokSym", List(a)), Con("TokSym", List(b)))) => Some(Con("strEq", List(a, b)))
  case _ => None
}

def tokEqMismatch(t: Term): Option[Term] = t match {
  case Con("tokEq", List(a, b)) => Some(Con("false", Nil))
  case _ => None
}

def stateTokens(t: Term): Option[Term] = t match {
  case Con("stateTokens", List(Con("MkState", List(toks, pos)))) => Some(toks)
  case _ => None
}

def statePos(t: Term): Option[Term] = t match {
  case Con("statePos", List(Con("MkState", List(toks, pos)))) => Some(pos)
  case _ => None
}

def stateAdvance(t: Term): Option[Term] = t match {
  case Con("stateAdvance", List(Con("MkState", List(Con("Cons", List(v_t, ts)), pos)))) => Some(Con("MkState", List(ts, Con("add", List(pos, Lit("1"))))))
  case _ => None
}

def parseLit(t: Term): Option[Term] = t match {
  case Con("parseLit", List(s, Con("MkState", List(Con("Cons", List(Con("TokSym", List(s0)), rest)), pos)))) if s0 == s => Some(Con("ParseOk", List(Con("Lit", List(s)), Con("MkState", List(rest, Con("add", List(pos, Lit("1"))))))))
  case _ => None
}

def parseLitFail(t: Term): Option[Term] = t match {
  case Con("parseLit", List(s, Con("MkState", List(Con("Cons", List(v_t, rest)), pos)))) => Some(Con("ParseFail", List(Con("concat", List(Lit("\"expected \""), s)), Con("MkState", List(Con("Cons", List(v_t, rest)), pos)))))
  case _ => None
}

def parseIdent(t: Term): Option[Term] = t match {
  case Con("parseIdent", List(Con("MkState", List(Con("Cons", List(Con("TokIdent", List(name)), rest)), pos)))) => Some(Con("ParseOk", List(Con("Var", List(name)), Con("MkState", List(rest, Con("add", List(pos, Lit("1"))))))))
  case _ => None
}

def parseIdentFail(t: Term): Option[Term] = t match {
  case Con("parseIdent", List(Con("MkState", List(Con("Cons", List(v_t, rest)), pos)))) => Some(Con("ParseFail", List(Lit("\"expected identifier\""), Con("MkState", List(Con("Cons", List(v_t, rest)), pos)))))
  case _ => None
}

def parseSeq(t: Term): Option[Term] = t match {
  case Con("parseSeq", List(p1, p2, state)) => Some(Con("case", List(Con("parse", List(p1, state)), Con("ParseOk", List(Var("t1"), Var("s1"))), Con("case", List(Con("parse", List(p2, Var("s1"))), Con("ParseOk", List(Var("t2"), Var("s2"))), Con("ParseOk", List(Con("Con", List(Lit("\"seq\""), Con("Cons", List(Var("t1"), Con("Cons", List(Var("t2"), Con("Nil", Nil))))))), Var("s2"))), Con("ParseFail", List(Var("msg"), Var("s"))), Con("ParseFail", List(Var("msg"), Var("s"))))), Con("ParseFail", List(Var("msg"), Var("s"))), Con("ParseFail", List(Var("msg"), Var("s"))))))
  case _ => None
}

def parseAlt(t: Term): Option[Term] = t match {
  case Con("parseAlt", List(p1, p2, state)) => Some(Con("case", List(Con("parse", List(p1, state)), Con("ParseOk", List(Var("t"), Var("s"))), Con("ParseOk", List(Var("t"), Var("s"))), Con("ParseFail", List(Var("msg1"), Var("s1"))), Con("case", List(Con("parse", List(p2, state)), Con("ParseOk", List(Var("t"), Var("s"))), Con("ParseOk", List(Var("t"), Var("s"))), Con("ParseFail", List(Var("msg2"), Var("s2"))), Con("ParseFail", List(Con("concat", List(Var("msg1"), Con("concat", List(Lit("\" or \""), Var("msg2"))))), state)))))))
  case _ => None
}

def parseStar(t: Term): Option[Term] = t match {
  case Con("parseStar", List(p, state)) => Some(Con("case", List(Con("parse", List(p, state)), Con("ParseOk", List(Var("t"), Var("s"))), Con("case", List(Con("parseStar", List(p, Var("s"))), Con("ParseOk", List(Con("Con", List(Lit("\"list\""), Var("ts"))), Var("s2"))), Con("ParseOk", List(Con("Con", List(Lit("\"list\""), Con("Cons", List(Var("t"), Var("ts"))))), Var("s2"))), Con("ParseFail", List(Var("msg"), Var("s2"))), Con("ParseOk", List(Con("Con", List(Lit("\"list\""), Con("Cons", List(Var("t"), Con("Nil", Nil))))), Var("s"))))), Con("ParseFail", List(Var("msg"), Var("s"))), Con("ParseOk", List(Con("Con", List(Lit("\"list\""), Con("Nil", Nil))), state)))))
  case _ => None
}

def parseOpt(t: Term): Option[Term] = t match {
  case Con("parseOpt", List(p, state)) => Some(Con("case", List(Con("parse", List(p, state)), Con("ParseOk", List(Var("t"), Var("s"))), Con("ParseOk", List(Con("Con", List(Lit("\"some\""), Con("Cons", List(Var("t"), Con("Nil", Nil))))), Var("s"))), Con("ParseFail", List(Var("msg"), Var("s"))), Con("ParseOk", List(Con("Con", List(Lit("\"none\""), Con("Nil", Nil))), state)))))
  case _ => None
}

def parseCon(t: Term): Option[Term] = t match {
  case Con("parseCon", List(name, p, state)) => Some(Con("case", List(Con("parse", List(p, state)), Con("ParseOk", List(Var("t"), Var("s"))), Con("ParseOk", List(Con("Con", List(name, Con("Cons", List(Var("t"), Con("Nil", Nil))))), Var("s"))), Con("ParseFail", List(Var("msg"), Var("s"))), Con("ParseFail", List(Var("msg"), Var("s"))))))
  case _ => None
}

def parseGEmpty(t: Term): Option[Term] = t match {
  case Con("parse", List(Con("GEmpty", Nil), state)) => Some(Con("ParseOk", List(Con("Con", List(Lit("\"unit\""), Con("Nil", Nil))), state)))
  case _ => None
}

def parseGLit(t: Term): Option[Term] = t match {
  case Con("parse", List(Con("GLit", List(s)), state)) => Some(Con("parseLit", List(s, state)))
  case _ => None
}

def parseGRef(t: Term): Option[Term] = t match {
  case Con("parse", List(Con("GRef", List(Lit("\"ident\""))), state)) => Some(Con("parseIdent", List(state)))
  case _ => None
}

def parseGSeq(t: Term): Option[Term] = t match {
  case Con("parse", List(Con("GSeq", List(g1, g2)), state)) => Some(Con("parseSeq", List(g1, g2, state)))
  case _ => None
}

def parseGAlt(t: Term): Option[Term] = t match {
  case Con("parse", List(Con("GAlt", List(g1, g2)), state)) => Some(Con("parseAlt", List(g1, g2, state)))
  case _ => None
}

def parseGStar(t: Term): Option[Term] = t match {
  case Con("parse", List(Con("GStar", List(g)), state)) => Some(Con("parseStar", List(g, state)))
  case _ => None
}

def parseGOpt(t: Term): Option[Term] = t match {
  case Con("parse", List(Con("GOpt", List(g)), state)) => Some(Con("parseOpt", List(g, state)))
  case _ => None
}

def parseGCon(t: Term): Option[Term] = t match {
  case Con("parse", List(Con("GCon", List(name, g)), state)) => Some(Con("parseCon", List(name, g, state)))
  case _ => None
}

def printLit(t: Term): Option[Term] = t match {
  case Con("print", List(Con("GLit", List(s)), Con("Lit", List(s0)))) if s0 == s => Some(Con("PrintOk", List(Con("Cons", List(Con("TokSym", List(s)), Con("Nil", Nil))))))
  case _ => None
}

def printIdent(t: Term): Option[Term] = t match {
  case Con("print", List(Con("GRef", List(Lit("\"ident\""))), Con("Var", List(name)))) => Some(Con("PrintOk", List(Con("Cons", List(Con("TokIdent", List(name)), Con("Nil", Nil))))))
  case _ => None
}

def printSeq(t: Term): Option[Term] = t match {
  case Con("print", List(Con("GSeq", List(g1, g2)), Con("Con", List(Lit("\"seq\""), Con("Cons", List(t1, Con("Cons", List(t2, Con("Nil", Nil))))))))) => Some(Con("case", List(Con("print", List(g1, t1)), Con("PrintOk", List(Var("toks1"))), Con("case", List(Con("print", List(g2, t2)), Con("PrintOk", List(Var("toks2"))), Con("PrintOk", List(Con("append", List(Var("toks1"), Var("toks2"))))), Con("PrintFail", List(Var("msg"))), Con("PrintFail", List(Var("msg"))))), Con("PrintFail", List(Var("msg"))), Con("PrintFail", List(Var("msg"))))))
  case _ => None
}

def printCon(t: Term): Option[Term] = t match {
  case Con("print", List(Con("GCon", List(name, g)), Con("Con", List(name0, Con("Cons", List(v_t, Con("Nil", Nil))))))) if name0 == name => Some(Con("print", List(g, v_t)))
  case _ => None
}

def grammarIso(t: Term): Option[Term] = t match {
  case Con("grammarIso", List(g)) => Some(Con("MkIso", List(Con("Lam", List(Con("binder", List(Lit("input"), Con("case", List(Con("parse", List(g, Con("tokenize", List(Con("input", Nil))))), Con("ParseOk", List(Var("t"), Var("s"))), Con("Some", List(Var("t"))), Con("ParseFail", List(Var("msg"), Var("s"))), Con("None", Nil))))))), Con("Lam", List(Con("binder", List(Lit("term"), Con("case", List(Con("print", List(g, Var("term"))), Con("PrintOk", List(Var("toks"))), Con("Some", List(Con("detokenize", List(Var("toks"))))), Con("PrintFail", List(Var("msg"))), Con("None", Nil))))))))))
  case _ => None
}

def matchVarMeta(t: Term): Option[Term] = t match {
  case Con("match", List(Con("Var", List(name)), v_t)) => Some(Con("Some", List(Con("Bind", List(name, v_t, Con("Empty", Nil))))))
  case _ => None
}

def matchListNil(t: Term): Option[Term] = t match {
  case Con("matchList", List(Con("Nil", Nil), Con("Nil", Nil))) => Some(Con("Some", List(Con("Empty", Nil))))
  case _ => None
}

def matchListCons(t: Term): Option[Term] = t match {
  case Con("matchList", List(Con("Cons", List(p, ps)), Con("Cons", List(v_t, ts)))) => Some(Con("merge", List(Con("match", List(p, v_t)), Con("matchList", List(ps, ts)))))
  case _ => None
}

def mergeEnvs(t: Term): Option[Term] = t match {
  case Con("merge", List(Con("Some", List(e1)), Con("Some", List(e2)))) => Some(Con("Some", List(Con("append", List(e1, e2)))))
  case _ => None
}

def substVarHit(t: Term): Option[Term] = t match {
  case Con("subst", List(Con("Var", List(name)), Con("Bind", List(name0, v_val, rest)))) if name0 == name => Some(v_val)
  case _ => None
}

def substVarMiss(t: Term): Option[Term] = t match {
  case Con("subst", List(Con("Var", List(name)), Con("Bind", List(other, v_val, rest)))) => Some(Con("subst", List(Con("Var", List(name)), rest)))
  case _ => None
}

def substVarEmpty(t: Term): Option[Term] = t match {
  case Con("subst", List(Con("Var", List(name)), Con("Empty", Nil))) => Some(Con("Var", List(name)))
  case _ => None
}

def applyRule(t: Term): Option[Term] = t match {
  case Con("apply", List(Con("MkRule", List(name, pat, tmpl)), v_t)) => Some(Con("case", List(Con("match", List(pat, v_t)), Con("Some", List(Var("env"))), Con("subst", List(tmpl, Var("env"))), Con("None", Nil), Con("None", Nil))))
  case _ => None
}

def tryRulesFirst(t: Term): Option[Term] = t match {
  case Con("tryRules", List(Con("Cons", List(r, rs)), v_t)) => Some(Con("case", List(Con("apply", List(r, v_t)), Con("Some", List(Var("result"))), Con("Some", List(Var("result"))), Con("None", Nil), Con("tryRules", List(rs, v_t)))))
  case _ => None
}

def tryRulesEmpty(t: Term): Option[Term] = t match {
  case Con("tryRules", List(Con("Nil", Nil), v_t)) => Some(Con("None", Nil))
  case _ => None
}

def normalizeStep(t: Term): Option[Term] = t match {
  case Con("normalize", List(rules, v_t)) => Some(Con("let", List(Var("t'"), Con("normalizeOnce", List(rules, v_t)), Con("if", List(Con("eq", List(v_t, Var("t'"))), v_t, Con("normalize", List(rules, Var("t'"))))))))
  case _ => None
}

def normalizeOnceTop(t: Term): Option[Term] = t match {
  case Con("normalizeOnce", List(rules, v_t)) => Some(Con("case", List(Con("tryRules", List(rules, v_t)), Con("Some", List(Var("result"))), Var("result"), Con("None", Nil), Con("normalizeChildren", List(rules, v_t)))))
  case _ => None
}

def normalizeChildrenVar(t: Term): Option[Term] = t match {
  case Con("normalizeChildren", List(rules, Con("Var", List(x)))) => Some(Con("Var", List(x)))
  case _ => None
}

def normalizeChildrenLit(t: Term): Option[Term] = t match {
  case Con("normalizeChildren", List(rules, Con("Lit", List(s)))) => Some(Con("Lit", List(s)))
  case _ => None
}

def normalizeChildrenCon(t: Term): Option[Term] = t match {
  case Con("normalizeChildren", List(rules, Con("Con", List(name, args)))) => Some(Con("Con", List(name, Con("map", List(Con("normalizeOnce", List(rules)), args)))))
  case _ => None
}

def rosettaTranslate(t: Term): Option[Term] = t match {
  case Con("translate", List(Con("MkLang", List(n1, g1, iso1)), Con("MkLang", List(n2, g2, iso2)), src)) => Some(Con("forward", List(iso2, Con("backward", List(iso1, src)))))
  case _ => None
}

def roundTrip(t: Term): Option[Term] = t match {
  case Con("roundtrip", List(Con("MkLang", List(n, g, Con("MkIso", List(parse, print)))), src)) => Some(Con("bind", List(Con("App", List(parse, src)), Var("ast"), Con("App", List(print, Var("ast"))))))
  case _ => None
}

def mapNil(t: Term): Option[Term] = t match {
  case Con("map", List(f, Con("Nil", Nil))) => Some(Con("Nil", Nil))
  case _ => None
}

def mapCons(t: Term): Option[Term] = t match {
  case Con("map", List(f, Con("Cons", List(x, xs)))) => Some(Con("Cons", List(Con("App", List(f, x)), Con("map", List(f, xs)))))
  case _ => None
}

def foldNil(t: Term): Option[Term] = t match {
  case Con("fold", List(f, acc, Con("Nil", Nil))) => Some(acc)
  case _ => None
}

def foldCons(t: Term): Option[Term] = t match {
  case Con("fold", List(f, acc, Con("Cons", List(x, xs)))) => Some(Con("fold", List(f, Con("App", List(f, acc, x)), xs)))
  case _ => None
}

def appendNil(t: Term): Option[Term] = t match {
  case Con("append", List(Con("Nil", Nil), ys)) => Some(ys)
  case _ => None
}

def appendCons(t: Term): Option[Term] = t match {
  case Con("append", List(Con("Cons", List(x, xs)), ys)) => Some(Con("Cons", List(x, Con("append", List(xs, ys)))))
  case _ => None
}

def ifTrue(t: Term): Option[Term] = t match {
  case Con("if", List(Con("true", Nil), v_then, v_else)) => Some(v_then)
  case _ => None
}

def ifFalse(t: Term): Option[Term] = t match {
  case Con("if", List(Con("false", Nil), v_then, v_else)) => Some(v_else)
  case _ => None
}

def eqSame(t: Term): Option[Term] = t match {
  case Con("eq", List(x, x0)) if x0 == x => Some(Con("true", Nil))
  case _ => None
}

def bindSome(t: Term): Option[Term] = t match {
  case Con("bind", List(Con("Some", List(x)), v_var, body)) => Some(Con("subst", List(body, Con("Bind", List(v_var, x, Con("Empty", Nil))))))
  case _ => None
}

def bindNone(t: Term): Option[Term] = t match {
  case Con("bind", List(Con("None", Nil), v_var, body)) => Some(Con("None", Nil))
  case _ => None
}

def prodName(t: Term): Option[Term] = t match {
  case Con("prodName", List(Con("MkProd", List(name, expr, con)))) => Some(name)
  case _ => None
}

def prodGrammar(t: Term): Option[Term] = t match {
  case Con("prodGrammar", List(Con("MkProd", List(name, expr, con)))) => Some(expr)
  case _ => None
}

def prodCon(t: Term): Option[Term] = t match {
  case Con("prodCon", List(Con("MkProd", List(name, expr, con)))) => Some(con)
  case _ => None
}

def astToGrammarLit(t: Term): Option[Term] = t match {
  case Con("astToGrammar", List(Con("Con", List(Lit("\"lit\""), Con("Cons", List(Con("Con", List(Lit("\"string\""), Con("Cons", List(Con("Lit", List(s)), Con("Nil", Nil))))), Con("Nil", Nil))))))) => Some(Con("GLit", List(Con("stripQuotes", List(s)))))
  case _ => None
}

def astToGrammarRef(t: Term): Option[Term] = t match {
  case Con("astToGrammar", List(Con("Con", List(Lit("\"ref\""), Con("Cons", List(Con("Con", List(Lit("\"ident\""), Con("Cons", List(Con("Var", List(name)), Con("Nil", Nil))))), Con("Nil", Nil))))))) => Some(Con("GRef", List(name)))
  case _ => None
}

def astToGrammarSpecial(t: Term): Option[Term] = t match {
  case Con("astToGrammar", List(Con("Con", List(Lit("\"special\""), Con("Cons", List(Con("Var", List(s)), Con("Nil", Nil))))))) => Some(Con("GRef", List(Con("concat", List(Lit("\"TOKEN.\""), Con("stripAngleBrackets", List(s)))))))
  case _ => None
}

def astToGrammarSeq(t: Term): Option[Term] = t match {
  case Con("astToGrammar", List(Con("Con", List(Lit("\"seq\""), args)))) => Some(Con("foldr", List(Con("GSeq", Nil), Con("GEmpty", Nil), Con("map", List(Con("astToGrammar", Nil), args)))))
  case _ => None
}

def astToGrammarAlt(t: Term): Option[Term] = t match {
  case Con("astToGrammar", List(Con("Con", List(Lit("\"alt\""), args)))) => Some(Con("let", List(Var("parts"), Con("splitByPipe", List(args)), Con("foldr1", List(Con("GAlt", Nil), Con("map", List(Con("astToGrammar", Nil), Var("parts"))))))))
  case _ => None
}

def astToGrammarStar(t: Term): Option[Term] = t match {
  case Con("astToGrammar", List(Con("Con", List(Lit("\"star\""), Con("Cons", List(g, Con("Nil", Nil))))))) => Some(Con("GStar", List(Con("astToGrammar", List(g)))))
  case _ => None
}

def astToGrammarPlus(t: Term): Option[Term] = t match {
  case Con("astToGrammar", List(Con("Con", List(Lit("\"plus\""), Con("Cons", List(g, Con("Nil", Nil))))))) => Some(Con("GPlus", List(Con("astToGrammar", List(g)))))
  case _ => None
}

def astToGrammarOpt(t: Term): Option[Term] = t match {
  case Con("astToGrammar", List(Con("Con", List(Lit("\"opt\""), Con("Cons", List(g, Con("Nil", Nil))))))) => Some(Con("GOpt", List(Con("astToGrammar", List(g)))))
  case _ => None
}

def astToGrammarNot(t: Term): Option[Term] = t match {
  case Con("astToGrammar", List(Con("Con", List(Lit("\"not\""), Con("Cons", List(g, Con("Nil", Nil))))))) => Some(Con("GNot", List(Con("astToGrammar", List(g)))))
  case _ => None
}

def astToGrammarAnd(t: Term): Option[Term] = t match {
  case Con("astToGrammar", List(Con("Con", List(Lit("\"and\""), Con("Cons", List(g, Con("Nil", Nil))))))) => Some(Con("GAnd", List(Con("astToGrammar", List(g)))))
  case _ => None
}

def extractParentNames(t: Term): Option[Term] = t match {
  case Con("extractParentNames", List(Con("Con", List(Lit("\"DLang\""), args)))) => Some(Con("filterMap", List(Con("extractParentFromArg", Nil), args)))
  case _ => None
}

def extractParentNamesOther(t: Term): Option[Term] = t match {
  case Con("extractParentNames", List(other)) => Some(Con("Nil", Nil))
  case _ => None
}

def extractParentFromArg(t: Term): Option[Term] = t match {
  case Con("extractParentFromArg", List(Con("Con", List(Lit("\"DImports\""), imports)))) => Some(Con("Some", List(Con("filterMap", List(Con("extractIdentName", Nil), imports)))))
  case _ => None
}

def extractParentFromArgOther(t: Term): Option[Term] = t match {
  case Con("extractParentFromArg", List(other)) => Some(Con("None", Nil))
  case _ => None
}

def extractIdentName(t: Term): Option[Term] = t match {
  case Con("extractIdentName", List(Con("Con", List(Lit("\"ident\""), Con("Cons", List(Con("Var", List(name)), Con("Nil", Nil))))))) => Some(Con("Some", List(name)))
  case _ => None
}

def extractIdentNameOther(t: Term): Option[Term] = t match {
  case Con("extractIdentName", List(other)) => Some(Con("None", Nil))
  case _ => None
}

def extractProductions(t: Term): Option[Term] = t match {
  case Con("extractProductions", List(Con("Con", List(Lit("\"DGrammar\""), Con("Cons", List(Con("Con", List(Lit("\"ident\""), Con("Cons", List(Con("Var", List(lang)), Con("Nil", Nil))))), Con("Cons", List(pieces, Con("Nil", Nil))))))))) => Some(Con("concatMap", List(Con("extractPieceProductions", Nil), Con("getList", List(pieces)))))
  case _ => None
}

def extractPieceProductions(t: Term): Option[Term] = t match {
  case Con("extractPieceProductions", List(Con("Con", List(Lit("\"DPiece\""), Con("Cons", List(Con("Con", List(Lit("\"ident\""), Con("Cons", List(Con("Var", List(pieceName)), Con("Nil", Nil))))), Con("Cons", List(members, Con("Nil", Nil))))))))) => Some(Con("concatMap", List(Con("extractMemberProd", List(pieceName)), Con("getList", List(members)))))
  case _ => None
}

def extractMemberProdSyntax(t: Term): Option[Term] = t match {
  case Con("extractMemberProd", List(piece, Con("Con", List(Lit("\"DSyntax\""), Con("Cons", List(Con("Con", List(Lit("\"ident\""), Con("Cons", List(Con("Var", List(cat)), Con("Nil", Nil))))), Con("Cons", List(alts, Con("Nil", Nil))))))))) => Some(Con("map", List(Con("mkProduction", List(piece, cat)), Con("splitByPipe", List(Con("getList", List(alts)))))))
  case _ => None
}

def mkProduction(t: Term): Option[Term] = t match {
  case Con("mkProduction", List(piece, cat, alt)) => Some(Con("let", List(Var("conName"), Con("extractConName", List(alt)), Con("MkProd", List(Con("concat", List(piece, Con("concat", List(Lit("\".\""), cat)))), Con("astToGrammar", List(alt)), Var("conName"))))))
  case _ => None
}

def extractConName(t: Term): Option[Term] = t match {
  case Con("extractConName", List(alt)) => Some(Con("case", List(Con("findArrow", List(alt)), Con("Some", List(Var("name"))), Var("name"), Con("None", Nil), Lit("\"node\""))))
  case _ => None
}

def extractRules(t: Term): Option[Term] = t match {
  case Con("extractRules", List(Con("Con", List(Lit("\"DGrammar\""), Con("Cons", List(lang, Con("Cons", List(pieces, Con("Nil", Nil))))))))) => Some(Con("concatMap", List(Con("extractPieceRules", Nil), Con("getList", List(pieces)))))
  case _ => None
}

def extractPieceRules(t: Term): Option[Term] = t match {
  case Con("extractPieceRules", List(Con("Con", List(Lit("\"DPiece\""), Con("Cons", List(name, Con("Cons", List(members, Con("Nil", Nil))))))))) => Some(Con("filterMap", List(Con("extractRule", Nil), Con("getList", List(members)))))
  case _ => None
}

def extractRule(t: Term): Option[Term] = t match {
  case Con("extractRule", List(Con("Con", List(Lit("\"DRule\""), Con("Cons", List(Con("Con", List(Lit("\"ident\""), Con("Cons", List(Con("Var", List(name)), Con("Nil", Nil))))), Con("Cons", List(pat, Con("Cons", List(template, Con("Nil", Nil))))))))))) => Some(Con("Some", List(Con("MkRule", List(name, pat, template)))))
  case _ => None
}

def extractRuleNone(t: Term): Option[Term] = t match {
  case Con("extractRule", List(other)) => Some(Con("None", Nil))
  case _ => None
}

def parseWithGrammar(t: Term): Option[Term] = t match {
  case Con("parseWithGrammar", List(Con("MkGrammar", List(prods, tokProds, syms, start)), input)) => Some(Con("let", List(Var("tokens"), Con("tokenize", List(input)), Con("let", List(Var("state"), Con("MkState", List(Var("tokens"), Lit("0"))), Con("parseProduction", List(start, prods, Var("state"))))))))
  case _ => None
}

def parseProduction(t: Term): Option[Term] = t match {
  case Con("parseProduction", List(name, prods, state)) => Some(Con("case", List(Con("findProd", List(name, prods)), Con("Some", List(Con("MkProd", List(Var("n"), Var("g"), Var("c"))))), Con("parse", List(Var("g"), state)), Con("None", Nil), Con("ParseFail", List(Con("concat", List(Lit("\"unknown production: \""), name)), state)))))
  case _ => None
}

def findProdHit(t: Term): Option[Term] = t match {
  case Con("findProd", List(name, Con("Cons", List(Con("MkProd", List(name0, g, c)), rest)))) if name0 == name => Some(Con("Some", List(Con("MkProd", List(name, g, c)))))
  case _ => None
}

def findProdMiss(t: Term): Option[Term] = t match {
  case Con("findProd", List(name, Con("Cons", List(Con("MkProd", List(other, g, c)), rest)))) => Some(Con("findProd", List(name, rest)))
  case _ => None
}

def findProdEmpty(t: Term): Option[Term] = t match {
  case Con("findProd", List(name, Con("Nil", Nil))) => Some(Con("None", Nil))
  case _ => None
}

def printWithGrammar(t: Term): Option[Term] = t match {
  case Con("printWithGrammar", List(Con("MkGrammar", List(prods, tokProds, syms, start)), prodName, term)) => Some(Con("case", List(Con("findProd", List(prodName, prods)), Con("Some", List(Con("MkProd", List(Var("n"), Var("g"), Var("c"))))), Con("print", List(Var("g"), term)), Con("None", Nil), Con("PrintFail", List(Con("concat", List(Lit("\"unknown production: \""), prodName)))))))
  case _ => None
}

def stripQuotes(t: Term): Option[Term] = t match {
  case Con("stripQuotes", List(s)) => Some(Con("if", List(Con("and", List(Con("startsWith", List(s, Lit("\"\\\"\""))), Con("endsWith", List(s, Lit("\"\\\"\""))))), Con("drop", List(Lit("1"), Con("dropRight", List(Lit("1"), s)))), s)))
  case _ => None
}

def stripAngleBrackets(t: Term): Option[Term] = t match {
  case Con("stripAngleBrackets", List(s)) => Some(Con("if", List(Con("and", List(Con("startsWith", List(s, Lit("\"<\""))), Con("endsWith", List(s, Lit("\">\""))))), Con("drop", List(Lit("1"), Con("dropRight", List(Lit("1"), s)))), s)))
  case _ => None
}

def splitByPipe(t: Term): Option[Term] = t match {
  case Con("splitByPipe", List(ts)) => Some(Con("splitBy", List(Con("Lit", List(Lit("\"|\""))), ts)))
  case _ => None
}

def getList(t: Term): Option[Term] = t match {
  case Con("getList", List(Con("Con", List(Lit("\"list\""), xs)))) => Some(xs)
  case _ => None
}

def getListOther(t: Term): Option[Term] = t match {
  case Con("getList", List(v_t)) => Some(Con("Cons", List(v_t, Con("Nil", Nil))))
  case _ => None
}

def rtGrammar(t: Term): Option[Term] = t match {
  case Con("rtGrammar", List(Con("MkRuntime", List(grammar, rules)))) => Some(grammar)
  case _ => None
}

def rtRules(t: Term): Option[Term] = t match {
  case Con("rtRules", List(Con("MkRuntime", List(grammar, rules)))) => Some(rules)
  case _ => None
}

def loadBootstrap(t: Term): Option[Term] = t match {
  case Con("loadBootstrap", List(content)) => Some(Con("case", List(Con("parseBootstrap", List(content)), Con("Some", List(Var("ast"))), Con("let", List(Var("prods"), Con("extractProductions", List(Var("ast"))), Con("let", List(Var("rules"), Con("extractRules", List(Var("ast"))), Con("Some", List(Con("MkRuntime", List(Con("MkGrammar", List(Var("prods"), Con("Nil", Nil), Con("Nil", Nil), Lit("\"File.legoFile\""))), Var("rules"))))))))), Con("None", Nil), Con("None", Nil))))
  case _ => None
}

def parseBootstrap(t: Term): Option[Term] = t match {
  case Con("parseBootstrap", List(content)) => Some(Con("hardcodedParse", List(content)))
  case _ => None
}

def loadLego(t: Term): Option[Term] = t match {
  case Con("loadLego", List(bootstrapRt, content)) => Some(Con("case", List(Con("parseLegoFile", List(bootstrapRt, content)), Con("Some", List(Var("ast"))), Con("let", List(Var("prods"), Con("extractProductions", List(Var("ast"))), Con("let", List(Var("rules"), Con("extractRules", List(Var("ast"))), Con("let", List(Var("bootstrapProds"), Con("rtGrammar", List(bootstrapRt)), Con("Some", List(Con("MkRuntime", List(Con("MkGrammar", List(Con("append", List(Var("prods"), Con("grammarProds", List(Var("bootstrapProds"))))), Con("Nil", Nil), Con("Nil", Nil), Lit("\"File.legoFile\""))), Con("append", List(Var("rules"), Con("rtRules", List(bootstrapRt)))))))))))))), Con("None", Nil), Con("None", Nil))))
  case _ => None
}

def parseLegoFile(t: Term): Option[Term] = t match {
  case Con("parseLegoFile", List(rt, content)) => Some(Con("parseWithGrammar", List(Con("rtGrammar", List(rt)), content)))
  case _ => None
}

def parseLegoFileE(t: Term): Option[Term] = t match {
  case Con("parseLegoFileE", List(rt, content)) => Some(Con("case", List(Con("parseWithGrammar", List(Con("rtGrammar", List(rt)), content)), Con("ParseOk", List(Var("t"), Var("s"))), Con("Ok", List(Var("t"))), Con("ParseFail", List(Var("msg"), Var("s"))), Con("Err", List(Var("msg"))))))
  case _ => None
}

def loadLanguage(t: Term): Option[Term] = t match {
  case Con("loadLanguage", List(rt, path)) => Some(Con("loadLanguageWithParents", List(rt, path, Con("Nil", Nil))))
  case _ => None
}

def loadLanguageWithParents(t: Term): Option[Term] = t match {
  case Con("loadLanguageWithParents", List(rt, path, visited)) => Some(Con("if", List(Con("elem", List(path, visited)), Con("Err", List(Con("concat", List(Lit("\"Circular language inheritance: \""), path)))), Con("case", List(Con("readFile", List(path)), Con("Some", List(Var("content"))), Con("loadLanguageContent", List(rt, path, Var("content"), Con("Cons", List(path, visited)))), Con("None", Nil), Con("Err", List(Con("concat", List(Lit("\"Cannot read file: \""), path)))))))))
  case _ => None
}

def loadLanguageContent(t: Term): Option[Term] = t match {
  case Con("loadLanguageContent", List(rt, path, content, visited)) => Some(Con("case", List(Con("parseLegoFile", List(rt, content)), Con("Some", List(Var("ast"))), Con("let", List(Var("parentNames"), Con("extractParentNames", List(Var("ast"))), Con("loadWithParents", List(rt, path, Var("ast"), Var("parentNames"), visited)))), Con("None", Nil), Con("Err", List(Lit("\"parse failed\""))))))
  case _ => None
}

def loadWithParents(t: Term): Option[Term] = t match {
  case Con("loadWithParents", List(rt, path, ast, parentNames, visited)) => Some(Con("case", List(Con("loadParentGrammars", List(rt, path, parentNames, visited)), Con("Ok", List(Var("inheritedProds"), Var("inheritedTokProds"))), Con("let", List(Var("childProds"), Con("extractProductions", List(ast)), Con("let", List(Var("childTokProds"), Con("extractTokenProductions", List(ast)), Con("let", List(Var("mergedProds"), Con("append", List(Var("inheritedProds"), Var("childProds"))), Con("let", List(Var("mergedTokProds"), Con("append", List(Var("inheritedTokProds"), Var("childTokProds"))), Con("let", List(Var("syms"), Con("extractSymbols", List(Var("mergedProds"))), Con("let", List(Var("start"), Con("findStartProd", List(Var("childProds"))), Con("Ok", List(Con("MkGrammar", List(Var("mergedProds"), Var("mergedTokProds"), Var("syms"), Var("start"))))))))))))))))), Con("Err", List(Var("e"))), Con("Err", List(Var("e"))))))
  case _ => None
}

def loadParentGrammars(t: Term): Option[Term] = t match {
  case Con("loadParentGrammars", List(rt, childPath, Con("Nil", Nil), visited)) => Some(Con("Ok", List(Con("Nil", Nil), Con("Nil", Nil))))
  case _ => None
}

def loadParentGrammarsNonEmpty(t: Term): Option[Term] = t match {
  case Con("loadParentGrammars", List(rt, childPath, Con("Cons", List(parent, rest)), visited)) => Some(Con("case", List(Con("resolveParentPath", List(parent, childPath)), Con("Some", List(Var("parentPath"))), Con("case", List(Con("loadLanguageWithParents", List(rt, Var("parentPath"), visited)), Con("Ok", List(Var("parentGrammar"))), Con("case", List(Con("loadParentGrammars", List(rt, childPath, rest, visited)), Con("Ok", List(Var("restProds"), Var("restTokProds"))), Con("Ok", List(Con("append", List(Con("grammarProds", List(Var("parentGrammar"))), Var("restProds"))), Con("append", List(Con("grammarTokProds", List(Var("parentGrammar"))), Var("restTokProds"))))), Con("Err", List(Var("e"))), Con("Err", List(Var("e"))))), Con("Err", List(Var("e"))), Con("Err", List(Con("concat", List(Lit("\"Failed to load parent \""), Con("concat", List(parent, Con("concat", List(Lit("\": \""), Var("e"))))))))))), Con("None", Nil), Con("if", List(Con("eq", List(parent, Lit("\"Bootstrap\""))), Con("case", List(Con("loadParentGrammars", List(rt, childPath, rest, visited)), Con("Ok", List(Var("restProds"), Var("restTokProds"))), Con("Ok", List(Con("append", List(Con("grammarProds", List(Con("rtGrammar", List(rt)))), Var("restProds"))), Con("append", List(Con("grammarTokProds", List(Con("rtGrammar", List(rt)))), Var("restTokProds"))))), Con("Err", List(Var("e"))), Con("Err", List(Var("e"))))), Con("Err", List(Con("concat", List(Lit("\"Cannot find parent language: \""), parent)))))))))
  case _ => None
}

def resolveParentPath(t: Term): Option[Term] = t match {
  case Con("resolveParentPath", List(parentName, childPath)) => Some(Con("findFirst", List(Con("fileExists", Nil), Con("Cons", List(Con("concat", List(Con("dirname", List(childPath)), Con("concat", List(Lit("\"/\""), Con("concat", List(parentName, Lit("\".lego\""))))))), Con("Cons", List(Con("concat", List(Lit("\"test/\""), Con("concat", List(parentName, Lit("\".lego\""))))), Con("Cons", List(Con("concat", List(Lit("\"src/Lego/\""), Con("concat", List(parentName, Lit("\".lego\""))))), Con("Cons", List(Con("concat", List(Lit("\"src/Rosetta/\""), Con("concat", List(parentName, Lit("\".lego\""))))), Con("Nil", Nil))))))))))))
  case _ => None
}

def grammarProds(t: Term): Option[Term] = t match {
  case Con("grammarProds", List(Con("MkGrammar", List(prods, tokProds, syms, start)))) => Some(prods)
  case _ => None
}

def grammarTokProds(t: Term): Option[Term] = t match {
  case Con("grammarTokProds", List(Con("MkGrammar", List(prods, tokProds, syms, start)))) => Some(tokProds)
  case _ => None
}

def extractTokenProductions(t: Term): Option[Term] = t match {
  case Con("extractTokenProductions", List(ast)) => Some(Con("filter", List(Con("isTokenProd", Nil), Con("extractProductions", List(ast)))))
  case _ => None
}

def isTokenProd(t: Term): Option[Term] = t match {
  case Con("isTokenProd", List(Con("MkProd", List(name, g, c)))) => Some(Con("startsWith", List(name, Lit("\"TOKEN.\""))))
  case _ => None
}

def extractSymbols(t: Term): Option[Term] = t match {
  case Con("extractSymbols", List(prods)) => Some(Con("nub", List(Con("concatMap", List(Con("prodSymbols", Nil), prods)))))
  case _ => None
}

def prodSymbols(t: Term): Option[Term] = t match {
  case Con("prodSymbols", List(Con("MkProd", List(name, g, c)))) => Some(Con("grammarSymbols", List(g)))
  case _ => None
}

def grammarSymbolsRef(t: Term): Option[Term] = t match {
  case Con("grammarSymbols", List(Con("GRef", List(name)))) => Some(Con("Cons", List(name, Con("Nil", Nil))))
  case _ => None
}

def grammarSymbolsSeq(t: Term): Option[Term] = t match {
  case Con("grammarSymbols", List(Con("GSeq", List(g1, g2)))) => Some(Con("append", List(Con("grammarSymbols", List(g1)), Con("grammarSymbols", List(g2)))))
  case _ => None
}

def grammarSymbolsAlt(t: Term): Option[Term] = t match {
  case Con("grammarSymbols", List(Con("GAlt", List(g1, g2)))) => Some(Con("append", List(Con("grammarSymbols", List(g1)), Con("grammarSymbols", List(g2)))))
  case _ => None
}

def grammarSymbolsStar(t: Term): Option[Term] = t match {
  case Con("grammarSymbols", List(Con("GStar", List(g)))) => Some(Con("grammarSymbols", List(g)))
  case _ => None
}

def grammarSymbolsOther(t: Term): Option[Term] = t match {
  case Con("grammarSymbols", List(g)) => Some(Con("Nil", Nil))
  case _ => None
}

def findStartProd(t: Term): Option[Term] = t match {
  case Con("findStartProd", List(Con("Cons", List(Con("MkProd", List(name, g, c)), rest)))) => Some(name)
  case _ => None
}

def findStartProdEmpty(t: Term): Option[Term] = t match {
  case Con("findStartProd", List(Con("Nil", Nil))) => Some(Lit("\"File.legoFile\""))
  case _ => None
}

def normalize(t: Term): Option[Term] = t match {
  case Con("normalize", List(rt, term)) => Some(Con("normalizeWith", List(Lit("1000"), Con("rtRules", List(rt)), term)))
  case _ => None
}

def normalizeWith(t: Term): Option[Term] = t match {
  case Con("normalizeWith", List(Lit("0"), rules, v_t)) => Some(v_t)
  case _ => None
}

def normalizeWithFuel(t: Term): Option[Term] = t match {
  case Con("normalizeWith", List(n, rules, v_t)) => Some(Con("case", List(Con("tryApplyRules", List(rules, v_t)), Con("Some", List(Var("t'"))), Con("normalizeWith", List(Con("sub", List(n, Lit("1"))), rules, Var("t'"))), Con("None", Nil), Con("normalizeChildren", List(n, rules, v_t)))))
  case _ => None
}

def tryApplyRules(t: Term): Option[Term] = t match {
  case Con("tryApplyRules", List(Con("Cons", List(Con("MkRule", List(name, pat, tmpl)), rest)), v_t)) => Some(Con("case", List(Con("matchPat", List(pat, v_t)), Con("Some", List(Var("bindings"))), Con("Some", List(Con("subst", List(tmpl, Var("bindings"))))), Con("None", Nil), Con("tryApplyRules", List(rest, v_t)))))
  case _ => None
}

def tryApplyRulesEmpty(t: Term): Option[Term] = t match {
  case Con("tryApplyRules", List(Con("Nil", Nil), v_t)) => Some(Con("None", Nil))
  case _ => None
}

def normalizeChildren(t: Term): Option[Term] = t match {
  case Con("normalizeChildren", List(n, rules, Con("Var", List(x)))) => Some(Con("Var", List(x)))
  case _ => None
}

def printTerm(t: Term): Option[Term] = t match {
  case Con("printTerm", List(rt, term, prodName)) => Some(Con("case", List(Con("printWithGrammar", List(Con("rtGrammar", List(rt)), prodName, term)), Con("PrintOk", List(Var("tokens"))), Con("Some", List(Con("joinTokens", List(Var("tokens"))))), Con("PrintFail", List(Var("msg"))), Con("None", Nil))))
  case _ => None
}

def joinTokens(t: Term): Option[Term] = t match {
  case Con("joinTokens", List(tokens)) => Some(Con("intercalate", List(Lit("\" \""), Con("map", List(Con("tokenToString", Nil), tokens)))))
  case _ => None
}

def tokenToString(t: Term): Option[Term] = t match {
  case Con("tokenToString", List(Con("TokIdent", List(s)))) => Some(s)
  case _ => None
}

def tokenToStringStr(t: Term): Option[Term] = t match {
  case Con("tokenToString", List(Con("TokString", List(s)))) => Some(Con("concat", List(Lit("\"\\\"\""), Con("concat", List(s, Lit("\"\\\"\""))))))
  case _ => None
}

def tokenToStringSym(t: Term): Option[Term] = t match {
  case Con("tokenToString", List(Con("TokSym", List(s)))) => Some(s)
  case _ => None
}

def initRuntime(t: Term): Option[Term] = t match {
  case Con("initRuntime", List(bootstrapContent, legoContent)) => Some(Con("case", List(Con("loadBootstrap", List(bootstrapContent)), Con("Some", List(Var("bootstrapRt"))), Con("case", List(Con("loadLego", List(Var("bootstrapRt"), legoContent)), Con("Some", List(Var("legoRt"))), Con("Ok", List(Var("legoRt"))), Con("None", Nil), Con("Err", List(Lit("\"failed to load Lego.lego\""))))), Con("None", Nil), Con("Err", List(Lit("\"failed to load Bootstrap.lego\""))))))
  case _ => None
}

def valErrorFormat(t: Term): Option[Term] = t match {
  case Con("valErrorFormat", List(Con("UndefinedProduction", List(ref, source)))) => Some(Con("concat", List(Con("concat", List(Con("concat", List(Lit("\"ERROR: Undefined production '\""), ref)), Lit("\"' referenced from '\""))), Con("concat", List(source, Lit("\"'\""))))))
  case _ => None
}

def valErrorFormatDup(t: Term): Option[Term] = t match {
  case Con("valErrorFormat", List(Con("DuplicateProduction", List(name)))) => Some(Con("concat", List(Con("concat", List(Lit("\"ERROR: Duplicate production '\""), name)), Lit("\"'\""))))
  case _ => None
}

def valErrorFormatUnbound(t: Term): Option[Term] = t match {
  case Con("valErrorFormat", List(Con("UnboundVariable", List(v_var, rule)))) => Some(Con("concat", List(Con("concat", List(Con("concat", List(Con("concat", List(Lit("\"ERROR: Unbound variable '\""), v_var)), Lit("\"' in rule '\""))), rule)), Lit("\"'\""))))
  case _ => None
}

def valErrorFormatCircular(t: Term): Option[Term] = t match {
  case Con("valErrorFormat", List(Con("CircularImport", List(mod)))) => Some(Con("concat", List(Con("concat", List(Lit("\"ERROR: Circular import of '\""), mod)), Lit("\"'\""))))
  case _ => None
}

def valErrorFormatInvalid(t: Term): Option[Term] = t match {
  case Con("valErrorFormat", List(Con("InvalidSyntax", List(ctx, msg)))) => Some(Con("concat", List(Con("concat", List(Con("concat", List(Lit("\"ERROR: Invalid syntax in \""), ctx)), Lit("\": \""))), msg)))
  case _ => None
}

def valWarnFormatConflict(t: Term): Option[Term] = t match {
  case Con("valWarnFormat", List(Con("ConflictingRules", List(r1, r2, reason)))) => Some(Con("concat", List(Con("concat", List(Con("concat", List(Con("concat", List(Con("concat", List(Lit("\"WARNING: Conflicting rules '\""), r1)), Lit("\"' and '\""))), r2)), Lit("\"': \""))), reason)))
  case _ => None
}

def valWarnFormatDirectLR(t: Term): Option[Term] = t match {
  case Con("valWarnFormat", List(Con("DirectLeftRecursion", List(name)))) => Some(Con("concat", List(Con("concat", List(Lit("\"WARNING: Direct left recursion in production '\""), name)), Lit("\"'\""))))
  case _ => None
}

def valWarnFormatIndirectLR(t: Term): Option[Term] = t match {
  case Con("valWarnFormat", List(Con("IndirectLeftRecursion", List(path)))) => Some(Con("concat", List(Lit("\"WARNING: Indirect left recursion: \""), Con("intercalate", List(Lit("\" -> \""), path)))))
  case _ => None
}

def valWarnFormatUnused(t: Term): Option[Term] = t match {
  case Con("valWarnFormat", List(Con("UnusedProduction", List(name)))) => Some(Con("concat", List(Con("concat", List(Lit("\"WARNING: Unused production '\""), name)), Lit("\"'\""))))
  case _ => None
}

def valWarnFormatShadow(t: Term): Option[Term] = t match {
  case Con("valWarnFormat", List(Con("ShadowedProduction", List(name, by)))) => Some(Con("concat", List(Con("concat", List(Con("concat", List(Con("concat", List(Lit("\"WARNING: Production '\""), name)), Lit("\"' shadowed by '\""))), by)), Lit("\"'\""))))
  case _ => None
}

def valWarnFormatAmbig(t: Term): Option[Term] = t match {
  case Con("valWarnFormat", List(Con("AmbiguousGrammar", List(name, reason)))) => Some(Con("concat", List(Con("concat", List(Con("concat", List(Con("concat", List(Lit("\"WARNING: Ambiguous grammar for '\""), name)), Lit("\"': \""))), reason)), Lit("\"\""))))
  case _ => None
}

def valWarnFormatMissingCut(t: Term): Option[Term] = t match {
  case Con("valWarnFormat", List(Con("MissingCut", List(prod, kw)))) => Some(Con("concat", List(Con("concat", List(Con("concat", List(Con("concat", List(Lit("\"OPTIMIZE: Production '\""), prod)), Lit("\"' could add cut after '\""))), kw)), Lit("\"' for better errors\""))))
  case _ => None
}

def valWarnFormatCycle(t: Term): Option[Term] = t match {
  case Con("valWarnFormat", List(Con("RuleCycle", List(cycle)))) => Some(Con("concat", List(Lit("\"WARNING: Potential non-terminating rule cycle: \""), Con("intercalate", List(Lit("\" -> \""), cycle)))))
  case _ => None
}

def valWarnFormatUnreachable(t: Term): Option[Term] = t match {
  case Con("valWarnFormat", List(Con("UnreachableAlt", List(prod, idx)))) => Some(Con("concat", List(Con("concat", List(Con("concat", List(Lit("\"WARNING: Alternative \""), Con("toString", List(idx)))), Lit("\" in '\""))), Con("concat", List(prod, Lit("\"' is unreachable\""))))))
  case _ => None
}

def valWarnFormatRedundant(t: Term): Option[Term] = t match {
  case Con("valWarnFormat", List(Con("RedundantAlt", List(prod, i, j)))) => Some(Con("concat", List(Con("concat", List(Con("concat", List(Con("concat", List(Con("concat", List(Lit("\"WARNING: Alternatives \""), Con("toString", List(i)))), Lit("\" and \""))), Con("toString", List(j)))), Lit("\" in '\""))), Con("concat", List(prod, Lit("\"' are redundant\""))))))
  case _ => None
}

def valResultEmpty(t: Term): Option[Term] = t match {
  case Con("valResultEmpty", Nil) => Some(Con("MkValidationResult", List(Con("Nil", Nil), Con("Nil", Nil))))
  case _ => None
}

def valResultAppend(t: Term): Option[Term] = t match {
  case Con("valResultAppend", List(Con("MkValidationResult", List(e1, w1)), Con("MkValidationResult", List(e2, w2)))) => Some(Con("MkValidationResult", List(Con("append", List(e1, e2)), Con("append", List(w1, w2)))))
  case _ => None
}

def valResultAddError(t: Term): Option[Term] = t match {
  case Con("valResultAddError", List(Con("MkValidationResult", List(errs, warns)), e)) => Some(Con("MkValidationResult", List(Con("Cons", List(e, errs)), warns)))
  case _ => None
}

def valResultAddWarning(t: Term): Option[Term] = t match {
  case Con("valResultAddWarning", List(Con("MkValidationResult", List(errs, warns)), w)) => Some(Con("MkValidationResult", List(errs, Con("Cons", List(w, warns)))))
  case _ => None
}

def valResultHasErrors(t: Term): Option[Term] = t match {
  case Con("valResultHasErrors", List(Con("MkValidationResult", List(errs, warns)))) => Some(Con("not", List(Con("null", List(errs)))))
  case _ => None
}

def valResultFormat(t: Term): Option[Term] = t match {
  case Con("valResultFormat", List(Con("MkValidationResult", List(errs, warns)))) => Some(Con("append", List(Con("map", List(Con("valErrorFormat", Nil), errs)), Con("map", List(Con("valWarnFormat", Nil), warns)))))
  case _ => None
}

def builtinProductions(t: Term): Option[Term] = t match {
  case Con("builtinProductions", Nil) => Some(Con("Cons", List(Lit("\"nat\""), Con("Cons", List(Lit("\"int\""), Con("Cons", List(Lit("\"str\""), Con("Cons", List(Lit("\"string\""), Con("Cons", List(Lit("\"ident\""), Con("Cons", List(Lit("\"char\""), Con("Cons", List(Lit("\"float\""), Con("Cons", List(Lit("\"bool\""), Con("Nil", Nil))))))))))))))))))
  case _ => None
}

def extractRefsEmpty(t: Term): Option[Term] = t match {
  case Con("extractRefs", List(Con("GEmpty", Nil))) => Some(Con("Nil", Nil))
  case _ => None
}

def extractRefsLit(t: Term): Option[Term] = t match {
  case Con("extractRefs", List(Con("GLit", List(s)))) => Some(Con("Nil", Nil))
  case _ => None
}

def extractRefsRef(t: Term): Option[Term] = t match {
  case Con("extractRefs", List(Con("GRef", List(name)))) => Some(Con("Cons", List(name, Con("Nil", Nil))))
  case _ => None
}

def extractRefsSeq(t: Term): Option[Term] = t match {
  case Con("extractRefs", List(Con("GSeq", List(g1, g2)))) => Some(Con("append", List(Con("extractRefs", List(g1)), Con("extractRefs", List(g2)))))
  case _ => None
}

def extractRefsAlt(t: Term): Option[Term] = t match {
  case Con("extractRefs", List(Con("GAlt", List(g1, g2)))) => Some(Con("append", List(Con("extractRefs", List(g1)), Con("extractRefs", List(g2)))))
  case _ => None
}

def extractRefsStar(t: Term): Option[Term] = t match {
  case Con("extractRefs", List(Con("GStar", List(g)))) => Some(Con("extractRefs", List(g)))
  case _ => None
}

def extractRefsPlus(t: Term): Option[Term] = t match {
  case Con("extractRefs", List(Con("GPlus", List(g)))) => Some(Con("extractRefs", List(g)))
  case _ => None
}

def extractRefsOpt(t: Term): Option[Term] = t match {
  case Con("extractRefs", List(Con("GOpt", List(g)))) => Some(Con("extractRefs", List(g)))
  case _ => None
}

def extractRefsNot(t: Term): Option[Term] = t match {
  case Con("extractRefs", List(Con("GNot", List(g)))) => Some(Con("extractRefs", List(g)))
  case _ => None
}

def extractRefsAnd(t: Term): Option[Term] = t match {
  case Con("extractRefs", List(Con("GAnd", List(g)))) => Some(Con("extractRefs", List(g)))
  case _ => None
}

def extractRefsCon(t: Term): Option[Term] = t match {
  case Con("extractRefs", List(Con("GCon", List(name, g)))) => Some(Con("extractRefs", List(g)))
  case _ => None
}

def checkUndefinedRefs(t: Term): Option[Term] = t match {
  case Con("checkUndefinedRefs", List(grammar)) => Some(Con("let", List(Var("defined"), Con("grammarDefinedNames", List(grammar)), Con("let", List(Var("builtins"), Con("builtinProductions", Nil), Con("foldl", List(Con("acc", List(Con("binder", List(Lit("prod"), Con("let", List(Var("refs"), Con("extractRefs", List(Con("grammarLookup", List(grammar, Var("prod"))))), Con("foldl", List(Con("acc2", List(Con("binder", List(Lit("ref"), Con("if", List(Con("or", List(Con("contains", List(Var("defined"), Var("ref"))), Con("contains", List(Var("builtins"), Con("baseName", List(Var("ref"))))))), Var("acc2"), Con("valResultAddError", List(Var("acc2"), Con("UndefinedProduction", List(Var("ref"), Var("prod"))))))))))), Var("acc"), Var("refs"))))))))), Con("valResultEmpty", Nil), Con("grammarProductions", List(grammar)))))))))
  case _ => None
}

def isDirectLeftRecEmpty(t: Term): Option[Term] = t match {
  case Con("isDirectLeftRec", List(name, Con("GEmpty", Nil))) => Some(Con("False", Nil))
  case _ => None
}

def isDirectLeftRecLit(t: Term): Option[Term] = t match {
  case Con("isDirectLeftRec", List(name, Con("GLit", List(s)))) => Some(Con("False", Nil))
  case _ => None
}

def isDirectLeftRecRef(t: Term): Option[Term] = t match {
  case Con("isDirectLeftRec", List(name, Con("GRef", List(ref)))) => Some(Con("eq", List(ref, name)))
  case _ => None
}

def isDirectLeftRecSeq(t: Term): Option[Term] = t match {
  case Con("isDirectLeftRec", List(name, Con("GSeq", List(g1, g2)))) => Some(Con("isDirectLeftRec", List(name, g1)))
  case _ => None
}

def isDirectLeftRecAlt(t: Term): Option[Term] = t match {
  case Con("isDirectLeftRec", List(name, Con("GAlt", List(g1, g2)))) => Some(Con("or", List(Con("isDirectLeftRec", List(name, g1)), Con("isDirectLeftRec", List(name, g2)))))
  case _ => None
}

def isDirectLeftRecStar(t: Term): Option[Term] = t match {
  case Con("isDirectLeftRec", List(name, Con("GStar", List(g)))) => Some(Con("isDirectLeftRec", List(name, g)))
  case _ => None
}

def isDirectLeftRecPlus(t: Term): Option[Term] = t match {
  case Con("isDirectLeftRec", List(name, Con("GPlus", List(g)))) => Some(Con("isDirectLeftRec", List(name, g)))
  case _ => None
}

def isDirectLeftRecOpt(t: Term): Option[Term] = t match {
  case Con("isDirectLeftRec", List(name, Con("GOpt", List(g)))) => Some(Con("isDirectLeftRec", List(name, g)))
  case _ => None
}

def isDirectLeftRecCon(t: Term): Option[Term] = t match {
  case Con("isDirectLeftRec", List(name, Con("GCon", List(c, g)))) => Some(Con("isDirectLeftRec", List(name, g)))
  case _ => None
}

def checkLeftRecursion(t: Term): Option[Term] = t match {
  case Con("checkLeftRecursion", List(grammar)) => Some(Con("foldl", List(Con("acc", List(Con("binder", List(Lit("prod"), Con("if", List(Con("isDirectLeftRec", List(Var("prod"), Con("grammarLookup", List(grammar, Var("prod"))))), Con("valResultAddWarning", List(Var("acc"), Con("DirectLeftRecursion", List(Var("prod"))))), Var("acc"))))))), Con("valResultEmpty", Nil), Con("grammarProductions", List(grammar)))))
  case _ => None
}

def varsInVar(t: Term): Option[Term] = t match {
  case Con("varsIn", List(Con("Var", List(v)))) => Some(Con("Cons", List(v, Con("Nil", Nil))))
  case _ => None
}

def varsInLit(t: Term): Option[Term] = t match {
  case Con("varsIn", List(Con("Lit", List(s)))) => Some(Con("Nil", Nil))
  case _ => None
}

def varsInCon(t: Term): Option[Term] = t match {
  case Con("varsIn", List(Con("Con", List(c, args)))) => Some(Con("flatMap", List(Con("varsIn", Nil), args)))
  case _ => None
}

def patternVarsVar(t: Term): Option[Term] = t match {
  case Con("patternVars", List(Con("Var", List(v)))) => Some(Con("if", List(Con("startsWith", List(v, Lit("\"$\""))), Con("Cons", List(v, Con("Nil", Nil))), Con("Nil", Nil))))
  case _ => None
}

def patternVarsLit(t: Term): Option[Term] = t match {
  case Con("patternVars", List(Con("Lit", List(s)))) => Some(Con("Nil", Nil))
  case _ => None
}

def patternVarsCon(t: Term): Option[Term] = t match {
  case Con("patternVars", List(Con("Con", List(c, args)))) => Some(Con("flatMap", List(Con("patternVars", Nil), args)))
  case _ => None
}

def checkUnboundVars(t: Term): Option[Term] = t match {
  case Con("checkUnboundVars", List(rules)) => Some(Con("foldl", List(Con("acc", List(Con("binder", List(Lit("rule"), Con("let", List(Var("patVars"), Con("patternVars", List(Con("rulePattern", List(Var("rule"))))), Con("let", List(Var("tplVars"), Con("filter", List(Con("binder", List(Lit("v"), Con("startsWith", List(Var("v"), Lit("\"$\""))))), Con("varsIn", List(Con("ruleTemplate", List(Var("rule"))))))), Con("let", List(Var("unbound"), Con("filter", List(Con("binder", List(Lit("v"), Con("not", List(Con("contains", List(Var("patVars"), Var("v"))))))), Var("tplVars"))), Con("foldl", List(Con("acc2", List(Con("binder", List(Lit("v"), Con("valResultAddError", List(Var("acc2"), Con("UnboundVariable", List(Var("v"), Con("ruleName", List(Var("rule"))))))))))), Var("acc"), Var("unbound"))))))))))))), Con("valResultEmpty", Nil), rules)))
  case _ => None
}

def patternKeyVar(t: Term): Option[Term] = t match {
  case Con("patternKey", List(Con("Var", List(v)))) => Some(Lit("\"_\""))
  case _ => None
}

def patternKeyLit(t: Term): Option[Term] = t match {
  case Con("patternKey", List(Con("Lit", List(s)))) => Some(Con("concat", List(Con("concat", List(Lit("\"\\\"\""), s)), Lit("\"\\\"\""))))
  case _ => None
}

def patternKeyCon(t: Term): Option[Term] = t match {
  case Con("patternKey", List(Con("Con", List(name, args)))) => Some(Con("concat", List(Con("concat", List(Con("concat", List(Lit("\"(\""), name)), Con("concat", List(Lit("\" \""), Con("intercalate", List(Lit("\" \""), Con("map", List(Con("patternKey", Nil), args)))))))), Lit("\")\""))))
  case _ => None
}

def checkConflictingRules(t: Term): Option[Term] = t match {
  case Con("checkConflictingRules", List(rules)) => Some(Con("let", List(Var("grouped"), Con("groupBy", List(Con("binder", List(Lit("r"), Con("patternKey", List(Con("rulePattern", List(Var("r"))))))), rules)), Con("foldl", List(Con("acc", List(Con("binder", List(Lit("group"), Con("if", List(Con("gt", List(Con("length", List(Var("group"))), Lit("1"))), Con("let", List(Var("names"), Con("map", List(Con("ruleName", Nil), Var("group"))), Con("valResultAddWarning", List(Var("acc"), Con("ConflictingRules", List(Con("head", List(Var("names"))), Con("head", List(Con("tail", List(Var("names"))))), Lit("\"same pattern structure\""))))))), Var("acc"))))))), Con("valResultEmpty", Nil), Con("mapValues", List(Var("grouped"))))))))
  case _ => None
}

def validateGrammar(t: Term): Option[Term] = t match {
  case Con("validateGrammar", List(grammar, rules)) => Some(Con("valResultAppend", List(Con("valResultAppend", List(Con("checkUndefinedRefs", List(grammar)), Con("checkLeftRecursion", List(grammar)))), Con("valResultAppend", List(Con("checkUnboundVars", List(rules)), Con("checkConflictingRules", List(rules)))))))
  case _ => None
}

def formatValidationResult(t: Term): Option[Term] = t match {
  case Con("formatValidationResult", List(result)) => Some(Con("let", List(Var("lines"), Con("valResultFormat", List(result)), Con("intercalate", List(Lit("\"\\n\""), Var("lines"))))))
  case _ => None
}

