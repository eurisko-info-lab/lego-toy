// generated/Rosetta/LegoScala.scala
// What Lego.rosetta would generate via rosetta2scala
// This is a MANUAL rendering for verification

package lego.generated

// From Lego.rosetta adt Iso → Scala enum/case class
sealed trait Iso[A, B] {
  def forward: A => Option[B]
  def backward: B => Option[A]
}

object Iso {
  case class MkIso[A, B](forward: A => Option[B], backward: B => Option[A]) extends Iso[A, B]
  
  // From: rewrite id: Iso.id ~> ...
  def id[A]: Iso[A, A] = MkIso(Some(_), Some(_))
  
  // From: rewrite comp: (Iso.comp $f $g) ~> ...
  def comp[A, B, C](f: Iso[A, B], g: Iso[B, C]): Iso[A, C] = MkIso(
    a => f.forward(a).flatMap(g.forward),
    c => g.backward(c).flatMap(f.backward)
  )
  
  // From: rewrite par: (Iso.par $f $g) ~> ...
  def par[A, B, C, D](f: Iso[A, B], g: Iso[C, D]): Iso[(A, C), (B, D)] = MkIso(
    { case (a, c) => for { b <- f.forward(a); d <- g.forward(c) } yield (b, d) },
    { case (b, d) => for { a <- f.backward(b); c <- g.backward(d) } yield (a, c) }
  )
  
  // From: rewrite choice: (Iso.choice $f $g) ~> ...
  def choice[A, B, C](f: Iso[A, C], g: Iso[B, C]): Iso[Either[A, B], C] = MkIso(
    {
      case Left(a) => f.forward(a)
      case Right(b) => g.forward(b)
    },
    c => f.backward(c).map(Left(_)).orElse(g.backward(c).map(Right(_)))
  )
  
  // From: rewrite orElse: (Iso.orElse $f $g) ~> ...
  def orElse[A, B](f: Iso[A, B], g: Iso[A, B]): Iso[A, B] = MkIso(
    a => f.forward(a).orElse(g.forward(a)),
    b => f.backward(b).orElse(g.backward(b))
  )
  
  // From: rewrite sym: (Iso.sym $f) ~> ...
  def sym[A, B](f: Iso[A, B]): Iso[B, A] = MkIso(f.backward, f.forward)
}

// From Lego.rosetta adt Term → Scala enum
enum Term {
  case Var(name: String)
  case Lit(value: String)
  case Con(name: String, args: List[Term])
}

object Term {
  // From: rewrite atom: (Term.atom $s) ~> (Con $s Nil)
  def atom(s: String): Term = Term.Con(s, Nil)
  
  // From: rewrite app: (Term.app $f $args) ~> (Con $f $args)
  def app(f: String, args: List[Term]): Term = Term.Con(f, args)
  
  // From: rewrite matchPattern: ...
  def matchPattern(pat: Term, t: Term): Option[List[(String, Term)]] = (pat, t) match {
    case (Term.Var(name), _) if name.startsWith("$") => Some(List(name -> t))
    case (Term.Var(name), t2) if pat == t2 => Some(Nil)
    case (Term.Lit(a), Term.Lit(b)) if a == b => Some(Nil)
    case (Term.Con(c1, args1), Term.Con(c2, args2)) if c1 == c2 && args1.length == args2.length =>
      matchList(args1, args2)
    case _ => None
  }
  
  private def matchList(pats: List[Term], terms: List[Term]): Option[List[(String, Term)]] =
    (pats, terms) match {
      case (Nil, Nil) => Some(Nil)
      case (p :: ps, t :: ts) => 
        for {
          m1 <- matchPattern(p, t)
          m2 <- matchList(ps, ts)
        } yield m1 ++ m2
      case _ => None
    }
  
  // From: rewrite substVar, substLit, substCon
  def substitute(t: Term, env: List[(String, Term)]): Term = t match {
    case Term.Var(name) if name.startsWith("$") =>
      env.find(_._1 == name).map(_._2).getOrElse(t)
    case Term.Var(_) => t
    case Term.Lit(s) => Term.Lit(s)
    case Term.Con(c, args) => Term.Con(c, args.map(substitute(_, env)))
  }
}

// From Lego.rosetta adt Token → Scala enum
enum Token {
  case Ident(s: String)
  case TokenLit(s: String)
  case Sym(s: String)
  case Number(s: String)
  
  def asString: String = this match {
    case Token.Ident(s) => s
    case Token.TokenLit(s) => s
    case Token.Sym(s) => s
    case Token.Number(s) => s
  }
}

// From Lego.rosetta adt GrammarExpr → Scala enum
enum GrammarF[+A] {
  case Empty
  case GLit(s: String)
  case Ref(name: String)
  case Seq(a: A, b: A)
  case Alt(a: A, b: A)
  case Star(g: A)
  case Bind(name: String, g: A)
  case Node(name: String, g: A)
  case Cut(g: A)
  case Ordered(a: A, b: A)
  case Longest(gs: List[A])
}

case class GrammarExpr(value: GrammarF[GrammarExpr])

object GrammarExpr {
  def empty: GrammarExpr = GrammarExpr(GrammarF.Empty)
  def lit(s: String): GrammarExpr = GrammarExpr(GrammarF.GLit(s))
  def ref(s: String): GrammarExpr = GrammarExpr(GrammarF.Ref(s))
  def seq(a: GrammarExpr, b: GrammarExpr): GrammarExpr = GrammarExpr(GrammarF.Seq(a, b))
  def alt(a: GrammarExpr, b: GrammarExpr): GrammarExpr = GrammarExpr(GrammarF.Alt(a, b))
  def star(g: GrammarExpr): GrammarExpr = GrammarExpr(GrammarF.Star(g))
  
  // From: rewrite plus: (Grammar.plus $g) ~> (Seq $g (Star $g))
  def plus(g: GrammarExpr): GrammarExpr = seq(g, star(g))
  
  // From: rewrite opt: (Grammar.opt $g) ~> (Alt $g Empty)
  def opt(g: GrammarExpr): GrammarExpr = alt(g, empty)
}

// From Lego.rosetta adt Rule → Scala case class
case class Rule(name: String, pattern: Term, template: Term) {
  // From: rewrite applyRule: (Rule.apply (MkRule $name $pat $repl) $term) ~> ...
  def apply(term: Term): Option[Term] =
    Term.matchPattern(pattern, term).map(bindings => Term.substitute(template, bindings))
}

object Rule {
  // From: rewrite applyFirst: (Rule.applyFirst Nil $term) ~> None
  def applyFirst(rules: List[Rule], term: Term): Option[Term] =
    rules.view.flatMap(_.apply(term)).headOption
  
  // From: rewrite normalize: (Rule.normalize $rules $term) ~> ...
  @annotation.tailrec
  def normalize(rules: List[Rule], term: Term): Term =
    applyFirst(rules, term) match {
      case None => term
      case Some(t2) => normalize(rules, t2)
    }
}

// From Lego.rosetta adt ParseResult → Scala enum
enum ParseResult {
  case Success(remaining: List[Token], term: Term)
  case Failure(message: String)
}
