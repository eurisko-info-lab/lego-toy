package lego.runtime

import scala.collection.mutable

/**
 * Lego Runtime Library for Scala
 *
 * This module provides the core runtime infrastructure for Lego-generated Scala code.
 * It includes:
 * - Core types (Term, GrammarExpr, etc.)
 * - Parsing engine (parseGrammar, lexGrammar)
 * - IO operations (readFile, writeFile)
 * - Memoization (HashMap-based Packrat)
 *
 * Generated Rosetta code should: import lego.runtime._
 */
object Runtime {

  //============================================================================
  // Core Types
  //============================================================================

  /** The universal Term type for AST representation */
  sealed trait Term
  case class Var(name: String) extends Term
  case class Lit(value: String) extends Term
  case class Con(name: String, args: List[Term]) extends Term

  object Term {
    def show(t: Term): String = t match {
      case Var(n) => s"Var($n)"
      case Lit(v) => s"Lit($v)"
      case Con(n, args) => s"Con($n, [${args.map(show).mkString(", ")}])"
    }
  }

  /** Grammar expression algebra */
  sealed trait GrammarExpr
  case object Empty extends GrammarExpr
  case class GLit(s: String) extends GrammarExpr
  case class Ref(name: String) extends GrammarExpr
  case class Seq(g1: GrammarExpr, g2: GrammarExpr) extends GrammarExpr
  case class Alt(g1: GrammarExpr, g2: GrammarExpr) extends GrammarExpr
  case class Star(g: GrammarExpr) extends GrammarExpr
  case class Plus(g: GrammarExpr) extends GrammarExpr
  case class Opt(g: GrammarExpr) extends GrammarExpr
  case class Node(name: String, g: GrammarExpr) extends GrammarExpr

  /** Grammar production: (name, grammar, annotation) */
  case class Production(name: String, grammar: GrammarExpr, annotation: String = "")

  type Productions = List[Production]

  /** Rewrite rule: name, lhs pattern, rhs template */
  case class Rule(name: String, lhs: Term, rhs: Term)

  //============================================================================
  // Token Types
  //============================================================================

  /** Token types for lexing */
  sealed trait Token
  case class TokLit(value: String) extends Token
  case class TokIdent(name: String) extends Token
  case class TokSym(sym: String) extends Token
  case class TokNumber(num: String) extends Token

  object Token {
    def show(t: Token): String = t match {
      case TokLit(v) => s"\"$v\""
      case TokIdent(n) => n
      case TokSym(s) => s
      case TokNumber(n) => n
    }
  }

  //============================================================================
  // Parse State
  //============================================================================

  /** Packrat memoization entry */
  case class MemoEntry(result: Option[(Term, Int, List[(String, Term)])])

  /** Parse state */
  case class ParseState(
    tokens: List[Token],
    pos: Int = 0,
    memo: mutable.HashMap[(Int, String), MemoEntry] = mutable.HashMap.empty,
    binds: List[(String, Term)] = Nil
  )

  /** Parse result: (parsed term, new state) or failure */
  type ParseResult = (Option[(Term, ParseState)], mutable.HashMap[(Int, String), MemoEntry])

  //============================================================================
  // Core Parsing Engine
  //============================================================================

  /** Find a production by name */
  def findProduction(prods: Productions, name: String): Option[GrammarExpr] =
    prods.find(_.name == name).map(_.grammar)

  /** Find all productions with the same base name and combine with alt */
  def findAllProductions(prods: Productions, name: String): Option[GrammarExpr] = {
    val matching = prods.filter(_.name == name)
    matching match {
      case Nil => None
      case p :: Nil => Some(p.grammar)
      case p :: ps => Some(ps.foldLeft(p.grammar)((acc, prod) => Alt(acc, prod.grammar)))
    }
  }

  /** Combine two terms in sequence */
  def combineSeq(t1: Term, t2: Term): Term = (t1, t2) match {
    case (Con("unit", Nil), t) => t
    case (t, Con("unit", Nil)) => t
    case (Con("seq", ts), t) => Con("seq", ts :+ t)
    case (t, Con("seq", ts)) => Con("seq", t :: ts)
    case (t1, t2) => Con("seq", List(t1, t2))
  }

  /** Wrap term in a constructor node */
  def wrapNode(name: String, t: Term): Term = Con(name, List(t))

  /** Parse grammar expression (main parsing engine)
   *  Uses fuel for termination and Packrat memoization for efficiency */
  def parseGrammar(fuel: Int, prods: Productions, g: GrammarExpr, st: ParseState): ParseResult = {
    if (fuel <= 0) return (None, st.memo)

    g match {
      case Empty => (Some((Con("unit", Nil), st)), st.memo)

      case GLit(s) =>
        st.tokens match {
          case TokLit(l) :: rest if l == s =>
            (Some((Lit(s), st.copy(tokens = rest, pos = st.pos + 1))), st.memo)
          case TokSym(l) :: rest if l == s =>
            (Some((Lit(s), st.copy(tokens = rest, pos = st.pos + 1))), st.memo)
          case TokIdent(l) :: rest if l == s =>
            (Some((Lit(s), st.copy(tokens = rest, pos = st.pos + 1))), st.memo)
          case _ => (None, st.memo)
        }

      case Ref(name) =>
        // Handle built-in token types (TOKEN.*)
        if (name.startsWith("TOKEN.")) {
          val tokType = name.drop(6)
          (tokType, st.tokens) match {
            case ("ident", TokIdent(s) :: rest) =>
              (Some((Var(s), st.copy(tokens = rest, pos = st.pos + 1))), st.memo)
            case ("string", TokLit(s) :: rest) if s.startsWith("\"") =>
              (Some((Lit(s), st.copy(tokens = rest, pos = st.pos + 1))), st.memo)
            case ("number", TokNumber(s) :: rest) =>
              (Some((Lit(s), st.copy(tokens = rest, pos = st.pos + 1))), st.memo)
            case ("sym", TokSym(s) :: rest) =>
              (Some((Var(s), st.copy(tokens = rest, pos = st.pos + 1))), st.memo)
            case _ => (None, st.memo)
          }
        } else {
          // Packrat memoization for production references
          val key = (st.pos, name)
          st.memo.get(key) match {
            case Some(entry) =>
              entry.result match {
                case Some((term, endPos, newBinds)) =>
                  val tokenCount = endPos - st.pos
                  val newTokens = st.tokens.drop(tokenCount)
                  (Some((term, st.copy(tokens = newTokens, pos = endPos, binds = newBinds))), st.memo)
                case None => (None, st.memo)
              }
            case None =>
              findAllProductions(prods, name) match {
                case Some(g2) =>
                  val (result, memo2) = parseGrammar(fuel - 1, prods, g2, st)
                  result match {
                    case Some((term, st2)) =>
                      val entry = MemoEntry(Some((term, st2.pos, st2.binds)))
                      memo2.put(key, entry)
                      (Some((term, st2.copy(memo = memo2))), memo2)
                    case None =>
                      val entry = MemoEntry(None)
                      memo2.put(key, entry)
                      (None, memo2)
                  }
                case None => (None, st.memo)
              }
          }
        }

      case Seq(g1, g2) =>
        val (r1, memo1) = parseGrammar(fuel - 1, prods, g1, st)
        r1 match {
          case Some((t1, st1)) =>
            val st1p = st1.copy(memo = memo1)
            val (r2, memo2) = parseGrammar(fuel - 1, prods, g2, st1p)
            r2 match {
              case Some((t2, st2)) => (Some((combineSeq(t1, t2), st2)), memo2)
              case None => (None, memo2)
            }
          case None => (None, memo1)
        }

      case Alt(g1, g2) =>
        val (r1, memo1) = parseGrammar(fuel - 1, prods, g1, st)
        r1 match {
          case Some(result) => (Some(result), memo1)
          case None =>
            val st2 = st.copy(memo = memo1)
            parseGrammar(fuel - 1, prods, g2, st2)
        }

      case Star(g2) =>
        def loop(acc: List[Term], st: ParseState, memo: mutable.HashMap[(Int, String), MemoEntry], loopFuel: Int): ParseResult = {
          if (loopFuel <= 0) {
            val result = if (acc.isEmpty) Con("unit", Nil) else Con("seq", acc.reverse)
            (Some((result, st)), memo)
          } else {
            val st2 = st.copy(memo = memo)
            val (r, memo2) = parseGrammar(fuel - 1, prods, g2, st2)
            r match {
              case Some((t, st3)) => loop(t :: acc, st3, memo2, loopFuel - 1)
              case None =>
                val result = if (acc.isEmpty) Con("unit", Nil) else Con("seq", acc.reverse)
                (Some((result, st.copy(memo = memo2))), memo2)
            }
          }
        }
        loop(Nil, st, st.memo, fuel - 1)

      case Plus(g2) =>
        val (first, memo1) = parseGrammar(fuel - 1, prods, g2, st)
        first match {
          case None => (None, memo1)
          case Some((t, st2)) =>
            val (rest, memo2) = parseGrammar(fuel - 1, prods, Star(g2), st2.copy(memo = memo1))
            rest match {
              case Some((Con("unit", Nil), st3)) => (Some((t, st3)), memo2)
              case Some((ts, st3)) => (Some((combineSeq(t, ts), st3)), memo2)
              case None => (Some((t, st2)), memo2)
            }
        }

      case Opt(g2) =>
        val (r, memo2) = parseGrammar(fuel - 1, prods, g2, st)
        r match {
          case Some(result) => (Some(result), memo2)
          case None => (Some((Con("unit", Nil), st.copy(memo = memo2))), memo2)
        }

      case Node(name, g2) =>
        val (r, memo2) = parseGrammar(fuel - 1, prods, g2, st)
        r match {
          case Some((t, st2)) => (Some((wrapNode(name, t), st2)), memo2)
          case None => (None, memo2)
        }
    }
  }

  //============================================================================
  // IO Operations
  //============================================================================

  /** Read file contents */
  def readFile(path: String): String =
    scala.io.Source.fromFile(path).mkString

  /** Write file contents */
  def writeFile(path: String, content: String): Unit = {
    val pw = new java.io.PrintWriter(path)
    try pw.write(content)
    finally pw.close()
  }

  /** Check if file exists */
  def fileExists(path: String): Boolean =
    new java.io.File(path).exists()

  //============================================================================
  // Term Utilities
  //============================================================================

  /** Pattern match helper */
  def matchPattern(pattern: Term, t: Term): Option[List[(String, Term)]] = (pattern, t) match {
    case (Var(x), t) => Some(List((x, t)))
    case (Lit(s1), Lit(s2)) if s1 == s2 => Some(Nil)
    case (Con(n1, args1), Con(n2, args2)) if n1 == n2 && args1.length == args2.length =>
      val results = args1.zip(args2).map { case (p, t) => matchPattern(p, t) }
      if (results.forall(_.isDefined)) Some(results.flatMap(_.get))
      else None
    case _ => None
  }

  /** Substitute bindings in a term */
  def substitute(binds: List[(String, Term)], t: Term): Term = t match {
    case Var(x) => binds.find(_._1 == x).map(_._2).getOrElse(t)
    case Lit(s) => Lit(s)
    case Con(n, args) => Con(n, args.map(substitute(binds, _)))
  }

  /** Apply a single rewrite rule */
  def applyRule(rule: Rule, t: Term): Option[Term] =
    matchPattern(rule.lhs, t).map(binds => substitute(binds, rule.rhs))

  /** Normalize term using rewrite rules */
  def normalize(rules: List[Rule], t: Term, fuel: Int = 1000): Term = {
    if (fuel <= 0) return t

    // Try each rule
    rules.flatMap(r => applyRule(r, t)).headOption match {
      case Some(t2) => normalize(rules, t2, fuel - 1)
      case None =>
        // Recursively normalize children
        t match {
          case Con(n, args) => Con(n, args.map(normalize(rules, _, fuel - 1)))
          case other => other
        }
    }
  }
}
