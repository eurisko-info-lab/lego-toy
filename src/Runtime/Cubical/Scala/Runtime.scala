package cubical.runtime

import scala.collection.mutable

/**
 * Cubical Runtime Library for Scala
 *
 * This module provides the runtime infrastructure for Cubical type theory
 * generated from .lego specifications via the cubical2rosetta → rosetta2scala pipeline.
 *
 * It includes:
 * - Core Term type (shared with lego.runtime)
 * - Cubical-specific types (Dim, Cof, Level)
 * - De Bruijn index operations (shift, subst)
 * - Normalization engine
 * - Cubical operations (coe, hcom, com)
 *
 * Generated code should: import cubical.runtime._
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
    def ix(n: Int): Term = Con("ix", List(Lit(n.toString)))
    
    def show(t: Term): String = t match {
      case Var(n) => s"Var($n)"
      case Lit(v) => s"Lit($v)"
      case Con(n, args) => s"Con($n, [${args.map(show).mkString(", ")}])"
    }
  }

  //============================================================================
  // Cubical-Specific Types
  //============================================================================

  /** Dimension values (interval endpoints and variables) */
  sealed trait Dim
  case object I0 extends Dim    // 0 endpoint
  case object I1 extends Dim    // 1 endpoint
  case class IVar(idx: Int) extends Dim  // dimension variable

  /** Cofibrations (face formulas) */
  sealed trait Cof
  case object CTop extends Cof                    // ⊤ (always true)
  case object CBot extends Cof                    // ⊥ (always false)
  case class CEq(r: Dim, s: Dim) extends Cof      // r = s
  case class CConj(phi: Cof, psi: Cof) extends Cof // φ ∧ ψ
  case class CDisj(phi: Cof, psi: Cof) extends Cof // φ ∨ ψ

  /** Universe levels */
  sealed trait Level
  case object LZero extends Level
  case class LSuc(l: Level) extends Level
  case class LMax(l1: Level, l2: Level) extends Level
  case class LVar(idx: Int) extends Level

  /** Tube element: (cofibration, partial element) */
  case class Tube(cof: Term, element: Term)

  //============================================================================
  // De Bruijn Index Operations
  //============================================================================

  /** Shift (weaken) a term: increment free variables >= cutoff by amount */
  def shift(cutoff: Int, amount: Int, t: Term): Term = t match {
    case Con("ix", List(Lit(n))) =>
      val idx = n.toInt
      if (idx >= cutoff) Con("ix", List(Lit((idx + amount).toString)))
      else t
    case Con("lam", List(body)) =>
      Con("lam", List(shift(cutoff + 1, amount, body)))
    case Con("pi", List(dom, cod)) =>
      Con("pi", List(shift(cutoff, amount, dom), shift(cutoff + 1, amount, cod)))
    case Con("sigma", List(fst, snd)) =>
      Con("sigma", List(shift(cutoff, amount, fst), shift(cutoff + 1, amount, snd)))
    case Con("letE", List(ty, value, body)) =>
      Con("letE", List(shift(cutoff, amount, ty), shift(cutoff, amount, value), shift(cutoff + 1, amount, body)))
    case Con("plam", List(body)) =>
      Con("plam", List(shift(cutoff + 1, amount, body)))
    case Con(name, args) =>
      Con(name, args.map(shift(cutoff, amount, _)))
    case _ => t
  }

  /** Substitute: replace variable at index with term, adjusting indices */
  def subst(idx: Int, replacement: Term, t: Term): Term = t match {
    case Con("ix", List(Lit(n))) =>
      val i = n.toInt
      if (i == idx) replacement
      else if (i > idx) Con("ix", List(Lit((i - 1).toString)))
      else t
    case Con("lam", List(body)) =>
      Con("lam", List(subst(idx + 1, shift(0, 1, replacement), body)))
    case Con("pi", List(dom, cod)) =>
      Con("pi", List(subst(idx, replacement, dom), subst(idx + 1, shift(0, 1, replacement), cod)))
    case Con("sigma", List(fst, snd)) =>
      Con("sigma", List(subst(idx, replacement, fst), subst(idx + 1, shift(0, 1, replacement), snd)))
    case Con("letE", List(ty, value, body)) =>
      Con("letE", List(subst(idx, replacement, ty), subst(idx, replacement, value), 
                       subst(idx + 1, shift(0, 1, replacement), body)))
    case Con("plam", List(body)) =>
      Con("plam", List(subst(idx + 1, shift(0, 1, replacement), body)))
    case Con(name, args) =>
      Con(name, args.map(subst(idx, replacement, _)))
    case _ => t
  }

  /** Substitute dimension in a term */
  def substDim(idx: Int, dim: Term, t: Term): Term = t match {
    case Con("dimVar", List(Lit(n))) =>
      val i = n.toInt
      if (i == idx) dim else t
    case Con("plam", List(body)) =>
      Con("plam", List(substDim(idx + 1, dim, body)))
    case Con(name, args) =>
      Con(name, args.map(substDim(idx, dim, _)))
    case _ => t
  }

  //============================================================================
  // Cofibration Evaluation
  //============================================================================

  /** Check if a cofibration is satisfied (true) */
  def evalCof(phi: Term): Boolean = phi match {
    case Con("cof_top", Nil) => true
    case Con("cof_bot", Nil) => false
    case Con("cof_eq", List(r, s)) => r == s
    case Con("cof_and", List(phi1, phi2)) => evalCof(phi1) && evalCof(phi2)
    case Con("cof_or", List(phi1, phi2)) => evalCof(phi1) || evalCof(phi2)
    case _ => false
  }

  /** Simplify cofibration */
  def simplifyCof(phi: Term): Term = phi match {
    case Con("cof_eq", List(r, s)) if r == s => Con("cof_top", Nil)
    case Con("cof_eq", List(Con("dim0", Nil), Con("dim1", Nil))) => Con("cof_bot", Nil)
    case Con("cof_eq", List(Con("dim1", Nil), Con("dim0", Nil))) => Con("cof_bot", Nil)
    case Con("cof_and", List(Con("cof_top", Nil), psi)) => simplifyCof(psi)
    case Con("cof_and", List(psi, Con("cof_top", Nil))) => simplifyCof(psi)
    case Con("cof_and", List(Con("cof_bot", Nil), _)) => Con("cof_bot", Nil)
    case Con("cof_and", List(_, Con("cof_bot", Nil))) => Con("cof_bot", Nil)
    case Con("cof_or", List(Con("cof_top", Nil), _)) => Con("cof_top", Nil)
    case Con("cof_or", List(_, Con("cof_top", Nil))) => Con("cof_top", Nil)
    case Con("cof_or", List(Con("cof_bot", Nil), psi)) => simplifyCof(psi)
    case Con("cof_or", List(psi, Con("cof_bot", Nil))) => simplifyCof(psi)
    case _ => phi
  }

  //============================================================================
  // Level Operations
  //============================================================================

  /** Simplify level expressions */
  def simplifyLevel(l: Term): Term = l match {
    case Con("lmax", List(l1, l2)) =>
      val l1p = simplifyLevel(l1)
      val l2p = simplifyLevel(l2)
      if (l1p == l2p) l1p
      else (l1p, l2p) match {
        case (Con("lzero", Nil), _) => l2p
        case (_, Con("lzero", Nil)) => l1p
        case (Con("lsuc", List(a)), Con("lsuc", List(b))) =>
          Con("lsuc", List(simplifyLevel(Con("lmax", List(a, b)))))
        case _ => Con("lmax", List(l1p, l2p))
      }
    case _ => l
  }

  //============================================================================
  // Kan Operations
  //============================================================================

  /** Coercion along a line of types */
  def coe(r: Term, s: Term, ty: Term, tm: Term): Term =
    if (r == s) tm
    else Con("coe", List(r, s, ty, tm))

  /** Homogeneous composition */
  def hcom(r: Term, s: Term, ty: Term, phi: Term, cap: Term): Term =
    if (r == s) cap
    else if (evalCof(phi)) cap
    else Con("hcom", List(r, s, ty, phi, cap))

  /** V-in: introduction for V-types */
  def vin(r: Term, a: Term, b: Term): Term = r match {
    case Con("dim0", Nil) => a
    case Con("dim1", Nil) => b
    case _ => Con("vin", List(r, a, b))
  }

  //============================================================================
  // Normalization Engine
  //============================================================================

  /** Pattern matching for rules */
  def matchPattern(pattern: Term, term: Term): Option[Map[String, Term]] =
    matchInner(pattern, term, Map.empty)

  private def matchInner(pattern: Term, term: Term, bindings: Map[String, Term]): Option[Map[String, Term]] =
    (pattern, term) match {
      case (Var(name), _) =>
        bindings.get(name) match {
          case Some(existing) => if (existing == term) Some(bindings) else None
          case None => Some(bindings + (name -> term))
        }
      case (Lit(p), Lit(t)) if p == t => Some(bindings)
      case (Con(pname, pargs), Con(tname, targs)) if pname == tname && pargs.length == targs.length =>
        pargs.zip(targs).foldLeft(Option(bindings)) { case (accOpt, (p, t)) =>
          accOpt.flatMap(acc => matchInner(p, t, acc))
        }
      case _ => None
    }

  /** Substitute bindings into a template */
  def substitute(bindings: Map[String, Term], template: Term): Term = template match {
    case Var(name) => bindings.getOrElse(name, template)
    case Con(name, args) => Con(name, args.map(substitute(bindings, _)))
    case _ => template
  }

  /** One step of reduction */
  def step(rules: List[(Term, Term)], t: Term): Option[Term] = t match {
    // β-reduction
    case Con("app", List(Con("lam", List(body)), arg)) =>
      Some(subst(0, arg, body))
    case Con("fst", List(Con("pair", List(a, _)))) =>
      Some(a)
    case Con("snd", List(Con("pair", List(_, b)))) =>
      Some(b)
    case Con("letE", List(_, value, body)) =>
      Some(subst(0, value, body))
    case Con("papp", List(Con("plam", List(body)), r)) =>
      Some(substDim(0, r, body))
    case Con("papp", List(Con("refl", List(a)), _)) =>
      Some(a)
    
    // Kan operations
    case Con("coe", List(r, s, _, tm)) if r == s =>
      Some(tm)
    case Con("hcom", List(r, s, _, _, cap)) if r == s =>
      Some(cap)
    
    // V-types
    case Con("vin", List(Con("dim0", Nil), a, _)) => Some(a)
    case Con("vin", List(Con("dim1", Nil), _, b)) => Some(b)
    
    // Cofibration simplification
    case c @ Con("cof_eq", _) =>
      val simplified = simplifyCof(c)
      if (simplified != c) Some(simplified) else None
    case c @ Con("cof_and", _) =>
      val simplified = simplifyCof(c)
      if (simplified != c) Some(simplified) else None
    case c @ Con("cof_or", _) =>
      val simplified = simplifyCof(c)
      if (simplified != c) Some(simplified) else None
    
    // Level simplification
    case l @ Con("lmax", _) =>
      val simplified = simplifyLevel(l)
      if (simplified != l) Some(simplified) else None
    
    // Circle
    case Con("loop", List(Con("dim0", Nil))) => Some(Con("base", Nil))
    case Con("loop", List(Con("dim1", Nil))) => Some(Con("base", Nil))
    case Con("circleElim", List(_, b, _, Con("base", Nil))) => Some(b)
    
    // Natural numbers
    case Con("natElim", List(_, z, _, Con("zero", Nil))) => Some(z)
    case Con("natElim", List(p, z, s, Con("suc", List(n)))) =>
      val rec = Con("natElim", List(p, z, s, n))
      Some(Con("app", List(Con("app", List(s, n)), rec)))
    
    // Subtypes
    case Con("subOut", List(Con("subIn", List(e)))) => Some(e)
    
    // User rules
    case _ =>
      rules.collectFirst {
        case (lhs, rhs) if matchPattern(lhs, t).isDefined =>
          substitute(matchPattern(lhs, t).get, rhs)
      }
  }

  /** Normalize with fuel limit */
  def normalize(fuel: Int, rules: List[(Term, Term)], t: Term): Term = {
    if (fuel <= 0) t
    else step(rules, t) match {
      case Some(tp) => normalize(fuel - 1, rules, tp)
      case None => t match {
        case Con(name, args) =>
          val argsNew = args.map(normalize(fuel, rules, _))
          if (argsNew == args) t else Con(name, argsNew)
        case _ => t
      }
    }
  }

  /** Check if two terms are convertible */
  def conv(rules: List[(Term, Term)], fuel: Int, t1: Term, t2: Term): Boolean = {
    val n1 = normalize(fuel, rules, t1)
    val n2 = normalize(fuel, rules, t2)
    n1 == n2
  }

  //============================================================================
  // Arithmetic Builtins
  //============================================================================

  def add(a: Int, b: Int): Int = a + b
  def sub(a: Int, b: Int): Int = a - b
  def gt(a: Int, b: Int): Boolean = a > b
  def geq(a: Int, b: Int): Boolean = a >= b
}
