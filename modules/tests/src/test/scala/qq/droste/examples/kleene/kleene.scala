package qq.droste
package examples

import qq.droste.data._
import qq.droste.data.prelude._
import qq.droste.macros.deriveTraverse
import cats.implicits._

import cats.Order
import cats.implicits._

@deriveTraverse
sealed abstract class KleeneF[+A] extends Product with Serializable

object KleeneF {
  final case class Plus[+A](l: A, r: A) extends KleeneF[A]
  final case class Times[+A](l: A, r: A) extends KleeneF[A]
  final case class Star[+A](value: A) extends KleeneF[A]
  case object Zero extends KleeneF[Nothing]
  case object One extends KleeneF[Nothing]
}

sealed abstract class Match[+A] extends Product with Serializable

object Match {
  final case class Literal[+A](value: A) extends Match[A]

  /** An inclusive range */
  final case class Range[+A](lower: A, upper: A) extends Match[A]
  case object Wildcard extends Match[Nothing]
  case object EOF extends Match[Nothing]
}

object regex {
  type Free[F[_], A] = Mu[CoattrF[F, A, ?]]
  type RegexF[A, B] = CoattrF[KleeneF, Match[A], B]
  type Regex[A] = Free[KleeneF, Match[A]]
  type Consume[A] = Stream[A] => Stream[Stream[A]]

  private def checkHead[A](f: A => Boolean): Consume[A] = {
    case h #:: t if (f(h)) => Stream(t)
    case _ => Stream.empty
  }

  def checkMatch[A:Order](m: Match[A]): Consume[A] = m match {
    case Match.Literal(expected) => checkHead(_ === expected)
    case Match.Wildcard => checkHead(_ => true)
    case Match.Range(l, r) => checkHead(a => a >= l && a <= r)
    case Match.EOF => sa => if (sa.isEmpty) Stream(sa) else Stream.empty
  }

  private def repeatApply[A](f: Stream[A] => Stream[Stream[A]]): Stream[A] => Stream[Stream[A]] =
    sa => Stream.cons(sa, f(sa).flatMap(repeatApply(f)))

  def kleeneFStreamAlgebra[A]: Algebra[KleeneF, Stream[A] => Stream[Stream[A]]] = Algebra{
    case KleeneF.Plus(l, r) => sa => l(sa) #::: r(sa)
    case KleeneF.Times(l, r) => sa => l(sa).flatMap(r)
    case KleeneF.Star(f) => repeatApply(f)
    case KleeneF.Zero => _ => Stream.empty
    case KleeneF.One => Stream(_)
  }

  // TODO is there a simpler way to wrap things in Mu?
  def toMu[A]: Fix[CoattrF[KleeneF, A, ?]] => Mu[CoattrF[KleeneF, A, ?]] = scheme.hylo(
    Mu.algebra[CoattrF[KleeneF, A, ?]],
    Fix.coalgebra[CoattrF[KleeneF, A, ?]])

  def literal[A](value: A): Regex[A] = toMu(Fix(CoattrF.pure(Match.Literal(value))))

  def range[A](l: A, r: A): Regex[A] = toMu(Fix(CoattrF.pure(Match.Range(l, r))))

  def or[A](l: Regex[A], r: Regex[A]): Regex[A] = Mu(CoattrF.roll(KleeneF.Plus(l, r)))

  def andThen[A](l: Regex[A], r: Regex[A]): Regex[A] = Mu(CoattrF.roll(KleeneF.Times(l, r)))

  def star[A](value: Regex[A]): Regex[A] = Mu(CoattrF.roll(KleeneF.Star(value)))

  def wildcard[A]: Regex[A] = toMu(Fix(CoattrF.pure(Match.Wildcard)))

  def eof[A]: Regex[A] = toMu(Fix(CoattrF.pure(Match.EOF)))

  def consume[A:Order]: Algebra[CoattrF[KleeneF, Match[A], ?], Consume[A]] =
    Algebra[CoattrF[KleeneF, Match[A], ?], Consume[A]]{
      CoattrF.un(_) match {
        case Left(ma) => checkMatch(ma)
        case Right(kf) => kleeneFStreamAlgebra(kf)
      }
    }

  def stringMatcher(r: Regex[Char]): String => Boolean = {
    val m = r(consume)
    s => m(s.toStream).exists(_.isEmpty)
  }
}

import org.scalacheck.Properties

final class RegexTests extends Properties("Regex"){
  import regex._

  property("literal match") = stringMatcher(literal('b'))("b")

  property("literal non-match") = !stringMatcher(literal('b'))("a")

  property("literal with trailing") = !stringMatcher(literal('b'))("ba")

  property("or left match") = stringMatcher(or(literal('b'), literal('c')))("b")

  property("or left match with trailing") = !stringMatcher(or(literal('b'), literal('c')))("bc")

  property("or right match") = stringMatcher(or(literal('b'), literal('c')))("c")

  property("or right match with trailing") = !stringMatcher(or(literal('b'), literal('c')))("cb")

  property("or no match") = !stringMatcher(or(literal('b'), literal('c')))("a")

  property("or no match with trailing") = !stringMatcher(or(literal('b'), literal('c')))("ad")

  property("andThen match") = stringMatcher(andThen(literal('b'), literal('c')))("bc")

  property("andThen left only") = !stringMatcher(andThen(literal('b'), literal('c')))("bd")

  property("andThen right only") = !stringMatcher(andThen(literal('b'), literal('c')))("ac")

  property("andThen with trailing") = !stringMatcher(andThen(literal('b'), literal('c')))("bcd")

  property("star zero") = stringMatcher(star(literal('b')))("")

  property("star one") = stringMatcher(star(literal('b')))("b")

  property("star two") = stringMatcher(star(literal('b')))("bb")

  property("star three") = stringMatcher(star(or(literal('b'), literal('c'))))("bcb")

  property("star trailing") = !stringMatcher(star(or(literal('b'), literal('c'))))("bcbd")

  property("wildcard") = stringMatcher(wildcard[Char])("b")

  property("wildcard trailing") = !stringMatcher(wildcard[Char])("bc")

  property("wildcard empty") = !stringMatcher(wildcard[Char])("")

  property("eof empty") = stringMatcher(eof[Char])("")

  property("eof one") = !stringMatcher(eof[Char])("a")

  property("eof two") = !stringMatcher(eof[Char])("ab")

  property("inside range") = stringMatcher(range('a', 'c'))("b")

  property("left range") = stringMatcher(range('a', 'c'))("a")

  property("right range") = stringMatcher(range('a', 'c'))("c")

  property("outside range") = !stringMatcher(range('a', 'c'))("d")
}
