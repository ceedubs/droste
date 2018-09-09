package qq.droste
package examples

import qq.droste.data._
import qq.droste.data.prelude._
import cats.implicits._

import cats.{Applicative, Eval, Order, Traverse}
import cats.implicits._

sealed abstract class KleeneF[+A] extends Product with Serializable

object KleeneF {
  final case class Plus[+A](l: A, r: A) extends KleeneF[A]
  final case class Times[+A](l: A, r: A) extends KleeneF[A]
  final case class Star[+A](value: A) extends KleeneF[A]
  case object Zero extends KleeneF[Nothing]
  case object One extends KleeneF[Nothing]

  implicit val traverseKleeneF: Traverse[KleeneF] = new Traverse[KleeneF] {
    def traverse[G[_], A, B](fa: KleeneF[A])(f: A => G[B])(implicit G: Applicative[G]): G[KleeneF[B]] =
      fa match {
        case Plus(l, r) => G.map2(f(l), f(r))((lb, rb) => Plus(lb, rb))
        case Times(l, r) => G.map2(f(l), f(r))((lb, rb) => Times(lb, rb))
        case Star(x) => G.map(f(x))(Star(_))
        case Zero => G.pure(Zero)
        case One => G.pure(One)
      }

    def foldLeft[A, B](fa: KleeneF[A], b: B)(f: (B, A) => B): B = fa match {
        case Plus(l, r) => f(f(b, l), r)
        case Times(l, r) => f(f(b, l), r)
        case Star(x) => f(b, x)
        case Zero => b
        case One => b
    }

    def foldRight[A, B](fa: KleeneF[A], lb: Eval[B])(f: (A, Eval[B]) => Eval[B]): Eval[B] = fa match {
        case Plus(l, r) => f(l, f(r, lb))
        case Times(l, r) => f(l, f(r, lb))
        case Star(x) => f(x, lb)
        case Zero => lb
        case One => lb
    }
  }
}

sealed abstract class Match[+A] extends Product with Serializable

object Match {
  final case class Literal[+A](value: A) extends Match[A]

  /** An inclusive range */
  final case class Range[+A](lower: A, upper: A) extends Match[A]

  case object Wildcard extends Match[Nothing]
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

  /**
   * AKA `+` in regular expressions, but I avoided confusion with `Plus` corresponding to "or".
   */
  def oneOrMore[A](value: Regex[A]): Regex[A] = andThen(value, star(value))

  def star[A](value: Regex[A]): Regex[A] = Mu(CoattrF.roll(KleeneF.Star(value)))

  def wildcard[A]: Regex[A] = toMu(Fix(CoattrF.pure(Match.Wildcard)))

  /**
   * A match on the empty string (this should always succeed and consume no input).
   */
  def empty[A]: Regex[A] = Mu(CoattrF.roll(KleeneF.One))

  def count[A](n: Int, r: Regex[A]): Regex[A] = (1 to n).foldLeft(empty[A])((acc, _) => andThen(acc, r)) 

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

object ScalacheckRegex {
  import org.scalacheck.{Arbitrary, Gen}, Gen.Choose
  import regex._

  def matchGen[A](m: Match[A])(implicit arbA: Arbitrary[A], chooseA: Choose[A]): Gen[A] = m match {
    case Match.Literal(expected) => Gen.const(expected)
    case Match.Wildcard => arbA.arbitrary
    case Match.Range(l, r) => chooseA.choose(l, r)
  }

  def kleeneFStreamAlgebra[A]: Algebra[KleeneF, Gen[Stream[A]]] = Algebra{
    case KleeneF.Plus(l, r) => Gen.oneOf(l, r)
    case KleeneF.Times(l, r) => l.flatMap(ls => r.map(rs => ls ++ rs))
    // TODO ceedubs probably need to do something fancier so we don't get large nested structures
    case KleeneF.Star(g) => Gen.sized(maxSize =>
      for {
        size <- Gen.chooseNum(0, maxSize)
        sa <- g
      } yield Stream.fill(size)(sa).flatten
    )
    case KleeneF.Zero => Gen.fail
    case KleeneF.One => Gen.const(Stream.empty)
  }

  def regexGen[A:Arbitrary:Choose]: Algebra[CoattrF[KleeneF, Match[A], ?], Gen[Stream[A]]] =
    Algebra[CoattrF[KleeneF, Match[A], ?], Gen[Stream[A]]]{
      CoattrF.un(_) match {
        case Left(ma) => matchGen(ma).map(Stream(_))
        case Right(kf) => kleeneFStreamAlgebra(kf)
      }
    }

  def regexStringGen(r: Regex[Char]): Gen[String] = r(regexGen[Char]).map(_.mkString)
}

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

  property("inside range") = stringMatcher(range('a', 'c'))("b")

  property("left range") = stringMatcher(range('a', 'c'))("a")

  property("right range") = stringMatcher(range('a', 'c'))("c")

  property("outside range") = !stringMatcher(range('a', 'c'))("d")

  property("oneOrMore zero") = !stringMatcher(oneOrMore(literal('b')))("")

  property("oneOrMore one") = stringMatcher(oneOrMore(literal('b')))("b")

  property("oneOrMore two") = stringMatcher(oneOrMore(literal('b')))("bb")

  property("oneOrMore three") = stringMatcher(oneOrMore(literal('b')))("bbb")

  property("count zero empty") = stringMatcher(count(0, literal('b')))("")

  property("count zero non-empty") = !stringMatcher(count(0, literal('b')))("b")

  property("count 1 empty") = !stringMatcher(count(1, literal('b')))("")

  property("count 1 match") = stringMatcher(count(1, literal('b')))("b")

  property("count 1 non-match") = !stringMatcher(count(1, literal('b')))("c")

  property("count 2 match") = stringMatcher(count(2, literal('b')))("bb")

  property("count 2 non-match") = !stringMatcher(count(2, literal('b')))("bc")
}

final class ScalacheckRegexTests extends Properties("Regex"){
  import regex._
  import ScalacheckRegex._
  import org.scalacheck.Prop

  property("testing") = {
    val r = andThen(or(literal('a'), star(literal('b'))), literal('c'))
    val matcher = stringMatcher(r)
    Prop.forAll(regexStringGen(r)){ matcher(_) }
  }
}
