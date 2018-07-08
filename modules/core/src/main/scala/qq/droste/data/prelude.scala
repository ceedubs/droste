package qq.droste
package data

import cats.Applicative
import cats.Functor
import cats.Traverse

import cats.syntax.functor._
import cats.syntax.traverse._

import util.DefaultTraverse

package object prelude extends DataPrelude
import prelude._

private[droste] trait DataPrelude 
    extends DataInstances
    with DataOps

private[data] sealed trait DataOps {
  implicit def toCofreeOps[F[_], A](cofree: Cofree[F, A]): Cofree.Ops[F, A] =
    new Cofree.Ops[F, A](cofree)

  implicit def toEnvTOps[E, W[_], A](envT: EnvT[E, W, A]): EnvT.Ops[E, W, A] =
    new EnvT.Ops[E, W, A](envT)
}

private[data] sealed trait DataInstances extends DataInstances0 {
  implicit def drosteEnvTTraverse[E, W[_]: Traverse]: Traverse[EnvT[E, W, ?]] =
    new EnvTTraverse[E, W]
}

private[data] sealed trait DataInstances0 {
  implicit def drosteEnvTFunctor[E, W[_]: Functor]: Functor[EnvT[E, W, ?]] =
    new EnvTFunctor[E, W]
}

private[data] class EnvTFunctor[E, W[_]: Functor] extends Functor[EnvT[E, W, ?]] {
  def map[A, B](fa: EnvT[E, W, A])(f: A => B): EnvT[E, W, B] =
    EnvT(fa.ask, fa.lower.map(f))
}

private[data] final class EnvTTraverse[E, W[_]: Traverse]
    extends EnvTFunctor[E, W]
    with DefaultTraverse[EnvT[E, W, ?]]
{
  def traverse[G[_]: Applicative, A, B](fa: EnvT[E, W, A])(f: A => G[B]): G[EnvT[E, W, B]] =
    fa.lower.traverse(f).map(EnvT(fa.ask, _))
}
