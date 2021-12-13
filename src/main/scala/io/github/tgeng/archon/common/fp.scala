package io.github.tgeng.archon.common

import scala.collection.IterableFactory

trait Functor[F[_]]:
  extension[T] (f: F[T])
    def map[S](g: T => S): F[S]

trait Applicative[A[_]] extends Functor[A] :
  def pure[S](s: S): A[S]

  extension[T] (a: A[T])
    infix def <*>[S](f: A[T => S]): A[S]

trait Monad[M[_]] extends Applicative[M] :
  extension[T] (m: M[T])
    def flatMap[S](f: T => M[S]): M[S]
    override def <*>[S](f: M[T => S]): M[S] =
      for
        t <- m
        f <- f
      yield
        f(t)

trait Alternative[A[_]] extends Applicative[A] :
  def empty[S] : A[S]
  extension[T] (a: A[T])
    infix def <|>(b: A[T]) : A[T]

trait MonadPlus[M[_]] extends Monad[M] with Alternative[M]

private def mapInternal[T, S](ts: Iterable[T], g: T => S) = ts.map(g)
private def flatMapInternal[T, S](ts: Iterable[T], g: T => Iterable[S]) = ts.flatMap(g)

given[CC[_] <: Iterable[_]] (using factory: IterableFactory[CC]): Monad[CC] with
  def pure[S](s: S): CC[S] = factory.from(Iterable(s))

  extension[T] (m: CC[T])
    def map[S](g: T => S): CC[S] = mapInternal(m, g.asInstanceOf[Any => Any]).asInstanceOf[CC[S]]
    def flatMap[S](f: T => CC[S]): CC[S] = flatMapInternal(m, f.asInstanceOf[Any => CC[Any]]).asInstanceOf[CC[S]]

given IterableFactory[List] = List
given IterableFactory[Set] = Set

given [L]: Monad[[R] =>> Either[L, R]] with
  def pure[R](r: R): Either[L, R] = Right(r)

  extension[R] (e: Either[L, R])
    def map[S](g: R => S) : Either[L, S] = e match
      case Right(r) => Right(g(r))
      case Left(l) => Left(l)

    def flatMap[S](g: R => Either[L, S]) : Either[L, S] = e match
      case Right(r) => g(r)
      case Left(l) => Left(l)

