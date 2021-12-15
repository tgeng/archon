package io.github.tgeng.archon.common

import scala.collection.IterableFactory

type Id[T] = T

trait Functor[F[+_]]:
  def map[T, S](f: F[T], g: T => S): F[S]

trait Applicative[A[+_]] extends Functor[A] :
  def pure[S](s: S): A[S]

  def starApply[T, S](a: A[T], f: =>A[T => S]): A[S]

trait Monad[M[+_]] extends Applicative[M] :
  def flatMap[T, S](m: M[T], f: T => M[S]): M[S] = flatten(map(m, f))
  def flatten[T](m: M[M[T]]) : M[T] = flatMap(m, t => t)

  override def starApply[T, S](m: M[T], f: =>M[T => S]): M[S] = flatMap(m, t => map(f, f => f(t)))

trait Alternative[A[+_]] extends Applicative[A] :
  def empty[S]: A[S]

  def or[T](a: A[T], b: => A[T]): A[T]

trait MonadPlus[M[+_]] extends Monad[M] with Alternative[M]

extension[T, F[+_]] (using env: Functor[F])(f: F[T])
  def map[S](g: T => S): F[S] = env.map(f, g)

extension[T, A[+_]] (using env: Applicative[A])(a: A[T])
  infix def <*>[S](f: =>A[T => S]): A[S] = env.starApply(a, f)

extension[T, M[+_]] (using env: Monad[M])(m: M[T])
  def flatMap[S](f: T => M[S]): M[S] = env.flatMap(m, f)

extension[T, M[+_]] (using env: Monad[M])(m: M[M[T]])
  def flatten = env.flatten(m)

extension[T, A[+_]] (using env: Alternative[A])(a: A[T])
  infix def <|>(b: => A[T]): A[T] = env.or(a, b)

trait Distributor[M1[_], M2[_]]:
  def distribute[T](m: M1[M2[T]]): M2[M1[T]]

object ListGivens {
  given MonadPlusList: MonadPlus[List] with
    override def map[T, S](a: List[T], g: T => S): List[S] = a.map(g)

    override def pure[T](t: T): List[T] = List(t)

    override def flatMap[T, S](a: List[T], g: T => List[S]): List[S] = a.flatMap(g)

    override def empty[S]: List[S] = List.empty

    override def or[T](a: List[T], p: => List[T]): List[T] = a ++ p
}

object OptionGivens {
  given MonadPlusOption: MonadPlus[Option] with
    override def map[T, S](a: Option[T], g: T => S): Option[S] = a.map(g)

    override def pure[T](t: T): Option[T] = Option(t)

    override def flatMap[T, S](a: Option[T], g: T => Option[S]): Option[S] = a.flatMap(g)

    override def empty[S]: Option[S] = Option.empty

    override def or[T](a: Option[T], p: => Option[T]): Option[T] = a.orElse(p)
}