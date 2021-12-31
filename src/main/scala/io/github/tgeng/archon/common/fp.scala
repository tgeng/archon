package io.github.tgeng.archon.common

import scala.collection.IterableFactory

type Id[T] = T

trait Functor[F[_]]:
  def map[T, S](f: F[T], g: T => S): F[S]

object Functor:
  def map[F[_], T, S](f: F[T], g: T => S)(using tc: Functor[F]): F[S] = tc.map(f, g)

  given Functor[List] with
    override def map[T, S](a: List[T], g: T => S): List[S] = a.map(g)

  given Functor[Option] with
    override def map[T, S](a: Option[T], g: T => S): Option[S] = a.map(g)

trait Applicative[A[_] : Functor]:
  def pure[S](s: S): A[S]

  def starApply[T, S](f: A[T => S], a: A[T]): A[S]


object Applicative:

  def pure[A[_], S](s: S)(using tc: Applicative[A]): A[S] = tc.pure(s)

  def starApply[A[_], T, S](f: A[T => S], a: A[T])(using tc: Applicative[A]): A[S] = tc.starApply(f, a)

  given Applicative[List] with
    override def pure[T](t: T): List[T] = List(t)

    override def starApply[T, S](f: List[T => S], a: List[T]): List[S] = f.flatMap(f => a.map(f))

  given Applicative[Option] with
    override def pure[T](t: T): Option[T] = Some(t)

    override def starApply[T, S](f: Option[T => S], a: Option[T]): Option[S] = f.flatMap(f => a.map(f))

trait Monad[M[_] : Applicative : Functor]:
  def flatMap[T, S](m: M[T], f: T => M[S]): M[S] = flatten(Functor.map(m, f))
  def flatten[T](m: M[M[T]]) : M[T] = flatMap(m, t => t)

object Monad:
  def flatMap[M[_] : Functor, T, S](m: M[T], f: T => M[S])(using tc: Monad[M]): M[S] = tc.flatten(Functor.map(m, f))
  def flatten[M[_], T](m: M[M[T]])(using tc: Monad[M]) : M[T] = tc.flatMap(m, t => t)

  given Monad[List] with
    override def flatMap[T, S](a: List[T], g: T => List[S]): List[S] = a.flatMap(g)

  given Monad[Option] with
    override def flatMap[T, S](a: Option[T], g: T => Option[S]): Option[S] = a.flatMap(g)

trait Alternative[A[_]: Applicative] :
  def empty[S]: A[S]

  def or[T](a: A[T], b: => A[T]): A[T]

object Alternative:
  def empty[A[_], S](using tc: Alternative[A]): A[S] = tc.empty

  def or[A[_], T](a: A[T], b: => A[T])(using tc: Alternative[A]): A[T] = tc.or(a, b)

  given Alternative[List] with
    override def empty[S]: List[S] = List.empty

    override def or[T](a: List[T], p: => List[T]): List[T] = a ++ p

  given Alternative[Option] with
    override def empty[S]: Option[S] = Option.empty

    override def or[T](a: Option[T], p: => Option[T]): Option[T] = a.orElse(p)
