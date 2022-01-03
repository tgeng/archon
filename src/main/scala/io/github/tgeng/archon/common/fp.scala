package io.github.tgeng.archon.common

import scala.collection.IterableFactory
import scala.deriving.Mirror

type Const = [A] =>> [T] =>> A
type Id[T] = T

trait Recursive[T]:
  def transform(recursiveT: =>Recursive[T], isT: Any => Boolean, t: T, f: T => Option[T]): T

object Recursive:
  import scala.deriving.*
  import scala.compiletime.*

  inline def transform[T](t: T, f: T => Option[T])(using r: Recursive[T]): T =
    def isT(a: Any) = a.isInstanceOf[T]
    r.transform(summonInline[Recursive[T]], isT, t, f)

  inline given derived[T](using m: Mirror.Of[T]) : Recursive[T] =
    lazy val recursiveIfPossible = summonAll[T, LiftK0[Recursive, m.MirroredElemTypes]]
    inline m match
      case s: Mirror.SumOf[T] => recursiveSum(s, recursiveIfPossible)
      case p: Mirror.ProductOf[T] => recursiveProduct(p)

  def recursiveSum[T](
    s: Mirror.SumOf[T],
    recursives: => List[Option[Recursive[T]]]
  ): Recursive[T] = new Recursive[T]:
    override def transform(recursiveT: =>Recursive[T], isT: Any => Boolean, t: T, f: T => Option[T]): T =
      f(t) match
        case Some(t) => t
        case None => recursives(s.ordinal(t)) match
          case Some(r) => r.transform(recursiveT, isT, t, f)
          case None => t

  def recursiveProduct[T](
    p: Mirror.ProductOf[T]
  ): Recursive[T] = new Recursive[T]:
    override def transform(recursiveT: =>Recursive[T], isT: Any => Boolean, t: T, f: T => Option[T]): T =
      val transformed = t.asInstanceOf[Product].productIterator.map {
        case t if isT(t) => recursiveT.transform(recursiveT, isT, t.asInstanceOf[T], f)
        case e => e
      }
      p.fromProduct(Tuple.fromArray(transformed.toArray))

  inline def summonAll[T, Tu <: Tuple] : List[Option[Recursive[T]]] =
    inline erasedValue[Tu] match
      case _: EmptyTuple => Nil
      case _: (t *: ts) => summonFrom {
        case r: t => Some(r.asInstanceOf[Recursive[T]])
        case _ => None
      } :: summonAll[T, ts]


trait Functor[F[_]]:
  def map[T, S](f: F[T], g: T => S): F[S]

object Functor:
  def map[F[_], T, S](f: F[T], g: T => S)(using tc: Functor[F]): F[S] = tc.map(f, g)

  inline given derived[F[_]](using m: K1[F]): Functor[F] =
    lazy val functors = summonK1AsList[LiftK1[Functor, m.MirroredElemTypes], Functor]
    inline m match
      case s: K1Sum[F] => functorCoproduct(s,  functors)
      case p: K1Product[F] => functorProduct(p, functors)

  private def functorCoproduct[F[_]](s: K1Sum[F], functors: => List[Functor[[X]=>> Any]]): Functor[F] =
    new Functor[F]:
      override def map[A, B](fa: F[A], f: A => B): F[B] =
        val ord = s.ordinal(fa.asInstanceOf[s.MirroredMonoType])
        functors(ord).map(fa, f).asInstanceOf[F[B]]

  private def functorProduct[F[_], T](p: K1Product[F], functors: => List[Functor[[X] =>> Any]]): Functor[F] =
    new Functor[F]:
      override def map[A, B](fa: F[A], f: A => B): F[B] =
        val mapped = fa.asInstanceOf[Product].productIterator.zip(functors.iterator).map{
          (fa, F) =>
            F.map(fa, f)
        }
        p.fromProduct(Tuple.fromArray(mapped.toArray)).asInstanceOf[F[B]]

  given Functor[Set] with
    override def map[T, S](a: Set[T], g: T => S): Set[S] = a.map(g)

  given Functor[List] with
    override def map[T, S](a: List[T], g: T => S): List[S] = a.map(g)

  given Functor[Option] with
    override def map[T, S](a: Option[T], g: T => S): Option[S] = a.map(g)

  given [E]: Functor[Either[E, *]] with
    override def map[A, B](ea: Either[E, A], f: A => B): Either[E, B] = ea.map(f)

  given [T]: Functor[T => *] with
    override def map[A, B](g: T => A, f: A => B): T => B = t => f(g(t))

  given Functor[Id] with
    override def map[A, B](a: A, f: A => B): B = f(a)

  given [T]: Functor[Const[T]] with
    override def map[A, B](t: T, f: A => B) : T = t

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
