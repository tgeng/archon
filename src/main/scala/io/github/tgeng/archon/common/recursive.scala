package io.github.tgeng.archon.common

import scala.compiletime.*
import scala.deriving.*

trait Recursive[T]:
  def transform[P >: T](recursiveParent: =>Recursive[P], isCurrentRecursive: Any => Boolean, t: T, f: P => Option[P]): P

object Recursive:
  inline def transform[T](t: T, f: T => Option[T])(using r: Recursive[T]): T =
    def isCurrentRecursive(a: Any) = a.isInstanceOf[T]
    r.transform(summonInline[Recursive[T]], isCurrentRecursive, t, f)

  inline given derived[T](using m: Mirror.Of[T]) : Recursive[T] =
    inline m match
      case s: Mirror.SumOf[T] =>
        lazy val recursives = summonAllRecursive[m.MirroredElemTypes]
        recursiveSum(s, recursives.asInstanceOf[List[Recursive[T]]])
      case p: Mirror.ProductOf[T] =>
        lazy val functorsIfPossible = summonAllIfPossible[ExtractFunctors[m.MirroredElemTypes], Functor[?]]
        recursiveProduct(p, functorsIfPossible)

  def recursiveSum[T](
    s: Mirror.SumOf[T],
    recursives: => List[Recursive[T]]
  ): Recursive[T] = new Recursive[T] :
    override def transform[P >: T](recursiveParent: => Recursive[P], isCurrentRecursive: Any => Boolean, t: T, f: P => Option[P]): P =
      f(t) match
        case Some(t) => t
        case None => recursives(s.ordinal(t)).transform(recursiveParent, isCurrentRecursive, t, f)

  def recursiveProduct[T](
    p: Mirror.ProductOf[T],
    functors: => List[Option[Functor[?]]]
  ): Recursive[T] = new Recursive[T] :
    override def transform[P >: T](recursiveParent: => Recursive[P], isCurrentRecursive: Any => Boolean, t: T, f: P => Option[P]): P =
      val transformed = t.asInstanceOf[Product].productIterator.zip(functors).map {
        case (t, _) if isCurrentRecursive(t) => recursiveParent.transform(recursiveParent, isCurrentRecursive, t.asInstanceOf[T], f)
        case (functorInstance, Some(functor)) => functor.mapAny(
          functorInstance,
          t => if isCurrentRecursive(t) then recursiveParent.transform(recursiveParent, isCurrentRecursive, t.asInstanceOf[T], f) else t
        )
        case (e, _) => e
      }
      p.fromProduct(Tuple.fromArray(transformed.toArray))

  private inline def summonAllRecursive[T <: Tuple] : List[Recursive[?]] =
    inline erasedValue[T] match
      case _: EmptyTuple => Nil
      case _: (t *: ts) => summonInline[Recursive[t]] :: summonAllRecursive[ts]

private inline def summonAllIfPossible[Tu <: Tuple, Tc] : List[Option[Tc]] =
  inline erasedValue[Tu] match
    case _: EmptyTuple => Nil
    case _: (t *: ts) => summonFrom {
      case r: t => Some(r.asInstanceOf[Tc])
      case _ => None
    } :: summonAllIfPossible[ts, Tc]

private type ExtractFunctors[Tu <: Tuple] <: Tuple =
  Tu match
    case List[_] *: ts => Functor[List] *: ExtractFunctors[ts]
    case Option[_] *: ts => Functor[Option] *: ExtractFunctors[ts]
    case Set[_] *: ts => Functor[Set] *: ExtractFunctors[ts]
    case Either[l, _] *: ts => Functor[Either[l, *]] *: ExtractFunctors[ts]
    case (a => _) *: ts => Functor[a => *] *: ExtractFunctors[ts]
    case (a, _) *: ts => Functor[(a, *)] *: ExtractFunctors[ts]
    case _ *: ts => Nothing *: ExtractFunctors[ts]
    case _ => EmptyTuple
