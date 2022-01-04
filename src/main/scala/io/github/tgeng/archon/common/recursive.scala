package io.github.tgeng.archon.common

trait Recursive[T]:
  def transform(recursiveT: =>Recursive[T], isT: Any => Boolean, t: T, f: T => Option[T]): T

object Recursive:
  import scala.deriving.*
  import scala.compiletime.*

  inline def transform[T](t: T, f: T => Option[T])(using r: Recursive[T]): T =
    def isT(a: Any) = a.isInstanceOf[T]
    r.transform(summonInline[Recursive[T]], isT, t, f)

  inline given derived[T](using m: Mirror.Of[T]) : Recursive[T] =
    lazy val recursiveIfPossible = summonAll[T, LiftK0[Recursive, m.MirroredElemTypes], Recursive[T]]
    lazy val functorsIfPossible = summonAll[T, ExtractFunctors[m.MirroredElemTypes], Functor[?]]
    inline m match
      case s: Mirror.SumOf[T] => recursiveSum(s, recursiveIfPossible)
      case p: Mirror.ProductOf[T] => recursiveProduct(p, functorsIfPossible)

  def recursiveSum[T](
                       s: Mirror.SumOf[T],
                       recursives: =>List[Option[Recursive[T]]]
                     ): Recursive[T] = new Recursive[T]:
    override def transform(recursiveT: =>Recursive[T], isT: Any => Boolean, t: T, f: T => Option[T]): T =
      f(t) match
        case Some(t) => t
        case None => recursives(s.ordinal(t)) match
          case Some(r) => r.transform(recursiveT, isT, t, f)
          case None => t

  def recursiveProduct[T](
                           p: Mirror.ProductOf[T],
                           functors: =>List[Option[Functor[?]]]
                         ): Recursive[T] = new Recursive[T]:
    override def transform(recursiveT: =>Recursive[T], isT: Any => Boolean, t: T, f: T => Option[T]): T =
      val transformed = t.asInstanceOf[Product].productIterator.zip(functors).map {
        case (t, _) if isT(t) => recursiveT.transform(recursiveT, isT, t.asInstanceOf[T], f)
        case (functorInstance, Some(functor)) => functor.mapAny(
          functorInstance,
          t => if isT(t) then recursiveT.transform(recursiveT, isT, t.asInstanceOf[T], f) else t
        )
        case (e, _) => e
      }
      p.fromProduct(Tuple.fromArray(transformed.toArray))

  inline def summonAll[T, Tu <: Tuple, Tc] : List[Option[Tc]] =
    inline erasedValue[Tu] match
      case _: EmptyTuple => Nil
      case _: (t *: ts) => summonFrom {
        case r: t => Some(r.asInstanceOf[Tc])
        case _ => None
      } :: summonAll[T, ts, Tc]

  type ExtractFunctors[Tu <: Tuple] <: Tuple =
    Tu match
      case List[_] *: ts => Functor[List] *: ExtractFunctors[ts]
      case Option[_] *: ts => Functor[Option] *: ExtractFunctors[ts]
      case Set[_] *: ts => Functor[Set] *: ExtractFunctors[ts]
      case Either[l, _] *: ts => Functor[Either[l, *]] *: ExtractFunctors[ts]
      case (a => _) *: ts => Functor[a => *] *: ExtractFunctors[ts]
      case (a, _) *: ts => Functor[(a, *)] *: ExtractFunctors[ts]
      case _ *: ts => Nothing *: ExtractFunctors[ts]
      case _ => EmptyTuple
