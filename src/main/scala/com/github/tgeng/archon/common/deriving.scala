package com.github.tgeng.archon.common

import scala.deriving.*
import scala.compiletime.*

type K1[F[_]] = Mirror {
  type MirroredType[X] = F[X]; type MirroredElemTypes[_] <: Tuple
}
type K1Sum[F[_]] = Mirror.Sum {
  type MirroredType[X] = F[X]; type MirroredElemTypes[_] <: Tuple
}
type K1Product[F[_]] = Mirror.Product {
  type MirroredType[X] = F[X]; type MirroredElemTypes[_] <: Tuple
}

type LiftK0[F[_], T <: Tuple] <: Tuple =
  T match
    case a *: _ => F[Tuple.Head[T]] *: LiftK0[F, Tuple.Tail[T]]
    case _      => EmptyTuple

type LiftK1[F[_[+_]], T <: [X] =>> Tuple] <: Tuple =
  T[Any] match
    case a *: _ =>
      F[[X] =>> Tuple.Head[T[X]]] *: LiftK1[F, [X] =>> Tuple.Tail[T[X]]]
    case _ => EmptyTuple

inline def summonK1AsList[T <: Tuple, K[_[+_]]]: List[K[[X] =>> Any]] =
  inline erasedValue[T] match
    case _: EmptyTuple => Nil
    case _: (t *: ts) =>
      summonInline[t].asInstanceOf[K[[X] =>> Any]] :: summonK1AsList[ts, K]

inline def summonK1AsListIfPossible[T <: Tuple, K[_[+_]]]
  : List[Option[K[[X] =>> Any]]] =
  inline erasedValue[T] match
    case _: EmptyTuple => Nil
    case _: (t *: ts) =>
      summonFrom {
        case f: t => Some(f.asInstanceOf[K[[X] =>> Any]])
        case _    => None
      } :: summonK1AsListIfPossible[ts, K]
