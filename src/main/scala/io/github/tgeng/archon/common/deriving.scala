package io.github.tgeng.archon.common

import scala.deriving.*
import scala.compiletime.*

type K1[F[_]] = Mirror { type MirroredType[X] = F[X] ; type MirroredElemTypes[_] <: Tuple }
type K1Sum[F[_]] = Mirror.Sum { type MirroredType[X] = F[X] ; type MirroredElemTypes[_] <: Tuple }
type K1Product[F[_]] = Mirror.Product { type MirroredType[X] = F[X] ; type MirroredElemTypes[_] <: Tuple }

type LiftP[F[_[+_]], T <: [X] =>> Tuple] <: Tuple =
  T[Any] match
    case a *: _ => F[[X] =>> Tuple.Head[T[X]]] *: LiftP[F, [X] =>> Tuple.Tail[T[X]]]
    case _ => EmptyTuple

inline def summonKindAsList[T <: Tuple, K[_[+_]]]: List[K[[X]=>> Any]] =
  inline erasedValue[T] match
    case _: EmptyTuple => Nil
    case _: (t *: ts) =>
      summonInline[t].asInstanceOf[K[[X]=>>Any]] :: summonKindAsList[ts, K]
