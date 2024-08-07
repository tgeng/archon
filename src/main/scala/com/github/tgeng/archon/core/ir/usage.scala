package com.github.tgeng.archon.core.ir

import com.github.tgeng.archon.common.*
import com.github.tgeng.archon.core.ir.Usage.UAff

import scala.annotation.{tailrec, targetName}
import scala.collection.immutable.MultiSet

/** Here we do not do the full generalization that allows user to define custom semirings for
  * grading. Instead, we use a specialized semiring that only accounts for counting usages.
  *
  * Usage forms a join-semilattice bounded by UAny.
  *
  * UAny
  * |   \
  * UAff URel
  * |  \ |
  * U0  U1
  */
enum Usage extends PartiallyOrdered[Usage]:
  case U0, U1, UAff, URel, UAny

  @tailrec
  final infix def +(that: Usage): Usage = (this, that) match
    case (U0, u)                       => u
    case (U1, U1 | UAff | URel | UAny) => URel
    case (UAff, URel)                  => URel
    case (UAff, UAff | UAny)           => UAny
    case (URel, URel | UAny)           => URel
    case (UAny, UAny)                  => UAny
    case (u1, u2)                      => u2 + u1

  @tailrec
  final infix def *(that: Usage): Usage = (this, that) match
    case (U0, _)             => U0
    case (U1, u)             => u
    case (UAff, UAff)        => UAff
    case (UAff, URel | UAny) => UAny
    case (URel, URel)        => URel
    case (URel | UAny, UAny) => UAny
    case (u1, u2)            => u2 * u1

  @tailrec
  final infix def |(that: Usage): Usage = (this, that) match
    case (u1, u2) if u1 == u2 => u1
    case (U0, U1 | UAff)      => UAff
    case (U0, URel | UAny)    => UAny
    case (U1, UAff)           => UAff
    case (U1, URel)           => URel
    case (U1, UAny)           => UAny
    case (UAff, URel | UAny)  => UAny
    case (URel | UAny, UAny)  => UAny
    case (u1, u2)             => u2 | u1

  final infix def &(that: Usage): Option[Usage] = (this, that) match
    case (U0, U1) | (U1, U0)         => None
    case (U0, _) | (_, U0)           => Some(U0)
    case (U1, _) | (_, U1)           => Some(U1)
    case (UAff, URel) | (URel, UAff) => Some(U1)
    case (UAff, _) | (_, UAff)       => Some(UAff)
    case (URel, _) | (_, URel)       => Some(URel)
    case (UAny, UAny)                => Some(UAny)

  final infix def isSubUsageOf(that: Usage): Boolean = (this, that) match
    case (u1, u2) if u1 == u2       => true
    case (U0, _) | (_, URel | UAny) => true
    case (U1, UAff)                 => true
    case (UAff, U1)                 => true
    case _                          => false

  override def tryCompareTo[B >: Usage: AsPartiallyOrdered](that: B): Option[Int] =
    (this, that) match
      case (u1, u2) if u1 == u2     => Some(0)
      case (U0, UAff | UAny)        => Some(-1)
      case (U1, UAff | URel | UAny) => Some(-1)
      case (UAff, UAny)             => Some(-1)
      case (URel, UAny)             => Some(-1)
      case (UAny, _)                => Some(1)
      case (URel, U1)               => Some(1)
      case (UAff, U0 | U1)          => Some(1)
      case _                        => None

private type UProd[T] = Seq[T | Usage]
private type USum[T] = Seq[UProd[T]]
type ULub[T] = Set[USum[T]] // non-empty

def uLubFromLiteral[T](usage: Usage): ULub[T] = Set(Seq(Seq(usage)))

def uLubFromT[T](t: T): ULub[T] = Set(Seq(Seq(t)))

def uLubProd[T](lubs: Iterable[ULub[T]]): ULub[T] = uLubNormalize(
  lubs.fold[ULub[T]](uLubFromLiteral(Usage.U1)) { (lub1, lub2) =>
    for
      sum1 <- lub1
      sum2 <- lub2
    yield uSumProd(sum1, sum2)
  },
)

def uLubSum[T](lubs: Iterable[ULub[T]]): ULub[T] = uLubNormalize(
  lubs.fold[ULub[T]](uLubFromLiteral(Usage.U0)) { (lub1, lub2) =>
    for
      sum1 <- lub1
      sum2 <- lub2
    yield uSumSum(sum1, sum2)
  },
)

def uLubJoin[T](lubs: Iterable[ULub[T]]): ULub[T] = uLubNormalize(
  lubs.flatten.map(uSumNormalize).toSet,
)

private def uLubNormalize[T](lub: ULub[T]): ULub[T] =
  val r = lub
    .map:
      _.partitionMap { prod =>
        if prod.isEmpty then Right(Usage.U1)
        else if prod.size == 1 && prod.head.isInstanceOf[Usage] then
          Right(prod.head.asInstanceOf[Usage])
        else Left(prod)
      }
    .groupMapReduce(e => MultiSet.from(e._1))(_._2.fold(Usage.U0)(_ + _))(_ | _)
    .toSet
    .map { (sum, literal) =>
      if literal == Usage.U0 then sum.toSeq
      else sum.toSeq ++ uSumFromLiteral(literal)
    }
  // UAny is an absorbing element for |
  if r.contains(uSumFromLiteral(Usage.UAny)) then uLubFromLiteral(Usage.UAny)
  else r

private def uSumFromLiteral[T](usage: Usage): USum[T] = Seq(Seq(usage))

private def uSumProd[T](sum1: USum[T], sum2: USum[T]): USum[T] =
  val prods =
    for
      prod1 <- sum1
      prod2 <- sum2
    yield uProdProd(prod1, prod2)
  uSumNormalize(prods)

private def uSumSum[T](sum1: USum[T], sum2: USum[T]): USum[T] = uSumNormalize(
  sum1 ++ sum2,
)

private def uSumNormalize[T](sum: Iterable[UProd[T]]): USum[T] =
  val r = sum
    .map:
      _.partitionMap:
        case u: Usage => Right(u)
        case t        => Left(t)
    .groupMapReduce(e => MultiSet.from(e._1))(_._2.fold(Usage.U1)(_ * _))(_ + _)
    .toSeq
    .map { (prod, literal) =>
      if literal == Usage.U1 then prod.toSeq
      else prod.toSeq ++ uProdFromLiteral(literal)
    }
  // URel is an absorbing element for +
  if r.contains(Seq(Usage.URel)) then uSumFromLiteral(Usage.URel)
  else r

private def uProdFromLiteral[T](usage: Usage): UProd[T] = Seq(usage)

private def uProdProd[T](prod1: UProd[T], prod2: UProd[T]): UProd[T] =
  val r = prod1 ++ prod2
  // U0 is an absorbing element for *
  if r.contains(Usage.U0) then Seq(Usage.U0)
  else r
