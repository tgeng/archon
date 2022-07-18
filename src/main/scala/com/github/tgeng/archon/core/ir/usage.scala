package com.github.tgeng.archon.core.ir

import com.github.tgeng.archon.core.ir.Usage.UAff

import scala.annotation.tailrec

/**
 * Here we do not do the full generalization and allow user to define custom semirings for grading.
 * Instead, we use a specialized semiring that only accounts for counting usages.
 */
enum Usage extends PartiallyOrdered[Usage] :
  case U0, U1, UAff, URel, UAny

  @tailrec
  final infix def +(that: Usage): Usage = (this, that) match
    case (U0, u) => u
    case (U1, U1 | UAff | URel | UAny) => URel
    case (UAff, UAff | URel | UAny) => UAny
    case (URel, URel | UAny) => URel
    case (UAny, UAny) => UAny
    case (u1, u2) => u2 + u1

  @tailrec
  final infix def *(that: Usage): Usage = (this, that) match
    case (U0, _) => U0
    case (U1, u) => u
    case (UAff, UAff) => UAff
    case (UAff, URel | UAny) => UAny
    case (URel, URel) => URel
    case (URel | UAny, UAny) => UAny
    case (u1, u2) => u2 * u1

  @tailrec
  final infix def |(that: Usage): Usage = (this, that) match
    case (u1, u2) if u1 == u2 => u1
    case (U0, U1 | UAff) => UAff
    case (U0, URel | UAny) => UAny
    case (U1, UAff) => UAff
    case (U1, URel) => URel
    case (U1, UAny) => UAny
    case (UAff, URel | UAny) => UAny
    case (URel | UAny, UAny) => UAny
    case (u1, u2) => u2 | u1

  override def tryCompareTo[B >: Usage : AsPartiallyOrdered](that: B): Option[Int] = (this, that) match
    case (u1, u2) if u1 == u2 => Some(0)
    case (U0, UAff | UAny) => Some(-1)
    case (U1, UAff | URel | UAny) => Some(-1)
    case (UAff, UAny) => Some(-1)
    case (URel, UAny) => Some(-1)
    case (UAny, _) => Some(1)
    case (URel, U1) => Some(1)
    case (UAff, U0 | U1) => Some(1)
    case _ => None
