package com.github.tgeng.archon.core.ir

import com.github.tgeng.archon.common.*
import com.github.tgeng.archon.core.common.*
import com.github.tgeng.archon.core.ir.SourceInfo.{SiEffectUnion, SiLevelSuc}

trait SourceInfoOwner[T]:
  def sourceInfo: SourceInfo
  def withSourceInfo(sourceInfo: SourceInfo): T

case class Range(
  /** Inclusive */
  start: Nat,

  /** Exclusive */
  end: Nat,
):
  def +(that: Range): Range = Range(math.min(this.start, that.start), math.max(this.end, that.end))

extension (s: String)
  def substring(r: Range): String = s.substring(r.start, r.end).!!

enum SourceInfo:
  case SiEmpty
  case SiText(text: String, range: Range)
  case SiLevelSuc(operand: SourceInfo)
  case SiLevelMax(operand1: SourceInfo, operand2: SourceInfo)
  case SiEffectUnion(operand1: SourceInfo, operand2: SourceInfo)
  case SiTypeOf(tm: SourceInfo)
  case SiDerived(qn: QualifiedName)
  case SiBuiltin(qn: QualifiedName)

  override def toString: String = this match
    case SiEmpty => "<empty>"
    case SiText(text, range) => s"'${text.substring(range)}'"
    case SiLevelSuc(operand) => s"<suc $operand>"
    case SiLevelMax(operand1, operand2) => s"<max $operand1 $operand2>"
    case SiEffectUnion(operand1, operand2) => s"<union $operand1 $operand2>"
    case SiTypeOf(tm) => s"<type of $tm>"
    case SiDerived(qn) => qn.toString
    case SiBuiltin(qn) => qn.toString

object SourceInfo:
  def siMerge(sis: SourceInfo*): SourceInfo = sis.fold(SiEmpty) {
    (_, _) match
      case (SiEmpty, si2) => si2
      case (si1, SiEmpty) => si1
      case (SiText(input1, range1), SiText(input2, range2)) if input1 == input2 => SiText(
        input1,
        range1 + range2
      )
      case _ => throw IllegalArgumentException()
  }

