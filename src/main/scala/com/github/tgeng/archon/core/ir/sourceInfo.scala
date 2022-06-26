package com.github.tgeng.archon.core.ir

import com.github.tgeng.archon.common.*
import com.github.tgeng.archon.core.common.*
import com.github.tgeng.archon.core.ir.SourceInfo.{SiEffectUnion, SiLevelSuc}

trait SourceInfoOwner:
  def sourceInfo: SourceInfo

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
  case SiBuiltin

  override def toString: String = this match
    case SiEmpty => "<empty>"
    case SiText(text, range) => s"'${text.substring(range)}'"
    case SiLevelSuc(operand) => s"<suc $operand>"
    case SiLevelMax(operand1, operand2) => s"<max $operand1 $operand2>"
    case SiEffectUnion(operand1, operand2) => s"<union $operand1 $operand2>"
    case SiTypeOf(tm) => s"<type of $tm>"
    case SiDerived(qn) => s"<derived def of $qn>"
    case SiBuiltin => s"<builtin>"


