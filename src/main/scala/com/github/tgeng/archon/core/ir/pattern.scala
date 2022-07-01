package com.github.tgeng.archon.core.ir

import com.github.tgeng.archon.common.*
import com.github.tgeng.archon.core.common.*

import SourceInfo.*

enum Pattern(val sourceInfo: SourceInfo) extends SourceInfoOwner[Pattern] :
  case PVar(idx: Nat)(using sourceInfo: SourceInfo) extends Pattern(sourceInfo)
  case PRefl()(using sourceInfo: SourceInfo) extends Pattern(sourceInfo)

  /**
   * Note that matching computation type is prohibited. This should simplify compilation. In addition, it's unclear how
   * type checking of effects can work if we allow matching computation because the matched effect types become unbound
   * at type level.
   */
  case PDataType(qn: QualifiedName, args: List[Pattern])
    (using sourceInfo: SourceInfo) extends Pattern(sourceInfo)
  case PForcedDataType(qn: QualifiedName, args: List[Pattern])
    (using sourceInfo: SourceInfo) extends Pattern(sourceInfo)
  // Note that we do not allow matching specific values of level, effect, and heap because there are no corresponding
  // eliminators. All these can only be matched with a pattern variable.
  case PConstructor(name: Name, args: List[Pattern])(using sourceInfo: SourceInfo) extends Pattern(
    sourceInfo
  )
  case PForcedConstructor(name: Name, args: List[Pattern])
    (using sourceInfo: SourceInfo) extends Pattern(sourceInfo)
  case PForced(term: VTerm)(using sourceInfo: SourceInfo) extends Pattern(sourceInfo)
  case PAbsurd()(using sourceInfo: SourceInfo) extends Pattern(sourceInfo)

  override def withSourceInfo(sourceInfo: SourceInfo): Pattern =
    given SourceInfo = sourceInfo
    this match
      case PVar(idx) => PVar(idx)
      case PRefl() => PRefl()
      case PDataType(qn, args) => PDataType(qn, args)
      case PForcedDataType(qn, args) => PForcedDataType(qn, args)
      case PConstructor(name, args) => PConstructor(name, args)
      case PForcedConstructor(name, args) => PForcedConstructor(name, args)
      case PForced(term) => PForced(term)
      case PAbsurd() => PAbsurd()

import Pattern.*
import VTerm.*

extension (p: Pattern)
  def toTerm: Option[VTerm] =
    given SourceInfo = p.sourceInfo

    p match
      case PVar(idx) => Some(Var(idx))
      case PRefl() => Some(Refl())
      case PDataType(qn, args) =>
        for args <- transpose(args.map(_.toTerm))
          yield DataType(qn, args)
      case PForcedDataType(qn, args) =>
        for args <- transpose(args.map(_.toTerm))
          yield DataType(qn, args)
      case PConstructor(name, args) =>
        for args <- transpose(args.map(_.toTerm))
          yield Con(name, args)
      case PForcedConstructor(name, args) =>
        for args <- transpose(args.map(_.toTerm))
          yield Con(name, args)
      case PForced(t) => Some(t)
      case PAbsurd() => None

enum CoPattern(val sourceInfo: SourceInfo) extends SourceInfoOwner[CoPattern] :
  case CPattern(pattern: Pattern) extends CoPattern(pattern.sourceInfo)
  case CProjection(name: Name)(using sourceInfo: SourceInfo) extends CoPattern(sourceInfo)

  override def withSourceInfo(sourceInfo: SourceInfo): CoPattern =
    given SourceInfo = sourceInfo
    this match
      case CPattern(pattern) => CPattern(pattern)
      case CProjection(name) => CProjection(name)

object CoPattern:
  def pVars(firstIndex: Nat, lastIndex: Nat = 0): List[CoPattern] = firstIndex
    .to(lastIndex, -1)
    .map(i => CPattern(Pattern.PVar(i)(using SiEmpty))).toList

enum Elimination[T](val sourceInfo: SourceInfo) extends SourceInfoOwner[Elimination[T]] :
  case ETerm(v: T)(using sourceInfo: SourceInfo) extends Elimination[T](sourceInfo)
  case EProj(n: Name)(using sourceInfo: SourceInfo) extends Elimination[T](sourceInfo)

  override def withSourceInfo(sourceInfo: SourceInfo): Elimination[T] =
    given SourceInfo = sourceInfo
    this match
      case ETerm(v) => ETerm(v)
      case EProj(n) => EProj(n)

import CoPattern.*
import Elimination.*

extension (q: CoPattern)
  def toElimination: Option[Elimination[VTerm]] = q match
    case CPattern(p) => p.toTerm.map(ETerm.apply)
    case CProjection(name) => Some(EProj(name))
