package io.github.tgeng.archon.core.ir

import io.github.tgeng.archon.common.*
import io.github.tgeng.archon.core.common.*

enum Pattern:
  case PVar(idx: Nat)
  case PRefl

  /**
   * Note that matching computation type is prohibited. This should simplify compilation. In addition, it's unclear how
   * type checking of effects can work if we allow matching computation because the matched effect types become unbound
   * at type level.
   */
  case PDataType(qn: QualifiedName, args: List[Pattern])
  case PForcedDataType(qn: QualifiedName, args: List[Pattern])
  // Note that we do not allow matching specific values of level, effect, and heap because there are no corresponding
  // eliminators. All these can only be matched with a pattern variable.
  case PConstructor(name: Name, args: List[Pattern])
  case PForcedConstructor(name: Name, args: List[Pattern])
  case PForced(term: VTerm)
  case PAbsurd

import Pattern.*
import VTerm.*

extension (p: Pattern)
  def toTerm: Option[VTerm] = p match
    case PVar(idx) => Some(Var(idx))
    case PRefl => Some(Refl)
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
    case PAbsurd => None

enum CoPattern:
  case CPattern(p: Pattern)
  case CProjection(name: Name)

object CoPattern:
  def pVars(firstIndex: Nat, lastIndex: Nat = 0): List[CoPattern] = firstIndex
    .to(lastIndex, -1)
    .map(i => CPattern(Pattern.PVar(i))).toList

enum Elimination[T]:
  case ETerm(v: T)
  case EProj(n: Name)

import CoPattern.*
import Elimination.*

extension (q: CoPattern)
  def toElimination: Option[Elimination[VTerm]] = q match
    case CPattern(p) => p.toTerm.map(ETerm.apply)
    case CProjection(name) => Some(EProj(name))
