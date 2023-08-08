package com.github.tgeng.archon.core.ir

import collection.mutable
import com.github.tgeng.archon.common.*
import com.github.tgeng.archon.core.common.*
import QualifiedName.*
import SourceInfo.*
import EqDecidability.*
import Usage.*
import com.github.tgeng.archon.core.ir.VTerm.EqDecidabilityLiteral

def getFreeVars
  (tele: Telescope)
  (using bar: Nat)
  (using Σ: Signature)
  : ( /* positive */ Set[Nat], /* negative */ Set[Nat]) = tele match
  case Nil => (Set.empty, Set.empty)
  case binding :: rest =>
    union(getFreeVars(binding.ty), getFreeVars(rest)(using bar + 1) - 1)

private object FreeVarsVisitorObject extends FreeVarsVisitor

trait FreeVarsVisitor extends Visitor[Nat, ( /* positive */ Set[Nat], /* negative */ Set[Nat])]:

  import VTerm.*
  import CTerm.*

  override def withBindings
    (bindingNames: => List[Name])
    (action: Nat ?=> (Set[Nat], Set[Nat]))
    (using bar: Nat)
    (using Σ: Signature)
    : (Set[Nat], Set[Nat]) =
    action(using bar + bindingNames.size)

  override def combine
    (freeVars: ( /* positive */ Set[Nat], /* negative */ Set[Nat])*)
    (using bar: Nat)
    (using Σ: Signature)
    : ( /* positive */ Set[Nat], /* negative */ Set[Nat]) =
    freeVars.fold((Set.empty, Set.empty))(union)

  override def visitVar
    (v: Var)
    (using bar: Nat)
    (using Σ: Signature)
    : ( /* positive */ Set[Nat], /* negative */ Set[Nat]) =
    if v.idx < bar then (Set.empty, Set.empty) else (Set(v.idx - bar), Set.empty)

  override def visitDataType
    (dataType: DataType)
    (using bar: Nat)
    (using Σ: Signature)
    : ( /* positive */ Set[Nat], /* negative */ Set[Nat]) =
    val data = Σ.getData(dataType.qn)

    combine(
      (data.tParamTys ++ data.tIndexTys.map((_, Variance.INVARIANT)))
        .zip(dataType.args)
        .map { case ((_, variance), arg) =>
          variance match
            case Variance.COVARIANT     => visitVTerm(arg)
            case Variance.CONTRAVARIANT => swap(visitVTerm(arg))
            case Variance.INVARIANT     => mix(visitVTerm(arg))
        }
        .toSeq: _*,
    )

  override def visitCellType
    (cellType: CellType)
    (using ctx: Nat)
    (using Σ: Signature)
    : (Set[Nat], Set[Nat]) = combine(
    visitVTerm(cellType.heap),
    mix(visitVTerm(cellType.ty)),
  )

  override def visitRecordType
    (recordType: RecordType)
    (using bar: Nat)
    (using Σ: Signature)
    : ( /* positive */ Set[Nat], /* negative */ Set[Nat]) =
    val record = Σ.getRecord(recordType.qn)
    combine(
      visitVTerm(recordType.effects) +:
        record.tParamTys
          .zip(recordType.args)
          .map { case ((_, variance), arg) =>
            variance match
              case Variance.COVARIANT     => visitVTerm(arg)
              case Variance.CONTRAVARIANT => swap(visitVTerm(arg))
              case Variance.INVARIANT     => mix(visitVTerm(arg))
          }
          .toSeq: _*,
    )

  override def visitFunctionType
    (functionType: CTerm.FunctionType)
    (using bar: Nat)
    (using Σ: Signature)
    : (Set[Nat], Set[Nat]) =
    combine(
      visitVTerm(functionType.effects),
      swap(visitVTerm(functionType.binding.ty)),
      visitCTerm(functionType.bodyTy)(using bar + 1),
    )

def getFreeVars
  (tm: VTerm)
  (using bar: Nat)
  (using Σ: Signature)
  : ( /* positive */ Set[Nat], /* negative */ Set[Nat]) =
  FreeVarsVisitorObject.visitVTerm(
    tm,
  )

def getFreeVars
  (tm: CTerm)
  (using bar: Nat)
  (using Σ: Signature)
  : ( /* positive */ Set[Nat], /* negative */ Set[Nat]) =
  FreeVarsVisitorObject.visitCTerm(tm)

def getFreeVars
  (ul: ULevel)
  (using bar: Nat)
  (using Σ: Signature)
  : ( /* positive */ Set[Nat], /* negative */ Set[Nat]) =
  import ULevel.*
  ul match
    case USimpleLevel(l) => getFreeVars(l)
    case UωLevel(_)      => (Set.empty, Set.empty)

def getFreeVars
  (eff: Eff)
  (using bar: Nat)
  (using Σ: Signature)
  : ( /* positive */ Set[Nat], /* negative */ Set[Nat]) = eff._2
  .map(getFreeVars)
  .reduceOption(union)
  .getOrElse((Set.empty, Set.empty))

def getFreeVars
  (args: Iterable[VTerm])
  (using bar: Nat)
  (using Σ: Signature)
  : ( /* positive */ Set[Nat], /* negative */ Set[Nat]) = args
  .map(getFreeVars)
  .reduceOption(union)
  .getOrElse((Set.empty, Set.empty))

private def union
  (freeVars1: (Set[Nat], Set[Nat]), freeVars2: (Set[Nat], Set[Nat]))
  : (Set[Nat], Set[Nat]) =
  (freeVars1._1 | freeVars2._1, freeVars1._2 | freeVars2._2)

extension(freeVars1: (Set[Nat], Set[Nat]))
  private def -(offset: Nat): (Set[Nat], Set[Nat]) =
    (freeVars1._1.map(_ - offset), freeVars1._2.map(_ - offset))

def mix(freeVars: (Set[Nat], Set[Nat])) =
  val r = freeVars._1 | freeVars._2
  (r, r)
