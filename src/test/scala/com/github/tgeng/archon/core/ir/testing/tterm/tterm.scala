package com.github.tgeng.archon.core.ir.testing.tterm

import com.github.tgeng.archon.common.Nat
import com.github.tgeng.archon.core.common.{Name, QualifiedName}
import com.github.tgeng.archon.core.ir.*

enum UsageOperator:
  case UoProd, UoSum, UoJoin

case class TBinding(name: String, ty: TTerm, usage: TTerm)
case class THandlerImpl(handlerConstraint: HandlerConstraint, body: TTerm)

enum TTerm:
  case TId(id: String)
  case TDef(qn: QualifiedName)
  case TU(t: TTerm)
  case TThunk(t: TTerm)
  case TUsageLiteral(usage: Usage)
  case TUsageOp(op: UsageOperator, operands: Seq[TTerm])
  case TEffectsUnion(effects: Seq[TTerm])
  case TEffectsFilter(effect: TTerm)
  case TLevelLiteral(level: Nat)
  case TLevelSuc(level: TTerm)
  case TAuto()
  case TF(ty: TTerm, effects: TTerm, usage: TTerm)
  case TLet(t: TTerm, ty: TTerm, effects: TTerm, usage: TTerm, body: TTerm)
  case TRedex(t: TTerm, elims: List[Elimination[TTerm]])
  case TFunctionType(arg: TBinding, bodyType: TTerm)
  case TOperationCall(effQn: QualifiedName, effArgs: List[TTerm], name: Name, args: List[TTerm])
  case THandler
    (
      eff: TTerm,
      otherEffects: TTerm,
      outputEffects: TTerm,
      outputUsage: TTerm,
      outputTy: TTerm,
      parameter: TTerm,
      parameterBinding: TBinding,
      parameterDisposer: Option[TTerm],
      parameterReplicator: Option[TTerm],
      transform: TTerm,
      handlers: Seq[(QualifiedName, THandlerImpl)],
      input: TTerm,
      inputBinding: TTerm,
    )
