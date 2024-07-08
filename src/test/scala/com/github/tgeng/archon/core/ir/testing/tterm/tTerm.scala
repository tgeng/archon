package com.github.tgeng.archon.core.ir.testing.tterm

import com.github.tgeng.archon.common.Nat
import com.github.tgeng.archon.core.common.QualifiedName
import com.github.tgeng.archon.core.ir.*

case class TBinding(name: String, ty: TTerm, usage: TTerm)(using val sourceInfo: SourceInfo)
case class THandlerImpl(handlerConstraint: HandlerConstraint, body: TTerm, boundNames: Seq[String])

enum TTerm(val sourceInfo: SourceInfo):
  case TId(id: String)(using sourceInfo: SourceInfo) extends TTerm(sourceInfo)
  case TDef(qn: QualifiedName)(using sourceInfo: SourceInfo) extends TTerm(sourceInfo)
  case TU(t: TTerm)(using sourceInfo: SourceInfo) extends TTerm(sourceInfo)
  case TForce(t: TTerm)(using sourceInfo: SourceInfo) extends TTerm(sourceInfo)
  case TThunk(t: TTerm)(using sourceInfo: SourceInfo) extends TTerm(sourceInfo)
  case TLevelLiteral(level: Nat)(using sourceInfo: SourceInfo) extends TTerm(sourceInfo)
  case TAuto()(using sourceInfo: SourceInfo) extends TTerm(sourceInfo)
  case TF(ty: TTerm, effects: TTerm, usage: TTerm)(using sourceInfo: SourceInfo)
    extends TTerm(sourceInfo)
  case TLet
    (name: String, t: TTerm, ty: TTerm, effects: TTerm, usage: TTerm, body: TTerm)
    (using sourceInfo: SourceInfo) extends TTerm(sourceInfo)
  case TRedex(c: TTerm, elims: List[Elimination[TTerm]])(using sourceInfo: SourceInfo)
    extends TTerm(sourceInfo)
  case TFunctionType(arg: TBinding, bodyType: TTerm, effects: TTerm)
    extends TTerm(SourceInfo.merge(arg.sourceInfo, bodyType.sourceInfo))
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
      inputBinding: TBinding,
    )
    (using sourceInfo: SourceInfo) extends TTerm(sourceInfo)
