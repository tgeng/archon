package com.github.tgeng.archon.core.ir.testing.tterm

import com.github.tgeng.archon.core.common.QualifiedName
import com.github.tgeng.archon.core.ir.testing.tterm.TTerm.*
import com.github.tgeng.archon.core.ir.testing.tterm.TranslationError.UnresolvedSymbol
import com.github.tgeng.archon.core.ir.{CTerm, VTerm}

case class TranslationContext
  (
    nextDeBruijnIndex: Int = 0,
    localVars: Map[String, Int] = Map.empty,
    globalDefs: Map[String, QualifiedName] = Map.empty,
  ) {
  def bind(name: String, target: Either[Unit, QualifiedName]): TranslationContext =
    target match
      case Left(_) =>
        val newIndex = nextDeBruijnIndex + 1
        this.copy(nextDeBruijnIndex = newIndex, localVars = localVars + (name -> nextDeBruijnIndex))
      case Right(qualifiedName) => this.copy(globalDefs = globalDefs + (name -> qualifiedName))

  def lookup(name: String): Either[Int, QualifiedName] =
    localVars.get(name) match
      case Some(index) => Left(index)
      case None =>
        globalDefs.get(name) match
          case Some(qualifiedName) => Right(qualifiedName)
          case None                => throw UnresolvedSymbol(name)
}

extension (tTerm: TTerm)
  def toCTerm(using context: TranslationContext): CTerm = tTerm match
    case TId(id)                                    => ???
    case TDef(qn)                                   => ???
    case TU(t)                                      => ???
    case TThunk(t)                                  => ???
    case TUsageLiteral(usage)                       => ???
    case TUsageOp(op, operands)                     => ???
    case TEffectsUnion(effects)                     => ???
    case TEffectsFilter(effect)                     => ???
    case TLevelLiteral(level)                       => ???
    case TLevelSuc(level)                           => ???
    case TAuto()                                    => ???
    case TF(ty, effects, usage)                     => ???
    case TLet(t, ty, effects, usage, body)          => ???
    case TRedex(t, elims)                           => ???
    case TFunctionType(arg, bodyType)               => ???
    case TOperationCall(effQn, effArgs, name, args) => ???
    case THandler(
        eff,
        otherEffects,
        outputEffects,
        outputUsage,
        outputTy,
        parameter,
        parameterBinding,
        parameterDisposer,
        parameterReplicator,
        transform,
        handlers,
        input,
        inputBinding,
      ) =>
      ???

  def toVTerm(using context: TranslationContext): VTerm =
    ???
