package com.github.tgeng.archon.core.ir

import com.github.tgeng.archon.common.*
import com.github.tgeng.archon.common.IndentPolicy.*
import com.github.tgeng.archon.core.common.*
import com.github.tgeng.archon.core.ir
import com.github.tgeng.archon.core.ir.CTerm.*
import com.github.tgeng.archon.core.ir.Declaration.*
import com.github.tgeng.archon.core.ir.IrError.*
import com.github.tgeng.archon.core.ir.PrettyPrinter.pprint
import com.github.tgeng.archon.core.ir.Usage.*
import com.github.tgeng.archon.core.ir.VTerm.*

import scala.annotation.tailrec

@throws(classOf[IrError])
def checkData(data: Data)(using Σ: Signature)(using ctx: TypingContext): Data =
  given Context = IndexedSeq()
  ctx.trace(s"checking data signature ${data.qn}"):
    val tParamsTysTelescope =
      ctx.solveTerm(checkParameterTyDeclarations(data.context.map(_._1).toTelescope))
    {
      given tParamTys: Context = Context.fromTelescope(tParamsTysTelescope)
      val tIndexTys =
        ctx.solveTerm(checkParameterTyDeclarations(data.tIndexTys))
      checkTParamsAreUnrestricted((tParamTys ++ tIndexTys).toTelescope)
      val level = ctx.solveTerm(checkLevel(data.level))
      Data(data.qn, tParamTys.zip(data.context.map(_._2)), tIndexTys, level)
    }

@throws(classOf[IrError])
def checkDataConstructor
  (qn: QualifiedName, con: Constructor)
  (using Σ: Signature)
  (using ctx: TypingContext)
  : Constructor =
  Σ.getDataOption(qn) match
    case None => throw MissingDeclaration(qn)
    case Some(data) =>
      given Γ: Context = data.context.map(_._1)
      ctx.trace(s"checking data constructor $qn.${con.name}"):
        val paramTys = ctx.solveTerm(checkParameterTyDeclarations(con.paramTys, Some(data.level)))
        val tArgsContext = Γ ++ paramTys
        val tArgs =
          checkTypes(con.tArgs, data.tIndexTys.weaken(con.paramTys.size, 0))(using tArgsContext)
            .map(ctx.solveTerm(_)(using tArgsContext))
        val violatingVars =
          VarianceChecker.visitTelescope(con.paramTys)(using data.context, Variance.COVARIANT, 0)
        if violatingVars.nonEmpty then throw IllegalVarianceInData(data.qn, violatingVars.toSet)
        Constructor(con.name, paramTys, tArgs)

@throws(classOf[IrError])
def checkRecord(record: Record)(using Σ: Signature)(using ctx: TypingContext): Record =
  given Context = IndexedSeq()
  ctx.trace(s"checking record signature ${record.qn}"):
    val tParams = record.context.map(_._1)
    val tParamTysTelescope = ctx.solveTerm(checkParameterTyDeclarations(tParams.toList))
    {
      given tParamTys: Context = Context.fromTelescope(tParamTysTelescope)
      checkTParamsAreUnrestricted(tParamTysTelescope)
      val level = ctx.solveTerm(checkLevel(record.level))
      // There is no need to check selfBinding since it's generated by elaboration and is guaranteed
      // to be correct.
      Record(
        record.qn,
        tParamTys.zip(record.context.map(_._2)),
        level,
        record.selfBinding,
      )
    }

@throws(classOf[IrError])
def checkRecordField
  (qn: QualifiedName, field: Field)
  (using Σ: Signature)
  (using ctx: TypingContext)
  : Field =
  Σ.getRecordOption(qn) match
    case None => throw MissingDeclaration(qn)
    case Some(record) =>
      given Context = record.context.map(_._1).toIndexedSeq :+ record.selfBinding

      ctx.trace(s"checking record field $qn.${field.name}"):
        val ty = ctx.solveTerm(checkIsCType(field.ty, Some(record.level.weakened)))
        val violatingVars =
          // 1 is to offset self binding.
          VarianceChecker.visitCTerm(field.ty)(using record.context, Variance.COVARIANT, 1)
        if violatingVars.nonEmpty then throw IllegalVarianceInRecord(record.qn, violatingVars.toSet)
        Field(field.name, ty)

private object VarianceChecker extends Visitor[(TContext, Variance, Nat), Seq[Var]]:
  override def combine
    (violatedVars: Seq[Var]*)
    (using ctx: (TContext, Variance, Nat))
    (using Σ: Signature)
    : Seq[Var] =
    violatedVars.flatten

  override def withBoundNames
    (bindingNames: => Seq[Ref[Name]])
    (action: ((TContext, Variance, Nat)) ?=> Seq[Var])
    (using ctx: (TContext, Variance, Nat))
    (using Σ: Signature)
    : Seq[Var] =
    val (tContext, variance, offset) = ctx
    action(using (tContext, variance, offset + bindingNames.size))

  override def visitVar
    (v: Var)
    (using ctx: (TContext, Variance, Nat))
    (using Σ: Signature)
    : Seq[Var] =
    val (tContext, variance, offset) = ctx
    val index = v.idx - offset
    if index < 0 then return Nil
    tContext.resolve(index)._2 match
      case Variance.INVARIANT => Nil
      case declaredVariance =>
        if declaredVariance == variance then Nil
        else Seq(v.strengthen(offset, 0).asInstanceOf[Var])

  override def visitVTerm
    (tm: VTerm)
    (using ctx: (TContext, Variance, Nat))
    (using Σ: Signature)
    : Seq[Var] =
    val (tContext, _, offset) = ctx
    tm match
      case _: (Type | Var | U | DataType) => super.visitVTerm(tm)(using ctx)
      case _ => super.visitVTerm(tm)(using (tContext, Variance.INVARIANT, offset))

  override def visitDataType
    (dataType: DataType)
    (using ctx: (TContext, Variance, Nat))
    (using Σ: Signature)
    : Seq[Var] =
    val (tContext, variance, offset) = ctx
    val data = Σ.getData(dataType.qn)
    (data.context.map(_._2) ++ data.tIndexTys.map(_ => Variance.INVARIANT))
      .zip(dataType.args)
      .flatMap:
        case (Variance.INVARIANT, arg) =>
          visitVTerm(arg)(using (tContext, Variance.INVARIANT, offset))
        case (Variance.COVARIANT, arg) => visitVTerm(arg)(using ctx)
        case (Variance.CONTRAVARIANT, arg) =>
          visitVTerm(arg)(using (tContext, variance.flip, offset))
      .toSeq

  override def visitCTerm
    (tm: CTerm)
    (using ctx: (TContext, Variance, Nat))
    (using Σ: Signature)
    : Seq[Var] =
    val (tContext, _, offset) = ctx
    tm match
      case _: (CType | F | FunctionType | RecordType) => super.visitCTerm(tm)(using ctx)
      case _ => super.visitCTerm(tm)(using (tContext, Variance.INVARIANT, offset))

  override def visitCType
    (cType: CType)
    (using ctx: (TContext, Variance, Nat))
    (using Σ: Signature)
    : Seq[Var] =
    val (tContext, _, offset) = ctx
    combine(
      visitCTerm(cType.upperBound),
      visitVTerm(cType.effects)(using (tContext, Variance.INVARIANT, offset)),
    )
  override def visitF(f: F)(using ctx: (TContext, Variance, Nat))(using Σ: Signature): Seq[Var] =
    val (tContext, _, offset) = ctx
    val invariantCtx = (tContext, Variance.INVARIANT, offset)
    combine(
      visitVTerm(f.vTy),
      visitVTerm(f.effects)(using invariantCtx),
      visitVTerm(f.usage)(using invariantCtx),
    )

  override def visitFunctionType
    (functionType: FunctionType)
    (using ctx: (TContext, Variance, Nat))
    (using Σ: Signature)
    : Seq[Var] =
    val (tContext, variance, offset) = ctx
    val invariantCtx = (tContext, Variance.INVARIANT, offset)
    val contravariantCtx = (tContext, variance.flip, offset)
    combine(
      visitVTerm(functionType.binding.ty)(using contravariantCtx),
      withBoundNames(Seq(functionType.binding.name)) {
        visitCTerm(functionType.bodyTy)
      },
      visitVTerm(functionType.effects)(using invariantCtx),
    )
  override def visitRecordType
    (recordType: RecordType)
    (using ctx: (TContext, Variance, Nat))
    (using Σ: Signature)
    : Seq[Var] =
    val (tContext, variance, offset) = ctx
    val record = Σ.getRecord(recordType.qn)
    record.context
      .map(_._2)
      .zip(recordType.args)
      .flatMap:
        case (Variance.INVARIANT, arg) =>
          visitVTerm(arg)(using (tContext, Variance.INVARIANT, offset))
        case (Variance.COVARIANT, arg) => visitVTerm(arg)(using ctx)
        case (Variance.CONTRAVARIANT, arg) =>
          visitVTerm(arg)(using (tContext, variance.flip, offset))
      .toSeq

@throws(classOf[IrError])
def checkDef(definition: Definition)(using Signature)(using ctx: TypingContext): Definition =
  // TODO[P0]: do escape analysis here.
  given Context = definition.context.map(_._1)
  ctx.trace(s"checking def signature ${definition.qn}"):
    val ty = checkIsCType(definition.ty)
    Definition(definition.qn, definition.context, ty)

@throws(classOf[IrError])
def checkEffect(effect: Effect)(using Signature)(using ctx: TypingContext): Effect =
  given Context = Context.empty
  ctx.trace(s"checking effect signature ${effect.qn}"):
    val telescope = ctx.solveTerm(checkParameterTyDeclarations(effect.context.toTelescope))
    checkTParamsAreUnrestricted(telescope)

    {
      given Γ: Context = Context.fromTelescope(telescope)
      val continuationUsage = ctx.solveTerm(checkType(effect.continuationUsage, UsageType()))
      Effect(effect.qn, Γ, continuationUsage)
    }

@throws(classOf[IrError])
def checkOperation
  (qn: QualifiedName, operation: Operation)
  (using Σ: Signature)
  (using ctx: TypingContext)
  : Operation =
  Σ.getEffectOption(qn) match
    case None => throw MissingDeclaration(qn)
    case Some(effect) =>
      given Γ: Context = effect.context

      ctx.trace(s"checking effect operation $qn.${operation.name}"):
        val paramTys = ctx.solveTerm(checkParameterTyDeclarations(operation.paramTys))
        {
          given Context = Γ ++ paramTys
          val resultTy = ctx.solveTerm(checkIsType(operation.resultTy))
          val resultUsage =
            ctx.solveTerm(checkType(operation.resultUsage, UsageType(None)))
          Operation(
            operation.name,
            paramTys,
            resultTy,
            resultUsage,
          )
        }

@tailrec
@throws(classOf[IrError])
private def checkTParamsAreUnrestricted
  (tParamTys: Telescope)
  (using Γ: Context)
  (using Σ: Signature)
  (using ctx: TypingContext)
  : Unit = tParamTys match
  case Nil =>
  case binding :: rest =>
    ctx.checkSolved(
      checkUsageSubsumption(binding.usage, UsageLiteral(UAny)),
      ExpectUnrestrictedTypeParameterBinding(binding),
    )
    checkTParamsAreUnrestricted(rest)(using Γ :+ binding)

@throws(classOf[IrError])
private def checkParameterTyDeclarations
  (tParamTys: Telescope, levelBound: Option[VTerm] = None)
  (using Γ: Context)
  (using Σ: Signature)
  (using TypingContext)
  : Telescope = tParamTys match
  case Nil => Nil
  case binding :: rest =>
    val ty = checkIsType(binding.ty, levelBound)
    val usage = checkType(binding.usage, UsageType(None))
    Binding(ty, usage)(binding.name) :: checkParameterTyDeclarations(rest)(using Γ :+ binding)
