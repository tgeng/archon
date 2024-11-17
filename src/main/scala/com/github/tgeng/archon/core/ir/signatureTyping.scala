package com.github.tgeng.archon.core.ir

import com.github.tgeng.archon
import com.github.tgeng.archon.common.*
import com.github.tgeng.archon.core
import com.github.tgeng.archon.core.common.*
import com.github.tgeng.archon.core.ir
import com.github.tgeng.archon.core.ir.CTerm.*
import com.github.tgeng.archon.core.ir.Declaration.*
import com.github.tgeng.archon.core.ir.EscapeStatus.{EsLocal, EsReturned, EsUnknown}
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
      ctx.solveTerm(data.context.map(_._1).toTelescope)
    {
      given tParamTys: Context = Context.fromTelescope(tParamsTysTelescope)
      val tIndexTys = ctx.solveTerm(data.tIndexTys)
      checkTParamsAreUnrestricted((tParamTys ++ tIndexTys).toTelescope)
      val level = ctx.solveTerm(data.level)
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
        val paramTys = ctx.solveTerm(con.paramTys)
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
    val tParamTysTelescope = ctx.solveTerm(tParams.toList)
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
        val ty = ctx.solveTerm(field.ty)
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

private object PatternEscapeStatusCollector extends Visitor[Nat, Set[Nat]]:
  override def combine(rs: Set[Nat]*)(using ctxSize: Nat)(using Σ: Signature): Set[Nat] =
    rs.flatten.toSet

  override def withBoundNames
    (bindingNames: => Seq[Ref[Name]])
    (action: Nat ?=> Set[Nat])
    (using ctxSize: Nat)
    (using Σ: Signature)
    : Set[Nat] = action(using ctxSize + bindingNames.size)

  override def visitPVar
    (pVar: core.ir.Pattern.PVar)
    (using ctxSize: Nat)
    (using Σ: Signature)
    : Set[Nat] = Set(ctxSize - 1 - pVar.idx)

  override def visitPForced
    (pForced: archon.core.ir.Pattern.PForced)
    (using ctx: Nat)
    (using Σ: Signature)
    : Set[Nat] = Set()

@throws(classOf[IrError])
def checkDef
  (definition: Definition, clauses: Seq[Clause])
  (using Σ: Signature)
  (using ctx: TypingContext)
  : Definition =
  val d = definition.copy(ty = ctx.solveTerm(definition.ty)(using definition.context.map(_._1)))

  def checkClause(clause: Clause): collection.Seq[EscapeStatus] =
    given Context = clause.context
    val actualEscapeStatuses: Map[Nat, EscapeStatus] =
      computeEscapeStatuses(clause.rhs, clause.context.indices.toSet)

    // 1. collect escape statuses of the def context variables
    val defContextEscapeStatuses = definition.context.zipWithIndex.map {
      case ((_, declaredEscapeStatus), dbNumber) =>
        if declaredEscapeStatus == null then actualEscapeStatuses(dbNumber)
        else if declaredEscapeStatus < actualEscapeStatuses.getOrElse(dbNumber, EsLocal) then
          throw VariableEscaped(
            declaredEscapeStatus,
            actualEscapeStatuses(dbNumber),
            dbNumber,
            definition,
            clause,
          )
        else declaredEscapeStatus
    }

    // 2. check escape statuses of the (co)pattern-matched variables
    def combineEscapeStatuses
      (m1: collection.Map[Nat, EscapeStatus], m2: collection.Map[Nat, EscapeStatus])
      : collection.Map[Nat, EscapeStatus] =
      val result = m1.to(collection.mutable.Map)
      for (k, v) <- m2 do result(k) = result.getOrElse(k, EsUnknown) & v
      result

    def getDeclaredEscapeStatusesInClauseContext
      (coPatterns: List[CoPattern], ty: CTerm)
      (using ctxSize: Nat)
      : collection.Map[Nat, EscapeStatus] = (coPatterns, ty) match
      case (Nil, _) => Map()
      case (CoPattern.CPattern(p) :: coPatterns, FunctionType(_, bodyTy, _, es)) =>
        combineEscapeStatuses(
          PatternEscapeStatusCollector.visitPattern(p).map((_, es)).toMap,
          getDeclaredEscapeStatusesInClauseContext(coPatterns, bodyTy)(using ctxSize + 1),
        )
      case (CoPattern.CProjection(name) :: coPatterns, RecordType(qn, _, _)) =>
        getDeclaredEscapeStatusesInClauseContext(coPatterns, Σ.getField(qn, name).ty)
      case _ => throw IllegalStateException(s"type error:\ncoPatterns: ${coPatterns}\nty:${ty}")

    for (dbNumber, declaredEscapeStatus) <- getDeclaredEscapeStatusesInClauseContext(
        clause.lhs,
        definition.ty,
      )(using definition.context.size)
    do
      val actualEscapeStatus = actualEscapeStatuses.getOrElse(dbNumber, EscapeStatus.EsLocal)
      if declaredEscapeStatus < actualEscapeStatus then
        throw VariableEscaped(
          declaredEscapeStatus,
          actualEscapeStatuses(dbNumber),
          dbNumber,
          definition,
          clause,
        )

    // 3. return the new context escape status since the user provided definition may contain null
    // escape status, which is like mini meta-variables for escape status.
    defContextEscapeStatuses

  val newContextEscapeStatuses: Seq[EscapeStatus] =
    clauses.map(checkClause).transpose.map(_.fold(EsLocal)(_ | _))
  definition.copy(context = definition.context.map(_._1).zip(newContextEscapeStatuses))

@throws(classOf[IrError])
def checkEffect(effect: Effect)(using Signature)(using ctx: TypingContext): Effect =
  given Context = Context.empty
  ctx.trace(s"checking effect signature ${effect.qn}"):
    given Γ: Context = Context.fromTelescope(effect.context.toTelescope)
    val continuationUsage = ctx.solveTerm(effect.continuationUsage)
    Effect(effect.qn, Γ, continuationUsage)

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
        val paramTys = ctx.solveTerm(operation.paramTys)
        {
          given Context = Γ ++ paramTys
          val resultTy = ctx.solveTerm(operation.resultTy)
          val resultUsage = ctx.solveTerm(operation.resultUsage)
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
