package com.github.tgeng.archon.core.ir
import com.github.tgeng.archon
import com.github.tgeng.archon.common.*
import com.github.tgeng.archon.common.eitherUtil.*
import com.github.tgeng.archon.core
import com.github.tgeng.archon.core.common.*
import com.github.tgeng.archon.core.ir
import com.github.tgeng.archon.core.ir.CTerm.*
import com.github.tgeng.archon.core.ir.Declaration.*
import com.github.tgeng.archon.core.ir.EscapeStatus.{EsLocal, EsUnknown}
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
      data.copy(
        context = tParamTys.zip(data.context.map(_._2)),
        tIndexTys = tIndexTys,
        level = level,
      )
    }

@throws(classOf[IrError])
def checkDataConstructor
  (qn: QualifiedName, con: Constructor)
  (using Σ: Signature)
  (using ctx: TypingContext)
  : Constructor =
  val data = Σ.getData(qn).getOrThrow
  given Γ: Context = data.context.map(_._1)
  ctx.trace(s"checking data constructor $qn.${con.name}"):
    val paramTys = ctx.solveTerm(con.paramTys)
    val tArgsContext = Γ ++ paramTys
    val tArgs =
      checkTypes(con.tArgs, data.tIndexTys.weaken(con.paramTys.size, 0))(using tArgsContext)
        .map(ctx.solveTerm(_)(using tArgsContext))
    val violatingVars =
      VarianceChecker.visitTelescope(con.paramTys)(using
        data.context,
        Variance.COVARIANT,
        0,
        Γ,
        ctx,
      )
    if violatingVars.nonEmpty then throw IllegalVarianceInData(data.qn, violatingVars.toSet)
    Constructor(con.name, paramTys, tArgs)

@throws(classOf[IrError])
def checkCorecord(corecord: Corecord)(using Σ: Signature)(using ctx: TypingContext): Corecord =
  given Context = IndexedSeq()
  ctx.trace(s"checking corecord signature ${corecord.qn}"):
    val tParams = corecord.context.map(_._1)
    val tParamTysTelescope = ctx.solveTerm(tParams.toList)
    {
      given tParamTys: Context = Context.fromTelescope(tParamTysTelescope)
      checkTParamsAreUnrestricted(tParamTysTelescope)
      val level = ctx.solveTerm(checkLevel(corecord.level))
      // There is no need to check selfBinding since it's generated by elaboration and is guaranteed
      // to be correct.
      corecord.copy(
        context = tParamTys.zip(corecord.context.map(_._2)),
        level = level,
      )
    }

@throws(classOf[IrError])
def checkCorecordCofield
  (qn: QualifiedName, cofield: Cofield)
  (using Σ: Signature)
  (using ctx: TypingContext)
  : Cofield = {
  val corecord = Σ.getCorecord(qn).getOrThrow
  given Γ: Context = corecord.context.map(_._1).toIndexedSeq :+ corecord.selfBinding

  ctx.trace(s"checking corecord cofield $qn.${cofield.name}"):
    val ty = ctx.solveTerm(cofield.ty)
    val violatingVars =
      // 1 is to offset self binding.
      VarianceChecker.visitCTerm(cofield.ty)(using
        corecord.context,
        Variance.COVARIANT,
        1,
        Γ,
        ctx,
      )
    if violatingVars.nonEmpty then
      throw IllegalVarianceInCorecord(corecord.qn, violatingVars.toSet)(using
        corecord.context.map(_._1).toIndexedSeq,
      )
    Cofield(cofield.name, ty)
}

object VarianceChecker
  extends TermVisitor[(TContext, Variance, Nat, Context, TypingContext), Seq[Var]]:
  override def combine
    (violatedVars: Seq[Var]*)
    (using ctx: (TContext, Variance, Nat, Context, TypingContext))
    (using Σ: Signature)
    (using TypingContext)
    : Seq[Var] =
    violatedVars.flatten

  override def withTelescope
    (telescope: => Telescope)
    (action: ((TContext, Variance, Nat, Context, TypingContext)) ?=> Seq[VTerm.Var])
    (using ctx: (TContext, Variance, Nat, Context, TypingContext))
    (using Σ: Signature)
    (using TypingContext)
    : Seq[VTerm.Var] =
    val (tContext, variance, offset, _Γ, tctx) = ctx
    action(using (tContext, variance, offset + telescope.size, _Γ, tctx))

  override def visitCollapse
    (collapse: VTerm.Collapse)
    (using ctx: (TContext, Variance, Nat, Context, TypingContext))
    (using Σ: Signature)
    (using TypingContext)
    : Seq[VTerm.Var] =
    val (tContext, variance, offset, _Γ, tctx) = ctx
    collapse.normalized(using _Γ)(using Σ)(using tctx) match
      case Collapse(ctm) => visitCTerm(ctm)
      case t             => visitVTerm(t)

  override def visitVar
    (v: Var)
    (using ctx: (TContext, Variance, Nat, Context, TypingContext))
    (using Σ: Signature)
    (using TypingContext)
    : Seq[Var] =
    val (tContext, variance, offset, _Γ, tctx) = ctx
    val index = v.idx - offset
    if index < 0 then return Nil
    tContext.resolve(index)._2 match
      case Variance.INVARIANT => Nil
      case declaredVariance =>
        if declaredVariance == variance then Nil
        else Seq(v.strengthen(offset, 0).asInstanceOf[Var])

  override def visitVTerm
    (tm: VTerm)
    (using ctx: (TContext, Variance, Nat, Context, TypingContext))
    (using Σ: Signature)
    (using TypingContext)
    : Seq[Var] =
    val (tContext, _, offset, _Γ, tctx) = ctx
    tm match
      case _: (Type | Var | U | DataType) => super.visitVTerm(tm)(using ctx)
      case _ => super.visitVTerm(tm)(using (tContext, Variance.INVARIANT, offset, _Γ, tctx))

  override def visitDataType
    (dataType: DataType)
    (using ctx: (TContext, Variance, Nat, Context, TypingContext))
    (using Σ: Signature)
    (using TypingContext)
    : Seq[Var] =
    val (tContext, variance, offset, _Γ, tctx) = ctx
    val data = Σ.getData(dataType.qn)(using tctx).asRight
    (data.context.map(_._2) ++ data.tIndexTys.map(_ => Variance.INVARIANT))
      .zip(dataType.args)
      .flatMap:
        case (Variance.INVARIANT, arg) =>
          visitVTerm(arg)(using (tContext, Variance.INVARIANT, offset, _Γ, tctx))
        case (Variance.COVARIANT, arg) => visitVTerm(arg)(using ctx)
        case (Variance.CONTRAVARIANT, arg) =>
          visitVTerm(arg)(using (tContext, variance.flip, offset, _Γ, tctx))
      .toSeq

  override def visitCTerm
    (tm: CTerm)
    (using ctx: (TContext, Variance, Nat, Context, TypingContext))
    (using Σ: Signature)
    (using TypingContext)
    : Seq[Var] =
    val (tContext, _, offset, _Γ, tctx) = ctx
    tm match
      case _: (CType | F | FunctionType | CorecordType) => super.visitCTerm(tm)(using ctx)
      case _ => super.visitCTerm(tm)(using (tContext, Variance.INVARIANT, offset, _Γ, tctx))

  override def visitCType
    (cType: CType)
    (using ctx: (TContext, Variance, Nat, Context, TypingContext))
    (using Σ: Signature)
    (using TypingContext)
    : Seq[Var] =
    val (tContext, _, offset, _Γ, tctx) = ctx
    combine(
      visitCTerm(cType.upperBound),
      visitVTerm(cType.effects)(using (tContext, Variance.INVARIANT, offset, _Γ, tctx)),
    )

  override def visitF
    (f: F)
    (using ctx: (TContext, Variance, Nat, Context, TypingContext))
    (using Σ: Signature)
    (using TypingContext)
    : Seq[Var] =
    val (tContext, _, offset, _Γ, tctx) = ctx
    val invariantCtx = (tContext, Variance.INVARIANT, offset, _Γ, tctx)
    combine(
      visitVTerm(f.vTy),
      visitVTerm(f.effects)(using invariantCtx),
      visitVTerm(f.usage)(using invariantCtx),
    )

  override def visitFunctionType
    (functionType: FunctionType)
    (using ctx: (TContext, Variance, Nat, Context, TypingContext))
    (using Σ: Signature)
    (using TypingContext)
    : Seq[Var] =
    val (tContext, variance, offset, _Γ, tctx) = ctx
    val invariantCtx = (tContext, Variance.INVARIANT, offset, _Γ, tctx)
    val contravariantCtx = (tContext, variance.flip, offset, _Γ, tctx)
    combine(
      visitVTerm(functionType.binding.ty)(using contravariantCtx),
      withTelescope(List(functionType.binding)) {
        visitCTerm(functionType.bodyTy)
      },
      visitVTerm(functionType.effects)(using invariantCtx),
    )
  override def visitCorecordType
    (corecordType: CorecordType)
    (using ctx: (TContext, Variance, Nat, Context, TypingContext))
    (using Σ: Signature)
    (using TypingContext)
    : Seq[Var] =
    val (tContext, variance, offset, _Γ, tctx) = ctx
    Σ.getCorecord(corecordType.qn)(using tctx)
      .asRight
      .context
      .map(_._2)
      .zip(corecordType.args)
      .flatMap:
        case (Variance.INVARIANT, arg) =>
          visitVTerm(arg)(using (tContext, Variance.INVARIANT, offset, _Γ, tctx))
        case (Variance.COVARIANT, arg) => visitVTerm(arg)(using ctx)
        case (Variance.CONTRAVARIANT, arg) =>
          visitVTerm(arg)(using (tContext, variance.flip, offset, _Γ, tctx))
      .toSeq

private object PatternEscapeStatusCollector extends Visitor[Nat, Set[Nat]]:
  override def combine
    (rs: Set[Nat]*)
    (using ctxSize: Nat)
    (using Σ: Signature)
    (using TypingContext)
    : Set[Nat] =
    rs.flatten.toSet

  override def withBoundNames
    (bindingNames: => Seq[Ref[Name]])
    (action: Nat ?=> Set[Nat])
    (using ctxSize: Nat)
    (using Σ: Signature)
    (using TypingContext)
    : Set[Nat] = action(using ctxSize + bindingNames.size)

  override def visitPVar
    (pVar: core.ir.Pattern.PVar)
    (using ctxSize: Nat)
    (using Σ: Signature)
    (using TypingContext)
    : Set[Nat] = Set(ctxSize - 1 - pVar.idx)

  override def visitPForced
    (pForced: archon.core.ir.Pattern.PForced)
    (using ctx: Nat)
    (using Σ: Signature)
    (using TypingContext)
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
      case (CoPattern.CProjection(name) :: coPatterns, CorecordType(qn, _, _)) =>
        getDeclaredEscapeStatusesInClauseContext(coPatterns, Σ.getCofield(qn, name).asRight.ty)
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
  d.copy(context = definition.context.map(_._1).zip(newContextEscapeStatuses))

@throws(classOf[IrError])
def checkEffect(effect: Effect)(using Signature)(using ctx: TypingContext): Effect =
  given Context = Context.empty
  ctx.trace(s"checking effect signature ${effect.qn}"):
    given Γ: Context = Context.fromTelescope(effect.context.toTelescope)
    val continuationUsage = ctx.solveTerm(effect.continuationUsage)
    effect.copy(
      context = Γ,
      continuationUsage = continuationUsage,
    )

@throws(classOf[IrError])
def checkOperation
  (qn: QualifiedName, operation: Operation)
  (using Σ: Signature)
  (using ctx: TypingContext)
  : Operation =
  val effect = Σ.getEffect(qn).getOrThrow
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
