package com.github.tgeng.archon.core.ir

import com.github.tgeng.archon.common.Nat
import com.github.tgeng.archon.core.common.gn
import com.github.tgeng.archon.core.ir.CTerm.*
import com.github.tgeng.archon.core.ir.EscapeStatus.EsLocal
import com.github.tgeng.archon.core.ir.VTerm.*

/** @param dbNumbersToCompute
  *   DeBruijn number indicating which variables should be tracked for escape status. The outermost
  *   one has number 0. DeBruijn number is used instead of DeBruijn index because the former does
  *   not change when a new variable is bound. These numbers must not exceed `Γ`.
  * @return
  *   [[EscapeStatus]] corresponding to the requested `dbNumbersToCompute`.
  */
def computeEscapeStatuses
  (c: CTerm, dbNumbersToCompute: Set[Nat])
  (using Γ: Context)
  (using Σ: Signature)
  (using ctx: TypingContext)
  : Map[Nat, EscapeStatus] =
  assert(dbNumbersToCompute.forall(_ < Γ.size))

  val esCtx = EscapeStatusContext(dbNumbersToCompute, Γ, ctx)
  EscapeStatusVisitor.visitCTerm(c)(using esCtx)

/** @param dbNumbersToTrack
  *   the DeBruijn numbers to track
  * @param currentContextSize
  *   the size of Γ
  */
case class EscapeStatusContext
  (
    dbNumbersToTrack: Set[Nat],
    Γ: Context,
    typingContext: TypingContext,
  )

private object EscapeStatusVisitor extends TermVisitor[EscapeStatusContext, Map[Nat, EscapeStatus]]:
  override def withTelescope
    (telescope: => Telescope)
    (action: EscapeStatusContext ?=> Map[Nat, EscapeStatus])
    (using ctx: EscapeStatusContext)
    (using Σ: Signature)
    : Map[Nat, EscapeStatus] = action(using ctx.copy(Γ = ctx.Γ ++ telescope))

  override def combine
    (rs: Map[Nat, EscapeStatus]*)
    (using ctx: EscapeStatusContext)
    (using Σ: Signature)
    : Map[Nat, EscapeStatus] =
    val result = collection.mutable.Map[Nat, EscapeStatus]()
    for
      m <- rs
      (n, es) <- m
    do result(n) = result.getOrElse(n, EscapeStatus.EsLocal) | es
    result.toMap

  override def visitVar
    (v: VTerm.Var)
    (using ctx: EscapeStatusContext)
    (using Σ: Signature)
    : Map[Nat, EscapeStatus] =
    val dbNumber = ctx.Γ.size - 1 - v.idx
    if ctx.dbNumbersToTrack(dbNumber) then Map(dbNumber -> EscapeStatus.EsReturned)
    else Map()

  override def visitRedex
    (redex: CTerm.Redex)
    (using ctx: EscapeStatusContext)
    (using Σ: Signature)
    : Map[Nat, EscapeStatus] =
    given Context = ctx.Γ
    given TypingContext = ctx.typingContext
    val ty = inferType(redex.t)._2

    def processArgs
      (ty: CTerm, elims: List[Elimination[VTerm]], processedElims: List[Elimination[VTerm]])
      : Map[Nat, EscapeStatus] =
      (ty, elims) match
        case (_, Nil) => Map()
        case (FunctionType(_, ty, _, es), (elim @ Elimination.ETerm(arg)) :: elims) =>
          combine(multiply(es, visitVTerm(arg)), processArgs(ty, elims, processedElims :+ elim))
        case (CorecordType(qn, args, _), (elim @ Elimination.EProj(name)) :: elims) =>
          processArgs(
            Σ.getCofield(qn, name).ty.substLowers(args :+ Thunk(Redex(redex.t, processedElims))*),
            elims,
            processedElims :+ elim,
          )
        case _ => throw IllegalStateException("type error")

    combine(visitCTerm(redex.t), processArgs(ty, redex.elims, Nil))

  override def visitLet
    (let: CTerm.Let)
    (using ctx: EscapeStatusContext)
    (using Σ: Signature)
    : Map[Nat, EscapeStatus] =
    val tEscapeStatuses = visitCTerm(let.t)
    val newCtx =
      ctx.copy(Γ = ctx.Γ :+ let.tBinding, dbNumbersToTrack = ctx.dbNumbersToTrack + ctx.Γ.size)
    val bodyEscapeStatuses = visitCTerm(let.body)(using newCtx)
    combine(
      multiply(bodyEscapeStatuses.getOrElse(ctx.Γ.size, EsLocal), tEscapeStatuses),
      bodyEscapeStatuses - ctx.Γ.size,
    )

  override def visitHandler
    (handler: CTerm.Handler)
    (using ctx: EscapeStatusContext)
    (using Σ: Signature)
    : Map[Nat, EscapeStatus] =
    // parameter is passed into handlers and for simplicity we won't track the escape status of it
    val parameterEscapeStatuses = multiply(EscapeStatus.EsUnknown, visitVTerm(handler.parameter))
    val inputEscapeStatuses = withTelescope(
      List(
        Binding(
          EffectInstanceType(
            handler.eff,
            handler.handlers.values.foldLeft(HandlerConstraint(Usage.U1, HandlerType.Simple))(
              (c, impl) => c | impl.handlerConstraint,
            ),
          ),
        )(gn"e"),
      ),
    ):
      visitCTerm(handler.input)
    val parameterProcessorEscapeStatuses =
      withTelescope(List(handler.parameterBinding)):
        multiply(
          EscapeStatus.EsLocal,
          combine(
            handler.parameterDisposer.map(visitCTerm).getOrElse(Map()),
            handler.parameterReplicator.map(visitCTerm).getOrElse(Map()),
          ),
        )

    val inputDbNumber = ctx.Γ.size + 1
    val transformEscapeStatuses =
      withTelescope(List(handler.parameterBinding)):
        given EscapeStatusContext = ctx.copy(
          Γ = ctx.Γ :+ handler.inputBinding,
          dbNumbersToTrack = ctx.dbNumbersToTrack + inputDbNumber,
        )
        visitCTerm(handler.transform)

    val realInputEscapeStatuses =
      multiply(transformEscapeStatuses.getOrElse(inputDbNumber, EsLocal), inputEscapeStatuses)
    combine(
      parameterEscapeStatuses,
      parameterProcessorEscapeStatuses,
      realInputEscapeStatuses,
      transformEscapeStatuses - inputDbNumber,
      combine(
        handler.handlers.toSeq.map((qn, handlerImpl) =>
          visitHandlerImpl(handler.eff, handler.parameterBinding, qn, handlerImpl),
        )*,
      ),
    )

  override def visitOperationCall
    (operationCall: CTerm.OperationCall)
    (using ctx: EscapeStatusContext)
    (using Σ: Signature)
    : Map[Nat, EscapeStatus] =
    combine(
      multiply(EscapeStatus.EsLocal, visitVTerm(operationCall.effInstance)),
      multiply(
        // Any argument passed to operation is treated as unknown for simplicity.
        EscapeStatus.EsUnknown,
        operationCall.args.map(visitVTerm).foldRight(Map())(combine(_, _)),
      ),
    )

  private def multiply
    (escapeStatus: EscapeStatus, escapeStatuses: Map[Nat, EscapeStatus])
    : Map[Nat, EscapeStatus] = escapeStatuses.view.mapValues(escapeStatus * _).toMap
