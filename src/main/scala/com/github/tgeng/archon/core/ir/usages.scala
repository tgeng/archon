package com.github.tgeng.archon.core.ir

import com.github.tgeng.archon.common.*
import com.github.tgeng.archon.core.common.*
import com.github.tgeng.archon.core.ir.CTerm.*
import com.github.tgeng.archon.core.ir.HandlerType.Simple
import com.github.tgeng.archon.core.ir.IrError.*
import com.github.tgeng.archon.core.ir.VTerm.*

import scala.collection.immutable.SeqMap

type Usages = Seq[VTerm]

object Usages:
  def zero(using Γ: Context): Usages = Seq.fill(Γ.size)(UsageLiteral(Usage.U0))

  def single(v: VTerm.Var, u: VTerm = VTerm.UsageLiteral(Usage.U1))(using Γ: Context): Usages =
    (Seq.fill(Γ.size - v.idx - 1)(UsageLiteral(Usage.U0)) :+ u)
      ++ Seq.fill(v.idx)(UsageLiteral(Usage.U0))

extension (us1: Usages)
  infix def +(us2: Usages): Usages =
    if us1.size != us2.size then throw IllegalArgumentException("mismatched size")
    else us1.zip(us2).map { (u1, u2) => UsageSum(u1, u2) }

  infix def |(us2: Usages): Usages =
    if us1.size != us2.size then throw IllegalArgumentException("mismatched size")
    else us1.zip(us2).map { (u1, u2) => UsageJoin(u1, u2) }

  infix def *(scalar: VTerm): Usages = us1.map(u => UsageProd(u, scalar))
  infix def *(scalar: Usage)(using SourceInfo): Usages =
    us1.map(u => UsageProd(u, UsageLiteral(scalar)))

def collectUsages
  (tm: VTerm, ty: Option[VTerm])
  (using Γ: Context)
  (using Σ: Signature)
  (using ctx: TypingContext)
  : Usages =
  ctx.trace[Usages](
    "collectUsages",
    ty match
      case Some(ty) => Block(PrettyPrinter.pprint(tm), ":", PrettyPrinter.pprint(ty))
      case None     => PrettyPrinter.pprint(tm),
    successMsg = PrettyPrinter.pprint,
  ):
    tm match
      case Type(upperBound) => collectUsages(upperBound, None)
      case Top(level)       => collectUsages(level, Some(LevelType()))
      case v: Var           => Usages.single(v)
      case Collapse(ctm)    => collectUsages(ctm, ty.map(F(_, Total(), uAny)))
      case U(cty)           => collectUsages(cty, None)
      case Thunk(ctm) =>
        collectUsages(
          ctm,
          ty.map(ctx.solveTerm).map {
            case U(ty) => ty
            case ty    => throw IllegalStateException(s"bad type, expect U but got $ty")
          },
        )
      case DataType(qn, args) =>
        val data = Σ.getData(qn)
        collectArgsUsages(args, (data.context.map(_._1) ++ data.tIndexTys).toList)
      case Con(name, args) =>
        ty.map(ctx.solveTerm) match
          case Some(DataType(qn, dArgs)) =>
            val data = Σ.getData(qn)
            val constructor = Σ.getConstructor(qn, name)
            val telescope =
              constructor.paramTys.map(_.substLowers(dArgs.take(data.context.size)*))
            collectArgsUsages(args, telescope)
          case ty => throw IllegalStateException(s"bad type, expect data type but got $ty")
      case UsageType(upperBound) =>
        upperBound.map(collectUsages(_, Some(UsageType()))).getOrElse(Usages.zero)
      case UsageLiteral(_) => Usages.zero
      case UsageProd(operands) =>
        operands.map(collectUsages(_, Some(UsageType()))).fold(Usages.zero)(_ + _)
      case UsageSum(operands) =>
        operands.toSeq.map(collectUsages(_, Some(UsageType()))).fold(Usages.zero)(_ + _)
      case UsageJoin(operands) =>
        operands.map(collectUsages(_, Some(UsageType()))).fold(Usages.zero)(_ + _)
      case EffectsType(continuationUsage) => collectUsages(continuationUsage, Some(UsageType()))
      case Effects(effectInstances, unionOperands) =>
        effectInstances
          // The type here doesn't matter because in nowhere is this type used to direct usage collection.
          .map(
            collectUsages(
              _,
              Some(HandlerKeyType((Builtins.DivQn, Nil), HandlerConstraint(Usage.U1, Simple))),
            ),
          )
          .fold(Usages.zero)(_ + _) +
          unionOperands.keys.map(collectUsages(_, Some(EffectsType()))).fold(Usages.zero)(_ + _)
      case LevelType(_) => Usages.zero
      case Level(_, maxOperands) =>
        maxOperands.keys.map(collectUsages(_, Some(LevelType()))).fold(Usages.zero)(_ + _)
      case Auto() =>
        throw IllegalStateException("All auto should have been replaced by meta variables.")

def collectUsages
  (tm: CTerm, ty: Option[CTerm])
  (using Γ: Context)
  (using Σ: Signature)
  (using ctx: TypingContext)
  : Usages =
  ctx.trace[Usages](
    "collectUsages",
    ty match
      case Some(ty) => Block(PrettyPrinter.pprint(tm), ":", PrettyPrinter.pprint(ty))
      case None     => PrettyPrinter.pprint(tm),
    successMsg = PrettyPrinter.pprint,
  ):
    tm match
      case Hole => throw IllegalStateException("Hole should not appear here.")
      case CapturedContinuationTip(_) =>
        throw IllegalStateException("CapturedContinuationTip should not appear here.")
      case CType(upperBound, effects) =>
        collectUsages(upperBound, None) + collectUsages(effects, Some(EffectsType()))
      case CTop(level, effects) =>
        collectUsages(level, Some(LevelType())) + collectUsages(effects, Some(EffectsType()))
      case m: Meta => collectUsages(ctx.solveTerm(m), ty)
      case Def(_)  => Usages.zero
      case Force(v) =>
        collectUsages(
          v,
          ty.map(ctx.solveTerm).map {
            case F(ty, _, _) => ty
            case ty          => throw IllegalStateException(s"bad type, expect F but got $ty")
          },
        )
      case F(vty, effects, usage) =>
        collectUsages(vty, None) + collectUsages(effects, Some(EffectsType())) +
          collectUsages(usage, Some(UsageType()))
      case Return(value, usage) =>
        collectUsages(
          value,
          ty.map(ctx.solveTerm).map {
            case F(ty, _, _) => ty
            case ty          => throw IllegalStateException(s"bad type, expect F but got $ty")
          },
        ) * usage.normalized
      case Let(t, tBinding, eff, body) =>
        val tUsages = collectUsages(t, Some(F(tBinding.ty, eff, tBinding.usage)))
        val bodyUsages = {
          given Context = Γ :+ tBinding

          val bodyUsages = collectUsages(body, ty.map(_.weakened))
          val actualTUsage = bodyUsages.last
          ctx.checkSolved(
            checkUsageSubsumption(actualTUsage, tBinding.usage),
            NotUsageSubsumption(actualTUsage, tBinding.usage),
          )
          bodyUsages.dropRight(1).map { t =>
            // A variable's usage may reference the variable bound to the value returned from `t`. In
            // this case, strength would fail and the referenced usage can take any value. Hence, we
            // just approximate it with `uAny`.
            try t.strengthened
            catch case _: StrengthenException => uAny
          }
        }
        val continuationUsage = getEffectsContinuationUsage(eff)
        tUsages + bodyUsages * continuationUsage
      case Redex(t, elims) =>
        val (_, ty) = inferType(t)
        def impl(ty: CTerm, elims: List[Elimination[VTerm]]): Usages =
          (ty, elims) match
            case (_, Nil) => Usages.zero
            case (r @ RecordType(qn, args, _), Elimination.EProj(name) :: elims) =>
              val field = Σ.getField(qn, name)
              val fieldTy = field.ty.substLowers(args :+ Thunk(r)*)
              impl(fieldTy, elims)
            case (FunctionType(binding, bodyTy, _), Elimination.ETerm(arg) :: elims) =>
              collectUsages(arg, Some(binding.ty)) * binding.usage + impl(
                bodyTy.substLowers(arg),
                elims,
              )
            case _ => throw IllegalStateException(s"bad redex with\nty=$ty\nelims=$elims")
        impl(ty, elims)
      case FunctionType(binding, bodyTy, effects) =>
        val bindingUsages =
          collectUsages(binding.ty, None) + collectUsages(binding.usage, Some(UsageType()))
        val effectsUsages = collectUsages(effects, Some(EffectsType()))
        // There is no need to check the last usage corresponding to the bound arg because the bound
        // arg is used in types, which don't consume any usages (aka, usage is multiplied by u0)
        val bodyUsages = collectUsages(bodyTy, None)(using Γ :+ binding)
          .dropRight(1)
          .map(t =>
            try t.strengthened
            catch case _: StrengthenException => uAny,
          )
        bindingUsages + effectsUsages + bodyUsages
      case RecordType(qn, args, effects) =>
        val record = Σ.getRecord(qn)
        collectArgsUsages(args, record.context.map(_._1).toList) +
          collectUsages(effects, Some(EffectsType()))
      case OperationCall(effectInstance, name, args) =>
        val (qn, tArgs) = inferType(effectInstance)._1 match
          case HandlerKeyType(eff, _) => eff
          case _ =>
            throw IllegalStateException(
              "operation should have been type checked and verified to be simple before reduction",
            )
        val operation = Σ.getOperation(qn, name)
        collectArgsUsages(args, operation.paramTys.substLowers(tArgs*))
      case Continuation(_, _) => Usages.zero
      case Handler(
          eff: Eff,
          otherEffects: VTerm,
          handlerEffects: VTerm,
          outputUsage: VTerm,
          outputTy: VTerm,
          parameter: VTerm,
          parameterBinding: Binding[VTerm],
          parameterDisposer: Option[CTerm],
          parameterReplicator: Option[CTerm],
          transform: CTerm,
          handlers: SeqMap[QualifiedName, HandlerImpl],
          input: CTerm,
          inputBinding: Binding[VTerm],
          _: Option[HandlerKey],
        ) =>
        val (qn, tArgs) = eff
        val handlerUsages = Σ
          .getOperations(qn)
          .map { (op: Operation) =>
            val opTelescope = op.paramTys.substLowers(tArgs*)
            val opQn = qn / op.name
            val handler = handlers(opQn)
            val handlerTelescope = handler.handlerConstraint match
              case HandlerConstraint(_, HandlerType.Simple) => parameterBinding +: opTelescope
              case HandlerConstraint(_, HandlerType.Complex) =>
                parameterBinding +: opTelescope :+
                  Binding(handler.continuationType.get, u1)(gn"continuation")
            val handlerUsages =
              collectUsages(handler.body, Some(handler.bodyTy))(using Γ ++ handlerTelescope)
            partiallyVerifyUsages(handlerUsages, handlerTelescope)
          }
          .fold(Usages.zero)(_ + _)

        val parameterUsages =
          collectUsages(parameter, Some(parameterBinding.ty)) * parameterBinding.usage
        val inputΓ = Γ :+ Binding(
          HandlerKeyType(
            eff,
            handlers.values.foldLeft(HandlerConstraint(Usage.U1, HandlerType.Simple))((c, impl) =>
              c | impl.handlerConstraint,
            ),
          ),
        )(gn"e")
        val inputEffects =
          Effects(Set(Var(0)), SeqMap(otherEffects.weakened /* for effect instance */ -> false))
            .normalized(using inputΓ)
        val inputUsages = collectUsages(
          input,
          Some(
            F(
              inputBinding.ty.weakened,
              inputEffects,
              inputBinding.usage.weakened,
            ),
          ),
        )(using inputΓ).dropRight(1).map { t =>
          t.strengthened // safe since the last binding is effect instance.
        }
        val transformTelescope = List(parameterBinding, inputBinding.weakened)
        val transformUsages =
          partiallyVerifyUsages(
            collectUsages(
              transform,
              Some(F(outputTy, handlerEffects, outputUsage).weaken(2, 0)),
            )(using Γ ++ transformTelescope),
            transformTelescope,
          )
        val parameterDisposerUsages =
          parameterDisposer match
            case None => Usages.zero
            case Some(parameterDisposer) =>
              partiallyVerifyUsages(
                collectUsages(
                  parameterDisposer,
                  Some(
                    F(
                      DataType(Builtins.UnitQn, Nil),
                      EffectsRetainSimpleLinear(handlerEffects).weakened,
                    ),
                  ),
                )(using Γ :+ parameterBinding),
                List(parameterBinding),
              )
        val parameterReplicatorUsages =
          parameterReplicator match
            case None => Usages.zero
            case Some(parameterReplicator) =>
              partiallyVerifyUsages(
                collectUsages(
                  parameterReplicator,
                  Some(
                    F(
                      DataType(
                        Builtins.PairQn,
                        List(
                          LevelUpperBound(),
                          parameterBinding.usage,
                          parameterBinding.ty,
                          parameterBinding.usage,
                          parameterBinding.ty,
                        ),
                      ),
                      EffectsRetainSimpleLinear(handlerEffects),
                    ),
                  ),
                )(using Γ :+ parameterBinding),
                List(parameterBinding),
              )

        inputUsages + handlerUsages + parameterUsages + transformUsages + parameterDisposerUsages + parameterReplicatorUsages

private def collectEffUsages
  (eff: Eff)
  (using Context)
  (using Σ: Signature)
  (using TypingContext)
  : Usages =
  val (qn, args) = eff
  val effect = Σ.getEffect(qn)
  collectArgsUsages(args, effect.context.toList)

private def collectArgsUsages
  (args: List[VTerm], telescope: Telescope)
  (using Context)
  (using Signature)
  (using TypingContext)
  : Usages =
  (args, telescope) match
    case (Nil, Nil) => Usages.zero
    case (arg :: args, binding :: telescope) =>
      collectUsages(arg, Some(binding.ty)) * binding.usage +
        collectArgsUsages(args, telescope.map(_.substLowers(arg)))
    case _ => throw IllegalStateException("mismatched length")

/** Verifies the usages corresponding to the given telescope and return the unverified ones
  * corresponding to the context.
  */
def partiallyVerifyUsages
  (usages: Usages, telescope: Telescope)
  (using Context)
  (using Signature)
  (using ctx: TypingContext)
  : Usages =
  def impl(usages: Usages, telescope: Telescope)(using Context): Unit =
    (usages, telescope) match
      case (Nil, Nil) =>
      case (usage :: usages, binding :: telescope) =>
        ctx.checkSolved(
          checkUsageSubsumption(usage, binding.usage),
          NotUsageSubsumption(usage, binding.usage),
        )
        impl(usages, telescope)(using summon[Context] :+ binding)
      case _ => throw IllegalArgumentException("mismatched length")
  impl(usages.takeRight(telescope.size), telescope)
  usages
    .dropRight(telescope.size)
    .map(t =>
      try t.strengthen(telescope.size, 0)
      catch
        // Any usages corresponding to inner bindings are approximated with uAny
        case _: StrengthenException => uAny,
    )

// TODO: delete things below
private object UsagesCollector extends TermVisitor[(Context, TypingContext), Usages]:
  // TODO: do not count usages in type!! Also take continuation usage into account. Also do use
  // usage multiplication when handling function args.

  override def combine
    (rs: Usages*)
    (using ctx: (Context, TypingContext))
    (using Σ: Signature)
    : Usages =
    rs.fold(Usages.zero(using ctx._1))(_ + _)

  override def visitDataType
    (dataType: VTerm.DataType)
    (using ctx: (Context, TypingContext))
    (using Σ: Signature)
    : Usages = ???

  override def visitCon
    (con: VTerm.Con)
    (using ctx: (Context, TypingContext))
    (using Σ: Signature)
    : Usages = ???

  override def withTelescope
    (telescope: => Telescope)
    (action: ((Context, TypingContext)) ?=> Usages)
    (using ctx: (Context, TypingContext))
    (using Σ: Signature)
    : Usages =
    given tCtx: TypingContext = ctx._2
    val usages = action(using (ctx._1 ++ telescope, ctx._2))
    def verifyUsages(usages: Usages, telescope: Telescope)(using Context): Unit =
      (usages, telescope) match
        case (Nil, Nil) =>
        case (usage :: usages, binding :: telescope) =>
          tCtx.checkSolved(
            checkUsageSubsumption(usage, binding.usage),
            NotUsageSubsumption(usage, binding.usage),
          )
          verifyUsages(usages, telescope)(using summon[Context] :+ binding)
        case _ => throw IllegalArgumentException("mismatched length")
    verifyUsages(usages.takeRight(telescope.size), telescope)(using ctx._1)
    usages.dropRight(telescope.size)

  override def visitVar
    (v: VTerm.Var)
    (using ctx: (Context, TypingContext))
    (using Σ: Signature)
    : Usages = Usages.single(v)(using ctx._1)

  override def visitBinding
    (binding: Binding[VTerm])
    (using ctx: (Context, TypingContext))
    (using Σ: Signature)
    : Usages = Usages.zero(using ctx._1)

  override def visitTelescope
    (telescope: List[Binding[VTerm]])
    (using ctx: (Context, TypingContext))
    (using Σ: Signature)
    : Usages = Usages.zero(using ctx._1)

  override def visitAuto
    (auto: VTerm.Auto)
    (using ctx: (Context, TypingContext))
    (using Σ: Signature)
    : Usages = throw IllegalStateException(
    "all auto should have been replaced during type checking",
  )

  override def visitHole(using ctx: (Context, TypingContext))(using Σ: Signature): Usages =
    throw IllegalStateException("hole should only exist temporarily during reduction")

  override def visitCapturedContinuationTip
    (cct: CTerm.CapturedContinuationTip)
    (using ctx: (Context, TypingContext))
    (using Σ: Signature)
    : Usages = Usages.zero(using ctx._1)

  override def visitMeta
    (m: CTerm.Meta)
    (using ctx: (Context, TypingContext))
    (using Σ: Signature)
    : Usages =
    visitCTerm(ctx._2.solveTerm(m)(using ctx._1)(using Σ))(using ctx)(using Σ)

  override def visitF(f: CTerm.F)(using ctx: (Context, TypingContext))(using Σ: Signature): Usages =
    visitVTerm(f.vTy)

  override def visitReturn
    (r: CTerm.Return)
    (using ctx: (Context, TypingContext))
    (using Σ: Signature)
    : Usages = visitVTerm(r.v)

  override def visitLet
    (let: CTerm.Let)
    (using ctx: (Context, TypingContext))
    (using Σ: Signature)
    : Usages =
    visitCTerm(let.t)
    withTelescope(List(let.tBinding)) {
      visitCTerm(let.body)
    }
