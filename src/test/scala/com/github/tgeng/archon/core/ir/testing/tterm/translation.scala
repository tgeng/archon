package com.github.tgeng.archon.core.ir.testing.tterm

import com.github.tgeng.archon.core.common.{Name, QualifiedName, gn}
import com.github.tgeng.archon.core.ir.*
import com.github.tgeng.archon.core.ir.CTerm.*
import com.github.tgeng.archon.core.ir.VTerm.*
import com.github.tgeng.archon.core.ir.testing.tterm.TTerm.*
import com.github.tgeng.archon.core.ir.testing.tterm.TranslationError.UnresolvedSymbol
import com.github.tgeng.archon.core.ir.testing.tterm.UsageOperator.{UoJoin, UoProd, UoSum}

import scala.collection.immutable.SeqMap

enum TranslationError extends Exception:
  case UnresolvedSymbol(name: String)

case class TranslationContext
  (
    nextDeBruijnIndex: Int = 0,
    localVars: Map[String, Int] = Map.empty,
    globalDefs: Map[String, QualifiedName] = Map.empty,
  ):
  def bindLocal(name: String): TranslationContext =
    val newIndex = nextDeBruijnIndex + 1
    this.copy(nextDeBruijnIndex = newIndex, localVars = localVars + (name -> nextDeBruijnIndex))

  def bindLocals(names: Seq[String]): TranslationContext =
    names.foldLeft(this) { (ctx, name) => ctx.bindLocal(name) }

  def bindDef(name: String, qn: QualifiedName): TranslationContext =
    this.copy(globalDefs = globalDefs + (name -> qn))

  def lookup(name: String): Either[Int, QualifiedName] =
    localVars.get(name) match
      case Some(index) => Left(index)
      case None =>
        globalDefs.get(name) match
          case Some(qualifiedName) => Right(qualifiedName)
          case None                => throw UnresolvedSymbol(name)

extension (tTerm: TTerm)
  def toCTerm(using context: TranslationContext): CTerm =
    given SourceInfo = tTerm.sourceInfo
    tTerm match
      case TU(t)                => Return(U(t.toCTerm))
      case TThunk(t)            => Return(Thunk(t.toCTerm))
      case TUsageLiteral(usage) => Return(VTerm.UsageLiteral(usage))
      case TUsageOp(op, op1, op2) =>
        for
          op1 <- op1.toCTerm
          op2 <- op2.toCTerm
        yield op match
          case UoProd => UsageProd(op1, op2)
          case UoSum  => UsageSum(op1, op2)
          case UoJoin => UsageJoin(op1, op2)
      case TEffectsUnion(eff1, eff2) =>
        for
          eff1 <- eff1.toCTerm
          eff2 <- eff2.toCTerm
        yield EffectsUnion(eff1, eff2)
      case TEffectsFilter(eff) =>
        for eff <- eff.toCTerm
        yield EffectsRetainSimpleLinear(eff)
      case TLevelLiteral(level) => Return(LevelLiteral(level))
      case TLevelSuc(level) =>
        for level <- level.toCTerm
        yield LevelSuc(level)
      case TAuto() => Return(Auto())
      case TId(id) =>
        context.lookup(id) match
          case Left(index) => Return(Var(index))
          case Right(qn)   => Def(qn)
      case TDef(qn)  => Def(qn)
      case TForce(t) => t.toCTerm.flatMap(Force(_))
      case TF(ty, effects, usage) =>
        for
          ty <- ty.toCTerm
          effects <- effects.toCTerm
          usage <- usage.toCTerm
          r <- F(ty, effects, usage)
        yield r
      case TLet(name, t, ty, effects, usage, body) =>
        for
          ty <- ty.toCTerm
          effects <- effects.toCTerm
          usage <- usage.toCTerm
          r <- Let(
            t.toCTerm,
            ty,
            effects,
            usage,
            body.toCTerm(using summon[TranslationContext].bindLocal(name)),
          )(Name.Normal(name))
        yield r
      case TApp(f, arg) =>
        for
          arg <- arg.toCTerm
          r <- redex(f.toCTerm, arg)
        yield r
      case TFunctionType(arg, bodyType, effects) =>
        for
          effects <- effects.toCTerm
          argTy <- arg.ty.toCTerm
          argUsage <- arg.usage.toCTerm
          r <- FunctionType(
            Binding(argTy, argUsage)(Name.Normal(arg.name)),
            bodyType.toCTerm(using summon[TranslationContext].bindLocal(arg.name)),
            effects,
          )
        yield r
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
        for
          eff <- eff.toCTerm
          otherEffects <- otherEffects.toCTerm
          outputEffects <- outputEffects.toCTerm
          outputUsage <- outputUsage.toCTerm
          outputTy <- outputTy.toCTerm
          parameter <- parameter.toCTerm
          parameterTy <- parameterBinding.ty.toCTerm
          parameterUsage <- parameterBinding.usage.toCTerm
          inputTy <- inputBinding.ty.toCTerm
          inputUsage <- inputBinding.usage.toCTerm
          r <- Handler(
            eff,
            otherEffects,
            outputEffects,
            outputUsage,
            outputTy,
            parameter,
            Binding(parameterTy, parameterUsage)(Name.Normal(parameterBinding.name)),
            parameterDisposer.map(_.toCTerm),
            parameterReplicator.map(_.toCTerm),
            transform.toCTerm,
            handlers
              .map { case (qn, THandlerImpl(h, body, boundNames)) =>
                qn -> HandlerImpl(
                  h,
                  body.toCTerm(using
                    summon[TranslationContext].bindLocals(parameterBinding.name +: boundNames),
                  ),
                )(boundNames.map(n => Name.Normal(n)))
              }
              .to(SeqMap),
            input.toCTerm,
            Binding(inputTy, inputUsage)(Name.Normal(inputBinding.name)),
          )
        yield r

extension (self: CTerm)
  def map(f: TranslationContext ?=> VTerm => VTerm)(using ctx: TranslationContext): CTerm =
    val newCtx = ctx.bindLocal("")
    given SourceInfo = SourceInfo.SiEmpty
    Let(
      self,
      Auto(),
      Auto(),
      Auto(),
      Return(f(using newCtx)(Var(0))),
    )(gn"v")

  def flatMap(f: TranslationContext ?=> VTerm => CTerm)(using ctx: TranslationContext): CTerm =
    val newCtx = ctx.bindLocal("")
    given SourceInfo = SourceInfo.SiEmpty
    Let(
      self,
      Auto(),
      Auto(),
      Auto(),
      f(using newCtx)(Var(0)),
    )(gn"v")
