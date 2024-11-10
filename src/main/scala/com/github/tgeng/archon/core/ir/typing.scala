package com.github.tgeng.archon.core.ir

import com.github.tgeng.archon.common.*
import com.github.tgeng.archon.common.IndentPolicy.*
import com.github.tgeng.archon.common.WrapPolicy.*
import com.github.tgeng.archon.core.common.*
import com.github.tgeng.archon.core.ir
import com.github.tgeng.archon.core.ir.CTerm.*
import com.github.tgeng.archon.core.ir.Declaration.*
import com.github.tgeng.archon.core.ir.Elimination.*
import com.github.tgeng.archon.core.ir.IrError.*
import com.github.tgeng.archon.core.ir.MetaVariable.*
import com.github.tgeng.archon.core.ir.PrettyPrinter.pprint
import com.github.tgeng.archon.core.ir.Reducible.reduce
import com.github.tgeng.archon.core.ir.Usage.*
import com.github.tgeng.archon.core.ir.VTerm.*

import scala.annotation.tailrec
import scala.collection.immutable.{MultiSet, SeqMap, Set}

@throws(classOf[IrError])
private def checkLevel
  (level: VTerm)
  (using Γ: Context)
  (using Signature)
  (using TypingContext)
  : VTerm = checkType(level, LevelType(LevelOrder.upperBound))

// Precondition: tm is already type-checked and is normalized
@throws(classOf[IrError])
def inferLevel(ty: VTerm)(using Γ: Context)(using Σ: Signature)(using ctx: TypingContext): VTerm =
  ctx.trace[VTerm](
    "inferLevel",
    Block(ChopDown, Aligned, yellow(ty.sourceInfo), pprint(ty)),
    level => Block(ChopDown, Aligned, yellow(level.sourceInfo), green(pprint(level))),
  ):
    ctx.withMetaResolved(ty):
      case u: ResolvedMetaVariable =>
        val levelBound =
          Collapse(ctx.addUnsolved(F(LevelType(LevelOrder.upperBound))))
        val typeBound =
          Collapse(ctx.addUnsolved(F(Type(Top(levelBound)))))
        val effects =
          Collapse(ctx.addUnsolved(F(EffectsType())))
        val usage =
          Collapse(ctx.addUnsolved(F(UsageType())))
        ctx.checkSolved(
          checkIsConvertible(u.ty, F(Type(typeBound), effects, usage), None),
          NotTypeError(ty),
        )
        inferLevel(typeBound.normalized)
      case Type(upperBound) => LevelSuc(inferLevel(upperBound))
      case Top(level)       => level
      case r: Var =>
        val levelBound =
          Collapse(ctx.addUnsolved(F(LevelType(LevelOrder.upperBound))))
        val typeBound =
          Collapse(ctx.addUnsolved(F(Type(Top(levelBound)))))
        ctx.checkSolved(
          checkIsConvertible(Γ.resolve(r).ty, Type(typeBound), None),
          NotTypeError(ty),
        )
        inferLevel(typeBound.normalized)
      case t: Collapse =>
        val (_, ty) = inferType(t)
        val levelBound =
          Collapse(ctx.addUnsolved(F(LevelType(LevelOrder.upperBound))))
        val typeBound =
          Collapse(ctx.addUnsolved(F(Type(Top(levelBound)))))
        ctx.checkSolved(
          checkIsConvertible(ty, Type(typeBound), None),
          NotTypeError(ty),
        )
        inferLevel(typeBound.normalized)
      case U(cty) => inferLevel(cty)
      case DataType(qn, args) =>
        val data = Σ.getData(qn)
        data.level.substLowers(args.take(data.context.size)*)
      case _: UsageType | _: EffectsType => LevelLiteral(0)
      case LevelType(strictUpperBound)   => LevelLiteral(strictUpperBound)
      case _ => throw IllegalArgumentException(s"should have been checked to be a type: $ty")

// Precondition: tm is already type-checked and is normalized
@throws(classOf[IrError])
private def inferLevel
  (telescope: Telescope)
  (using Γ: Context)
  (using Σ: Signature)
  (using ctx: TypingContext)
  : VTerm =
  telescope match
    case Nil             => LevelLiteral(0)
    case binding :: rest =>
      // strengthen is always safe because the only case that rest-level would reference 0 is when
      // arg is of type Level. But in that case the overall level would be ω.
      LevelMax(binding.ty.weakened, inferLevel(rest)(using Γ :+ binding)).normalized.strengthened

@throws(classOf[IrError])
def inferType
  (tm: VTerm)
  (using Γ: Context)
  (using Σ: Signature)
  (using ctx: TypingContext)
  : (VTerm, VTerm) = debugInferType(tm):
  tm match
    case Type(uncheckedUpperBound) =>
      val upperBound = checkIsType(uncheckedUpperBound)
      val newTm = Type(upperBound.normalized)(using tm.sourceInfo)
      (newTm, Type(newTm))
    case Top(uncheckedLevel) =>
      val level = checkLevel(uncheckedLevel)
      val newTm = Top(level)(using tm.sourceInfo)
      (newTm, Type(newTm))
    case r: Var => (r, Γ.resolve(r).ty)
    case Collapse(uncheckedCTm) =>
      val (cTm, cTy) = inferType(uncheckedCTm)
      val vTy = cTy match
        case F(vTy, _, u) if isTotal(cTm, Some(cTy)) =>
          ctx.checkSolved(checkUsageSubsumption(u, u1), CollapsingU0Term(cTm))
          vTy
        case F(_, _, _) => throw CollapsingEffectfulTerm(cTm)
        case _          => throw NotCollapsable(cTm)
      (Collapse(cTm), vTy)
    case U(uncheckedCty) =>
      val (cty, ctyTy) = inferType(uncheckedCty)
      val newTm = U(cty)(using tm.sourceInfo)
      val newTy = ctyTy match
        case CType(_, _) if isTotal(cty, Some(ctyTy)) => Type(newTm)
        case CType(_, _)                              => throw EffectfulCTermAsType(cty)
        case _                                        => throw NotTypeError(tm)
      (newTm, newTy)
    case Thunk(c) =>
      val (newC, cty) = inferType(c)
      (Thunk(newC), U(cty))
    case DataType(qn, uncheckedArgs) =>
      Σ.getDataOption(qn) match
        case None => throw MissingDeclaration(qn)
        case Some(data) =>
          val args = checkTypes(uncheckedArgs, (data.context.map(_._1) ++ data.tIndexTys).toList)
          val newTm = DataType(qn, args.map(_.normalized))(using tm.sourceInfo)
          (newTm, Type(newTm))
    case _: Con          => throw InternalIrError("cannot infer type of raw constructor")
    case u: UsageLiteral => (u, UsageType(Some(u)))
    case UsageProd(uncheckedOperands) =>
      val operands = uncheckedOperands.map(o => checkType(o, UsageType(None)))
      val newTm = UsageProd(operands)(using tm.sourceInfo).normalized
      (newTm, UsageType(Some(newTm)))
    case UsageSum(uncheckedOperands) =>
      val operands = uncheckedOperands.toSeq.map(o => checkType(o, UsageType(None)))
      val newTm = UsageSum(MultiSet.from(operands))(using tm.sourceInfo).normalized
      (newTm, UsageType(Some(newTm)))
    case UsageJoin(uncheckedOperands) =>
      val operands = uncheckedOperands.map(o => checkType(o, UsageType(None)))
      val newTm = UsageJoin(operands)(using tm.sourceInfo).normalized
      (newTm, UsageType(Some(newTm)))
    case u: UsageType =>
      u.upperBound.map(upperBound => checkType(upperBound, UsageType(None))) match
        case Some(upperBound) => (u, Type(UsageType(Some(upperBound))))
        case _                => (u, Type(u))
    case EffectsType(continuationUsage) =>
      val checkedContinuationUsage = checkType(continuationUsage, UsageType())
      val e = EffectsType(checkedContinuationUsage)
      (e, Type(e))
    case Effects(uncheckedLiteral, checkedOperands) =>
      val literal =
        uncheckedLiteral.map { effInstance =>
          inferType(effInstance) match
            case (newEffInstance, EffectInstanceType(_, _)) => newEffInstance
            case (_, _) => throw ExpectEffectInstance(effInstance)
        }
      val operands = checkedOperands.map { (ref, retainSimple) =>
        val v = checkType(ref, EffectsType())
        (v, retainSimple)
      }
      val newTm: Effects = Effects(literal, operands.to(SeqMap))(using tm.sourceInfo)
      val usage = getEffectsContinuationUsage(newTm)
      (newTm, EffectsType(usage))
    case EffectInstanceType(eff, handlerConstraint) =>
      val newTm = EffectInstanceType(checkEff(eff), handlerConstraint)
      (newTm, Type(newTm))
    case t @ EffectInstance(eff, handlerConstraint, _) =>
      // There is no need to check eff because EffectInstance is only created by reduction.
      (t, EffectInstanceType(eff, handlerConstraint))
    case LevelType(strictUpperBound) =>
      (LevelType(strictUpperBound), Type(LevelType(strictUpperBound)))
    case Level(literal, maxOperands) =>
      val operandsResults = maxOperands.toSeq.map((v, offset) => (inferType(v), offset))
      val newMaxOperands = operandsResults
        .map { case ((t, _), offset) => t -> offset }
        .to(SeqMap)
      val upperbound = operandsResults
        .map {
          case ((_, LevelType(upperbound)), offset) => upperbound.sucAsStrictUpperbound(offset)
          case ((_, t), _) =>
            ctx.checkSolved(
              checkIsConvertible(t, LevelType(LevelOrder.ω), None),
              NotLevelType(t),
            )
            LevelOrder.ω
        }
        .foldLeft(literal.suc())(LevelOrder.orderMax)
      (Level(literal, newMaxOperands), LevelType(upperbound))
    case Auto() => throw IllegalArgumentException("cannot infer type")

@throws(classOf[IrError])
def checkType
  (tm: VTerm, rawTy: VTerm)
  (using Γ: Context)
  (using Σ: Signature)
  (using ctx: TypingContext)
  : VTerm = debugCheckType(tm, rawTy):
  val ty = rawTy.normalized
  tm match
    case Collapse(c) =>
      val tm = checkType(c, F(ty))
      Collapse(tm)
    case Thunk(c) =>
      ty match
        case U(cty) =>
          val tm = checkType(c, cty)
          Thunk(tm)
        case _ => throw ExpectUType(ty)
    case c @ Con(name, uncheckedArgs) =>
      ty match
        case dataType @ DataType(qn, tArgs) =>
          Σ.getConstructorOption(qn, name) match
            case None => throw MissingConstructor(name, qn)
            case Some(con) =>
              val data = Σ.getData(qn)
              val tParamArgs = tArgs.take(data.context.size)
              val tIndexArgs = tArgs.drop(data.context.size)
              val args = checkTypes(uncheckedArgs, con.paramTys.substLowers(tParamArgs*))
              ctx.checkSolved(
                checkAreConvertible(
                  con.tArgs.map(_.substLowers(tParamArgs ++ args*)),
                  tIndexArgs,
                  data.tIndexTys.substLowers(tParamArgs*),
                ),
                UnmatchedDataIndex(c, dataType),
              )
              Con(name, args)
        case _ => throw ExpectDataType(ty)
    case Auto() => Collapse(ctx.addUnsolved(F(ty)))
    case _ =>
      val (newTm, inferred) = inferType(tm)
      val constraints = checkIsSubtype(inferred, ty)
      ctx.checkSolved(constraints, NotVSubtype(inferred, ty))
      newTm

// Precondition: tm is already type-checked
@throws(classOf[IrError])
def inferLevel(ty: CTerm)(using Γ: Context)(using Σ: Signature)(using ctx: TypingContext): VTerm =
  ctx.trace[VTerm](
    "inferLevel",
    Block(ChopDown, Aligned, yellow(ty.sourceInfo), pprint(ty)),
    level => Block(ChopDown, Aligned, yellow(level.sourceInfo), green(pprint(level))),
  ):
    Reducible.reduce(ty) match
      case CType(upperBound, _) => LevelSuc(inferLevel(upperBound))
      case CTop(level, _)       => level
      case F(vTy, _, _)         => inferLevel(vTy)
      case FunctionType(binding, bodyTy, _, _) =>
        val argLevel = inferLevel(binding.ty)
        val bodyLevel = inferLevel(bodyTy)(using Γ :+ binding)
        // strengthen is always safe because the only case that bodyLevel would reference 0 is when
        // arg is of type Level. But in that case the overall level would be ω.
        LevelMax(argLevel.weakened, bodyLevel).normalized(using Γ :+ binding).strengthened
      case RecordType(qn, args, _) => Σ.getRecord(qn).level.substLowers(args*)
      case Force(ctm) =>
        val (_, cty) = inferType(ctm)
        inferLevel(cty)
      case tm =>
        ctx.resolveMetaVariableType(tm) match
          case Some(ty) =>
            ty match
              case CType(upperBound, _) => inferLevel(upperBound)
              case cty =>
                val level = ctx.addUnsolved(F(LevelType(LevelOrder.ω)))
                val usage = ctx.addUnsolved(F(UsageType()))
                ctx.checkSolved(
                  checkIsConvertible(
                    cty,
                    CType(CTop(Collapse(level)), Collapse(usage)),
                    None,
                  ),
                  NotCTypeError(tm),
                )
                Collapse(level).normalized
          case _ => throw NotCTypeError(tm)

@throws(classOf[IrError])
def inferType
  (tm: CTerm)
  (using Γ: Context)
  (using Σ: Signature)
  (using ctx: TypingContext)
  : (CTerm, CTerm) =
  debugInferType(tm):
    tm.normalized match
      case Hole =>
        throw IllegalArgumentException(
          "hole should only be present during reduction",
        )
      case cct @ CapturedContinuationTip(ty) => (cct, ty)
      case CType(uncheckedUpperBound, uncheckedEffects) =>
        val effects = checkType(uncheckedEffects, EffectsType())
        val upperBound = checkIsCType(uncheckedUpperBound)
        val newTm = CType(upperBound.normalized(None), effects.normalized)
        (
          newTm,
          CType(newTm, Total()),
        )
      case CTop(uncheckedLevel, uncheckedEffects) =>
        val effects = checkType(uncheckedEffects, EffectsType())
        val level = checkLevel(uncheckedLevel)
        val newTm = CTop(level, effects.normalized)(using tm.sourceInfo)
        (newTm, CType(newTm, Total()))
      case m: Meta => (m, ctx.resolveMeta(m).contextFreeType)
      case d @ Def(qn) =>
        Σ.getDefinitionOption(qn) match
          case None => throw MissingDeclaration(qn)
          case Some(definition) =>
            (
              d,
              definition.context.foldRight(definition.ty) { case ((binding, es), bodyTy) =>
                FunctionType(
                  binding,
                  bodyTy,
                  Total(),
                  es match
                    // Recursive definition can cause partially elaborated definitions being
                    // referenced.
                    // In this case, we just approximate with EsUnknown to avoid further complexity
                    // in type checking.
                    // Practically, this should be fine since user can always manually annotate if
                    // they don't like this default value.
                    case null => EscapeStatus.EsUnknown
                    case es   => es,
                )
              },
            )
      case Force(uncheckedV) =>
        val (v, vTy) = inferType(uncheckedV)
        val cTy = vTy match
          // TODO: think about whether this is good enough.
          // Annotating all force as maybe-divergent because the computations may be dynamically
          // loaded from handlers and hence there is no way to statically detect cyclic references
          // between computations (functions, etc) unless I make the type system even more
          // complicated to somehow tracking possible call-hierarchy.
          case U(cty) => augmentEffect(Div(), cty)
          case _      => throw ExpectUType(vTy)
        (Force(v), cTy)
      case F(uncheckedVTy, uncheckedEffects, uncheckedUsage) =>
        val effects = checkType(uncheckedEffects, EffectsType())
        val unnormalizedUsage = checkType(uncheckedUsage, UsageType(None))
        val usage = unnormalizedUsage.normalized
        // Prevent returning value of U0 usage, which does not make sense.
        ctx.checkSolved(
          checkUsageSubsumption(usage, UsageLiteral(Usage.U1)),
          NotUsageSubsumption(usage, UsageLiteral(Usage.U1)),
        )
        val levelBound = Collapse(ctx.addUnsolved(F(LevelType(LevelOrder.upperBound))))
        val unnormalizedVTy = checkType(
          uncheckedVTy,
          Type(Collapse(ctx.addUnsolved(F(Type(Top(levelBound)))))),
        )
        val vTy = unnormalizedVTy.normalized
        val newTm = F(vTy, effects, usage)(using tm.sourceInfo)
        (newTm, CType(newTm, Total()))
      case Return(uncheckedV, usage) =>
        val (v, vTy) = inferType(uncheckedV)
        (Return(v, usage), F(vTy, Total()))
      case tm: Let => checkLet(tm, None)
      case FunctionType(binding, uncheckedBodyTy, uncheckedEffects, _) =>
        val effects = checkType(uncheckedEffects, EffectsType())
        val (ty, tyTy) = inferType(binding.ty)
        val bindingUsage = checkType(binding.usage, UsageType(None))
        val (newTm, funTyTy) = tyTy match
          case Type(_) =>
            val bodyContext = Γ :+ binding
            val (bodyTy, bodyTyTy) = inferType(uncheckedBodyTy)(using bodyContext)
            val newTm =
              FunctionType(Binding(ty, bindingUsage)(binding.name), bodyTy, effects.normalized)(
                using tm.sourceInfo,
              )
            bodyTyTy match
              case CType(_, _) if isTotal(bodyTy, Some(bodyTyTy))(using bodyContext) =>
                (
                  newTm,
                  CType(newTm, Total()),
                )
              // TODO[P3]: think about whether the following is actually desirable
              // Automatically promote Return(SomeVType) to F(SomeVType) and proceed type
              // inference.
              case F(Type(_), _, _) if isTotal(bodyTy, Some(bodyTyTy))(using bodyContext) =>
                (
                  newTm,
                  CType(newTm, Total()),
                )
              case CType(_, _) | F(Type(_), _, _) => throw EffectfulCTermAsType(bodyTy)
              case _                              => throw NotCTypeError(bodyTy)
          case _ => throw NotTypeError(binding.ty)
        (newTm, funTyTy)
      case Redex(c, elims) =>
        @throws(classOf[IrError])
        def checkElims
          (checkedElims: List[Elimination[VTerm]], cty: CTerm, elims: List[Elimination[VTerm]])
          : (List[Elimination[VTerm]], CTerm) =
          elims match
            case Nil                                        => (Nil, cty)
            case (e @ ETerm(uncheckedArg)) :: uncheckedRest =>
              // Note that this `cty` is created by `inferType` so it's already checked.
              cty match
                case FunctionType(binding, bodyTy, effects, _) =>
                  val arg = checkType(uncheckedArg, binding.ty)
                  val (rest, cty) =
                    checkElims(
                      e :: checkedElims,
                      bodyTy.substLowers(arg).normalized(None),
                      uncheckedRest,
                    )
                  (
                    ETerm(arg) :: rest,
                    augmentEffect(effects, cty),
                  )
                case _ => throw ExpectFunction(redex(c, checkedElims.reverse))
            case (e @ EProj(name)) :: uncheckedRest =>
              cty match
                case RecordType(qn, args, effects) =>
                  Σ.getFieldOption(qn, name) match
                    case None    => throw MissingField(name, qn)
                    case Some(f) =>
                      // `self` of record is only used in type checking. Hence usages of variables
                      // in the record are not counted.
                      val self = redex(c, checkedElims)
                      val (rest, checkedCty) = checkElims(
                        e :: checkedElims,
                        f.ty.substLowers(args :+ Thunk(self)*).normalized(None),
                        uncheckedRest,
                      )
                      (
                        EProj(name) :: rest,
                        augmentEffect(effects, checkedCty),
                      )
                case _ => throw ExpectRecord(redex(c, checkedElims.reverse))
        val (checkedC, cty) = inferType(c)
        val (_, resultCty) = checkElims(Nil, cty, elims)
        (redex(checkedC, elims), resultCty)
      case RecordType(qn, uncheckedArgs, uncheckedEffects) =>
        Σ.getRecordOption(qn) match
          case None => throw MissingDeclaration(qn)
          case Some(record) =>
            val effects = checkType(uncheckedEffects, EffectsType())
            val args = checkTypes(uncheckedArgs, record.context.map(_._1).toList)
            (RecordType(qn, args, effects), CType(tm, Total()))
      case OperationCall(effInstance, name, uncheckedArgs) =>
        val (qn, uncheckedTArgs) = inferType(effInstance)._2 match
          case EffectInstanceType(eff, _) => eff
          case _ =>
            throw IllegalStateException(
              "operation should have been type checked and verified to be simple before reduction",
            )
        Σ.getEffectOption(qn) match
          case None => throw MissingDeclaration(qn)
          case Some(effect) =>
            Σ.getOperationOption(qn, name) match
              case None => throw MissingDefinition(qn)
              case Some(op) =>
                val checkedTArgs = checkTypes(uncheckedTArgs, effect.context.toList)
                val tArgs = checkedTArgs.map(_.normalized)
                val args = checkTypes(uncheckedArgs, op.paramTys.substLowers(tArgs*))
                val newEff = EffectsLiteral(Set(effInstance))
                val newTm = OperationCall(newEff, name, args)(using tm.sourceInfo)
                val ty = op.resultTy.substLowers(tArgs ++ args*).normalized
                (
                  newTm,
                  F(
                    ty,
                    // TODO[p4]: figure out if there is way to better manage divergence for handler
                    // operations. The dynamic nature of handler dispatching makes it impossible to
                    // know at compile time whether this would lead to a cyclic reference in
                    // computations.
                    EffectsLiteral(Set(effInstance, div)),
                  ),
                )
      case Continuation(uncheckedHandler, continuationUsage) =>
        @tailrec
        def findTip(c: CTerm): CapturedContinuationTip = c match
          case c: CapturedContinuationTip => c
          case l: Let                     => findTip(l)
          case h: Handler                 => findTip(h.input)
          case r: Redex                   => findTip(r.t)
          case _                          => throw IllegalStateException("impossible term")
        val CapturedContinuationTip(F(resultTy, _, resultUsage)) = findTip(uncheckedHandler)
        val (checkedHandler, outputTy) = inferType(uncheckedHandler)
        val handler = checkedHandler.asInstanceOf[Handler]
        val paramLevel = inferLevel(handler.parameterBinding.ty)
        val resultLevel = inferLevel(resultTy)
        val outputLevel = inferLevel(outputTy)
        val continuationLevel = LevelMax(paramLevel, resultLevel, outputLevel).normalized
        (
          Continuation(handler, continuationUsage),
          RecordType(
            Builtins.ContinuationQn,
            List(
              continuationLevel,
              UsageLiteral(continuationUsage),
              handler.parameterBinding.usage,
              handler.parameterBinding.ty,
              resultUsage,
              resultTy,
              handler.otherEffects,
              handler.handlerEffects,
              handler.outputUsage,
              handler.outputTy,
            ),
          ),
        )
      case h: Handler => checkHandler(h, None)

@throws(classOf[IrError])
def checkType
  (tm: CTerm, ty: CTerm)
  (using Γ: Context)
  (using Σ: Signature)
  (using ctx: TypingContext)
  : CTerm = debugCheckType(tm, ty):
  tm match
    case Force(v) =>
      val checkedV = checkType(v, U(ty))
      Force(checkedV)
    case Return(v, uncheckedUsage) =>
      ty match
        case F(ty, _, expectedUsage) =>
          // Usage annotation is erased and hence its usages are ignored.
          val usage = checkType(uncheckedUsage, UsageType())
          val checkedV = checkType(v, ty)
          ctx.checkSolved(
            checkUsageSubsumption(usage, expectedUsage),
            NotUsageSubsumption(usage, expectedUsage),
          )
          Return(checkedV, usage)
        case _ => throw ExpectFType(ty)
    case l: Let     => checkLet(l, Some(ty))._1
    case h: Handler => checkHandler(h, Some(ty))._1
    case _ =>
      val (checkedTm, tmTy) = inferType(tm)
      val normalizedTy = ty.normalized(None)
      ctx.checkSolved(checkIsSubtype(tmTy, normalizedTy), NotCSubtype(tmTy, normalizedTy))
      checkedTm

private object MetaVarVisitor extends Visitor[TypingContext, Set[Int]]():
  override def combine(rs: Set[Int]*)(using ctx: TypingContext)(using Σ: Signature): Set[Int] =
    rs.flatten.to(Set)
  override def visitMeta(m: Meta)(using ctx: TypingContext)(using Σ: Signature): Set[Int] =
    Set(m.index) ++ (ctx.resolveMeta(m) match
      // bounds in unsolved doesn't need to be checked now. They will be checked when they become solved.
      case _: Unsolved             => Set.empty
      case Guarded(_, _, value, _) => visitCTerm(value)
      case Solved(_, _, value)     => visitCTerm(value)
    )

@throws(classOf[IrError])
def checkTypes
  (tms: Seq[VTerm], tys: Telescope)
  (using Γ: Context)
  (using Σ: Signature)
  (using ctx: TypingContext)
  : List[VTerm] =
  ctx.trace("checking multiple terms"):
    if tms.length != tys.length then throw TelescopeLengthMismatch(tms, tys)
    else
      tms
        .zip(tys)
        .zipWithIndex
        .map { case ((tm, binding), index) =>
          checkType(tm, binding.ty.substLowers(tms.take(index)*))
        }
        .toList

@throws(classOf[IrError])
private def checkLet
  (tm: Let, bodyTy: Option[CTerm])
  (using Γ: Context)
  (using Σ: Signature)
  (using TypingContext)
  : (CTerm, CTerm) =
  def checkInlinedBody(inlinedBody: CTerm, eff: VTerm) =
    val (newBody, newBodyTy) = bodyTy match
      case Some(bodyTy) =>
        val checkedBodyTy = checkIsCType(bodyTy)
        val newBody = checkType(inlinedBody, checkedBodyTy)
        (newBody, bodyTy)
      case None =>
        inferType(inlinedBody)
    (newBody, augmentEffect(eff, newBodyTy))

  def isAutoOrUAny(u: VTerm): Boolean = u match
    case Auto() | UsageLiteral(Usage.UAny) => true
    case _                                 => false
  def isAutoOrTotal(eff: VTerm): Boolean = eff match
    case Auto()     => true
    case e: Effects => e == total
    case _          => false
  tm match
    // Take the shortcut to inline immediate values. This is more than just an optimization because
    // one cannot infer type of constructors. Hence inlining constructor calls is the only way to
    // type check them without requiring type annotations on let.
    case Let(Return(v, u1), Binding(ty, u2), eff, body)
      if isAutoOrUAny(u1) && isAutoOrUAny(u2) && isAutoOrTotal(eff) =>
      ty match
        case Auto() =>
        case ty     => checkIsType(ty)
      checkInlinedBody(body.substLowers(v), eff)
    case Let(t, Binding(ty, usage), eff, body) =>
      val checkedEff = checkType(eff, EffectsType()).normalized
      val checkedUsage = checkType(usage, UsageType(None)).normalized
      val checkedTy = checkIsType(ty)
      val tTy = F(checkedTy, checkedEff, checkedUsage)
      val checkedT = checkType(t, tTy)
      //    // If some usages are not zero or unres, inlining `t` would change usage checking
      //    // result because
      //    //
      //    // * either some linear or relevant usages becomes zero because the computation
      //    //   gets removed
      //    //
      //    // * or if the term is wrapped inside a `Collapse` and get multiplied
      //    //
      //    // Such changes would alter usage checking result, which can be confusing for
      //    // users. Note that, it's still possible that with inlining causes usages to be
      //    // removed, but the `areTUsagesZeroOrUnrestricted` check ensures the var has
      //    // unrestricted usage. Hence, usage checking would still pass. On the other hand,
      //    // it's not possible for inlining to create usage out of nowhere.
      def areTUsagesZeroOrUnrestricted: Boolean =
        // Note that we can't do conversion check here because doing conversion check assumes it must be the case or
        // type check would fail. But here the usage can very well not be convertible with U0 or UAny.
        collectUsages(t, Some(tTy)).forall { usage =>
          usage == uAny || usage == u0
        }
      if isTotal(checkedT, Some(tTy)) && areTUsagesZeroOrUnrestricted then
        // When syntactically one cannot tell if `t` is simply a value, we do the more sophisticated
        // totality check, so that conversion check can take more specific values into account.
        val uncheckedNewBody = t.normalized(Some(tTy)) match
          case Return(v, _) => body.substLowers(v)
          case c            => body.substLowers(Collapse(c))
        checkInlinedBody(uncheckedNewBody, checkedEff)
      else
        val checkedBinding = Binding(checkedTy, checkedUsage)(gn"v")
        val (checkedBody, checkedBodyTy) =
          given Context = Γ :+ checkedBinding
          bodyTy match
            case None => inferType(tm.body)
            case Some(uncheckedBodyTy) =>
              val bodyTy = checkIsCType(uncheckedBodyTy)(using Γ)
              val body = checkType(tm.body, bodyTy.weakened)
              (body, bodyTy)
        val leakCheckedBodyTy =
          checkVar0Leak(checkedBodyTy, LeakedReferenceToEffectfulComputationResult(t))
        (
          Let(checkedT, checkedBinding, checkedEff, checkedBody)(using tm.sourceInfo),
          augmentEffect(checkedEff, leakCheckedBodyTy.strengthened),
        )

@throws(classOf[IrError])
def checkHandler
  (h: Handler, outputType: Option[CTerm])
  (using Γ: Context)
  (using Σ: Signature)
  (using ctx: TypingContext)
  : (CTerm, CTerm) =
  val eff = checkEff(h.eff)
  val operations = Σ.getOperations(eff._1).map(op => (eff._1 / op.name, eff._2, op)).toSet
  val expectedOperationNames = operations.map(_._1)
  val actualOperationNames = h.handlers.keySet
  if expectedOperationNames != actualOperationNames then
    throw HandlerOperationsMismatch(h, expectedOperationNames, actualOperationNames)
  val otherEffects = checkType(h.otherEffects, EffectsType()).normalized
  val inputTy = checkIsType(h.inputBinding.ty)
  // Unlike parameter, input is a computation and hence only executed linearly. The input binding usage is simply a
  // requirement on the final return type of the input computation.
  val inputBindingUsage = checkType(h.inputBinding.usage, UsageType())
  val inputBinding = Binding(inputTy, inputBindingUsage)(h.inputBinding.name)
  val inputΓ = Γ :+ Binding(
    EffectInstanceType(
      h.eff,
      h.handlers.values.foldLeft(HandlerConstraint(Usage.U1, HandlerType.Simple))((c, impl) =>
        c | impl.handlerConstraint,
      ),
    ),
  )(gn"e")
  val inputEffects =
    Effects(Set(Var(0)), SeqMap(otherEffects.weakened /* for effect instance */ -> false))
      .normalized(using inputΓ)
  val input = checkType(
    h.input,
    F(
      inputTy.weakened /* for effect instance */,
      inputEffects,
      inputBindingUsage.weakened, /* for effect instance */
    ),
  )(using inputΓ)
  val effInsDbNumber = Γ.size
  val effInsEscapeStatus =
    computeEscapeStatuses(h.input, Set(effInsDbNumber))(using inputΓ)(effInsDbNumber)
  effInsEscapeStatus match
    // If effect instance does not escape, there is no need to check anything.
    case EscapeStatus.EsLocal =>
    case _ =>
      ctx.checkSolved(
        checkEffectSubsumption(EffectsLiteral(Set(ndet)), otherEffects),
        EscapedEffectInstanceCausesNdet(h),
      )
  val handlerEffects = checkType(h.handlerEffects, EffectsType()).normalized
  val outputEffects = EffectsUnion(otherEffects, handlerEffects).normalized
  val outputUsage = checkType(h.outputUsage, UsageType()).normalized
  val outputTy = checkIsType(h.outputTy)
  outputType match
    case None =>
    case Some(outputType) =>
      ctx.checkSolved(
        checkIsSubtype(F(outputTy, outputEffects, outputUsage), outputType),
        NotCSubtype(F(outputTy, outputEffects, outputUsage), outputType),
      )
  val parameterTy = checkIsType(h.parameterBinding.ty)
  // parameter binding usage dictates how much resources the handler needs when consuming the parameter
  val parameterBindingUsage = checkType(h.parameterBinding.usage, UsageType())
  val parameterBinding = Binding(parameterTy, parameterBindingUsage)(h.parameterBinding.name)
  val parameter = checkType(h.parameter, parameterTy)
  val inputEffectsContinuationUsage = getEffectsContinuationUsage(inputEffects)
  val parameterDisposer = h.parameterDisposer match
    case Some(parameterDisposer) =>
      val checkedParameterDisposer = checkType(
        parameterDisposer,
        F(DataType(Builtins.UnitQn, Nil), EffectsRetainSimpleLinear(handlerEffects).weakened),
      )(using Γ :+ parameterBinding)
      Some(checkedParameterDisposer)
    case None =>
      (inputEffectsContinuationUsage, parameterBindingUsage) match
        case (UsageLiteral(effUsage), UsageLiteral(paramUsage))
          if effUsage <= Usage.URel || paramUsage >= Usage.U0 =>
          None
        case _ => throw ExpectParameterDisposer(h)
  val parameterReplicator = h.parameterReplicator match
    case Some(parameterReplicator) =>
      val checkedParameterReplicator = checkType(
        parameterReplicator,
        F(
          DataType(
            Builtins.PairQn,
            List(
              LevelUpperBound(),
              parameterBindingUsage,
              parameterTy,
              parameterBindingUsage,
              parameterTy,
            ),
          ),
          EffectsRetainSimpleLinear(handlerEffects),
        ).weakened,
      )(using Γ :+ parameterBinding)
      Some(checkedParameterReplicator)
    case None =>
      (inputEffectsContinuationUsage, parameterBindingUsage) match
        case (UsageLiteral(effUsage), UsageLiteral(paramUsage))
          if effUsage <= Usage.UAff || paramUsage >= Usage.URel || paramUsage == Usage.U0 =>
          None
        case _ => throw ExpectParameterReplicator(h)
  val transform = checkType(
    h.transform,
    F(outputTy, handlerEffects, outputUsage).weaken(2, 0),
  )(using Γ :+ parameterBinding :+ inputBinding.weakened)

  val handlerAndUsages = operations.map { (qn, effArgs, operation) =>
    val effect = Σ.getEffect(qn.parent)
    val handlerImpl = h.handlers(qn)
    // Note that usage subsumption check is reversed because this is checking how continuation
    // can be used by handler.
    checkUsageSubsumption(
      effect.continuationUsage.substLowers(effArgs*),
      UsageLiteral(handlerImpl.handlerConstraint.continuationUsage),
    )
    // The followings do not need to be weakened for handler parameter because after substituting the effect args,
    // they do not contain any free variables beyond beginning of paramTys.
    val paramTys = operation.paramTys.substLowers(effArgs*)
    val resultTy = operation.resultTy.substLowers(effArgs*)
    val resultUsage = operation.resultUsage.substLowers(effArgs*)
    val handlerImplBodyTy = checkIsCType(handlerImpl.bodyTy)
    val newHandlerImpl = handlerImpl.handlerConstraint match
      case HandlerConstraint(continuationUsage, HandlerType.Simple) =>
        given implΓ: Context = Γ ++ (parameterBinding +: paramTys)
        val implOffset = implΓ.size - Γ.size
        val uncheckedImplTy = continuationUsage match
          case U1 =>
            F(
              DataType(
                Builtins.PairQn,
                List(
                  Auto(),
                  Auto(),
                  parameterBindingUsage.weaken(implOffset, 0),
                  parameterTy.weaken(implOffset, 0),
                  resultUsage,
                  resultTy,
                ),
              ),
              Auto(),
              u1,
            )
          case U0 =>
            F(
              DataType(
                Builtins.PairQn,
                List(
                  Auto(),
                  Auto(),
                  parameterBindingUsage.weaken(implOffset, 0),
                  parameterTy.weaken(implOffset, 0),
                  outputUsage.weaken(implOffset, 0),
                  outputTy.weaken(implOffset, 0),
                ),
              ),
              Auto(),
              u1,
            )
          case UAff =>
            F(
              DataType(
                Builtins.PairQn,
                List(
                  Auto(),
                  Auto(),
                  parameterBindingUsage.weaken(implOffset, 0),
                  parameterTy.weaken(implOffset, 0),
                  u1,
                  DataType(
                    Builtins.EitherQn,
                    List(
                      Auto(),
                      Auto(),
                      outputUsage.weaken(implOffset, 0),
                      outputTy.weaken(implOffset, 0),
                      resultUsage,
                      resultTy,
                    ),
                  ),
                ),
              ),
              Auto(),
              u1,
            )
          case _ => throw IllegalStateException("bad continuation usage on operation")
        val implOutputEffects = handlerEffects.weaken(implOffset, 0)
        val bodyTy = checkIsCType(uncheckedImplTy)
        ctx.checkSolved(
          checkIsConvertible(handlerImplBodyTy, bodyTy, None),
          NotCConvertible(handlerImplBodyTy, bodyTy, None),
        )
        val body = checkType(handlerImpl.body, bodyTy)
        val effects = bodyTy.asInstanceOf[CType].effects
        // Simple operation can only perform U1 effects so that linear resources in the continuation
        // are managed correctly.
        ctx.checkSolved(
          checkUsageSubsumption(getEffectsContinuationUsage(effects), u1),
          ExpectU1Effect(qn),
        )
        ctx.checkSolved(
          checkEffectSubsumption(
            bodyTy.asInstanceOf[F].effects,
            EffectsRetainSimpleLinear(implOutputEffects),
          ),
          NotEffectSubsumption(effects, implOutputEffects),
        )
        handlerImpl.copy(body = body)(handlerImpl.boundNames)
      case HandlerConstraint(continuationUsage, HandlerType.Complex) =>
        given continuationΓ: Context = Γ ++ (parameterBinding +: paramTys.weakened)
        val continuationWeakenOffset = continuationΓ.size - Γ.size
        val continuationParameterTy = parameterTy.weaken(continuationWeakenOffset, 0)
        val continuationOutputTy = outputTy.weaken(continuationWeakenOffset, 0)
        val continuationOtherEffects = otherEffects.weaken(continuationWeakenOffset, 0)
        val continuationHandlerEffects = handlerEffects.weaken(continuationWeakenOffset, 0)
        val continuationOutputUsage = outputUsage.weaken(continuationWeakenOffset, 0)
        val continuationType = RecordType(
          Builtins.ContinuationQn,
          List(
            Auto(),
            UsageLiteral(continuationUsage),
            parameterBindingUsage.weaken(continuationWeakenOffset, 0),
            continuationParameterTy,
            resultUsage.weaken(continuationWeakenOffset, 0),
            resultTy,
            continuationOtherEffects,
            continuationHandlerEffects,
            continuationOutputUsage,
            continuationOutputTy,
          ),
        )
        val checkedContinuationType = U(checkIsCType(continuationType))
        val handlerImplContinuationType = handlerImpl.continuationType match
          case None =>
            throw IllegalStateException(
              "This cannot happen since it's checked during HandlerImpl construction",
            )
          case Some(continuationType) => checkIsType(continuationType)
        ctx.checkSolved(
          checkIsConvertible(handlerImplContinuationType, checkedContinuationType, None),
          NotVConvertible(handlerImplContinuationType, checkedContinuationType, None),
        )
        val implΓ: Context =
          continuationΓ :+ Binding(checkedContinuationType, u1)(
            gn"continuation",
          )
        val implOffset = implΓ.size - Γ.size
        val bodyTy = F(
          outputTy.weaken(implOffset, 0),
          outputEffects.weaken(implOffset, 0),
          outputUsage.weaken(implOffset, 0),
        )
        ctx.checkSolved(
          checkIsConvertible(handlerImplBodyTy, bodyTy, None),
          NotCConvertible(handlerImplBodyTy, bodyTy, None),
        )
        val body = checkType(
          handlerImpl.body,
          bodyTy,
        )(using implΓ)
        handlerImpl.copy(body = body)(handlerImpl.boundNames)
    (qn, newHandlerImpl)
  }
  (
    Handler(
      eff,
      otherEffects,
      handlerEffects,
      outputUsage,
      outputTy,
      parameter,
      parameterBinding,
      parameterDisposer,
      parameterReplicator,
      transform,
      handlerAndUsages.to(SeqMap),
      input,
      inputBinding,
    )(using h.sourceInfo),
    F(outputTy, outputEffects, outputUsage),
  )

@throws(classOf[IrError])
private def checkEff(eff: Eff)(using Γ: Context)(using Σ: Signature)(using TypingContext): Eff =
  val (qn, args) = eff
  val effect = Σ.getEffect(qn)
  val newArgs = checkTypes(args, effect.context.toList)
  (qn, newArgs)

// Input effects should be type-checked.
// returned effects should be normalized
@throws(classOf[IrError])
private def getEffectsContinuationUsage
  (effects: VTerm)
  (using Γ: Context)
  (using Σ: Signature)
  (using ctx: TypingContext)
  : VTerm =
  val usage = ctx.withMetaResolved(effects.normalized):
    case Effects(effectInstances, operands) =>
      val literalUsages = effectInstances.map { effectInstance =>
        inferType(effectInstance)._2 match
          case EffectInstanceType(_, handlerConstraint) =>
            UsageLiteral(handlerConstraint.continuationUsage)
          case _ => throw IllegalStateException("type error")
      }
      val usages = operands.keySet.map(getEffectsContinuationUsage)
      UsageJoin(Set(UsageLiteral(U1)) ++ usages ++ literalUsages)
    case v: Var =>
      Γ.resolve(v).ty match
        case EffectsType(continuationUsage) => continuationUsage
        case _                              => throw IllegalStateException("type error")
    case r: ResolvedMetaVariable =>
      r.ty match
        case F(EffectsType(continuationUsage), _, _) => continuationUsage
        case _                                       => throw IllegalStateException("type error")
    case _ => UsageLiteral(UAny)
  usage.normalized

@throws(classOf[IrError])
def checkIsType
  (uncheckedVTy: VTerm, levelBound: Option[VTerm] = None)
  (using Γ: Context)
  (using Signature)
  (using ctx: TypingContext)
  : VTerm =
  ctx.trace(
    "checking is type",
    Block(ChopDown, Aligned, yellow(uncheckedVTy.sourceInfo), pprint(uncheckedVTy)),
  ):
    checkType(
      uncheckedVTy,
      Type(Top(levelBound.getOrElse(LevelLiteral(LevelOrder.upperBound)))),
    )

@throws(classOf[IrError])
def checkIsCType
  (uncheckedCTy: CTerm, levelBound: Option[VTerm] = None)
  (using Γ: Context)
  (using Signature)
  (using ctx: TypingContext)
  : CTerm =
  ctx.trace("checking is C type", Block(yellow(uncheckedCTy.sourceInfo), pprint(uncheckedCTy))):
    checkType(
      uncheckedCTy,
      CType(
        CTop(
          levelBound.getOrElse(LevelLiteral(LevelOrder.upperBound)),
          Collapse(ctx.addUnsolved(F(EffectsType()))),
        ),
      ),
    )

@throws(classOf[IrError])
def reduceUsage(usage: CTerm)(using Context)(using Signature)(using ctx: TypingContext): VTerm =
  ctx.trace("reduce usage", Block(yellow(usage.sourceInfo), pprint(usage))):
    checkType(usage, F(UsageType()))
    val reduced = reduce(usage)
    reduced match
      case Return(u, _) => u
      case _ =>
        throw IllegalStateException(
          "type checking has bugs: reduced value of type `F(UsageType())` must be `Return(u)`.",
        )

@throws(classOf[IrError])
def reduceVType
  (uncheckedVTy: CTerm)
  (using Context)
  (using Signature)
  (using ctx: TypingContext)
  : VTerm =
  ctx.trace("reduce V type", Block(yellow(uncheckedVTy.sourceInfo), pprint(uncheckedVTy))):
    val (vTy, tyTy) = inferType(uncheckedVTy)
    tyTy match
      case F(Type(_), _, _) if isTotal(vTy, Some(tyTy)) =>
        reduce(vTy) match
          case Return(vTy, _) => vTy
          case _ =>
            throw IllegalStateException(
              "type checking has bugs: reduced value of type `F ...` must be `Return ...`.",
            )
      case F(_, _, _) => throw EffectfulCTermAsType(vTy)
      case _          => throw ExpectFType(vTy)

private def augmentEffect(eff: VTerm, cty: CTerm): CTerm = cty match
  case CType(upperBound, effects) =>
    CType(upperBound, EffectsUnion(eff, effects))
  case CTop(level, effects)   => CTop(level, EffectsUnion(eff, effects))
  case F(vTy, effects, usage) => F(vTy, EffectsUnion(eff, effects), usage)
  case FunctionType(binding, bodyTy, effects, es) =>
    FunctionType(
      binding,
      bodyTy,
      EffectsUnion(eff, effects),
      es,
    )
  case RecordType(qn, args, effects) =>
    RecordType(qn, args, EffectsUnion(eff, effects))
  case _ => throw IllegalArgumentException(s"trying to augment $cty with $eff")

// Report an error if the type of `body` needs to reference the effectful
// computation. User should use a dependent sum type to wrap such
// references manually to avoid the leak.
// TODO[P3]: in case weakened failed, provide better error message: ctxTy cannot depend on
//  the bound variable
@throws(classOf[IrError])
private def checkVar0Leak[T <: CTerm | VTerm](ty: T, error: => IrError)(using Σ: Signature): T =
  val freeVars = ty match
    case ty: CTerm => FreeVarsVisitor.visitCTerm(ty)(using 0)
    case ty: VTerm => FreeVarsVisitor.visitVTerm(ty)(using 0)
  if freeVars.exists(_.idx == 0) then throw error
  else
    ty match
      case ty: CTerm => ty.strengthened.asInstanceOf[T]
      case ty: VTerm => ty.strengthened.asInstanceOf[T]

def isMeta(t: VTerm): Boolean = t match
  case Collapse(Redex(Meta(_), _)) => true
  case Collapse(Meta(_))           => true
  case _                           => false

private def extractDistinctArgVars(args: Seq[VTerm]): Option[List[Nat]] =
  val argVars = args.collect { case v: Var => v.idx }
  if argVars.distinct.length == argVars.length then Some(argVars.toList)
  else None

@throws(classOf[IrError])
private inline def debugCheckType[R]
  (tm: CTerm | VTerm, ty: CTerm | VTerm)
  (result: => R)
  (using Context)
  (using Signature)
  (using ctx: TypingContext)
  : R =
  ctx.trace(
    "checkType",
    Block(
      ChopDown,
      Aligned,
      yellow(tm.sourceInfo),
      pprint(tm),
      ":",
      yellow(ty.sourceInfo),
      pprint(ty),
    ),
  )(
    result,
  )

private inline def debugInferType[R <: CTerm | VTerm]
  (tm: R)
  (result: => (R, R))
  (using Context)
  (using Signature)
  (using ctx: TypingContext)
  : (R, R) =
  ctx.trace[(R, R)](
    s"inferType",
    Block(ChopDown, Aligned, yellow(tm.sourceInfo), pprint(tm)),
    ty => Block(ChopDown, Aligned, yellow(ty._1.sourceInfo), green(pprint(ty._2))),
  ):
    result
