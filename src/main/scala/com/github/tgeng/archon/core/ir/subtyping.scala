package com.github.tgeng.archon.core.ir

import com.github.tgeng.archon.common.*
import com.github.tgeng.archon.common.IndentPolicy.*
import com.github.tgeng.archon.common.WrapPolicy.*
import com.github.tgeng.archon.core.common.*
import com.github.tgeng.archon.core.ir.CTerm.*
import com.github.tgeng.archon.core.ir.Declaration.*
import com.github.tgeng.archon.core.ir.EqDecidability.*
import com.github.tgeng.archon.core.ir.HandlerType.{Complex, Simple}
import com.github.tgeng.archon.core.ir.IrError.*
import com.github.tgeng.archon.core.ir.PrettyPrinter.pprint
import com.github.tgeng.archon.core.ir.ResolvedMetaVariable.*
import com.github.tgeng.archon.core.ir.UnsolvedMetaVariableConstraint.*
import com.github.tgeng.archon.core.ir.Usage.*
import com.github.tgeng.archon.core.ir.VTerm.*

import scala.collection.mutable.ArrayBuffer
import scala.math.Ordering.ordered

/** Preconditions: sub and sup are both checked to be types
  */
@throws(classOf[IrError])
def checkIsSubtype
  (sub: VTerm, sup: VTerm)
  (using Γ: Context)
  (using Σ: Signature)
  (using ctx: TypingContext)
  : Set[Constraint] = debugSubsumption("checkIsSubtype", sub, sup):
  check2(sub, sup):
    case (_, _) if sub == sup => Set.empty
    case (sub: VTerm, u @ RUnsolved(_, _, constraint, _, _)) =>
      ctx.adaptForMetaVariable(u, sub) match
        case None => Set(Constraint.VSubType(Γ, sub, sup))
        case Some(value) =>
          val newConstraint = constraint match
            case UmcNothing                      => UmcVSubtype(Set(value))
            case UmcVSubtype(existingLowerBound) => UmcVSubtype(existingLowerBound + value)
            case _                               => throw IllegalStateException("type error")
          ctx.updateConstraint(u, newConstraint)
          Set.empty
    case (u @ RUnsolved(_, _, UmcVSubtype(existingLowerBound), _, _), sup: VTerm) =>
      ctx.adaptForMetaVariable(u, sub) match
        case Some(value) if value == existingLowerBound => ctx.assignUnsolved(u, Return(value, u1))
        case _                                          => Set(Constraint.VSubType(Γ, sub, sup))
    case (_: ResolvedMetaVariable, _) | (_, _: ResolvedMetaVariable) =>
      Set(Constraint.VSubType(Γ, sub, sup))
    case (Type(upperBound1), Type(upperBound2)) => checkIsSubtype(upperBound1, upperBound2)
    case (ty: VTerm, Top(level2, eqD2)) =>
      val levelConstraints = checkLevelSubsumption(inferLevel(ty), level2)
      val eqDecidabilityConstraints = checkEqDecidabilitySubsumption(inferEqDecidability(ty), eqD2)
      levelConstraints ++ eqDecidabilityConstraints
    case (U(cty1), U(cty2)) => checkIsSubtype(cty1, cty2)
    case (DataType(qn1, args1), DataType(qn2, args2)) if qn1 == qn2 =>
      Σ.getDataOption(qn1) match
        case None => throw MissingDeclaration(qn1)
        case Some(data) =>
          val args = ArrayBuffer[VTerm]()
          args1
            .zip(args2)
            .zip(data.context ++ data.tIndexTys.map((_, Variance.INVARIANT)))
            .map { case ((arg1, arg2), (binding, variance)) =>
              variance match
                case Variance.INVARIANT =>
                  val r = checkIsConvertible(
                    arg1,
                    arg2,
                    Some(binding.ty.substLowers(args.toSeq: _*)),
                  )
                  args += arg1
                  r
                case Variance.COVARIANT =>
                  val (checkedArg1, _) = checkIsType(arg1)
                  val (checkedArg2, _) = checkIsType(arg2)
                  val r = checkIsSubtype(checkedArg1, checkedArg2)
                  args += checkedArg1
                  r
                case Variance.CONTRAVARIANT =>
                  val (checkedArg1, _) = checkIsType(arg1)
                  val (checkedArg2, _) = checkIsType(arg2)
                  val r = checkIsSubtype(checkedArg1, checkedArg2)
                  args += checkedArg2
                  r
            }
            .flatten
            .toSet
    case (
        EffectsType(continuationUsage1, handlerType1),
        EffectsType(continuationUsage2, handlerType2),
      ) =>
      checkHandlerTypeSubsumption(handlerType1, handlerType2)
      // Note that subsumption checking is reversed because the effect of the computation
      // marks how the continuation can be invoked. Normally, checking usage is checking
      // how a resource is *consumed*. But here, checking usage is checking how the
      // continuation (as a resource) is provided.
      checkUsageSubsumption(continuationUsage2, continuationUsage1)
    case (UsageType(Some(u1)), UsageType(Some(u2))) => checkUsageSubsumption(u1, u2)
    case (UsageType(Some(_)), UsageType(None))      => Set.empty
    case (v: Var, ty2: VTerm) =>
      Γ.resolve(v).ty match
        case Type(upperBound) => checkIsSubtype(upperBound, ty2)
        case _                => throw NotVSubtype(sub, sup)
    case (LevelType(ub1), LevelType(ub2)) => checkLevelSubsumption(ub1, ub2)
    case _                                => checkIsConvertible(sub, sup, None)

/** Preconditions: sub and sup are both types
  */
@throws(classOf[IrError])
def checkIsSubtype
  (sub: CTerm, sup: CTerm)
  (using Γ: Context)
  (using Σ: Signature)
  (using ctx: TypingContext)
  : Set[Constraint] = debugSubsumption("checkIsSubtype", sub, sup):
  check2(sub, sup):
    case (_, _) if sub == sup => Set.empty[Constraint]
    case (sub: CTerm, (u @ RUnsolved(_, _, constraint, _, _), Nil)) =>
      ctx.adaptForMetaVariable(u, sub) match
        case None => Set(Constraint.CSubType(Γ, sub, sup))
        case Some(value) =>
          val newConstraint = constraint match
            case UmcNothing                      => UmcCSubtype(Set(value))
            case UmcCSubtype(existingLowerBound) => UmcCSubtype(existingLowerBound + value)
            case _                               => throw IllegalStateException("type error")
          ctx.updateConstraint(u, newConstraint)
          Set.empty
    case ((u @ RUnsolved(_, _, UmcCSubtype(existingLowerBound), _, _), Nil), sup: CTerm) =>
      ctx.adaptForMetaVariable(u, sub) match
        case Some(value) if value == existingLowerBound => ctx.assignUnsolved(u, value)
        case _                                          => Set(Constraint.CSubType(Γ, sub, sup))
    case ((_: ResolvedMetaVariable, Nil), _) | (_, (_: ResolvedMetaVariable, Nil)) =>
      Set(Constraint.CSubType(Γ, sub, sup))
    case (CType(upperBound1, eff1), CType(upperBound2, eff2)) =>
      val effConstraint = checkEffSubsumption(eff1, eff2)
      val upperBoundConstraint = checkIsSubtype(upperBound1, upperBound2)
      effConstraint ++ upperBoundConstraint
    case (ty: IType, CTop(level2, eff2)) =>
      val levelConstraint = checkLevelSubsumption(inferLevel(sub), level2)
      val effConstraint = checkEffSubsumption(ty.effects, eff2)
      levelConstraint ++ effConstraint
    case (F(vTy1, eff1, u1), F(vTy2, eff2, u2)) =>
      val effConstraint = checkEffSubsumption(eff1, eff2)
      val usageConstraint = checkUsageSubsumption(u1, u2)
      val tyConstraint = checkIsSubtype(vTy1, vTy2)
      effConstraint ++ usageConstraint ++ tyConstraint
    case (
        FunctionType(binding1, bodyTy1, eff1),
        FunctionType(binding2, bodyTy2, eff2),
      ) =>
      val effConstraint = checkEffSubsumption(eff1, eff2)
      val tyConstraint = ctx.solve(checkIsSubtype(binding2.ty, binding1.ty))
      val bodyConstraint =
        if tyConstraint.isEmpty
        then checkIsSubtype(bodyTy1, bodyTy2)(using Γ :+ binding2)
        else
          given Context = Γ :+ binding2
          checkIsSubtype(
            bodyTy1,
            bodyTy2.subst {
              case 0 =>
                Some(
                  Collapse(
                    ctx.addGuarded(
                      F(binding1.ty.weakened, Total(), binding1.usage.weakened),
                      Return(Var(0), u1),
                      tyConstraint,
                    ),
                  ),
                )
              case _ => None
            },
          )
      effConstraint ++ tyConstraint ++ bodyConstraint
    case (RecordType(qn1, args1, eff1), RecordType(qn2, args2, eff2)) if qn1 == qn2 =>
      Σ.getRecordOption(qn1) match
        case None => throw MissingDeclaration(qn1)
        case Some(record) =>
          val args = ArrayBuffer[VTerm]()
          val effConstraint = checkEffSubsumption(eff1, eff2)
          val argConstraint = args1
            .zip(args2)
            .zip(record.context)
            .map { case ((arg1, arg2), (binding, variance)) =>
              variance match
                case Variance.INVARIANT =>
                  val r = checkIsConvertible(
                    arg1,
                    arg2,
                    Some(binding.ty.substLowers(args.toSeq: _*)),
                  )
                  args += arg1
                  r
                case Variance.COVARIANT =>
                  val (checkedArg1, _) = checkIsType(arg1)
                  val (checkedArg2, _) = checkIsType(arg2)
                  val r = checkIsSubtype(checkedArg1, checkedArg2)
                  args += checkedArg1
                  r
                case Variance.CONTRAVARIANT =>
                  val (checkedArg1, _) = checkIsType(arg1)
                  val (checkedArg2, _) = checkIsType(arg2)
                  val r = checkIsSubtype(checkedArg1, checkedArg2)
                  args += checkedArg2
                  r
            }
            .flatten
            .toSet
          effConstraint ++ argConstraint
    case _ => checkIsConvertible(sub, sup, None)

private type StuckComputationType = Redex | Force | Meta | Def | Let | Handler

@throws(classOf[IrError])
private def typeUnion
  (a: CTerm, b: CTerm)
  (using Γ: Context)
  (using Σ: Signature)
  (using TypingContext)
  : CTerm =
  if a == b then a
  else
    (a, b) match
      case (CType(upperBound1, effects1), CType(upperBound2, effects2)) =>
        val upperBound = typeUnion(upperBound1, upperBound2)
        val effects = EffectsUnion(effects1, effects2).normalized
        CType(upperBound, effects)
      case (CTop(level1, effects1), CTop(level2, effects2)) =>
        val level = LevelMax(level1, level2).normalized
        val effects = EffectsUnion(effects1, effects2).normalized
        CTop(level, effects)
      case (F(vty1, effects1, usage1), F(vty2, effects2, usage2)) =>
        val vty = typeUnion(vty1, vty2)
        val effects = EffectsUnion(effects1, effects2).normalized
        val usage = UsageJoin(usage1, usage2).normalized
        F(vty, effects, usage)
      // for simplicity we just treat types at contravariant position as invariant
      case (FunctionType(binding1, body1, effects1), FunctionType(binding2, body2, effects2))
        if binding1 == binding2 =>
        val effects = EffectsUnion(effects1, effects2).normalized
        val body = typeUnion(body1, body2)(using Γ :+ binding1)
        FunctionType(binding1, body, effects)
      case (r1 @ RecordType(qn1, args1, effects1), r2 @ RecordType(qn2, args2, effects2))
        if qn1 == qn2 =>
        val record = Σ.getRecord(qn1)
        val effects = EffectsUnion(effects1, effects2).normalized
        val args = args1
          .zip(args2)
          .zip(record.context)
          .map { case ((arg1, arg2), (_, variance)) =>
            variance match
              case Variance.COVARIANT => Some(typeUnion(arg1, arg2))
              case Variance.INVARIANT | Variance.CONTRAVARIANT =>
                if arg1 == arg2 then Some(arg1)
                else None
          }
        val actualArgs = args.collect { case Some(arg) => arg }
        if actualArgs.size == args.size then RecordType(qn1, actualArgs, effects)
        else getCTop(r1, r2)
      case (a: IType, b: IType) => getCTop(a, b)
      // One may want to treat `Force(Var(...))` to be the upperbound stored in the context corresponding to this
      // variable. But it doesn't seem to matter that much so let's not do that to keep things simple for now.
      case (_: StuckComputationType, _) | (_, _: StuckComputationType) =>
        throw CannotFindCTypeUnion(a, b)
      case _ => throw IllegalStateException("type error")

@throws(classOf[IrError])
private def getCTop
  (a: CTerm & IType, b: CTerm & IType)
  (using Γ: Context)
  (using Signature)
  (using TypingContext)
  : CTerm =
  val aLevel = inferLevel(a)
  val bLevel = inferLevel(b)
  val level = LevelMax(aLevel, bLevel).normalized
  val effects = EffectsUnion(a.effects, b.effects).normalized
  CTop(level, effects)

private type StuckValueType = Var | Collapse

@throws(classOf[IrError])
private def typeUnion
  (a: VTerm, b: VTerm)
  (using Γ: Context)
  (using Σ: Signature)
  (using TypingContext)
  : VTerm =
  if a == b then return a
  (a, b) match
    case (Type(upperBound1), Type(upperBound2)) =>
      Type(typeUnion(upperBound1, upperBound2))
    case (Top(level1, eqD1), Top(level2, eqD2)) =>
      val level = LevelMax(level1, level2).normalized
      Top(level, eqDecidabilityJoin(eqD1, eqD2))
    case (U(cty1), U(cty2)) =>
      val cty = typeUnion(cty1, cty2)
      U(cty)
    case (DataType(qn1, args1), DataType(qn2, args2)) if qn1 == qn2 =>
      val data = Σ.getData(qn1)
      val args = args1
        .zip(args2)
        .zip(data.context)
        .map { case ((arg1, arg2), (_, variance)) =>
          variance match
            case Variance.COVARIANT => Some(typeUnion(arg1, arg2))
            case Variance.INVARIANT | Variance.CONTRAVARIANT =>
              if arg1 == arg2 then Some(arg1)
              else None
        }
      val actualArgs = args.collect { case Some(arg) => arg }
      if actualArgs.size == args.size then DataType(qn1, actualArgs)
      else getTop(a, b)
    case (UsageType(_), UsageType(_))                    => UsageType(None)
    case (_: StuckValueType, _) | (_, _: StuckValueType) => throw CannotFindVTypeUnion(a, b)
    case (
        EffectsType(continuationUsage1, handlerType1),
        EffectsType(continuationUsage2, handlerType2),
      ) =>
      val continuationUsage = UsageJoin(continuationUsage1, continuationUsage2).normalized
      val handlerType =
        if handlerType1.normalized == HandlerTypeLiteral(
            Simple,
          ) && handlerType2.normalized == HandlerTypeLiteral(Simple)
        then HandlerTypeLiteral(Simple)
        else HandlerTypeLiteral(Complex)
      EffectsType(continuationUsage, handlerType)
    case (LevelType(level1), LevelType(level2)) =>
      LevelType(LevelMax(level1, level2).normalized)
    case _ => throw IllegalStateException("type error")

@throws(classOf[IrError])
private def getTop
  (a: VTerm, b: VTerm)
  (using Γ: Context)
  (using Signature)
  (using TypingContext)
  : VTerm =
  val aLevel = inferLevel(a)
  val aEqDecidability = inferEqDecidability(a)
  val bLevel = inferLevel(b)
  val bEqDecidability = inferEqDecidability(b)
  val level = LevelMax(aLevel, bLevel).normalized
  Top(level, eqDecidabilityJoin(aEqDecidability, bEqDecidability))

private def eqDecidabilityJoin(t1: VTerm, t2: VTerm): VTerm =
  (t1, t2) match
    case (EqDecidabilityLiteral(e1), EqDecidabilityLiteral(e2)) => EqDecidabilityLiteral(e1 | e2)
    case _ => EqDecidabilityLiteral(EqDecidability.EqUnknown)

@throws(classOf[IrError])
private def checkHandlerTypeSubsumption
  (handlerType1: VTerm, handlerType2: VTerm)
  (using Γ: Context)
  (using Signature)
  (using ctx: TypingContext)
  : Set[Constraint] = debugSubsumption("checkHandlerTypeSubsumption", handlerType1, handlerType2):
  check2(handlerType1, handlerType2):
    case (HandlerTypeLiteral(Simple), _) | (_, HandlerTypeLiteral(Complex)) =>
      Set.empty
    case (u: RUnsolved, HandlerTypeLiteral(Simple)) =>
      ctx.assignUnsolved(u, Return(handlerType2, u1))
    case (HandlerTypeLiteral(Complex), u: RUnsolved) =>
      ctx.assignUnsolved(u, Return(handlerType1, u1))
    case (_: ResolvedMetaVariable, _: ResolvedMetaVariable) =>
      Set(Constraint.HandlerTypeSubsumption(Γ, handlerType1, handlerType2))
    case _ => throw NotHandlerTypeSubsumption(handlerType1, handlerType2)

@throws(classOf[IrError])
private def checkEqDecidabilitySubsumption
  (eqD1: VTerm, eqD2: VTerm)
  (using Γ: Context)
  (using Signature)
  (using ctx: TypingContext)
  : Set[Constraint] = debugSubsumption("checkEqDecidabilitySubsumption", eqD1, eqD2):
  check2(eqD1, eqD2):
    case (EqDecidabilityLiteral(EqDecidability.EqDecidable), _) |
      (_, EqDecidabilityLiteral(EqDecidability.EqUnknown)) =>
      Set.empty
    case (u: RUnsolved, EqDecidabilityLiteral(EqDecidability.EqDecidable)) =>
      ctx.assignUnsolved(u, Return(eqD2, u1))
    case (EqDecidabilityLiteral(EqDecidability.EqUnknown), u: RUnsolved) =>
      ctx.assignUnsolved(u, Return(eqD1, u1))
    case (_: ResolvedMetaVariable, _: ResolvedMetaVariable) =>
      Set(Constraint.EqDecidabilitySubsumption(Γ, eqD1, eqD2))
    case _ => throw NotEqDecidabilitySubsumption(eqD1, eqD2)

/** @param invert
  *   useful when checking patterns where the consumed usages are actually provided usages because
  *   lhs patterns are multiplied by declared usages in function
  */
@throws(classOf[IrError])
private def checkUsagesSubsumption
  (usages: Usages, invert: Boolean = false)
  (using Γ: Context)
  (using Σ: Signature)
  (using TypingContext)
  : Set[Constraint] =
  assert(usages.size == Γ.size)
  Γ.indices
    .map { i =>
      given Γ2: Context = Γ.take(i)
      val binding = Γ(i)
      val providedUsage = binding.usage
      val consumedUsage = usages(i).strengthen(Γ.size - i, 0)
      if invert then checkUsageSubsumption(consumedUsage, providedUsage)
      else checkUsageSubsumption(providedUsage, consumedUsage)
    }
    .flatten
    .toSet

@throws(classOf[IrError])
def checkUsageSubsumption
  (sub: VTerm, sup: VTerm)
  (using Γ: Context)
  (using Σ: Signature)
  (using ctx: TypingContext)
  : Set[Constraint] = debugSubsumption("checkUsageSubsumption", sub, sup):
  check2(sub, sup):
    // Note on direction of usage comparison: UAny > U1 but UAny subsumes U1 when counting usage
    case (UsageLiteral(u1), UsageLiteral(u2)) if u1 >= u2 => Set.empty
    case (UsageLiteral(UAny), _)                          => Set.empty
    case (UsageJoin(operands1), v: VTerm) =>
      val operands2 = v match
        case UsageJoin(operands2) => operands2
        case v: VTerm             => Set(v)

      val spuriousOperands = operands2 -- operands1
      if spuriousOperands.isEmpty then Set.empty
      // If spurious operands are all stuck computation, it's possible for sup to be anything if all of these stuck
      // computation ends up being assigned values that are part of sub
      // Also, if sub contains stuck computation, it's possible for sub to end up including arbitrary usage terms and
      // hence we can't decide subsumption yet.
      else if spuriousOperands.forall(isMeta) || operands1.exists(isMeta) then
        Set(Constraint.UsageSubsumption(Γ, sub, sup))
      else throw NotUsageSubsumption(sub, sup)
    // Handle the special case that the right hand side simply contains the left hand side as an operand.
    case (UsageJoin(operands), RUnsolved(_, _, _, tm, _)) if operands.contains(Collapse(tm)) =>
      Set.empty
    case (v @ Var(_), UsageLiteral(u2)) =>
      Γ.resolve(v).ty match
        // Only UAny subsumes UAny and UAny is also convertible with itself.
        case UsageType(Some(UsageLiteral(Usage.UAny))) if u2 == Usage.UAny => Set.empty
        case UsageType(Some(u1Bound)) =>
          checkUsageSubsumption(u1Bound, UsageLiteral(u2))
        case _ => throw NotUsageSubsumption(sub, sup)
    case (u @ RUnsolved(_, _, constraint, _, _), sup: VTerm) =>
      ctx.adaptForMetaVariable(u, sup) match
        case None => Set(Constraint.UsageSubsumption(Γ, sub, sup))
        case Some(value) =>
          val newUpperBound = constraint match
            case UmcNothing => value
            case UmcUsageSubsumption(existingUpperBound) =>
              UsageJoin(existingUpperBound, value).normalized
            case _ => throw IllegalStateException("type error")
          newUpperBound match
            // If upper bound is already UAny, we know they must take that values.
            case UsageLiteral(Usage.UAny) => ctx.assignUnsolved(u, Return(newUpperBound, u1))
            case _ =>
              ctx.updateConstraint(u, UmcUsageSubsumption(newUpperBound))
              Set.empty
    case (sub: VTerm, u @ RUnsolved(_, _, UmcUsageSubsumption(existingUpperBound), _, _)) =>
      ctx.adaptForMetaVariable(u, sub) match
        case Some(value) if value == existingUpperBound => ctx.assignUnsolved(u, Return(value, u1))
        case Some(value @ (UsageLiteral(Usage.U0) | UsageLiteral(Usage.U1))) =>
          ctx.assignUnsolved(u, Return(value, u1))
        case _ => Set(Constraint.UsageSubsumption(Γ, sub, sup))
    case (_: ResolvedMetaVariable, _: ResolvedMetaVariable) =>
      Set(Constraint.UsageSubsumption(Γ, sub, sup))
    case _ =>
      if isMeta(sub) || isMeta(sup) then
        // We can't decide if the terms are unsolved.
        Set(Constraint.UsageSubsumption(Γ, sub, sup))
      else throw NotUsageSubsumption(sub, sup)

@throws(classOf[IrError])
private def checkEffSubsumption
  (sub: VTerm, sup: VTerm)
  (using Γ: Context)
  (using Σ: Signature)
  (using ctx: TypingContext)
  : Set[Constraint] = debugSubsumption("checkEffSubsumption", sub, sup):
  check2(sub, sup):
    // Handle the special case that the right hand side simply contains the left hand side as an operand.
    case (RUnsolved(_, _, _, tm, _), Effects(_, operands)) if operands.contains(Collapse(tm)) =>
      Set.empty
    // The case where the left hand side contains a meta variable which is the right hand side. In this case, all the
    // other parts on the left should be added as lower bound to the meta variable. This case is useful in solving effects
    // in operation implementations in handlers, where the continuation carries the same type as the final return type of
    // the handler.
    case (
        Effects(literal, operands),
        u @ RUnsolved(_, _, c: (UmcEffSubsumption | UmcNothing.type), tm, _),
      ) if operands.contains(Collapse(tm)) =>
      val otherOperands = operands - Collapse(tm)
      val newLowerBound = c match
        case UmcNothing => Effects(literal, otherOperands)
        case UmcEffSubsumption(existingLowerBound) =>
          EffectsUnion(existingLowerBound, Effects(literal, otherOperands)).normalized
      ctx.updateConstraint(u, UmcEffSubsumption(newLowerBound))
      Set.empty
    case (sub: VTerm, u @ RUnsolved(_, _, constraint, _, _)) =>
      ctx.adaptForMetaVariable(u, sub) match
        case None => Set(Constraint.EffSubsumption(Γ, sub, sup))
        case Some(value) =>
          val newLowerBound = constraint match
            case UmcNothing => value
            case UmcEffSubsumption(existingLowerBound) =>
              EffectsUnion(existingLowerBound, value).normalized
            case _ => throw IllegalStateException("type error")
          ctx.updateConstraint(u, UmcEffSubsumption(newLowerBound))
          Set.empty
    // If upper bound is total, the meta variable can only take total as the value.
    case (
        u @ RUnsolved(_, _, UmcEffSubsumption(_), _, _),
        Effects(literals, operands),
      ) if literals.isEmpty && operands.isEmpty =>
      ctx.assignUnsolved(u, Return(Total(), u1))
    case (u @ RUnsolved(_, _, UmcEffSubsumption(existingLowerBound), _, _), sup: VTerm) =>
      ctx.adaptForMetaVariable(u, sub) match
        case Some(value) if value == existingLowerBound => ctx.assignUnsolved(u, Return(value, u1))
        case _ => Set(Constraint.EffSubsumption(Γ, sub, sup))
    case (_: ResolvedMetaVariable, _: ResolvedMetaVariable) =>
      Set(Constraint.EffSubsumption(Γ, sub, sup))
    case (_, Effects(literals2, unionOperands2)) =>
      // Normalization would unwrap any wrappers with a single operand so we need to undo that here.
      val (literals1, unionOperands1) = sub match
        case Effects(literals1, unionOperands1) => (literals1, unionOperands1)
        case v: VTerm                           => (Set.empty, Map(v -> false))
      // false is considered "greater" because false means complex effects are not filtered out, which is "greater" than
      // true where complex effects are filtered out.
      given PartialOrdering[Boolean] = Ordering.fromLessThan[Boolean]:
        case (true, false) => true
        case _             => false
      val spuriousOperands = getSpurious(unionOperands1, unionOperands2)
      val spuriousLiterals = literals1 -- literals2
      val metaOperands2 = unionOperands2.keys.filter(isMeta)
      if spuriousOperands.isEmpty && literals1.subsetOf(literals2) then Set.empty
      else if metaOperands2.size == 1 then
        // The case where the right hand side contains a single meta variable and some other stuff.
        // In such a case, the meta variable should be assigned the difference between the left hand side and the literal
        // effects on the right. This is to accommodate the common use case when type checking handlers, where otherEffects
        // is left out as a meta variable.
        ctx.withMetaResolved(metaOperands2.head):
          case u @ RUnsolved(_, _, c: (UmcEffSubsumption | UmcNothing.type), _, _) =>
            val newLowerBound = c match
              case UmcNothing => Effects(spuriousLiterals, spuriousOperands)
              case UmcEffSubsumption(existingLowerBound) =>
                EffectsUnion(
                  existingLowerBound,
                  Effects(spuriousLiterals, spuriousOperands),
                ).normalized
            ctx.updateConstraint(u, UmcEffSubsumption(newLowerBound))
            Set.empty
          case _ => throw NotEffectSubsumption(sub, sup)
      // If spurious operands are all stuck computation, it's possible for sub to be if all of these stuck computation
      // ends up being assigned values that are part of sup
      // Also, if sup contains stuck computation, it's possible for sup to end up including arbitrary effects and hence
      // we can't decide subsumption yet.
      else if spuriousOperands.keys.forall(isMeta) || unionOperands2.keys.exists(isMeta) then
        Set(Constraint.EffSubsumption(Γ, sub, sup))
      else throw NotEffectSubsumption(sub, sup)
    case _ => throw NotEffectSubsumption(sub, sup)

/** Checks if l1 is smaller than l2.
  */
@throws(classOf[IrError])
private def checkLevelSubsumption
  (sub: VTerm, sup: VTerm)
  (using Γ: Context)
  (using Σ: Signature)
  (using ctx: TypingContext)
  : Set[Constraint] = debugSubsumption("checkLevelSubsumption", sub, sup):
  check2(sub, sup):
    case (v: VTerm, Level(literal2, operands2)) =>
      // Normalization would unwrap any wrappers with a single operand so we need to undo that here.
      val (literal1, operands1) = v match
        case Level(literal1, operands1) => (literal1, operands1)
        case v: VTerm                   => (LevelOrder.zero, Map(v -> 0))
      val spuriousOperands = getSpurious[VTerm, Int](operands1, operands2)
      if spuriousOperands.isEmpty && literal1.compareTo(literal2) <= 0 then Set.empty
      else
      // If spurious operands are all stuck computation, it's possible for sub to be if all of these stuck computation
      // ends up being assigned small levels
      // Also, if sup contains stuck computation, it's possible for sup to end up including arbitrary large level and
      // hence we can't decide subsumption yet.
      if spuriousOperands.keys.forall(isMeta) || operands2.keys.exists(isMeta) then
        Set(Constraint.LevelSubsumption(Γ, sub, sup))
      else throw NotLevelSubsumption(sub, sup)
    // Handle the special case that the right hand side simply contains the left hand side as an operand.
    case (RUnsolved(_, _, _, tm, _), Level(_, operands)) if operands.contains(Collapse(tm)) =>
      Set.empty
    case (sub: VTerm, u @ RUnsolved(_, _, constraint, _, _)) =>
      ctx.adaptForMetaVariable(u, sub) match
        case None => Set(Constraint.LevelSubsumption(Γ, sub, sup))
        case Some(value) =>
          val newLowerBound = constraint match
            case UmcNothing => value
            case UmcLevelSubsumption(existingLowerBound) =>
              LevelMax(existingLowerBound, value).normalized
            case _ => throw IllegalStateException("type error")
          ctx.updateConstraint(u, UmcLevelSubsumption(newLowerBound))
          Set.empty
    // If upper bound is zero, the meta variable can only take zero as the value.
    case (
        u @ RUnsolved(_, _, UmcLevelSubsumption(_), _, _),
        Level(LevelOrder.zero, operands),
      ) if operands.isEmpty =>
      ctx.assignUnsolved(u, Return(Level(LevelOrder.zero, Map()), u1))
    case (u @ RUnsolved(_, _, UmcLevelSubsumption(existingLowerBound), _, _), sup: VTerm) =>
      ctx.adaptForMetaVariable(u, sub) match
        case Some(value) if value == existingLowerBound => ctx.assignUnsolved(u, Return(value, u1))
        case _ => Set(Constraint.LevelSubsumption(Γ, sub, sup))
    case (_: ResolvedMetaVariable, _: ResolvedMetaVariable) =>
      Set(Constraint.LevelSubsumption(Γ, sub, sup))
    case _ => throw NotLevelSubsumption(sub, sup)

private def getSpurious[T, E: PartialOrdering](sub: Map[T, E], sup: Map[T, E]): Map[T, E] =
  sub.filter { case (operand1, e1) =>
    sup.get(operand1) match
      case None     => true
      case Some(e2) => summon[PartialOrdering[E]].gt(e1, e2)
  }

@throws(classOf[IrError])
private def check2
  (a: VTerm, b: VTerm)
  (action: (ResolvedMetaVariable | VTerm, ResolvedMetaVariable | VTerm) => Set[Constraint])
  (using Γ: Context)
  (using Signature)
  (using ctx: TypingContext)
  : Set[Constraint] =
  if a == b then Set.empty
  else ctx.withMetaResolved2(a.normalized, b.normalized)(action)

@throws(classOf[IrError])
private def check2
  (a: CTerm, b: CTerm)
  (
    action: (
      (ResolvedMetaVariable, List[Elimination[VTerm]]) | CTerm,
      (ResolvedMetaVariable, List[Elimination[VTerm]]) | CTerm,
    ) => Set[Constraint],
  )
  (using Γ: Context)
  (using Signature)
  (using ctx: TypingContext)
  : Set[Constraint] =
  if a == b then Set.empty
  else ctx.withMetaResolved2(a.normalized(None), b.normalized(None))(action)

@throws(classOf[IrError])
private inline def debugSubsumption[R]
  (name: String, rawSub: CTerm | VTerm, rawSup: CTerm | VTerm)
  (result: => R)
  (using Context)
  (using Signature)
  (using ctx: TypingContext)
  : R =
  ctx.trace(
    name,
    Block(
      ChopDown,
      Aligned,
      yellow(rawSub.sourceInfo),
      pprint(rawSub),
      "⪯",
      yellow(rawSup.sourceInfo),
      pprint(rawSup),
    ),
  )(result)

/* References
 [0]  Norell, Ulf. “Towards a practical programming language based on dependent type theory.” (2007).
 */
