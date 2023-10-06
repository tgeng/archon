package com.github.tgeng.archon.core.ir

import com.github.tgeng.archon.common.*
import com.github.tgeng.archon.common.eitherFilter.*
import com.github.tgeng.archon.core.common.*
import com.github.tgeng.archon.core.ir.Reducible.reduce

import VTerm.*
import CTerm.*
import IrError.*
import Declaration.*
import Elimination.*
import SourceInfo.*
import Usage.*
import EqDecidability.*
import MetaVariable.*
import PrettyPrinter.pprint
import WrapPolicy.*
import IndentPolicy.*
import DelimitPolicy.*
import UnsolvedMetaVariableConstraint.*
import ResolvedMetaVariable.*
import scala.collection.mutable.ArrayBuffer
import math.Ordering.ordered

/** Preconditions: sub and sup are both checked to be types
  */
def checkIsSubtype
  (sub: VTerm, sup: VTerm)
  (using Γ: Context)
  (using Σ: Signature)
  (using ctx: TypingContext)
  : Either[IrError, Set[Constraint]] = check2(sub, sup):
  case (_, _) if sub == sup => Right(Set.empty)
  case (sub: VTerm, u @ RUnsolved(_, _, constraint, tm, ty)) =>
    ctx.adaptForMetaVariable(u, sub) match
      case None => Right(Set(Constraint.VSubType(Γ, sub, sup)))
      case Some(value) =>
        val newConstraint = constraint match
          case UmcNothing                      => UmcVSubtype(Set(value))
          case UmcVSubtype(existingLowerBound) => UmcVSubtype(existingLowerBound + value)
          case _                               => throw IllegalStateException("type error")
        ctx.updateConstraint(u, newConstraint)
        Right(Set.empty)
  case (u @ RUnsolved(_, _, UmcVSubtype(existingLowerBound), tm, ty), sup: VTerm) =>
    ctx.adaptForMetaVariable(u, sub) match
      case Some(value) if value == existingLowerBound => ctx.assignUnsolved(u, Return(value, u1))
      case _                                          => Right(Set(Constraint.VSubType(Γ, sub, sup)))
  case (_: ResolvedMetaVariable, _) | (_, _: ResolvedMetaVariable) =>
    Right(Set(Constraint.VSubType(Γ, sub, sup)))
  case (Type(upperBound1), Type(upperBound2)) => checkIsSubtype(upperBound1, upperBound2)
  case (ty: VTerm, Top(level2, eqD2)) =>
    for
      level1 <- inferLevel(ty)
      levelConstraints <- checkLevelSubsumption(level1, level2)
      eqD1 <- inferEqDecidability(ty)
      eqDecidabilityConstraints <- checkEqDecidabilitySubsumption(eqD1, eqD2)
    yield levelConstraints ++ eqDecidabilityConstraints
  case (U(cty1), U(cty2)) => checkIsSubtype(cty1, cty2)
  case (DataType(qn1, args1), DataType(qn2, args2)) if qn1 == qn2 =>
    Σ.getDataOption(qn1) match
      case None => Left(MissingDeclaration(qn1))
      case Some(data) =>
        val args = ArrayBuffer[VTerm]()
        transpose(
          args1
            .zip(args2)
            .zip(data.tParamTys ++ data.tIndexTys.map((_, Variance.INVARIANT)))
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
                  for
                    (arg1, _) <- checkIsType(arg1)
                    (arg2, _) <- checkIsType(arg2)
                    r <- checkIsSubtype(arg1, arg2)
                  yield
                    args += arg1
                    r
                case Variance.CONTRAVARIANT =>
                  for
                    (arg1, _) <- checkIsType(arg1)
                    (arg2, _) <- checkIsType(arg2)
                    r <- checkIsSubtype(arg2, arg1)
                  yield
                    args += arg2
                    r
            },
        ).map(_.flatten.toSet)
  case (EffectsType(continuationUsage1, controlMode1), EffectsType(continuationUsage2, controlMode2)) =>
    if (controlMode1 == ControlMode.Simple || controlMode1 == controlMode2) then
      // Note that subsumption checking is reversed because the effect of the computation
      // marks how the continuation can be invoked. Normally, checking usage is checking
      // how a resource is *consumed*. But here, checking usage is checking how the
      // continuation (as a resource) is provided.
      checkUsageSubsumption(continuationUsage2, continuationUsage1)
    else Left(NotVSubtype(sub, sup))
  case (UsageType(Some(u1)), UsageType(Some(u2))) => checkUsageSubsumption(u1, u2)
  case (UsageType(Some(_)), UsageType(None))      => Right(Set.empty)
  case (v: Var, ty2: VTerm) =>
    Γ.resolve(v).ty match
      case Type(upperBound) => checkIsSubtype(upperBound, ty2)
      case _                => Left(NotVSubtype(sub, sup))
  case _ => checkIsConvertible(sub, sup, None)

/** Preconditions: sub and sup are both types
  */
def checkIsSubtype
  (sub: CTerm, sup: CTerm)
  (using Γ: Context)
  (using Σ: Signature)
  (using ctx: TypingContext)
  : Either[IrError, Set[Constraint]] = check2(sub, sup):
  case (_, _) if sub == sup => Right(Set.empty[Constraint])
  case (sub: CTerm, (u @ RUnsolved(_, _, constraint, tm, ty), Nil)) =>
    ctx.adaptForMetaVariable(u, sub) match
      case None => Right(Set(Constraint.CSubType(Γ, sub, sup)))
      case Some(value) =>
        val newConstraint = constraint match
          case UmcNothing                      => UmcCSubtype(Set(value))
          case UmcCSubtype(existingLowerBound) => UmcCSubtype(existingLowerBound + value)
          case _                               => throw IllegalStateException("type error")
        ctx.updateConstraint(u, newConstraint)
        Right(Set.empty)
  case ((u @ RUnsolved(_, _, UmcCSubtype(existingLowerBound), tm, ty), Nil), sup: CTerm) =>
    ctx.adaptForMetaVariable(u, sub) match
      case Some(value) if value == existingLowerBound => ctx.assignUnsolved(u, value)
      case _                                          => Right(Set(Constraint.CSubType(Γ, sub, sup)))
  case ((_: ResolvedMetaVariable, Nil), _) | (_, (_: ResolvedMetaVariable, Nil)) =>
    Right(Set(Constraint.CSubType(Γ, sub, sup)))
  case (CType(upperBound1, eff1), CType(upperBound2, eff2)) =>
    for
      effConstraint <- checkEffSubsumption(eff1, eff2)
      upperBoundConstraint <- checkIsSubtype(upperBound1, upperBound2)
    yield effConstraint ++ upperBoundConstraint
  case (ty: IType, CTop(level2, eff2)) =>
    for
      level1 <- inferLevel(sub)
      levelConstraint <- checkLevelSubsumption(level1, level2)
      effConstraint <- checkEffSubsumption(ty.effects, eff2)
    yield levelConstraint ++ effConstraint
  case (F(vTy1, eff1, u1), F(vTy2, eff2, u2)) =>
    for
      effConstraint <- checkEffSubsumption(eff1, eff2)
      usageConstraint <- checkUsageSubsumption(u1, u2)
      tyConstraint <- checkIsSubtype(vTy1, vTy2)
    yield effConstraint ++ usageConstraint ++ tyConstraint
  case (
      FunctionType(binding1, bodyTy1, eff1),
      FunctionType(binding2, bodyTy2, eff2),
    ) =>
    for
      effConstraint <- checkEffSubsumption(eff1, eff2)
      tyConstraint <- checkIsSubtype(binding2.ty, binding1.ty).flatMap(ctx.solve)
      bodyConstraint <-
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
    yield effConstraint ++ tyConstraint ++ bodyConstraint
  case (RecordType(qn1, args1, eff1), RecordType(qn2, args2, eff2)) if qn1 == qn2 =>
    Σ.getRecordOption(qn1) match
      case None => Left(MissingDeclaration(qn1))
      case Some(record) =>
        val args = ArrayBuffer[VTerm]()
        for
          effConstraint <- checkEffSubsumption(eff1, eff2)
          argConstraint <- transpose(
            args1
              .zip(args2)
              .zip(record.tParamTys)
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
                    for
                      (arg1, _) <- checkIsType(arg1)
                      (arg2, _) <- checkIsType(arg2)
                      r <- checkIsSubtype(arg1, arg2)
                    yield
                      args += arg1
                      r
                  case Variance.CONTRAVARIANT =>
                    for
                      (arg1, _) <- checkIsType(arg1)
                      (arg2, _) <- checkIsType(arg2)
                      r <- checkIsSubtype(arg2, arg1)
                    yield
                      args += arg2
                      r
              },
          ).map(_.flatten.toSet)
        yield effConstraint ++ argConstraint
  case _ => checkIsConvertible(sub, sup, None)

private type StuckComputationType = Redex | Force | Meta | Def | Let | Handler

private def typeUnion
  (a: CTerm, b: CTerm)
  (using Γ: Context)
  (using Σ: Signature)
  (using TypingContext)
  : Either[IrError, CTerm] =
  if a == b then Right(a)
  else
    (a, b) match
      case (CType(upperBound1, effects1), CType(upperBound2, effects2)) =>
        for
          upperBound <- typeUnion(upperBound1, upperBound2)
          effects <- EffectsUnion(effects1, effects2).normalized
        yield CType(upperBound, effects)
      case (CTop(level1, effects1), CTop(level2, effects2)) =>
        for
          level <- LevelMax(level1, level2).normalized
          effects <- EffectsUnion(effects1, effects2).normalized
        yield CTop(level, effects)
      case (F(vty1, effects1, usage1), F(vty2, effects2, usage2)) =>
        for
          vty <- typeUnion(vty1, vty2)
          effects <- EffectsUnion(effects1, effects2).normalized
          usage <- UsageJoin(usage1, usage2).normalized
        yield F(vty, effects, usage)
      // for simplicity we just treat types at contravariant position as invariant
      case (FunctionType(binding1, body1, effects1), FunctionType(binding2, body2, effects2)) if binding1 == binding2 =>
        for
          effects <- EffectsUnion(effects1, effects2).normalized
          body <- typeUnion(body1, body2)(using Γ :+ binding1)
        yield FunctionType(binding1, body, effects)
      case (r1 @ RecordType(qn1, args1, effects1), r2 @ RecordType(qn2, args2, effects2)) if qn1 == qn2 =>
        val record = Σ.getRecord(qn1)
        for
          effects <- EffectsUnion(effects1, effects2).normalized
          args <- transpose(
            args1
              .zip(args2)
              .zip(record.tParamTys)
              .map { case ((arg1, arg2), (binding, variance)) =>
                variance match
                  case Variance.COVARIANT => typeUnion(arg1, arg2).map(Some(_))
                  case Variance.INVARIANT | Variance.CONTRAVARIANT =>
                    if arg1 == arg2 then Right(Some(arg1))
                    else Right(None)
              },
          )
          r <-
            val actualArgs = args.collect { case Some(arg) => arg }
            if actualArgs.size == args.size then Right(RecordType(qn1, actualArgs, effects))
            else getCTop(r1, r2)
        yield r
      case (a: IType, b: IType) => getCTop(a, b)
      // One may want to treat `Force(Var(...))` to be the upperbound stored in the context corresponding to this
      // variable. But it doesn't seem to matter that much so let's not do that to keep things simple for now.
      case (_: StuckComputationType, _) | (_, _: StuckComputationType) => Left(CannotFindCTypeUnion(a, b))
      case _                                                           => throw IllegalStateException("type error")

private def getCTop
  (a: CTerm & IType, b: CTerm & IType)
  (using Γ: Context)
  (using Σ: Signature)
  (using TypingContext)
  : Either[IrError, CTerm] =
  for
    aLevel <- inferLevel(a)
    bLevel <- inferLevel(b)
    level <- LevelMax(aLevel, bLevel).normalized
    effects <- EffectsUnion(a.effects, b.effects).normalized
  yield CTop(level, effects)

private type StuckValueType = Var | Collapse

private def typeUnion
  (a: VTerm, b: VTerm)
  (using Γ: Context)
  (using Σ: Signature)
  (using TypingContext)
  : Either[IrError, VTerm] =
  if a == b then Right(a)
  else
    (a, b) match
      case (Type(upperBound1), Type(upperBound2)) =>
        for upperBound <- typeUnion(upperBound1, upperBound2)
        yield Type(upperBound)
      case (Top(level1, eqD1), Top(level2, eqD2)) =>
        for level <- LevelMax(level1, level2).normalized
        yield Top(level, eqDecidabilityJoin(eqD1, eqD2))
      case (U(cty1), U(cty2)) =>
        for cty <- typeUnion(cty1, cty2)
        yield U(cty)
      case (DataType(qn1, args1), DataType(qn2, args2)) if qn1 == qn2 =>
        val data = Σ.getData(qn1)
        for
          args <- transpose(
            args1
              .zip(args2)
              .zip(data.tParamTys)
              .map { case ((arg1, arg2), (binding, variance)) =>
                variance match
                  case Variance.COVARIANT => typeUnion(arg1, arg2).map(Some(_))
                  case Variance.INVARIANT | Variance.CONTRAVARIANT =>
                    if arg1 == arg2 then Right(Some(arg1))
                    else Right(None)
              },
          )
          r <-
            val actualArgs = args.collect { case Some(arg) => arg }
            if actualArgs.size == args.size then Right(DataType(qn1, actualArgs))
            else getTop(a, b)
        yield r
      case (UsageType(_), UsageType(_))                    => Right(UsageType(None))
      case (_: StuckValueType, _) | (_, _: StuckValueType) => Left(CannotFindVTypeUnion(a, b))
      case (EffectsType(continuationUsage1, controlMode1), EffectsType(continuationUsage2, controlMode2)) =>
        for
          continuationUsage <- UsageJoin(continuationUsage1, continuationUsage2).normalized
          controlMode = controlMode1 | controlMode2
        yield EffectsType(continuationUsage, controlMode)
      case (LevelType(level1), LevelType(level2)) =>
        for level <- LevelMax(level1, level2).normalized
        yield LevelType(level)
      case _ => throw IllegalStateException("type error")

private def getTop
  (a: VTerm, b: VTerm)
  (using Γ: Context)
  (using Σ: Signature)
  (using TypingContext)
  : Either[IrError, VTerm] =
  for
    aLevel <- inferLevel(a)
    aEqDecidability <- inferEqDecidability(a)
    bLevel <- inferLevel(b)
    bEqDecidability <- inferEqDecidability(b)
    level <- LevelMax(aLevel, bLevel).normalized
  yield Top(level, eqDecidabilityJoin(aEqDecidability, bEqDecidability))

private def eqDecidabilityJoin(t1: VTerm, t2: VTerm): VTerm =
  (t1, t2) match
    case (EqDecidabilityLiteral(e1), EqDecidabilityLiteral(e2)) => EqDecidabilityLiteral(e1 | e2)
    case _                                                      => EqDecidabilityLiteral(EqDecidability.EqUnknown)

private def checkEqDecidabilitySubsumption
  (eqD1: VTerm, eqD2: VTerm)
  (using Γ: Context)
  (using Σ: Signature)
  (using ctx: TypingContext)
  : Either[IrError, Set[Constraint]] = check2(eqD1, eqD2):
  case (EqDecidabilityLiteral(EqDecidability.EqDecidable), _) | (_, EqDecidabilityLiteral(EqDecidability.EqUnknown)) =>
    Right(Set.empty)
  case (u: RUnsolved, EqDecidabilityLiteral(EqDecidability.EqDecidable)) =>
    ctx.assignUnsolved(u, Return(eqD2, u1))
  case (EqDecidabilityLiteral(EqDecidability.EqUnknown), u: RUnsolved) =>
    ctx.assignUnsolved(u, Return(eqD1, u1))
  case (_: ResolvedMetaVariable, _: ResolvedMetaVariable) =>
    Right(Set(Constraint.EqDecidabilitySubsumption(Γ, eqD1, eqD2)))
  case _ => Left(NotEqDecidabilitySubsumption(eqD1, eqD2))

/** @param invert
  *   useful when checking patterns where the consumed usages are actually provided usages because lhs patterns are
  *   multiplied by declared usages in function
  */
private def checkUsagesSubsumption
  (usages: Usages, invert: Boolean = false)
  (using Γ: Context)
  (using Σ: Signature)
  (using ctx: TypingContext)
  : Either[IrError, Set[Constraint]] =
  assert(usages.size == Γ.size)
  transpose((0 until Γ.size).map { i =>
    given Γ2: Context = Γ.take(i)
    val binding = Γ(i)
    val providedUsage = binding.usage
    val consumedUsage = usages(i).strengthen(Γ.size - i, 0)
    if invert then checkUsageSubsumption(consumedUsage, providedUsage)
    else checkUsageSubsumption(providedUsage, consumedUsage)
  }).map(_.flatten.toSet)

def checkUsageSubsumption
  (sub: VTerm, sup: VTerm)
  (using Γ: Context)
  (using Σ: Signature)
  (using ctx: TypingContext)
  : Either[IrError, Set[Constraint]] = check2(sub, sup):
  // Note on direction of usage comparison: UAny > U1 but UAny subsumes U1 when counting usage
  case (UsageLiteral(u1), UsageLiteral(u2)) if u1 >= u2 => Right(Set.empty)
  case (UsageLiteral(UAny), _)                          => Right(Set.empty)
  case (UsageJoin(operands1), v: VTerm) =>
    val operands2 = v match
      case UsageJoin(operands2) => operands2
      case v: VTerm             => Set(v)

    val spuriousOperands = operands2 -- operands1
    if spuriousOperands.isEmpty then Right(Set.empty)
    else
    // If spurious operands are all stuck computation, it's possible for sup to be anything if all of these stuck
    // computation ends up being assigned values that are part of sub
    // Also, if sub contains stuck computation, it's possible for sub to end up including arbitrary usage terms and
    // hence we can't decide subsumption yet.
    if spuriousOperands.forall(isMeta) || operands1.exists(isMeta) then
      Right(Set(Constraint.UsageSubsumption(Γ, sub, sup)))
    else Left(NotUsageSubsumption(sub, sup))
  // Handle the special case that the right hand side simply contains the left hand side as an operand.
  case (UsageJoin(operands), RUnsolved(_, _, _, tm, _)) if operands.contains(Collapse(tm)) =>
    Right(Set.empty)
  case (v @ Var(_), UsageLiteral(u2)) =>
    Γ.resolve(v).ty match
      // Only UAny subsumes UAny and UAny is also convertible with itself.
      case UsageType(Some(UsageLiteral(Usage.UAny))) if u2 == Usage.UAny => Right(Set.empty)
      case UsageType(Some(u1Bound)) =>
        checkUsageSubsumption(u1Bound, UsageLiteral(u2))
      case _ => Left(NotUsageSubsumption(sub, sup))
  case (u @ RUnsolved(_, _, constraint, tm, ty), sup: VTerm) =>
    ctx.adaptForMetaVariable(u, sup) match
      case None => Right(Set(Constraint.UsageSubsumption(Γ, sub, sup)))
      case Some(value) =>
        for
          newUpperBound <- constraint match
            case UmcNothing => Right(value)
            case UmcUsageSubsumption(existingUpperBound) =>
              UsageJoin(existingUpperBound, value).normalized
            case _ => throw IllegalStateException("type error")
          r <- newUpperBound match
            // If upper bound is already UAny, we know they must take that values.
            case UsageLiteral(Usage.UAny) => ctx.assignUnsolved(u, Return(newUpperBound, u1))
            case _ =>
              ctx.updateConstraint(u, UmcUsageSubsumption(newUpperBound))
              Right(Set.empty)
        yield r
  case (sub: VTerm, u @ RUnsolved(_, _, UmcUsageSubsumption(existingUpperBound), tm, ty)) =>
    ctx.adaptForMetaVariable(u, sub) match
      case Some(value) if value == existingUpperBound                      => ctx.assignUnsolved(u, Return(value, u1))
      case Some(value @ (UsageLiteral(Usage.U0) | UsageLiteral(Usage.U1))) => ctx.assignUnsolved(u, Return(value, u1))
      case _ => Right(Set(Constraint.UsageSubsumption(Γ, sub, sup)))
  case (_: ResolvedMetaVariable, _: ResolvedMetaVariable) =>
    Right(Set(Constraint.UsageSubsumption(Γ, sub, sup)))
  case _ =>
    if isMeta(sub) || isMeta(sup) then
      // We can't decide if the terms are unsolved.
      Right(Set(Constraint.UsageSubsumption(Γ, sub, sup)))
    else Left(NotUsageSubsumption(sub, sup))

private def checkEffSubsumption
  (sub: VTerm, sup: VTerm)
  (using Γ: Context)
  (using Σ: Signature)
  (using ctx: TypingContext)
  : Either[IrError, Set[Constraint]] = check2(sub, sup):
  // Handle the special case that the right hand side simply contains the left hand side as an operand.
  case (RUnsolved(_, _, _, tm, _), Effects(_, operands)) if operands.contains(Collapse(tm)) => Right(Set.empty)
  // The case where the left hand side contains a meta variable which is the right hand side. In this case, all the
  // other parts on the left should be added as lower bound to the meta variable. This case is useful in solving effects
  // in operation implementations in handlers, where the continuation carries the same type as the final return type of
  // the handler.
  case (Effects(literal, operands), u @ RUnsolved(_, _, c: (UmcEffSubsumption | UmcNothing.type), tm, _))
    if operands.contains(Collapse(tm)) =>
    val otherOperands = operands - Collapse(tm)
    for newLowerBound <- c match
        case UmcNothing => Right(Effects(literal, otherOperands))
        case UmcEffSubsumption(existingLowerBound) =>
          EffectsUnion(existingLowerBound, Effects(literal, otherOperands)).normalized
    yield
      ctx.updateConstraint(u, UmcEffSubsumption(newLowerBound))
      Set.empty
  case (sub: VTerm, u @ RUnsolved(_, _, constraint, tm, ty)) =>
    ctx.adaptForMetaVariable(u, sub) match
      case None => Right(Set(Constraint.EffSubsumption(Γ, sub, sup)))
      case Some(value) =>
        for newLowerBound <- constraint match
            case UmcNothing                            => Right(value)
            case UmcEffSubsumption(existingLowerBound) => EffectsUnion(existingLowerBound, value).normalized
            case _                                     => throw IllegalStateException("type error")
        yield
          ctx.updateConstraint(u, UmcEffSubsumption(newLowerBound))
          Set.empty
  // If upper bound is total, the meta variable can only take total as the value.
  case (
      u @ RUnsolved(_, _, UmcEffSubsumption(existingLowerBound), tm, ty),
      Effects(literals, operands),
    ) if literals.isEmpty && operands.isEmpty =>
    ctx.assignUnsolved(u, Return(Total(), u1))
  case (u @ RUnsolved(_, _, UmcEffSubsumption(existingLowerBound), tm, ty), sup: VTerm) =>
    ctx.adaptForMetaVariable(u, sub) match
      case Some(value) if value == existingLowerBound => ctx.assignUnsolved(u, Return(value, u1))
      case _                                          => Right(Set(Constraint.EffSubsumption(Γ, sub, sup)))
  case (_: ResolvedMetaVariable, _: ResolvedMetaVariable) => Right(Set(Constraint.EffSubsumption(Γ, sub, sup)))
  case (_, Effects(literals2, unionOperands2))            =>
    // Normalization would unwrap any wrappers with a single operand so we need to undo that here.
    val (literals1, unionOperands1) = sub match
      case Effects(literals1, unionOperands1) => (literals1, unionOperands1)
      case v: VTerm                           => (Set.empty, Set(v))
    val spuriousOperands = unionOperands1 -- unionOperands2
    val spuriousLiterals = literals1 -- literals2
    val metaOperands2 = unionOperands2.filter(isMeta)
    if spuriousOperands.isEmpty && literals1.subsetOf(literals2) then Right(Set.empty)
    else if metaOperands2.size == 1 then
      // The case where the right hand side contains a single meta variable and some other stuff.
      // In such a case, the meta variable should be assigned the difference between the left hand side and the literal
      // effects on the right. This is to accomodate the common use case when type checking handlers, where otherEffects
      // is left out as a meta variable.
      ctx.withMetaResolved(metaOperands2.head):
        case u @ RUnsolved(_, _, c: (UmcEffSubsumption | UmcNothing.type), tm, _) =>
          for newLowerBound <- c match
              case UmcNothing => Right(Effects(spuriousLiterals, spuriousOperands))
              case UmcEffSubsumption(existingLowerBound) =>
                EffectsUnion(existingLowerBound, Effects(spuriousLiterals, spuriousOperands)).normalized
          yield
            ctx.updateConstraint(u, UmcEffSubsumption(newLowerBound))
            Set.empty
        case _ => Left(NotEffectSubsumption(sub, sup))
    // If spurious operands are all stuck computation, it's possible for sub to be if all of these stuck computation
    // ends up being assigned values that are part of sup
    // Also, if sup contains stuck computation, it's possible for sup to end up including arbitrary effects and hence
    // we can't decide subsumption yet.
    else if spuriousOperands.forall(isMeta) || unionOperands2.exists(isMeta) then
      Right(Set(Constraint.EffSubsumption(Γ, sub, sup)))
    else Left(NotEffectSubsumption(sub, sup))
  case _ => Left(NotEffectSubsumption(sub, sup))

/** Checks if l1 is smaller than l2.
  */
private def checkLevelSubsumption
  (sub: VTerm, sup: VTerm)
  (using Γ: Context)
  (using Σ: Signature)
  (using ctx: TypingContext)
  : Either[IrError, Set[Constraint]] = check2(sub, sup):
  case (v: VTerm, Level(literal2, operands2)) =>
    // Normalization would unwrap any wrappers with a single operand so we need to undo that here.
    val (literal1, operands1) = v match
      case Level(literal1, operands1) => (literal1, operands1)
      case v: VTerm                   => (LevelOrder.zero, Map(v -> 0))
    val spuriousOperands = getSpurious[VTerm, Int](operands1, operands2)
    if spuriousOperands.isEmpty && literal1.compareTo(literal2) <= 0 then Right(Set.empty)
    else
    // If spurious operands are all stuck computation, it's possible for sub to be if all of these stuck computation
    // ends up being assigned small levels
    // Also, if sup contains stuck computation, it's possible for sup to end up including arbitrary large level and
    // hence we can't decide subsumption yet.
    if spuriousOperands.keys.forall(isMeta) || operands2.keys.exists(isMeta) then
      Right(Set(Constraint.LevelSubsumption(Γ, sub, sup)))
    else Left(NotLevelSubsumption(sub, sup))
  // Handle the special case that the right hand side simply contains the left hand side as an operand.
  case (RUnsolved(_, _, _, tm, _), Level(_, operands)) if operands.contains(Collapse(tm)) => Right(Set.empty)
  case (sub: VTerm, u @ RUnsolved(_, _, constraint, tm, ty)) =>
    ctx.adaptForMetaVariable(u, sub) match
      case None => Right(Set(Constraint.LevelSubsumption(Γ, sub, sup)))
      case Some(value) =>
        for newLowerBound <- constraint match
            case UmcNothing                              => Right(value)
            case UmcLevelSubsumption(existingLowerBound) => LevelMax(existingLowerBound, value).normalized
            case _                                       => throw IllegalStateException("type error")
        yield
          ctx.updateConstraint(u, UmcLevelSubsumption(newLowerBound))
          Set.empty
  // If upper bound is zero, the meta variable can only take zero as the value.
  case (
      u @ RUnsolved(_, _, UmcLevelSubsumption(existingLowerBound), tm, ty),
      Level(LevelOrder.zero, operands),
    ) if operands.isEmpty =>
    ctx.assignUnsolved(u, Return(Level(LevelOrder.zero, Map()), u1))
  case (u @ RUnsolved(_, _, UmcLevelSubsumption(existingLowerBound), tm, ty), sup: VTerm) =>
    ctx.adaptForMetaVariable(u, sub) match
      case Some(value) if value == existingLowerBound => ctx.assignUnsolved(u, Return(value, u1))
      case _                                          => Right(Set(Constraint.LevelSubsumption(Γ, sub, sup)))
  case (_: ResolvedMetaVariable, _: ResolvedMetaVariable) => Right(Set(Constraint.LevelSubsumption(Γ, sub, sup)))
  case _                                                  => Left(NotLevelSubsumption(sub, sup))

private def getSpurious[T, E: PartialOrdering](sub: Map[T, E], sup: Map[T, E]): Map[T, E] =
  sub.filter { case (operand1, e1) =>
    sup.get(operand1) match
      case None     => true
      case Some(e2) => summon[PartialOrdering[E]].gt(e1, e2)
  }

private def check2
  (a: VTerm, b: VTerm)
  (action: (ResolvedMetaVariable | VTerm, ResolvedMetaVariable | VTerm) => Either[IrError, Set[Constraint]])
  (using Γ: Context)
  (using Σ: Signature)
  (using ctx: TypingContext)
  : Either[IrError, Set[Constraint]] =
  if a == b then Right(Set.empty)
  else
    debugSubsumption(a, b):
      for
        a <- a.normalized
        b <- b.normalized
        r <- ctx.withMetaResolved2(a, b)(action)
      yield r

private def check2
  (a: CTerm, b: CTerm)
  (
    action: (
      (ResolvedMetaVariable, List[Elimination[VTerm]]) | CTerm,
      (ResolvedMetaVariable, List[Elimination[VTerm]]) | CTerm,
    ) => Either[IrError, Set[Constraint]],
  )
  (using Γ: Context)
  (using Σ: Signature)
  (using ctx: TypingContext)
  : Either[IrError, Set[Constraint]] =
  if a == b then Right(Set.empty)
  else
    debugSubsumption(a, b):
      for
        a <- a.normalized(None)
        b <- b.normalized(None)
        r <- ctx.withMetaResolved2(a, b)(action)
      yield r

private inline def debugSubsumption[L, R]
  (rawSub: CTerm | VTerm, rawSup: CTerm | VTerm)
  (result: => Either[L, R])
  (using Context)
  (using Signature)
  (using ctx: TypingContext)
  : Either[L, R] =
  ctx.trace(
    s"deciding",
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
