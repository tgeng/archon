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

/** Preconditions: sub and sup are both checked to be types
  */
def checkIsSubtype
  (sub: VTerm, sup: VTerm)
  (using Γ: Context)
  (using Σ: Signature)
  (using ctx: TypingContext)
  : Either[IrError, Set[Constraint]] = debugIsSubtyping(sub, sup):
  if sub == sup then Right(Set.empty)
  else
    for
      sub <- sub.normalized
      sup <- sup.normalized
      r <- ctx.withMetaResolved2(sub, sup):
        case (_, _) if sub == sup                   => Right(Set.empty)
        // TODO: handle meta variable cases
        case (Type(upperBound1), Type(upperBound2)) => checkIsSubtype(upperBound1, upperBound2)
        case (ty: VTerm, Top(level2, eqD2)) =>
          for
            level1 <- inferLevel(ty)
            levelConstraints <- checkLevelSubsumption(level1, level2)
            eqD1 <- deriveTypeInherentEqDecidability(ty)
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
        case (EffectsType(continuationUsage1), EffectsType(continuationUsage2)) =>
          // Note that subsumption checking is reversed because the effect of the computation
          // marks how the continuation can be invoked. Normally, checking usage is checking
          // how a resource is *consumed*. But here, checking usage is checking how the
          // continuation (as a resource) is provided.
          checkContinuationUsageSubsumption(continuationUsage2, continuationUsage1)
        case (UsageType(Some(u1)), UsageType(Some(u2))) => checkUsageSubsumption(u1, u2)
        case (UsageType(Some(_)), UsageType(None))      => Right(Set.empty)
        case (v: Var, ty2: VTerm) =>
          Γ.resolve(v).ty match
            case Type(upperBound) => checkIsSubtype(upperBound, ty2)
            case _                => Left(NotVSubtype(sub, sup))
        case _ => checkIsConvertible(sub, sup, None)
    yield r

/** Preconditions: sub and sup are both types
  */
def checkIsSubtype
  (sub: CTerm, sup: CTerm)
  (using Γ: Context)
  (using Σ: Signature)
  (using ctx: TypingContext)
  : Either[IrError, Set[Constraint]] = debugIsSubtyping(sub, sup):
  if sub == sup then Right(Set.empty)
  else
    for
      sub <- sub.normalized(None)
      sup <- sup.normalized(None)
      r <- ctx.withMetaResolved2(sub, sup):
        case (_, _) if sub == sup => Right(Set.empty[Constraint])
        case (_, (u@RUnsolved(_, _, constraint, tm, ty), Nil)) => ctx.adaptForMetaVariable(u, sub) match
          case None => Right(Set(Constraint.CSubType(Γ, sub, sup)))
          case Some(value) =>
            for 
              newConstraint <- constraint match
                case UmcNothing => Right(UmcCSubtype(value))
                case UmcCSubtype(existingLowerBound) =>
                  for
                    lowerBound <- typeUnion(existingLowerBound, value)
                  yield UmcCSubtype(lowerBound)
                case _ => throw IllegalStateException("type error")
            yield 
              ctx.updateConstraint(u, newConstraint)
              Set.empty
        case ((u@RUnsolved(_, _, UmcCSubtype(existingLowerBound), tm, ty), Nil), sup: CTerm) => ctx.adaptForMetaVariable(u, sub) match
          case Some(value) if value == existingLowerBound => ctx.assignUnsolved(u, value)
          case _ => Right(Set(Constraint.CSubType(Γ, sub, sup)))
        case ((_: ResolvedMetaVariable, _), _) | (_, (_: ResolvedMetaVariable, _)) => Right(Set(Constraint.CSubType(Γ, sub, sup)))
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
                            Return(Var(0)),
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
    yield r

private def typeUnion(a: CTerm, b: CTerm): Either[IrError, CTerm] = ???
private def typeUnion(a: VTerm, b: VTerm): Either[IrError, VTerm] = ???

private def checkEqDecidabilitySubsumption
  (eqD1: VTerm, eqD2: VTerm)
  (using Γ: Context)
  (using Σ: Signature)
  (using
    ctx: TypingContext,
  )
  : Either[IrError, Set[Constraint]] = (eqD1.normalized, eqD2.normalized) match
  // TODO: handle meta variables
  case (Left(e), _)                               => Left(e)
  case (_, Left(e))                               => Left(e)
  case (Right(eqD1), Right(eqD2)) if eqD1 == eqD2 => Right(Set.empty)
  case (Right(EqDecidabilityLiteral(EqDecidability.EqDecidable)), _) |
    (_, Right(EqDecidabilityLiteral(EqDecidability.EqUnknown))) =>
    Right(Set.empty)
  case _ => Left(NotEqDecidabilitySubsumption(eqD1, eqD2))

/** @param invert
  *   useful when checking patterns where the consumed usages are actually provided usages because
  *   lhs patterns are multiplied by declared usages in function
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

private def checkContinuationUsageSubsumption
  (usage1: Option[Usage], usage2: Option[Usage])
  (using Γ: Context)
  (using Σ: Signature)
  (using ctx: TypingContext)
  : Either[IrError, Set[Constraint]] = (usage1, usage2) match
  case (None, None) => Right(Set.empty)
  case (None, Some(u)) =>
    checkUsageSubsumption(UsageLiteral(U1), UsageLiteral(u)) match
      case r @ Right(_) => r
      case Left(_: NotUsageSubsumption) =>
        Left(NotContinuationUsageSubsumption(usage1, usage2))
      case l @ Left(_) => l
  case (Some(u1), Some(u2)) =>
    checkUsageSubsumption(UsageLiteral(u1), UsageLiteral(u2)) match
      case r @ Right(_) => r
      case Left(_: NotUsageSubsumption) =>
        Left(NotContinuationUsageSubsumption(usage1, usage2))
      case l @ Left(_) => l
  case _ => Left(NotContinuationUsageSubsumption(usage1, usage2))

def checkUsageSubsumption
  (usage1: VTerm, usage2: VTerm)
  (using Γ: Context)
  (using Σ: Signature)
  (using ctx: TypingContext)
  : Either[IrError, Set[Constraint]] = (usage1.normalized, usage2.normalized) match
  // TODO: handle meta variables (consider handling meta variable in compound usage like how level and effects are
  // handled)
  case (Left(e), _)                                       => Left(e)
  case (_, Left(e))                                       => Left(e)
  case (Right(usage1), Right(usage2)) if usage1 == usage2 => Right(Set.empty)
  // Note on direction of usage comparison: UUnres > U1 but UUnres subsumes U1 when counting usage
  case (Right(UsageLiteral(u1)), Right(UsageLiteral(u2))) if u1 >= u2 =>
    Right(Set.empty)
  case (Right(UsageLiteral(UUnres)), _) => Right(Set.empty)
  case (Right(v @ Var(_)), Right(UsageLiteral(u2))) =>
    Γ.resolve(v).ty match
      // Only UUnres subsumes UUnres and UUnres is also convertible with itself.
      case UsageType(Some(UsageLiteral(Usage.UUnres))) if u2 == Usage.UUnres => Right(Set.empty)
      case UsageType(Some(u1Bound)) =>
        checkUsageSubsumption(u1Bound, UsageLiteral(u2))
      case _ => Left(NotUsageSubsumption(usage1, usage2))
  case _ => Left(NotUsageSubsumption(usage1, usage2))

private def checkEffSubsumption
  (eff1: VTerm, eff2: VTerm)
  (using Γ: Context)
  (using Σ: Signature)
  (using ctx: TypingContext)
  : Either[IrError, Set[Constraint]] =
  // TODO: handle meta variables (consider handling meta variables in the set by instantiating it to a union of missing
  // effects)
  (eff1.normalized, eff2.normalized) match
    case (Left(e), _)                               => Left(e)
    case (_, Left(e))                               => Left(e)
    case (Right(eff1), Right(eff2)) if eff1 == eff2 => Right(Set.empty)
    case (
        Right(Effects(literals1, unionOperands1)),
        Right(Effects(literals2, unionOperands2)),
      ) if literals1.subsetOf(literals2) && unionOperands1.subsetOf(unionOperands2) =>
      Right(Set.empty)
    case _ => Left(NotEffectSubsumption(eff1, eff2))

/** Checks if l1 is smaller than l2.
  */
private def checkLevelSubsumption
  (l1: VTerm, l2: VTerm)
  (using Γ: Context)
  (using Σ: Signature)
  (using TypingContext)
  : Either[IrError, Set[Constraint]] =
  def extractLiteralAndOperands(level: VTerm): Either[IrError, Option[(LevelOrder, Map[VTerm, Nat])]] =
    for level <- level.normalized
    yield level match
      case Level(l, operands) => Some((l, operands))
      case v: Var             => Some((LevelOrder.zero, Map(v -> 0)))
      // TODO: handle meta variable updates
      case c: Collapse => None
      case _           => throw IllegalStateException("type error")
  for
    l1Components <- extractLiteralAndOperands(l1)
    l2Components <- extractLiteralAndOperands(l2)
    r <-
      (l1Components, l2Components) match
        // Level 0 subsumes any level
        case (Some((LevelOrder.zero, operands)), _) if operands.isEmpty => Right(Set.empty)
        // Any stuck computation makes subsumption unknown so we just delay it.
        case (None, _) | (_, None) => Right(Set(Constraint.LevelSubsumption(Γ, l1, l2)))
        // Normal case where we can compare the literals and operands directly.
        case (Some((l1, operands1)), Some((l2, operands2)))
          if l1.compareTo(l2) <= 0 && operands1
            .forall((operand1, offset1) => operands2.get(operand1).getOrElse(-1) >= offset1) =>
          Right(Set.empty)
        // If l2 has some stuck computation, it's possible for l2 to be arbitrarily large so we just delay it.
        case (_, Some(_, operands)) if operands.keys.exists(hasCollapse) =>
          Right(Set(Constraint.LevelSubsumption(Γ, l1, l2)))
        // At this point l2 does not contain any meta variables. Hence, l2 is fixed and the only way for subsumption to
        // possibly work is that l1 only contains some extra stuck computations under operands. Otherwise, subsumption
        // eheck must fail.
        case (Some(literal1, _), Some(literal2, _)) if literal1.compareTo(literal2) > 0 =>
          Left(NotVSubsumption(l1, l2, Some(LevelType(LevelUpperBound()))))
        case (Some(_, operands1), Some(_, operands2)) =>
          // Offending operands are those that has an offset in l1 that is larger than the offset in l2 and is not a
          // stuck computation.
          val offendingOperands = operands1.filter { (operand1, offset1) =>
            operands2.get(operand1).getOrElse(-1) < offset1 && !hasCollapse(operand1)
          }
          if offendingOperands.isEmpty
          then Right(Set(Constraint.LevelSubsumption(Γ, l1, l2)))
          else Left(NotVSubsumption(l1, l2, Some(LevelType(LevelUpperBound()))))
  yield r

private inline def debugIsSubtyping[L, R]
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
