package com.github.tgeng.archon.core.ir

import com.github.tgeng.archon.common.*
import com.github.tgeng.archon.common.eitherFilter.*
import com.github.tgeng.archon.core.common.*
import com.github.tgeng.archon.core.ir.Reducible.reduce

import VTerm.*
import CTerm.*
import ULevel.*
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
import scala.collection.mutable.ArrayBuffer

/**
  * Preconditions: rawSub and rawSup are both types
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
        r <- (sub, sup) match
          case (_, _) if sub == sup => Right(Set.empty)
          case (Type(upperBound1), Type(upperBound2)) => checkIsSubtype(upperBound1, upperBound2)
          case (ty, Top(ul2, eqD2)) =>
            for
              ul1 <- inferLevel(ty)
              levelConstraints <- checkULevelSubsumption(ul1, ul2)
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
                          for (arg1, _) <- checkIsType(arg1)
                              (arg2, _) <- checkIsType(arg2)
                              r <- checkIsSubtype(arg1, arg2)
                          yield 
                            args += arg1
                            r
                        case Variance.CONTRAVARIANT =>
                          for (arg1, _) <- checkIsType(arg1)
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
          case (UsageType(Some(_)), UsageType(None)) => Right(Set.empty)
          case (CellType(heap1, ty1), CellType(heap2, ty2)) =>
            for
              heapConstraints <- checkIsConvertible(heap1, heap2, Some(HeapType()))
              tyConstraints <- checkIsSubtype(ty1, ty2)
            yield heapConstraints ++ tyConstraints
          case (v: Var, ty2) =>
            Γ.resolve(v).ty match
              case Type(upperBound) => checkIsSubtype(upperBound, ty2)
              case _ => Left(NotVSubtype(sub, sup))
          case _ => Left(NotVSubtype(sub, sup))
      yield r

/**
  * Preconditions: rawSub and rawSup are both types
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
        r <- (sub, sup) match
          case (_, _) if sub == sup => Right(Set.empty[Constraint])
          case _ => ???
      yield r


private def checkEqDecidabilitySubsumption
  (eqD1: VTerm, eqD2: VTerm)
  (using mode: CheckSubsumptionMode)
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
  case _ => Left(NotEqDecidabilitySubsumption(eqD1, eqD2, mode))

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
  (using mode: CheckSubsumptionMode)
  (using Γ: Context)
  (using Σ: Signature)
  (using ctx: TypingContext)
  : Either[IrError, Set[Constraint]] = (usage1, usage2) match
  case (None, None) => Right(Set.empty)
  case (None, Some(u)) =>
    checkUsageSubsumption(UsageLiteral(U1), UsageLiteral(u)) match
      case r @ Right(_) => r
      case Left(_: NotUsageSubsumption) =>
        Left(NotContinuationUsageSubsumption(usage1, usage2, mode))
      case l @ Left(_) => l
  case (Some(u1), Some(u2)) =>
    checkUsageSubsumption(UsageLiteral(u1), UsageLiteral(u2)) match
      case r @ Right(_) => r
      case Left(_: NotUsageSubsumption) =>
        Left(NotContinuationUsageSubsumption(usage1, usage2, mode))
      case l @ Left(_) => l
  case _ => Left(NotContinuationUsageSubsumption(usage1, usage2, mode))

private def checkUsageSubsumption
  (usage1: VTerm, usage2: VTerm)
  (using mode: CheckSubsumptionMode)
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
      case _ => Left(NotUsageSubsumption(usage1, usage2, mode))
  case _ => Left(NotUsageSubsumption(usage1, usage2, mode))

private def checkEffSubsumption
  (eff1: VTerm, eff2: VTerm)
  (using mode: CheckSubsumptionMode)
  (using Γ: Context)
  (using Σ: Signature)
  (using
    ctx: TypingContext,
  )
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
      )
      if mode == CheckSubsumptionMode.SUBSUMPTION &&
        literals1.subsetOf(literals2) && unionOperands1.subsetOf(unionOperands2) =>
      Right(Set.empty)
    case _ => Left(NotEffectSubsumption(eff1, eff2, mode))

/** Check that `ul1` is lower or equal to `ul2`.
  */
private def checkULevelSubsumption
  (ul1: ULevel, ul2: ULevel)
  (using mode: CheckSubsumptionMode)
  (using Γ: Context)
  (using Σ: Signature)
  (using
    TypingContext,
  )
  : Either[IrError, Set[Constraint]] =
  // TODO: handle meta variables (consider handle meta variables inside offset Map by instantiating a meta variable to a
  // level max)
  val ul1Normalized = ul1 match
    case USimpleLevel(v) =>
      v.normalized match
        case Left(e)       => return Left(e)
        case Right(v: Var) => USimpleLevel(Level(0, Map(v -> 0)))
        case Right(v)      => USimpleLevel(v)
    case _ => ul1
  val ul2Normalized = ul2 match
    case USimpleLevel(v) =>
      v.normalized match
        case Left(e)       => return Left(e)
        case Right(v: Var) => USimpleLevel(Level(0, Map(v -> 0)))
        case Right(v)      => USimpleLevel(v)
    case _ => ul2

  (ul1Normalized, ul2Normalized) match
    case _ if ul1Normalized == ul2Normalized => Right(Set.empty)
    case (
        USimpleLevel(Level(l1, maxOperands1)),
        USimpleLevel(Level(l2, maxOperands2)),
      )
      if l1 <= l2 &&
        maxOperands1.forall { (k, v) =>
          maxOperands2.getOrElse(k, -1) >= v
        } =>
      Right(Set.empty)
    case (USimpleLevel(_), UωLevel(_))          => Right(Set.empty)
    case (UωLevel(l1), UωLevel(l2)) if l1 <= l2 => Right(Set.empty)
    case _ => Left(NotLevelSubsumption(ul1Normalized, ul2Normalized, mode))

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
