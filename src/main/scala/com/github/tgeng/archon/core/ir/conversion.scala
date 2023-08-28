package com.github.tgeng.archon.core.ir

import com.github.tgeng.archon.common.*
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

/**
  * Preconditions: rawSub and rawSup are already type checked against ty, which is normalized.
  * @param rawTy optional if sub and sup are types
  */
def checkIsConvertible(sub: VTerm, sup: VTerm, ty: Option[VTerm])
  (using Γ: Context)
  (using Σ: Signature)
  (using ctx: TypingContext)
  : Either[IrError, Set[Constraint]] = debugConversion(sub, sup, ty):
    if sub == sup then Right(Set.empty)
    else 
      for 
        sub <- sub.normalized
        sup <- sup.normalized
        r <- (sub, sup, ty) match
          case (_, _, _) if sub == sup => Right(Set.empty)
          case (Type(upperBound1), Type(upperBound2), _) =>
            checkIsConvertible(upperBound1, upperBound2, None)
          case (ty, Top(ul2, eqD2), _) =>
            for
              ul1 <- inferLevel(ty)
              levelConstraints <- checkULevelSubsumption(ul1, ul2)
              eqD1 <- deriveTypeInherentEqDecidability(ty)
              eqDecidabilityConstraints <- checkIsConvertible(eqD1, eqD2, Some(EqDecidabilityType()))
            yield levelConstraints ++ eqDecidabilityConstraints
          case (U(cty1), U(cty2), _) => checkIsConvertible(cty1, cty2, None)
          case (Thunk(c1), Thunk(c2), Some(U(ty))) =>
            checkIsConvertible(c1, c2, Some(ty))
          case (DataType(qn1, args1), DataType(qn2, args2), _) if qn1 == qn2 =>
            Σ.getDataOption(qn1) match
              case None => Left(MissingDeclaration(qn1))
              case Some(data) =>
                transpose(
                  args1
                    .zip(args2)
                    .zip(data.tParamTys ++ data.tIndexTys.map((_, Variance.INVARIANT)))
                    .zipWithIndex
                    .map { case (((arg1, arg2), (binding, variance)), i) =>
                      checkIsConvertible( arg1, arg2, Some(binding.ty.substLowers(args1.take(i): _*)))
                    },
                ).map(_.flatten.toSet)
          case (Con(name1, args1), Con(name2, args2), Some(DataType(qn, _))) if name1 == name2 =>
            Σ.getConstructorOption(qn, name1) match
              case None => Left(MissingConstructor(name1, qn))
              case Some(con) =>
                var args = IndexedSeq[VTerm]()
                transpose(
                  args1
                    .zip(args2)
                    .zip(con.paramTys)
                    .zipWithIndex
                    .map { case (((arg1, arg2), binding), i) =>
                      checkIsConvertible( arg1, arg2, Some(binding.ty.substLowers(args1.take(i): _*)))
                    },
                ).map(_.flatten.toSet)
          case (EffectsType(continuationUsage1), EffectsType(continuationUsage2), _) =>
            // Note that subsumption checking is reversed because the effect of the computation
            // marks how the continuation can be invoked. Normally, checking usage is checking
            // how a resource is *consumed*. But here, checking usage is checking how the
            // continuation (as a resource) is provided.
            checkContinuationUsageSubsumption(continuationUsage2, continuationUsage1)
          case (UsageType(Some(u1)), UsageType(Some(u2)), _) =>
            checkIsConvertible(u1, u2, Some(UsageType()))
          case ( CellType(heap1, ty1), CellType(heap2, ty2), _) =>
            for
              heapConstraints <- checkIsConvertible(heap1, heap2, Some(HeapType()))
              tyConstraints <- checkIsConvertible(ty1, ty2, None)
            yield heapConstraints ++ tyConstraints
          case (Collapse(c), v, ty) => checkIsConvertible(c, Return(v), ty.map(F(_)))
          case (v, Collapse(c), ty) => checkIsConvertible(Return(v), c, ty.map(F(_)))
          case _ => Left(NotVConvertible(sub, sup, ty))
      yield r

/**
  * Preconditions: rawSub and rawSup are already type checked against ty, which is normalized.
  * @param rawTy optional if sub and sup are types
  */
def checkIsConvertible(sub: CTerm, sup: CTerm, ty: Option[CTerm])
  (using Γ: Context)
  (using Σ: Signature)
  (using ctx: TypingContext)
  : Either[IrError, Set[Constraint]] = debugConversion(sub, sup, ty):
    if sub == sup then Right(Set.empty)
    else
      for
        sub <- sub.normalized(ty)
        sup <- sup.normalized(ty)
        r <- (sub, sup, ty) match
          case (_, _, _) if sub == sup => Right(Set.empty)
          case (_, _, Some(FunctionType(binding, bodyTy, _))) =>
            checkIsConvertible(
              Application(sub.weakened, Var(0)),
              Application(sup.weakened, Var(0)),
              Some(bodyTy),
            )(using Γ :+ binding)
          case (_, _, Some(RecordType(qn, _, _))) =>
            Σ.getFieldsOption(qn) match
              case None => Left(MissingDefinition(qn))
              case Some(fields) =>
                transpose(
                  fields.map { field =>
                    checkIsConvertible(
                      Projection(sub, field.name),
                      Projection(sup, field.name),
                      Some(field.ty),
                    )
                  },
                ).map(_.flatten.toSet)
          case (CType(upperBound1, eff1), CType(upperBound2, eff2), _) =>
            for
              effConstraint <- checkIsConvertible(eff1, eff2, Some(EffectsType()))
              upperBoundConstraint <- checkIsConvertible(upperBound1, upperBound2, Some(sup))
            yield effConstraint ++ upperBoundConstraint
          case (ty: IType, CTop(ul2, eff2), _) =>
            for
              ul1 <- inferLevel(ty)
              levelConstraint <- checkULevelSubsumption(ul1, ul2)
              effConstraint <- checkIsConvertible(ty.effects, eff2, Some(EffectsType()))
            yield levelConstraint ++ effConstraint
          case (F(vTy1, eff1, u1), F(vTy2, eff2, u2), _) =>
            for
              effConstraint <- checkIsConvertible(eff1, eff2, Some(EffectsType()))
              usageConstraint <- checkIsConvertible(u1, u2, Some(UsageType()))
              tyConstraint <- checkIsConvertible(vTy1, vTy2, None)
            yield effConstraint ++ usageConstraint ++ tyConstraint
          case (Return(v1), Return(v2), Some(F(ty, _, _))) =>
            checkIsConvertible(v1, v2, Some(ty))
          case (Let(t1, ty1, eff1, usage1, ctx1), Let(t2, ty2, eff2, usage2, ctx2), ty) =>
            for
              tyConstraint <- checkIsConvertible(ty1, ty2, None)
              effConstraint <- checkIsConvertible(eff1, eff2, Some(EffectsType())).flatMap(ctx.solve)
              usageConstraint <- checkIsConvertible(usage1, usage2, Some(UsageType()))
              combinedEffects <- if effConstraint.isEmpty then Right(eff1) else EffectsUnion(eff1, eff2).normalized
              tConstraint <- checkIsConvertible(
                t1,
                t2,
                // Note on type used heres
                // * The concrete type passed here does not affect correctness of type checking.
                // * A combined effect is used to be safe (e.g. we don't want to normalize potentially diverging terms)
                // * Usage is not important during subsumption checking, hence we just pass UUnres.
                Some(F(ty1, combinedEffects, UsageLiteral(UUnres))),
              )
              ctxConstraint <- checkIsConvertible(ctx1, ctx2, ty.map(_.weakened))(
                // Using ty1 or ty2 doesn't really matter here. We don't need to do any lambda substitution because ty1
                // or ty2 are not referenced by anything in ctx1 or ctx2 or ty.
                using Γ :+ Binding(ty1, UsageLiteral(UUnres))(gn"v"),
              )
            yield tyConstraint ++ effConstraint ++ usageConstraint ++ tConstraint ++ ctxConstraint
          case (FunctionType(binding1, bodyTy1, eff1), FunctionType(binding2, bodyTy2, eff2), _) =>
            for
              effConstraint <- checkIsConvertible(eff1, eff2, Some(EffectsType()))
              tyConstraint <- checkIsConvertible(binding2.ty, binding1.ty, None).flatMap(ctx.solve)
              bodyConstraint <-
                if tyConstraint.isEmpty
                then checkIsConvertible(bodyTy1, bodyTy2, None)(using Γ :+ binding2)
                else
                  val meta = ctx.addMetaVar(
                    Guarded(
                      Γ :+ binding2,
                      F(binding1.ty.weakened, Total(), binding1.usage.weakened),
                      Return(Var(0)),
                      tyConstraint,
                    ),
                  )
                  checkIsConvertible(
                    bodyTy1,
                    bodyTy2.subst {
                      case 0 => Some(Collapse(vars(Γ.size).foldLeft[CTerm](meta)(Application(_, _))))
                      case _ => None
                    },
                    None,
                  )(using Γ :+ binding2)
            yield effConstraint ++ tyConstraint ++ bodyConstraint
          // bare meta should be very rare since almost all terms would be under some context. But if they do appear, we
          // just wrap them inside redux
          case (subM: Meta, supM: Meta, ty) =>
            checkReduxSubsumption(Redux(subM, Nil), Redux(supM, Nil), ty)
          case (subR: Redux, supR: Redux, ty) =>
            checkReduxSubsumption(Redux(subR, Nil), Redux(supR, Nil), ty)
          case (RecordType(qn1, args1, eff1), RecordType(qn2, args2, eff2), _) if qn1 == qn2 =>
            Σ.getRecordOption(qn1) match
              case None => Left(MissingDeclaration(qn1))
              case Some(record) =>
                var args = IndexedSeq[VTerm]()
                for
                  effConstraint <- checkIsConvertible(eff1, eff2, Some(EffectsType()))
                  argConstraint <- transpose(
                    args1
                      .zip(args2)
                      .zip(record.tParamTys)
                      .map { case ((arg1, arg2), (binding, variance)) =>
                        variance match
                          case Variance.INVARIANT =>
                            val r = checkIsConvertible( arg1, arg2, Some(binding.ty.substLowers(args: _*)))
                            args = args :+ arg1
                            r
                          case Variance.COVARIANT =>
                            val r = checkIsConvertible( arg1, arg2, Some(binding.ty.substLowers(args: _*)))
                            args = args :+ arg1
                            r
                          case Variance.CONTRAVARIANT =>
                            val r = checkIsConvertible( arg2, arg1, Some(binding.ty.substLowers(args: _*)))
                            args = args :+ arg2
                            r
                      },
                  ).map(_.flatten.toSet)
                yield effConstraint ++ argConstraint
          case (
              OperationCall((qn1, tArgs1), name1, args1),
              OperationCall((qn2, tArgs2), name2, args2),
              _,
            ) if qn1 == qn2 && name1 == name2 =>
            Σ.getOperationOption(qn1, name1) match
              case None => Left(MissingOperation(name1, qn1))
              case Some(operation) =>
                var args = IndexedSeq[VTerm]()
                Σ.getEffectOption(qn1) match
                  case None => Left(MissingDeclaration(qn1))
                  case Some(effect) =>
                    for
                      tArgConstraint <- transpose(
                        tArgs1.zip(tArgs2).zip(effect.tParamTys).map {
                          case ((tArg1, tArg2), binding) =>
                            val r = checkIsConvertible(tArg1, tArg2, Some(binding.ty))
                            args = args :+ tArg1
                            r
                        },
                      ).map(_.flatten.toSet)
                      argConstraint <- transpose(
                        args1.zip(args2).zip(operation.paramTys).map { case ((arg1, arg2), binding) =>
                          val r = checkIsConvertible(arg1, arg2, Some(binding.ty))
                          args = args :+ arg1
                          r
                        },
                      ).map(_.flatten.toSet)
                    yield tArgConstraint ++ argConstraint
          // For now, we skip the complex logic checking subsumption of handler and continuations. It
          // seems not all that useful to keep those. But we can always add them later if it's deemed
          // necessary.
          case _ => Left(NotCConvertible(sub, sup, ty))
      yield r

def checkAreConvertible(subs: List[VTerm], sups: List[VTerm], tys: Telescope)
  (using mode: CheckSubsumptionMode)
  (using Γ: Context)
  (using Σ: Signature)
  (using ctx: TypingContext)
  : Either[IrError, Set[Constraint]] =
  // See [0] Figure 3.8
  (subs, sups, tys) match
    case (Nil, Nil, Nil) => Right(Set.empty)
    case (sub :: tailSubs, sup :: tailSups, ty :: tys) =>
      for
        headConstraints <- checkIsConvertible(sub, sup, Some(ty.ty)).flatMap(ctx.solve)
        r <-
          if headConstraints.isEmpty
          then checkAreConvertible(tailSubs, tailSups, tys.substLowers(sub))
          else
            val (a, b) = getFreeVars(tys)(using 0)
            if a(0) || b(0)
              // if the head term is referenced in the tail, add the whole thing as a constraint
            then Right(Set(Constraint(Γ, subs, sups, tys, mode)))
            // the head term is not referenced in the tail, add the tail constraint in addition to the head
            // constraints
            else checkAreConvertible(tailSubs, tailSups, tys.strengthened).map(headConstraints ++ _)
      yield r
    case _ => throw IllegalArgumentException("length mismatch")

private inline def debugConversion[L, R]
  (
    rawSub: CTerm | VTerm,
    rawSup: CTerm | VTerm,
    rawTy: Option[CTerm | VTerm])
    ( result: => Either[L, R])
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
      "≡",
      yellow(rawSup.sourceInfo),
      pprint(rawSup),
      ":",
      yellow(rawTy.map(_.sourceInfo).getOrElse(SiEmpty)),
      rawTy.map(pprint),
    ),
  )(result)

/* References
 [0]  Norell, Ulf. “Towards a practical programming language based on dependent type theory.” (2007).
 */
