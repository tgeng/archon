package com.github.tgeng.archon.core.ir

import scala.util.boundary, boundary.break;
import com.github.tgeng.archon.common.eitherFilter.*
import com.github.tgeng.archon.common.*
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
import ResolvedMetaVariable.*

// def expectConvertible(target: CTerm, )

/** Preconditions: rawLeft and rawRight are already type checked against ty, which is normalized.
  * @param ty
  *   optional if left and right are types
  */
def checkIsConvertible
  (left: VTerm, right: VTerm, ty: Option[VTerm])
  (using Γ: Context)
  (using Σ: Signature)
  (using ctx: TypingContext)
  : Either[IrError, Set[Constraint]] = debugConversion(left, right, ty):
  if left == right then Right(Set.empty)
  else
    for
      left <- left.normalized
      right <- right.normalized
      r <- (left, right, ty) match
        case (_, _, _) if left == right                                      => Right(Set.empty)
        case (Level(literal1, operands1), Level(literal2, operands2), Some(LevelType(_))) =>
          // If meta some component is not reduced yet, we can't check subsumption
          if operands1.exists((v, _) => hasCollapse(v)) || operands2.exists(((v, _) => hasCollapse(v)))
          then Right(Set(Constraint.VConversion(Γ, left, right, ty)))
          else Left(NotVConvertible(left, right, ty))
        case (Effects(literal1, operands1), Effects(literal2, operands2), Some(EffectsType(_, _))) =>
          // If meta some component is not reduced yet, we can't check subsumption
          if operands1.exists(hasCollapse) || operands2.exists(hasCollapse)
          then Right(Set(Constraint.VConversion(Γ, left, right, ty)))
          else Left(NotVConvertible(left, right, ty))
        case (
            u: UsageCompound,
            _,
            Some(UsageType(_)),
          ) =>
          // If meta some component is not reduced yet, we can't check subsumption
          if u.distinctOperands.exists(hasCollapse)
          then Right(Set(Constraint.VConversion(Γ, left, right, ty)))
          else Left(NotVConvertible(left, right, ty))
        case (
            _,
            u: UsageCompound,
            Some(UsageType(_)),
          ) =>
          // If meta some component is not reduced yet, we can't check subsumption
          if u.distinctOperands.exists(hasCollapse)
          then Right(Set(Constraint.VConversion(Γ, left, right, ty)))
          else Left(NotVConvertible(left, right, ty))
        case (Type(upperBound1), Type(upperBound2), _) =>
          checkIsConvertible(upperBound1, upperBound2, None)
        case (ty, Top(level2, eqD2), _) =>
          for
            level1 <- inferLevel(ty)
            levelConstraints <- checkIsConvertible(
              level1,
              level2,
              Some(LevelType(LevelUpperBound())),
            )
            eqD1 <- inferEqDecidability(ty)
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
                    checkIsConvertible(arg1, arg2, Some(binding.ty.substLowers(args1.take(i): _*)))
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
                    checkIsConvertible(arg1, arg2, Some(binding.ty.substLowers(args1.take(i): _*)))
                  },
              ).map(_.flatten.toSet)
        case (UsageType(Some(u1)), UsageType(Some(u2)), _) =>
          checkIsConvertible(u1, u2, Some(UsageType()))
        case (Collapse(c), v, ty) => checkIsConvertible(c, Return(v), ty.map(F(_)))
        case (v, Collapse(c), ty) => checkIsConvertible(Return(v), c, ty.map(F(_)))
        case _                    => Left(NotVConvertible(left, right, ty))
    yield r

/** Preconditions: rawLeft and rawRight are already type checked against ty, which is normalized.
  * @param rawTy
  *   optional if left and right are types
  */
def checkIsConvertible
  (left: CTerm, right: CTerm, ty: Option[CTerm])
  (using Γ: Context)
  (using Σ: Signature)
  (using ctx: TypingContext)
  : Either[IrError, Set[Constraint]] = debugConversion(left, right, ty):
  if left == right then Right(Set.empty)
  else
    for
      left <- left.normalized(ty)
      right <- right.normalized(ty)
      r <- ty match
        case _ if left == right => Right(Set.empty)
        case Some(FunctionType(binding, bodyTy, _)) =>
          checkIsConvertible(
            Application(left.weakened, Var(0)),
            Application(right.weakened, Var(0)),
            Some(bodyTy),
          )(using Γ :+ binding)
        case Some(RecordType(qn, _, _)) =>
          Σ.getFieldsOption(qn) match
            case None => Left(MissingDefinition(qn))
            case Some(fields) =>
              transpose(
                fields.map { field =>
                  checkIsConvertible(
                    Projection(left, field.name),
                    Projection(right, field.name),
                    Some(field.ty),
                  )
                },
              ).map(_.flatten.toSet)
        case _ =>
          ctx.withMetaResolved2(left, right):
            // If heads are some unsolved meta variable, we can't know for sure that the elims should be the same because
            // the solved meta variables may simply drop whatever eliminations afterwards and hence normalizes to
            // convertible terms.
            case ((m1, elims1), (m2, elims2)) if m1 == m2 =>
              Right(Set(Constraint.CConversion(Γ, left, right, ty)))
            // However, elim checks on var is approprieate.
            case (Redex(t1 @ Force(v1: Var), elims1), Redex(Force(v2: Var), elims2)) if v1 == v2 =>
              Γ.resolve(v1).ty match
                case U(headTy) => checkElimIsConvertible(t1, elims1, elims2, headTy, ty)
                case _         => throw IllegalStateException("type error")
            case ((_: RGuarded, _), _) | (_, (_: RGuarded, _)) =>
              Right(Set(Constraint.CConversion(Γ, left, right, ty)))
            case ((u: RUnsolved, elims), t: CTerm)                  => checkRedexIsConvertible(u, elims, t, ty)
            case (t: CTerm, (u: RUnsolved, elims))                  => checkRedexIsConvertible(u, elims, t, ty)
            case ((u1: RUnsolved, elims1), (u2: RUnsolved, elims2)) =>
              // This step is to make meta variable delegation deterministic
              val (uSmall, elimsSmall, uBig, elimsBig) =
                if u1.index < u2.index
                then (u1, elims1, u2, elims2)
                else (u2, elims2, u1, elims1)
              ctx.adaptForMetaVariable(uSmall, uBig.tm) match
                case Some(bigTm) => ctx.assignUnsolved(uSmall, bigTm)
                case None =>
                  ctx.adaptForMetaVariable(uBig, uSmall.tm) match
                    case Some(smallTm) => ctx.assignUnsolved(uBig, smallTm)
                    case None          => Right(Set(Constraint.CConversion(Γ, left, right, ty)))
            case (CapturedContinuationTip(ty1), CapturedContinuationTip(ty2)) => checkIsConvertible(ty1, ty2, None)
            case (Return(v1), Return(v2)) =>
              ty match
                case Some(F(ty, _, _)) => checkIsConvertible(v1, v2, Some(ty))
                case _                 => throw IllegalStateException("should have been checked to be a F type")
            case (CType(upperBound1, eff1), CType(upperBound2, eff2)) =>
              for
                effConstraint <- checkIsConvertible(eff1, eff2, Some(EffectsType()))
                upperBoundConstraint <- checkIsConvertible(upperBound1, upperBound2, Some(right))
              yield effConstraint ++ upperBoundConstraint
            case (ty: (IType & CTerm), CTop(level2, eff2)) =>
              for
                level1 <- inferLevel(ty)
                levelConstraint <- checkIsConvertible(
                  level1,
                  level2,
                  Some(LevelType(LevelUpperBound())),
                )
                effConstraint <- checkIsConvertible(ty.effects, eff2, Some(EffectsType()))
              yield levelConstraint ++ effConstraint
            case (F(vTy1, eff1, u1), F(vTy2, eff2, u2)) =>
              for
                effConstraint <- checkIsConvertible(eff1, eff2, Some(EffectsType()))
                usageConstraint <- checkIsConvertible(u1, u2, Some(UsageType()))
                tyConstraint <- checkIsConvertible(vTy1, vTy2, None)
              yield effConstraint ++ usageConstraint ++ tyConstraint
            case (Let(t1, ty1, eff1, usage1, ctx1), Let(t2, ty2, eff2, usage2, ctx2)) =>
              for
                tyConstraint <- checkIsConvertible(ty1, ty2, None)
                effConstraint <- checkIsConvertible(eff1, eff2, Some(EffectsType()))
                  .flatMap(ctx.solve)
                usageConstraint <- checkIsConvertible(usage1, usage2, Some(UsageType()))
                combinedEffects <-
                  if effConstraint.isEmpty then Right(eff1) else EffectsUnion(eff1, eff2).normalized
                tConstraint <- checkIsConvertible(
                  t1,
                  t2,
                  // Note on type used heres
                  // * The concrete type passed here does not affect correctness of type checking.
                  // * A combined effect is used to be safe (e.g. we don't want to normalize potentially diverging terms)
                  // * Usage is not important during conversion checking, hence we just pass UAny.
                  Some(F(ty1, combinedEffects, UsageLiteral(UAny))),
                )
                ctxConstraint <- checkIsConvertible(ctx1, ctx2, ty.map(_.weakened))(
                  // Using ty1 or ty2 doesn't really matter here. We don't need to do any lambda substitution because ty1
                  // or ty2 are not referenced by anything in ctx1 or ctx2 or ty.
                  using Γ :+ Binding(ty1, UsageLiteral(UAny))(gn"v"),
                )
              yield tyConstraint ++ effConstraint ++ usageConstraint ++ tConstraint ++ ctxConstraint
            case (FunctionType(binding1, bodyTy1, eff1), FunctionType(binding2, bodyTy2, eff2)) =>
              for
                effConstraint <- checkIsConvertible(eff1, eff2, Some(EffectsType()))
                tyConstraint <- checkIsConvertible(binding2.ty, binding1.ty, None).flatMap(
                  ctx.solve,
                )
                bodyConstraint <-
                  if tyConstraint.isEmpty
                  then checkIsConvertible(bodyTy1, bodyTy2, None)(using Γ :+ binding2)
                  else
                    given Context = Γ :+ binding2
                    checkIsConvertible(
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
                      None,
                    )
              yield effConstraint ++ tyConstraint ++ bodyConstraint
            case (RecordType(qn1, args1, eff1), RecordType(qn2, args2, eff2)) if qn1 == qn2 =>
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
                              val r =
                                checkIsConvertible(
                                  arg1,
                                  arg2,
                                  Some(binding.ty.substLowers(args: _*)),
                                )
                              args = args :+ arg1
                              r
                            case Variance.COVARIANT =>
                              val r =
                                checkIsConvertible(
                                  arg1,
                                  arg2,
                                  Some(binding.ty.substLowers(args: _*)),
                                )
                              args = args :+ arg1
                              r
                            case Variance.CONTRAVARIANT =>
                              val r =
                                checkIsConvertible(
                                  arg2,
                                  arg1,
                                  Some(binding.ty.substLowers(args: _*)),
                                )
                              args = args :+ arg2
                              r
                        },
                    ).map(_.flatten.toSet)
                  yield effConstraint ++ argConstraint
            case (
                OperationCall((qn1, tArgs1), name1, args1),
                OperationCall((qn2, tArgs2), name2, args2),
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
                          tArgs1.zip(tArgs2).zip(effect.tParamTys).map { case ((tArg1, tArg2), binding) =>
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
            // For now, we skip the complex logic checking conversion of handler and continuations. It
            // seems not all that useful to keep those. But we can always add them later if it's deemed
            // necessary.
            case _ => Left(NotCConvertible(left, right, ty))
    yield r

def checkAreConvertible
  (lefts: List[VTerm], rights: List[VTerm], tys: Telescope)
  (using Γ: Context)
  (using Σ: Signature)
  (using ctx: TypingContext)
  : Either[IrError, Set[Constraint]] =
  // See [0] Figure 3.8
  (lefts, rights, tys) match
    case (Nil, Nil, Nil) => Right(Set.empty)
    case (left :: tailLefts, right :: tailRights, ty :: tys) =>
      for
        headConstraints <- checkIsConvertible(left, right, Some(ty.ty)).flatMap(ctx.solve)
        r <-
          if headConstraints.isEmpty
          then checkAreConvertible(tailLefts, tailRights, tys.substLowers(left))
          else
            val (a, b) = getFreeVars(tys)(using 0)
            if a(0) || b(0)
              // if the head term is referenced in the tail, add the whole thing as a constraint
            then Right(Set(Constraint.Conversions(Γ, lefts, rights, tys)))
            // the head term is not referenced in the tail, add the tail constraint in addition to the head
            // constraints
            else checkAreConvertible(tailLefts, tailRights, tys.strengthened).map(headConstraints ++ _)
      yield r
    case _ => throw IllegalArgumentException("length mismatch")

private def checkRedexIsConvertible
  (r: RUnsolved, extraElims: List[Elimination[VTerm]], target: CTerm, ty: Option[CTerm])
  (using Γ: Context)
  (using Σ: Signature)
  (using ctx: TypingContext)
  : Either[IrError, Set[Constraint]] =
  ctx.alignElims(target, extraElims) match
    case None => Right(Set(Constraint.CConversion(Γ, redex(r.tm, extraElims), target, ty)))
    case Some(target) =>
      ctx.adaptForMetaVariable(r, target) match
        case Some(value) => ctx.assignUnsolved(r, value)
        case None        => Right(Set(Constraint.CConversion(Γ, r.tm, target, ty)))

private def checkElimIsConvertible
  (
    head: CTerm,
    lefts: List[Elimination[VTerm]],
    rights: List[Elimination[VTerm]],
    headTy: CTerm,
    ty: Option[CTerm],
  )
  (using Γ: Context)
  (using Σ: Signature)
  (using ctx: TypingContext)
  : Either[IrError, Set[Constraint]] =
  val resultConstraint = Set(
    Constraint.CConversion(Γ, redex(head, lefts), redex(head, rights), ty),
  )
  (lefts, rights, headTy) match
    case (Nil, Nil, _) => Right(Set.empty)
    case (ETerm(left) :: lefts, ETerm(right) :: rights, headTy) =>
      headTy match
        case FunctionType(binding, bodyTy, _) =>
          for
            headConstraints <- checkIsConvertible(left, right, Some(binding.ty)).flatMap(ctx.solve)
            r <-
              if headConstraints.isEmpty then checkElimIsConvertible(Application(head, left), lefts, rights, bodyTy, ty)
              else
                val (a, b) = getFreeVars(bodyTy)(using 0)
                if a(0) || b(0) then Right(resultConstraint)
                else
                  checkElimIsConvertible(
                    Application(head, left),
                    lefts,
                    rights,
                    bodyTy.strengthened,
                    ty,
                  ).map(headConstraints ++ _)
          yield r
        case _ => throw IllegalStateException("should have been checked to be a function type")
    case (EProj(leftName) :: lefts, EProj(rightName) :: rights, rt) =>
      rt match
        case RecordType(qn, args, _) =>
          if leftName == rightName then
            checkElimIsConvertible(
              Projection(head, leftName),
              lefts,
              rights,
              Σ.getField(qn, leftName).ty.substLowers(args :+ Thunk(head): _*),
              ty,
            )
          else Right(resultConstraint)
        case _ => throw IllegalStateException("should have been checked to be a record type")
    case (ETerm(_) :: _, EProj(_) :: _, _) | (EProj(_) :: _, ETerm(_) :: _, _) =>
      throw IllegalArgumentException("type mismatch")
    // Different length may not be a problem since it's possible that one side may be calling more projection of some record
    case (_ :: _, Nil, _) | (Nil, _ :: _, _) => Right(resultConstraint)

private inline def debugConversion[L, R]
  (rawLeft: CTerm | VTerm, rawRight: CTerm | VTerm, rawTy: Option[CTerm | VTerm])
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
      yellow(rawLeft.sourceInfo),
      pprint(rawLeft),
      "≡",
      yellow(rawRight.sourceInfo),
      pprint(rawRight),
      ":",
      yellow(rawTy.map(_.sourceInfo).getOrElse(SiEmpty)),
      rawTy.map(pprint),
    ),
  )(result)

/* References
 [0]  Norell, Ulf. “Towards a practical programming language based on dependent type theory.” (2007).
 */
