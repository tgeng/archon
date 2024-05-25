package com.github.tgeng.archon.core.ir

import com.github.tgeng.archon.common.*
import com.github.tgeng.archon.common.IndentPolicy.*
import com.github.tgeng.archon.common.WrapPolicy.*
import com.github.tgeng.archon.core.common.*
import com.github.tgeng.archon.core.ir.CTerm.*
import com.github.tgeng.archon.core.ir.Declaration.*
import com.github.tgeng.archon.core.ir.Elimination.*
import com.github.tgeng.archon.core.ir.IrError.*
import com.github.tgeng.archon.core.ir.PrettyPrinter.pprint
import com.github.tgeng.archon.core.ir.ResolvedMetaVariable.*
import com.github.tgeng.archon.core.ir.SourceInfo.*
import com.github.tgeng.archon.core.ir.Usage.*
import com.github.tgeng.archon.core.ir.VTerm.*

// def expectConvertible(target: CTerm, )

/** Preconditions: rawLeft and rawRight are already type checked against ty, which is normalized.
  * @param ty
  *   optional if left and right are types
  */
@throws(classOf[IrError])
def checkIsConvertible
  (left: VTerm, right: VTerm, ty: Option[VTerm])
  (using Γ: Context)
  (using Σ: Signature)
  (using TypingContext)
  : Set[Constraint] = debugCheckIsConvertible(left, right, ty):
  if left == right then Set.empty
  else
    (left.normalized, right.normalized, ty) match
      case (left, right, _) if left == right                              => Set.empty
      case (Level(_, operands1), Level(_, operands2), Some(LevelType(_))) =>
        // If meta some component is not reduced yet, we can't check subsumption
        if operands1.exists((v, _) => isMeta(v)) || operands2.exists((v, _) => isMeta(v))
        then Set(Constraint.VConversion(Γ, left, right, ty))
        else throw NotVConvertible(left, right, ty)
      case (Effects(_, operands1), Effects(_, operands2), Some(EffectsType(_, _))) =>
        // If meta some component is not reduced yet, we can't check subsumption
        if operands1.keys.exists(isMeta) || operands2.keys.exists(isMeta)
        then Set(Constraint.VConversion(Γ, left, right, ty))
        else throw NotVConvertible(left, right, ty)
      case (u: UsageCompound, _, Some(UsageType(_))) =>
        // If meta some component is not reduced yet, we can't check subsumption
        if u.distinctOperands.exists(isMeta)
        then Set(Constraint.VConversion(Γ, left, right, ty))
        else throw NotVConvertible(left, right, ty)
      case (_, u: UsageCompound, Some(UsageType(_))) =>
        // If meta some component is not reduced yet, we can't check subsumption
        if u.distinctOperands.exists(isMeta)
        then Set(Constraint.VConversion(Γ, left, right, ty))
        else throw NotVConvertible(left, right, ty)
      case (Type(upperBound1), Type(upperBound2), _) =>
        checkIsConvertible(upperBound1, upperBound2, None)
      case (ty, Top(level2, eqD2), _) =>
        val level1 = inferLevel(ty)
        val levelConstraints = checkIsConvertible(
          level1,
          level2,
          Some(LevelType(LevelOrder.upperBound)),
        )
        val eqD1 = inferEqDecidability(ty)
        val eqDecidabilityConstraints = checkIsConvertible(eqD1, eqD2, Some(EqDecidabilityType()))
        levelConstraints ++ eqDecidabilityConstraints
      case (U(cty1), U(cty2), _) => checkIsConvertible(cty1, cty2, None)
      case (Thunk(c1), Thunk(c2), Some(U(ty))) =>
        checkIsConvertible(c1, c2, Some(ty))
      case (DataType(qn1, args1), DataType(qn2, args2), _) if qn1 == qn2 =>
        Σ.getDataOption(qn1) match
          case None => throw MissingDeclaration(qn1)
          case Some(data) =>
            args1
              .zip(args2)
              .zip(data.context ++ data.tIndexTys.map((_, Variance.INVARIANT)))
              .zipWithIndex
              .map { case (((arg1, arg2), (binding, _)), i) =>
                checkIsConvertible(arg1, arg2, Some(binding.ty.substLowers(args1.take(i)*)))
              }
              .flatten
              .toSet
      case (Con(name1, args1), Con(name2, args2), Some(DataType(qn, _))) if name1 == name2 =>
        Σ.getConstructorOption(qn, name1) match
          case None => throw MissingConstructor(name1, qn)
          case Some(con) =>
            args1
              .zip(args2)
              .zip(con.paramTys)
              .zipWithIndex
              .map { case (((arg1, arg2), binding), i) =>
                checkIsConvertible(arg1, arg2, Some(binding.ty.substLowers(args1.take(i)*)))
              }
              .flatten
              .toSet
      case (UsageType(Some(u1)), UsageType(Some(u2)), _) =>
        checkIsConvertible(u1, u2, Some(UsageType()))
      case (Collapse(c1), Collapse(c2), ty) => checkIsConvertible(c1, c2, ty.map(F(_, u1)))
      case (Collapse(c1), v2, ty)           => checkIsConvertible(c1, Return(v2), ty.map(F(_, u1)))
      case (v1, Collapse(c2), ty)           => checkIsConvertible(Return(v1), c2, ty.map(F(_, u1)))
      case _                                => throw NotVConvertible(left, right, ty)

/** Preconditions: rawLeft and rawRight are already type checked against ty, which is normalized.
  * @param ty
  *   optional if left and right are types
  */
@throws(classOf[IrError])
def checkIsConvertible
  (aLeft: CTerm, aRight: CTerm, ty: Option[CTerm])
  (using Γ: Context)
  (using Σ: Signature)
  (using ctx: TypingContext)
  : Set[Constraint] = debugCheckIsConvertible(aLeft, aRight, ty):
  val left = aLeft.normalized(ty)
  val right = aRight.normalized(ty)
  if left == right then Set.empty
  else
    ty match
      case Some(FunctionType(binding, bodyTy, _)) =>
        checkIsConvertible(
          Application(left.weakened, Var(0)),
          Application(right.weakened, Var(0)),
          Some(bodyTy),
        )(using Γ :+ binding)
      case Some(RecordType(qn, _, _)) =>
        Σ.getFieldsOption(qn) match
          case None => throw MissingDefinition(qn)
          case Some(fields) =>
            fields
              .map { field =>
                checkIsConvertible(
                  Projection(left, field.name),
                  Projection(right, field.name),
                  Some(field.ty),
                )
              }
              .flatten
              .toSet
      case _ =>
        ctx.withMetaResolved2(left, right):
          // If heads are some unsolved meta variable, we can't know for sure that the elims should be the same because
          // the solved meta variables may simply drop whatever eliminations afterwards and hence normalizes to
          // convertible terms.
          case ((m1, _), (m2, _)) if m1 == m2 =>
            Set(Constraint.CConversion(Γ, left, right, ty))
          // However, elim checks on var is appropriate.
          case (Redex(t1 @ Force(v1: Var), elims1), Redex(Force(v2: Var), elims2)) if v1 == v2 =>
            Γ.resolve(v1).ty match
              case U(headTy) => checkElimIsConvertible(t1, elims1, elims2, headTy, ty)
              case _         => throw IllegalStateException("type error")
          case ((_: RGuarded, _), _) | (_, (_: RGuarded, _)) =>
            Set(Constraint.CConversion(Γ, left, right, ty))
          case ((u: RUnsolved, elims), t: CTerm) => checkRedexIsConvertible(u, elims, t, ty)
          case (t: CTerm, (u: RUnsolved, elims)) => checkRedexIsConvertible(u, elims, t, ty)
          case ((u1: RUnsolved, elims1), (u2: RUnsolved, elims2)) if elims1 == elims2 =>
            // This step is to make meta variable delegation deterministic
            val (uSmall, uBig) =
              if u1.index < u2.index
              then (u1, u2)
              else (u2, u1)
            ctx.adaptForMetaVariable(uSmall, uBig.tm):
              case Some(bigTm) => ctx.assignUnsolved(uSmall, bigTm)
              case None =>
                ctx.adaptForMetaVariable(uBig, uSmall.tm):
                  case Some(smallTm) => ctx.assignUnsolved(uBig, smallTm)
                  case None          => Set(Constraint.CConversion(Γ, left, right, ty))
          case (CapturedContinuationTip(ty1), CapturedContinuationTip(ty2)) =>
            checkIsConvertible(ty1, ty2, None)
          case (Return(v1, usage1), Return(v2, usage2)) =>
            ty match
              case Some(F(ty, _, _)) =>
                checkIsConvertible(usage1, usage2, Some(UsageType())) ++ checkIsConvertible(
                  v1,
                  v2,
                  Some(ty),
                )
              case _ => throw IllegalStateException("should have been checked to be a F type")
          case (CType(upperBound1, eff1), CType(upperBound2, eff2)) =>
            checkIsConvertible(eff1, eff2, Some(EffectsType())) ++ checkIsConvertible(
              upperBound1,
              upperBound2,
              Some(right),
            )
          case (ty: (IType & CTerm), CTop(level2, eff2)) =>
            checkIsConvertible(
              inferLevel(ty),
              level2,
              Some(LevelType(LevelOrder.upperBound)),
            ) ++ checkIsConvertible(ty.effects, eff2, Some(EffectsType()))
          case (F(vTy1, eff1, u1), F(vTy2, eff2, u2)) =>
            checkIsConvertible(eff1, eff2, Some(EffectsType())) ++
              checkIsConvertible(u1, u2, Some(UsageType())) ++
              checkIsConvertible(vTy1, vTy2, None)
          case (Let(t1, ty1, eff1, usage1, ctx1), Let(t2, ty2, eff2, usage2, ctx2)) =>
            val tyConstraint = checkIsConvertible(ty1, ty2, None)
            val effConstraint = ctx.solve(checkIsConvertible(eff1, eff2, Some(EffectsType())))
            val usageConstraint = checkIsConvertible(usage1, usage2, Some(UsageType()))
            val combinedEffects =
              if effConstraint.isEmpty then eff1 else EffectsUnion(eff1, eff2).normalized
            val tConstraint = checkIsConvertible(
              t1,
              t2,
              // Note on type used heres
              // * The concrete type passed here does not affect correctness of type checking.
              // * A combined effect is used to be safe (e.g. we don't want to normalize potentially diverging terms)
              // * Usage is not important during conversion checking, hence we just pass UAny.
              Some(F(ty1, combinedEffects, UsageLiteral(UAny))),
            )
            val ctxConstraint = checkIsConvertible(ctx1, ctx2, ty.map(_.weakened))(
              // Using ty1 or ty2 doesn't really matter here. We don't need to do any lambda substitution because ty1
              // or ty2 are not referenced by anything in ctx1 or ctx2 or ty.
              using Γ :+ Binding(ty1, UsageLiteral(UAny))(gn"v"),
            )
            tyConstraint ++ effConstraint ++ usageConstraint ++ tConstraint ++ ctxConstraint
          case (FunctionType(binding1, bodyTy1, eff1), FunctionType(binding2, bodyTy2, eff2)) =>
            val effConstraint = checkIsConvertible(eff1, eff2, Some(EffectsType()))
            val tyConstraint = ctx.solve(checkIsConvertible(binding2.ty, binding1.ty, None))
            val bodyConstraint =
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
                            Return(Var(0), u1),
                            tyConstraint,
                          ),
                        ),
                      )
                    case _ => None
                  },
                  None,
                )
            effConstraint ++ tyConstraint ++ bodyConstraint
          case (RecordType(qn1, args1, eff1), RecordType(qn2, args2, eff2)) if qn1 == qn2 =>
            Σ.getRecordOption(qn1) match
              case None => throw MissingDeclaration(qn1)
              case Some(record) =>
                var args = IndexedSeq[VTerm]()
                val effConstraint = checkIsConvertible(eff1, eff2, Some(EffectsType()))
                val argConstraint = args1
                  .zip(args2)
                  .zip(record.context)
                  .map { case ((arg1, arg2), (binding, variance)) =>
                    variance match
                      case Variance.INVARIANT =>
                        val r =
                          checkIsConvertible(
                            arg1,
                            arg2,
                            Some(binding.ty.substLowers(args*)),
                          )
                        args = args :+ arg1
                        r
                      case Variance.COVARIANT =>
                        val r =
                          checkIsConvertible(
                            arg1,
                            arg2,
                            Some(binding.ty.substLowers(args*)),
                          )
                        args = args :+ arg1
                        r
                      case Variance.CONTRAVARIANT =>
                        val r =
                          checkIsConvertible(
                            arg2,
                            arg1,
                            Some(binding.ty.substLowers(args*)),
                          )
                        args = args :+ arg2
                        r
                  }
                  .flatten
                  .toSet
                effConstraint ++ argConstraint
          case (
              OperationCall((qn1, tArgs1), name1, args1),
              OperationCall((qn2, tArgs2), name2, args2),
            ) if qn1 == qn2 && name1 == name2 =>
            Σ.getOperationOption(qn1, name1) match
              case None => throw MissingOperation(name1, qn1)
              case Some(operation) =>
                var args = IndexedSeq[VTerm]()
                Σ.getEffectOption(qn1) match
                  case None => throw MissingDeclaration(qn1)
                  case Some(effect) =>
                    val tArgConstraint =
                      tArgs1
                        .zip(tArgs2)
                        .zip(effect.context)
                        .map { case ((tArg1, tArg2), binding) =>
                          val r = checkIsConvertible(tArg1, tArg2, Some(binding.ty))
                          args = args :+ tArg1
                          r
                        }
                        .flatten
                        .toSet
                    val argConstraint =
                      args1
                        .zip(args2)
                        .zip(operation.paramTys)
                        .map { case ((arg1, arg2), binding) =>
                          val r = checkIsConvertible(arg1, arg2, Some(binding.ty))
                          args = args :+ arg1
                          r
                        }
                        .flatten
                        .toSet
                    tArgConstraint ++ argConstraint
          case (Force(v1), Force(v2)) => checkIsConvertible(v1, v2, ty.map(U(_)))
          case (Force(v1), c: CTerm)  => checkIsConvertible(v1, Thunk(c), ty.map(U(_)))
          case (c: CTerm, Force(v2))  => checkIsConvertible(Thunk(c), v2, ty.map(U(_)))
          // For now, we skip the complex logic checking conversion of handler and continuations. It
          // seems not all that useful to keep those. But we can always add them later if it's deemed
          // necessary.
          case _ => throw NotCConvertible(left, right, ty)

@throws(classOf[IrError])
def checkAreConvertible
  (lefts: List[VTerm], rights: List[VTerm], tys: Telescope)
  (using Γ: Context)
  (using Σ: Signature)
  (using ctx: TypingContext)
  : Set[Constraint] =
  // See [0] Figure 3.8
  (lefts, rights, tys) match
    case (Nil, Nil, Nil) => Set.empty
    case (left :: tailLefts, right :: tailRights, ty :: tys) =>
      val headConstraints = ctx.solve(checkIsConvertible(left, right, Some(ty.ty)))
      if headConstraints.isEmpty
      then checkAreConvertible(tailLefts, tailRights, tys.substLowers(left))
      else if FreeVarsVisitor.visitTelescope(tys)(using 0).exists(_.idx == 0)
        // if the head term is referenced in the tail, add the whole thing as a constraint
      then Set(Constraint.Conversions(Γ, lefts, rights, tys))
      // the head term is not referenced in the tail, add the tail constraint in addition to the head
      // constraints
      else headConstraints ++ checkAreConvertible(tailLefts, tailRights, tys.strengthened)
    case _ => throw IllegalArgumentException("length mismatch")

@throws(classOf[IrError])
private def checkRedexIsConvertible
  (r: RUnsolved, extraElims: List[Elimination[VTerm]], target: CTerm, ty: Option[CTerm])
  (using Γ: Context)
  (using Σ: Signature)
  (using ctx: TypingContext)
  : Set[Constraint] =
  ctx.alignElims(target, extraElims) match
    case None => Set(Constraint.CConversion(Γ, redex(r.tm, extraElims), target, ty))
    case Some(target) =>
      ctx.adaptForMetaVariable(r, target):
        case Some(value) => ctx.assignUnsolved(r, value)
        case None        => Set(Constraint.CConversion(Γ, r.tm, target, ty))

@throws(classOf[IrError])
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
  : Set[Constraint] =
  val resultConstraint = Set(
    Constraint.CConversion(Γ, redex(head, lefts), redex(head, rights), ty),
  )
  (lefts, rights, headTy) match
    case (Nil, Nil, _) => Set.empty
    case (ETerm(left) :: lefts, ETerm(right) :: rights, headTy) =>
      headTy match
        case FunctionType(binding, bodyTy, _) =>
          val headConstraints = ctx.solve(checkIsConvertible(left, right, Some(binding.ty)))
          if headConstraints.isEmpty then
            checkElimIsConvertible(Application(head, left), lefts, rights, bodyTy, ty)
          else if FreeVarsVisitor.visitCTerm(bodyTy)(using 0).exists(_.idx == 0) then
            resultConstraint
          else
            headConstraints ++ checkElimIsConvertible(
              Application(head, left),
              lefts,
              rights,
              bodyTy.strengthened,
              ty,
            )
        case _ => throw IllegalStateException("should have been checked to be a function type")
    case (EProj(leftName) :: lefts, EProj(rightName) :: rights, rt) =>
      rt match
        case RecordType(qn, args, _) =>
          if leftName == rightName then
            checkElimIsConvertible(
              Projection(head, leftName),
              lefts,
              rights,
              Σ.getField(qn, leftName).ty.substLowers(args :+ Thunk(head)*),
              ty,
            )
          else resultConstraint
        case _ => throw IllegalStateException("should have been checked to be a record type")
    case (ETerm(_) :: _, EProj(_) :: _, _) | (EProj(_) :: _, ETerm(_) :: _, _) =>
      throw IllegalArgumentException("type mismatch")
    // Different length may not be a problem since it's possible that one side may be calling more projection of some record
    case (_ :: _, Nil, _) | (Nil, _ :: _, _) => resultConstraint

private inline def debugCheckIsConvertible[R]
  (rawLeft: CTerm | VTerm, rawRight: CTerm | VTerm, rawTy: Option[CTerm | VTerm])
  (result: => R)
  (using Context)
  (using Signature)
  (using ctx: TypingContext)
  : R =
  ctx.trace(
    s"checkIsConvertible",
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
