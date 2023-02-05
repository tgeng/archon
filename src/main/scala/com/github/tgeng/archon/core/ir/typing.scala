package com.github.tgeng.archon.core.ir

import scala.collection.immutable.{Map, Set}
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

import scala.annotation.tailrec
import PrettyPrinter.pprint
import WrapPolicy.*
import IndentPolicy.*
import DelimitPolicy.*

private val ANSI_RESET = "\u001b[0m"
private val ANSI_GRAY = "\u001b[90m"
private val ANSI_RED = "\u001b[31m"
private val ANSI_GREEN = "\u001b[32m"
private val ANSI_YELLOW = "\u001b[33m"
private val ANSI_BLUE = "\u001b[34m"
private val ANSI_CYAN = "\u001b[36m"
private val ANSI_WHITE = "\u001b[37m"

// TODO[P2]: make type checking logic rewrite terms so that all total computations are evaluated.
//  This should (usually) simplify terms and result in faster code. Also this would benefit further
//  lowering of the code.

def yellow(s: Any): String = ANSI_YELLOW + s.toString + ANSI_RESET
def green(s: Any): String = ANSI_GREEN + s.toString + ANSI_RESET

trait TypingContext(var traceLevel: Int, var enableDebugging: Boolean):

  inline def trace[L, R]
    (
      title: => String,
      description: => Block | String = "",
      successMsg: R => Block | String = (_: R) => "",
      failureMsg: L => Block | String = (l: L) => l.toString,
    )
    (action: => Either[L, R])
    (using Γ: Context)
    (using Signature)
    : Either[L, R] =
    val indent = "│ " * traceLevel
    lazy val result: Either[L, R] = action
    if enableDebugging then
      println(indent)
      println(
        indent + "   " + ANSI_BLUE + pprint(Γ.toList)(using IndexedSeq[Binding[VTerm]]()).toString
          .replaceAll("\n", "\n" + indent + "   ") + ANSI_RESET,
      )
      val stacktrace = Thread.currentThread().!!.getStackTrace.!!
      println(
        indent + "┌─ " + title + " " + ANSI_WHITE + "@" + stacktrace(
          2,
        ).toString + ANSI_RESET,
      )
      if description != "" then
        println(
          (indent + "│  " + description).replaceAll("\n", "\n" + indent + "│  "),
        )
      traceLevel += 1
      val endMessage = result match
        case Right(r) =>
          "✅ " + (ANSI_GREEN + successMsg(r)).replaceAll(
            "\n",
            "\n" + indent + "     ",
          )
        case Left(l) =>
          "❌ " + (ANSI_RED + failureMsg(l))
            .replaceAll("\n", "\n" + indent + "     ")
      traceLevel -= 1
      println(indent + "└─ " + endMessage + ANSI_RESET)
    result

  inline def debug[T](inline t: T): T =
    if enableDebugging then
      val indent = "│ " * traceLevel
      println(indent + " " + ANSI_CYAN + stringify(t) + " = " + t + ANSI_RESET)
    t

  def breakpoint: Unit = {
    if enableDebugging then
      val i = 1
  }

type Usages = Seq[VTerm]

object Usages:
  def zero(using Γ: Context): Usages = Seq.fill(Γ.size)(UsageLiteral(Usage.U0))

  def single(v: VTerm.Var, u: VTerm = VTerm.UsageLiteral(Usage.U1))(using Γ: Context): Usages =
    (Seq.fill(Γ.size - v.idx - 1)(UsageLiteral(Usage.U0)) :+ u)
      ++ Seq.fill(v.idx)(UsageLiteral(Usage.U0))

extension(us1: Usages)
  infix def +(us2: Usages): Usages =
    if us1.size != us2.size then throw IllegalArgumentException("mismatched size")
    else us1.zip(us2).map { (u1, u2) => UsageSum(u1, u2) }

  infix def *(scalar: VTerm): Usages = us1.map(u => UsageProd(u, scalar))
  infix def *(scalar: Usage)(using SourceInfo): Usages =
    us1.map(u => UsageProd(u, UsageLiteral(scalar)))

def checkData(data: Data)(using Σ: Signature)(using ctx: TypingContext): Either[IrError, Unit] =
  ctx.trace(s"checking data signature ${data.qn}") {
    given Context = IndexedSeq()

    val tParams = data.tParamTys.map(_._1) ++ data.tIndexTys
    for
      _ <- checkParameterTypeDeclarations(tParams.toList)
      _ <- checkTParamsAreUnrestricted(tParams.toList)
      _ <- checkULevel(data.ul)(using tParams.toIndexedSeq)
      _ <- checkType(data.inherentEqDecidability, EqDecidabilityType())(using tParams.toIndexedSeq)
    yield ()
  }

def checkDataConstructor
  (qn: QualifiedName, con: Constructor)
  (using Σ: Signature)
  (using ctx: TypingContext)
  : Either[IrError, Unit] =
  ctx.trace(s"checking data constructor $qn.${con.name}") {
    Σ.getDataOption(qn) match
      case None => Left(MissingDeclaration(qn))
      case Some(data) =>
        given Γ: Context = data.tParamTys.map(_._1)
        for
          // _ <- checkInherentUsage(Σ.getData(qn), con)
          _ <- checkInherentEqDecidable(Σ.getData(qn), con)
          _ <- checkParameterTypeDeclarations(con.paramTys, Some(data.ul))
          _ <- {
            given Γ2: Context = Γ ++ con.paramTys

            checkTypes(con.tArgs, data.tIndexTys.map(_.weaken(con.paramTys.size, 0)))
          }
          _ <- {
            // binding of positiveVars must be either covariant or invariant
            // binding of negativeVars must be either contravariant or invariant
            val (positiveVars, negativeVars) = getFreeVars(con.paramTys)(using 0)
            val tParamTysSize = data.tParamTys.size
            val bindingWithIncorrectUsage = data.tParamTys.zipWithIndex.filter {
              case ((_, variance), reverseIndex) =>
                val index = tParamTysSize - reverseIndex - 1
                variance match
                  case Variance.INVARIANT     => false
                  case Variance.COVARIANT     => negativeVars(index)
                  case Variance.CONTRAVARIANT => positiveVars(index)
            }
            if bindingWithIncorrectUsage.isEmpty then Right(())
            else
              Left(
                IllegalVarianceInData(
                  data.qn,
                  bindingWithIncorrectUsage.map(_._2),
                ),
              )
          }
        yield ()
  }

def checkRecord
  (record: Record)
  (using Σ: Signature)
  (using ctx: TypingContext)
  : Either[IrError, Unit] =
  ctx.trace(s"checking record signature ${record.qn}") {
    given Context = IndexedSeq()

    val tParams = record.tParamTys.map(_._1)
    for
      _ <- checkParameterTypeDeclarations(tParams.toList)
      _ <- checkTParamsAreUnrestricted(tParams.toList)
      _ <- checkULevel(record.ul)(using tParams.toIndexedSeq)
    yield ()
  }

def checkRecordField
  (qn: QualifiedName, field: Field)
  (using Σ: Signature)
  (using ctx: TypingContext)
  : Either[IrError, Unit] =
  ctx.trace(s"checking record field $qn.${field.name}") {
    Σ.getRecordOption(qn) match
      case None => Left(MissingDeclaration(qn))
      case Some(record) =>
        given Context =
          record.tParamTys.map(_._1).toIndexedSeq :+ getRecordSelfBinding(
            record,
          )

        for _ <- checkIsCType(field.ty, Some(record.ul.weakened))
        yield
          // binding of positiveVars must be either covariant or invariant
          // binding of negativeVars must be either contravariant or invariant
          val (positiveVars, negativeVars) = getFreeVars(field.ty)(using 0)
          val tParamTysSize = record.tParamTys.size
          val bindingWithIncorrectUsage = record.tParamTys.zipWithIndex.filter {
            case ((_, variance), reverseIndex) =>
              val index =
                tParamTysSize - reverseIndex // Offset by 1 to accommodate self reference
              variance match
                case Variance.INVARIANT     => false
                case Variance.COVARIANT     => negativeVars(index)
                case Variance.CONTRAVARIANT => positiveVars(index)
          }
          if bindingWithIncorrectUsage.isEmpty then ()
          else
            Left(
              IllegalVarianceInRecord(
                record.qn,
                bindingWithIncorrectUsage.map(_._2),
              ),
            )
  }

def getRecordSelfBinding(record: Record): Binding[VTerm] = Binding(
  U(
    RecordType(
      record.qn,
      (record.tParamTys.size - 1).to(0, -1).map(Var(_)).toList,
      Total,
    ),
  ),
  U1,
)(record.selfName)

def checkDef
  (definition: Definition)
  (using Σ: Signature)
  (using ctx: TypingContext)
  : Either[IrError, Unit] =
  ctx.trace(s"checking def signature ${definition.qn}") {
    given Context = IndexedSeq()

    checkIsCType(definition.ty)
  }

def checkClause
  (qn: QualifiedName, clause: Clause)
  (using Σ: Signature)
  (using ctx: TypingContext)
  : Either[IrError, Unit] = ctx.trace(s"checking def clause $qn") {
  val lhs = clause.lhs.foldLeft(Some(Def(qn)): Option[CTerm]) {
    case (Some(f), p) =>
      p.toElimination match
        case Some(ETerm(t))    => Some(Application(f, t))
        case Some(EProj(name)) => Some(Projection(f, name))
        case None              => None
    case (None, _) => None
  }
  lhs match
    case None => Right(()) // skip checking absurd clauses
    case Some(lhs) =>
      given Context = clause.bindings

      for
        lhsUsages <- checkType(lhs, clause.ty)
        _ <- checkUsagesSubsumption(lhsUsages, true)
        rhsUsages <- checkType(clause.rhs, clause.ty)
        _ <- checkUsagesSubsumption(rhsUsages)
      yield ()
}

def checkEffect
  (effect: Effect)
  (using Σ: Signature)
  (using ctx: TypingContext)
  : Either[IrError, Unit] =
  ctx.trace(s"checking effect signature ${effect.qn}") {
    given Context = IndexedSeq()

    for
      _ <- checkParameterTypeDeclarations(effect.tParamTys.toList)
      _ <- checkTParamsAreUnrestricted(effect.tParamTys.toList)
      _ <- checkAreEqDecidableTypes(effect.tParamTys.toList)
    yield ()
  }

def checkOperator
  (qn: QualifiedName, operator: Operator)
  (using Σ: Signature)
  (using ctx: TypingContext)
  : Either[IrError, Unit] =
  ctx.trace(s"checking effect operator $qn.${operator.name}") {
    Σ.getEffectOption(qn) match
      case None => Left(MissingDeclaration(qn))
      case Some(effect) =>
        val Γ = effect.tParamTys.toIndexedSeq

        checkParameterTypeDeclarations(operator.paramTys)(using Γ) >>
          checkIsType(operator.resultTy)(using Γ ++ operator.paramTys)
  }

private def checkTParamsAreUnrestricted
  (tParamTys: Telescope)
  (using Γ: Context)
  (using Σ: Signature)
  (using ctx: TypingContext)
  : Either[IrError, Unit] = tParamTys match
  case Nil => Right(())
  case binding :: rest =>
    for
      _ <- checkUsageSubsumption(binding.usage, UsageLiteral(UUnres))
      _ <- checkTParamsAreUnrestricted(rest)(using Γ :+ binding)
    yield ()

private def checkParameterTypeDeclarations
  (tParamTys: Telescope, levelBound: Option[ULevel] = None)
  (using Γ: Context)
  (using Σ: Signature)
  (using ctx: TypingContext)
  : Either[IrError, Unit] = tParamTys match
  case Nil => Right(())
  case binding :: rest =>
    checkIsType(binding.ty, levelBound) >>
      checkIsEqDecidableTypes(binding.ty) >>
      checkSubsumption(
        binding.usage,
        UsageLiteral(UUnres),
        Some(UsageType(None)),
      ) >>
      checkParameterTypeDeclarations(rest)(using Γ :+ binding)

private def checkULevel
  (ul: ULevel)
  (using Γ: Context)
  (using Σ: Signature)
  (using ctx: TypingContext)
  : Either[IrError, Usages] = ul match
  case ULevel.USimpleLevel(l) => checkType(l, LevelType())
  case ULevel.UωLevel(_)      => Right(Usages.zero)

// Precondition: tm is already type-checked
private def inferLevel
  (tm: VTerm)
  (using Γ: Context)
  (using Σ: Signature)
  (using ctx: TypingContext)
  : Either[IrError, ULevel] =
  tm match
    case Type(upperBound) => inferLevel(upperBound).map(ULevelSuc(_))
    case Top(ul, eqD)     => Right(ul)
    case r: Var =>
      Γ.resolve(r).ty match
        case Type(upperBound) => inferLevel(upperBound)
        case _                => Left(NotTypeError(tm))
    case Collapse(cTm)                 => inferLevel(cTm)
    case U(cty)                        => inferLevel(cty)
    case DataType(qn, args)            => Right(Σ.getData(qn).ul.substLowers(args: _*))
    case EqualityType(ty, left, right) => inferLevel(ty)
    case _: UsageType | _: EqDecidabilityType | _: EqDecidabilityLiteral | _: EffectsType |
      _: HeapType =>
      Right(ULevel.USimpleLevel(LevelLiteral(0)))
    case _: LevelType       => Right(ULevel.UωLevel(0))
    case CellType(_, ty, _) => inferLevel(ty)
    case _ => throw IllegalArgumentException(s"should have been checked to be a type: $tm")

def inferType
  (tm: VTerm)
  (using Γ: Context)
  (using Σ: Signature)
  (using ctx: TypingContext)
  : Either[IrError, (VTerm, Usages)] =
  debugInfer(
    tm,
    tm match
      case Type(upperBound) =>
        for case (upperBoundTy, upperBoundUsages) <- inferType(upperBound)
        yield (Type(tm), upperBoundUsages * UUnres)
      case Top(ul, eqD) =>
        for
          ulUsage <- checkULevel(ul)
          eqDUsage <- checkType(eqD, EqDecidabilityType())
        yield (Type(tm), (ulUsage + eqDUsage) * UUnres)
      case r: Var => Right((Γ.resolve(r).ty), Usages.single(r))
      case Collapse(cTm) =>
        for
          case (cTy, usage) <- inferType(cTm)
          case (vTy, u) <- cTy match
            case F(vTy, eff, u) if eff == Total => Right((vTy, u))
            case F(_, _, _)                     => Left(CollapsingEffectfulTerm(cTm))
            case _                              => Left(NotCollapsable(cTm))
        yield (vTy, usage)
      case U(cty) =>
        for
          case (ctyTy, usage) <- inferType(cty)
          r <- ctyTy match
            case CType(_, eff) if eff == Total => Right(Type(tm))
            // Automatically promote SomeVType to F(SomeVType)
            case F(Type(_), eff, _) if eff == Total => Right(Type(tm))
            case CType(_, _) | F(Type(_), _, _) =>
              Left(EffectfulCTermAsType(cty))
            case _ => Left(NotTypeError(tm))
        yield (r, usage * UUnres)
      case Thunk(c) =>
        for case (cty, usage) <- inferType(c)
        yield (U(cty), usage)
      case DataType(qn, args) =>
        Σ.getDataOption(qn) match
          case None => Left(MissingDeclaration(qn))
          case Some(data) =>
            for usage <- checkTypes(args, (data.tParamTys.map(_._1) ++ data.tIndexTys).toList)
            yield (Type(tm), usage * UUnres)
      case _: Con => throw IllegalArgumentException("cannot infer type")
      case EqualityType(ty, left, right) =>
        for
          case (tyTy, tyUsage) <- inferType(ty)
          r <- tyTy match
            case Type(_) =>
              for
                leftUsage <- checkType(left, ty)
                rightUsage <- checkType(right, ty)
              yield (Type(tm), (tyUsage + leftUsage + rightUsage) * UUnres)
            case _ => Left(NotTypeError(ty))
        yield r
      case Refl()          => throw IllegalArgumentException("cannot infer type")
      case u: UsageLiteral => Right(UsageType(Some(u)), Usages.zero)
      case UsageCompound(_, operands) =>
        for
          usagesSeq <- transpose(
            operands.multiToSeq.map(o => checkType(o, UsageType(None))),
          )
          usages = usagesSeq.reduce(_ + _)
          bound <- tm.normalized match
            case Right(u) => Right(Some(u))
            case _        => Right(None)
        yield (UsageType(bound), usages)
      case u: UsageType             => Right(Type(u), Usages.zero)
      case eqD: EqDecidabilityType  => Right(Type(eqD), Usages.zero)
      case _: EqDecidabilityLiteral => Right(EqDecidabilityType(), Usages.zero)
      case e: EffectsType           => Right(Type(e), Usages.zero)
      case eff @ Effects(literal, operands) =>
        for
          literalUsages <- transpose(
            literal.map { (qn, args) =>
              Σ.getEffectOption(qn) match
                case None         => Left(MissingDeclaration(qn))
                case Some(effect) => checkTypes(args, effect.tParamTys.toList)
            },
          ).map(_.reduce(_ + _))
          operandsUsages <- transpose(
            operands.map { ref => checkType(ref, EffectsType()) }.toList,
          ).map(_.reduce(_ + _))
          usage <- getEffectsContinuationUsage(eff)
        yield (
          EffectsType(usage),
          literalUsages + operandsUsages,
        )
      case LevelType() => Right((Type(LevelType())), Usages.zero)
      case Level(_, maxOperands) =>
        for usages <- transpose(maxOperands.map { (ref, _) =>
            checkType(ref, LevelType())
          }.toList).map(_.reduce(_ + _))
        yield (LevelType(), usages)
      case HeapType() => Right((Type(HeapType())), Usages.zero)
      case _: Heap    => Right(HeapType(), Usages.zero)
      case cellType @ CellType(heap, ty, _) =>
        for
          heapUsages <- checkType(heap, HeapType())
          case (tyTy, tyUsages) <- inferType(ty)
          r <- tyTy match
            case Type(_) => Right(Type(cellType))
            case _       => Left(NotTypeError(ty))
        yield (r, (heapUsages + tyUsages) * UUnres)
      case Cell(_, _) => throw IllegalArgumentException("cannot infer type"),
  )

def getEffectsContinuationUsage
  (effects: Effects)
  (using Γ: Context)
  (using Σ: Signature)
  (using ctx: TypingContext)
  : Either[IrError, Option[Usage]] =
  effects.normalized.map {
    case effects: Effects =>
      (effects.unionOperands.map { v => getEffVarContinuationUsage(v.asInstanceOf[Var]) } ++
        effects.literal.map { (qn, _) => Σ.getEffect(qn).continuationUsage })
        .foldLeft[Option[Usage]](None) {
          case (None, None) => None
          // None continuation usage is approximated as U1.
          case (Some(u), None)      => Some(Usage.U1 | u)
          case (None, Some(u))      => Some(Usage.U1 | u)
          case (Some(u1), Some(u2)) => Some(u1 | u2)
        }
    case _ => throw IllegalStateException("Effects should still be Effects after normalization")
  }

def checkType
  (tm: VTerm, ty: VTerm)
  (using Γ: Context)
  (using Σ: Signature)
  (using ctx: TypingContext)
  : Either[IrError, Usages] = debugCheck(
  tm,
  ty,
  tm match
    case Con(name, args) =>
      ty match
        case DataType(qn, tArgs) =>
          Σ.getConstructorOption(qn, name) match
            case None => Left(MissingConstructor(name, qn))
            case Some(con) =>
              checkTypes(args, con.paramTys.substLowers(tArgs: _*))
        case _ => Left(ExpectDataType(ty))
    case Refl() =>
      ty match
        case EqualityType(ty, left, right) =>
          for _ <- checkSubsumption(left, right, Some(ty))(using CONVERSION)
          yield Usages.zero
        case _ => Left(ExpectEqualityType(ty))
    case Cell(heapKey, _) =>
      ty match
        case CellType(heap, _, _) if Heap(heapKey) == heap => Right(Usages.zero)
        case _: CellType                                   => Left(ExpectCellTypeWithHeap(heapKey))
        case _                                             => Left(ExpectCellType(ty))
    case _ =>
      for
        case (inferred, usages) <- inferType(tm)
        _ <- checkSubsumption(inferred, ty, None)
      yield usages,
)

// Precondition: tm is already type-checked
private def inferLevel
  (tm: CTerm)
  (using Γ: Context)
  (using Σ: Signature)
  (using ctx: TypingContext)
  : Either[IrError, ULevel] =
  for
    tm <- Reducible.reduce(tm)
    ul <- tm match
      case CType(upperBound, effects) => inferLevel(upperBound).map(ULevelSuc(_))
      case CTop(ul, effects)          => Right(ul)
      case F(vTy, effects, usage)     => inferLevel(vTy)
      case FunctionType(binding, bodyTy, effects) =>
        for
          argLevel <- inferLevel(binding.ty)
          bodyLevel <- inferLevel(bodyTy)(using Γ :+ binding)
        // strengthen is always safe because the only case that bodyLevel would reference 0 is when
        // arg is of type Level. But in that case the overall level would be ω.
        yield ULevelMax(argLevel.weakened, bodyLevel).strengthened
      case RecordType(qn, args, effects) => Right(Σ.getRecord(qn).ul.substLowers(args: _*))
      case _ =>
        throw IllegalArgumentException(s"should have been checked to be a computation type: $tm ")
  yield ul

def inferType
  (tm: CTerm)
  (using Γ: Context)
  (using Σ: Signature)
  (using ctx: TypingContext)
  : Either[IrError, (CTerm, Usages)] =
  debugInfer(
    tm,
    tm match
      case Hole =>
        throw IllegalArgumentException(
          "hole should only be present during reduction",
        )
      case CType(upperBound, effects) =>
        for
          effUsages <- checkType(effects, EffectsType())
          case (upperBoundTy, upperBoundUsages) <- inferType(upperBound)
        yield (
          CType(tm, Total),
          (effUsages + upperBoundUsages) * UUnres,
        )
      case CTop(ul, effects) =>
        for
          uUsages <- checkType(effects, EffectsType())
          ulUsages <- checkULevel(ul)
        yield (CType(tm, Total), (uUsages + ulUsages) * UUnres)
      case Def(qn) =>
        Σ.getDefinitionOption(qn) match
          case None    => Left(MissingDeclaration(qn))
          case Some(d) => Right((d.ty, Usages.zero))
      case Force(v) =>
        for
          case (vTy, vUsages) <- inferType(v)
          cTy <- vTy match
            case U(cty) => Right(cty)
            case _      => Left(ExpectUType(vTy))
        yield (cTy, vUsages)
      case F(vTy, effects, usage) =>
        for
          effUsages <- checkType(effects, EffectsType())
          uUsages <- checkType(usage, UsageType(None))
          // Prevent returning value of U0 usage, which does not make sense.
          _ <- checkUsageSubsumption(usage, UsageLiteral(Usage.U1))
          case (vTyTy, vTyUsages) <- inferType(vTy)
          cTyTy <- vTyTy match
            case Type(_) => Right(CType(tm, Total))
            case _       => Left(NotTypeError(vTy))
        yield (cTyTy, (effUsages + uUsages + vTyUsages) * UUnres)
      case Return(v, usage) =>
        for
          _ <- checkUsageSubsumption(usage, UsageLiteral(Usage.U1))
          case (vTy, vUsages) <- inferType(v)
        yield (F(vTy, Total), vUsages * usage)
      case Let(t, body) =>
        for
          case (tTy, tUsages) <- inferType(t)
          r <- tTy match
            case F(ty, effects, tyUsage) =>
              for
                effects <- effects.normalized
                tUsages <- transpose(tUsages.map(_.normalized))
                (bodyTy, usages) <-
                  // If some usages are not zero or unres, inlining `t` would change usage checking
                  // result because
                  //
                  // * either some linear or relevant usages becomes zero because the computation
                  //   gets removed
                  //
                  // * or if the term is wrapped inside a `Collapse` and get multiplied
                  //
                  // Such changes would alter usage checking result, which can be confusing for
                  // users. Note that, it's still possible that with inlining causes usages to be
                  // removed, but the `areTUsagesZeroOrUnrestricted` check ensures the var has
                  // unrestricted usage. Hence, usage checking would still pass. On the other hand,
                  // it's not possible for inlining to create usage out of nowhere.
                  def areTUsagesZeroOrUnrestricted: Boolean =
                    tUsages.forall { usage =>
                      toBoolean(
                        checkUsageSubsumption(usage, UsageLiteral(Usage.UUnres))(using
                          CheckSubsumptionMode.CONVERSION,
                        ),
                      ) ||
                      toBoolean(
                        checkUsageSubsumption(usage, UsageLiteral(Usage.U0))(using
                          CheckSubsumptionMode.CONVERSION,
                        ),
                      )
                    }
                  if effects == Total && areTUsagesZeroOrUnrestricted then
                    // Do the reduction onsite so that type checking in sub terms can leverage the
                    // more specific type. More importantly, this way we do not need to reference
                    // the result of a computation in the inferred type.
                    for
                      t <- reduce(t)
                      r <- t match
                        case Return(v, _) => inferType(body.substLowers(v))
                        case c            => inferType(body.substLowers(Collapse(c)))
                    yield r
                  // Otherwise, just add the binding to the context and continue type checking.
                  else
                    for
                      case (bodyTy, usagesInBody) <- inferType(body)(using
                        Γ :+ Binding(ty, tyUsage)(gn"v"),
                      )
                      // Report an error if the type of `body` needs to reference the effectful
                      // computation. User should use a dependent sum type to wrap such
                      // references manually to avoid the leak.
                      // TODO[P3]: in case weakened failed, provide better error message: ctxTy cannot depend on
                      //  the bound variable
                      _ <- checkVar0Leak(
                        bodyTy,
                        LeakedReferenceToEffectfulComputationResult(t),
                      )
                      _ <- checkUsageSubsumption(usagesInBody.last.strengthened, tyUsage)(using
                        SUBSUMPTION,
                      )
                      usagesInContinuation <- effects match
                        // Join with U1 for normal execution without any call to effect handlers
                        case v: Var => Right(getEffVarContinuationUsage(v))
                        case eff @ Effects(literal, operands) => getEffectsContinuationUsage(eff)
                        case _ =>
                          throw IllegalStateException(s"expect to be of Effects type: $tm")
                    yield (
                      bodyTy.strengthened,
                      usagesInBody
                        .dropRight(1) // drop this binding
                        .map(_.strengthened) *
                        (UsageLiteral(usagesInContinuation.getOrElse(Usage.U1) | Usage.U1)),
                    )
              yield (augmentEffect(effects, bodyTy), usages)
            case _ => Left(ExpectFType(tTy))
        yield r
      case FunctionType(binding, bodyTy, effects) =>
        for
          effUsages <- checkType(effects, EffectsType())
          case (tyTy, tyUsages) <- inferType(binding.ty)
          case (funTyTy, bodyTyUsages) <- tyTy match
            case Type(_) =>
              for
                case (bodyTyTy, bodyTyUsages) <- inferType(bodyTy)(using Γ :+ binding)
                r <- bodyTyTy match
                  case CType(_, eff) if eff == Total =>
                    // Strengthen is safe here because if it references the binding, then the
                    // binding must be at level ω and hence ULevelMax would return big type.
                    // Also, there is no need to check the dropped usage because usages in types
                    // is always multiplied by U0.
                    Right(
                      CType(tm, Total),
                      bodyTyUsages.dropRight(1).map(_.strengthened),
                    )
                  // TODO[P3]: think about whether the following is actually desirable
                  // Automatically promote Return(SomeVType) to F(SomeVType) and proceed type
                  // inference.
                  case F(Type(_), eff, _) if eff == Total =>
                    Right(
                      CType(tm, Total),
                      bodyTyUsages.dropRight(1).map(_.strengthened),
                    )
                  case CType(_, _) | F(Type(_), _, _) =>
                    Left(EffectfulCTermAsType(bodyTy))
                  case _ => Left(NotCTypeError(bodyTy))
              yield r
            case _ => Left(NotTypeError(binding.ty))
        yield (funTyTy, (effUsages + tyUsages + bodyTyUsages) * UUnres)
      case Application(fun, arg) =>
        for
          case (funTy, funUsages) <- inferType(fun)
          r <- funTy match
            case FunctionType(binding, bodyTy, effects) =>
              for
                argUsages <- checkType(arg, binding.ty)
                bodyTy <- reduceCType(bodyTy.substLowers(arg))
              yield (
                augmentEffect(effects, bodyTy),
                funUsages + argUsages * binding.usage,
              )
            case _ => Left(ExpectFunction(fun))
        yield r
      case RecordType(qn, args, effects) =>
        Σ.getRecordOption(qn) match
          case None => Left(MissingDeclaration(qn))
          case Some(record) =>
            for
              effUsages <- checkType(effects, EffectsType())
              argsUsages <- checkTypes(args, record.tParamTys.map(_._1).toList)
            yield (CType(tm, Total), (effUsages + argsUsages) * UUnres)
      case Projection(rec, name) =>
        for
          case (recTy, recUsages) <- inferType(rec)
          ty <- recTy match
            case RecordType(qn, args, effects) =>
              Σ.getFieldOption(qn, name) match
                case None => Left(MissingField(name, qn))
                case Some(f) =>
                  Right(augmentEffect(effects, f.ty.substLowers(args :+ Thunk(rec): _*)))
            case _ => Left(ExpectRecord(rec))
        yield (ty, recUsages)
      case OperatorCall(eff @ (qn, tArgs), name, args) =>
        Σ.getEffectOption(qn) match
          case None => Left(MissingDeclaration(qn))
          case Some(effect) =>
            Σ.getOperatorOption(qn, name) match
              case None => Left(MissingDefinition(qn))
              case Some(op) =>
                for
                  effUsages <- checkTypes(tArgs, effect.tParamTys.toList)
                  argsUsages <- checkTypes(args, op.paramTys.substLowers(tArgs: _*))
                yield (
                  F(
                    op.resultTy.substLowers(tArgs ++ args: _*),
                    EffectsLiteral(Set(eff)),
                  ),
                  effUsages + argsUsages,
                )
      case _: Continuation | _: ContinuationReplicationState |
        _: ContinuationReplicationStateAppender =>
        throw IllegalArgumentException(
          "continuation is only created in reduction and hence should not be type checked.",
        )
      case h @ Handler(
          eff,
          parameter,
          parameterBinding,
          parameterDisposer,
          parameterReplicator,
          outputEffects,
          outputUsage,
          outputType,
          transform,
          handlers,
          input,
        ) =>
        def filterSimpleEffects(normalizedEffects: VTerm): Either[IrError, VTerm] =
          normalizedEffects match
            case v: Var => filterSimpleEffects(Effects(Set(), Set(v)))
            case Effects(literal, vars) =>
              Right(
                Effects(
                  literal.filter { case (effQn, _) =>
                    Σ.getEffect(effQn).continuationUsage match
                      // `None` means the effect is simple
                      case None => true
                      // Any other value means the effect is not simple and hence needs to be
                      // filtered out
                      case _ => false
                  },
                  vars.filter { v =>
                    Γ.resolve(v.asInstanceOf[Var]) match
                      // Only keep variables that are limited to simple effects
                      case Binding(EffectsType(None), _) => true
                      case _                             => false
                  },
                ),
              )
            case _ => Left(EffectTermToComplex(normalizedEffects))
        for
          eff <- eff.normalized
          effs <- eff match
            case Effects(effs, s) if s.isEmpty => Right(effs)
            case _                             => Left(EffectTermToComplex(eff))
          effUsages <- checkType(eff, EffectsType())
          singleParameterUsages <- checkType(parameter, parameterBinding.ty)
          parameterUsages = singleParameterUsages * parameterBinding.usage
          _ <- parameterReplicator match
            case Some(_) => checkType(outputEffects, EffectsType())
            // parameterReplicator is not specified, in this case, the outputEffects must not be
            // re-entrant.
            case None => checkType(outputEffects, EffectsType(Some(Usage.UAff)))
          outputEffects <- outputEffects.normalized
          parameterOpsEffects <- filterSimpleEffects(outputEffects)
          parameterOpsΓ = Γ :+ parameterBinding
          parameterDisposerUsages <- checkType(
            parameterDisposer,
            F(DataType(Builtins.UnitQn), parameterOpsEffects),
          )(using parameterOpsΓ)
          parameterTypeLevel <- inferLevel(parameterBinding.ty)
          parameterTypeLevel <- parameterTypeLevel match
            case ULevel.USimpleLevel(l) => Right(l)
            case _                      => Left(LevelTooBig(parameterTypeLevel))
          parameterDisposerUsages <- verifyUsages(parameterDisposerUsages)(1)(using parameterOpsΓ)
          parameterReplicatorUsages <- parameterReplicator match
            case Some(parameterReplicator) =>
              for
                parameterReplicatorUsages <- checkType(
                  parameterReplicator,
                  F(
                    DataType(
                      Builtins.PairQn,
                      List(
                        parameterTypeLevel,
                        EqDecidabilityLiteral(EqDecidability.EqUnknown),
                        parameterBinding.usage,
                        parameterBinding.ty,
                        parameterBinding.usage,
                        parameterBinding.ty,
                      ),
                    ),
                    parameterOpsEffects,
                  ).weakened,
                )(using parameterOpsΓ)
                parameterReplicatorUsages <- verifyUsages(parameterReplicatorUsages)(1)(using
                  parameterOpsΓ,
                )
              yield parameterReplicatorUsages
            case None => Right(List.fill(Γ.size)(UsageLiteral(Usage.U0)))
          case (inputCTy, inputUsages) <- inferType(input)
          case (inputTy, inputEff, inputUsage) <- inputCTy match
            case F(inputTy, inputEff, inputUsage) => Right((inputTy, inputEff, inputUsage))
            case _                                => Left(ExpectFType(inputCTy))
          inputBinding = Binding(inputTy, inputUsage)(gn"v")
          outputCType = F(outputType, outputEffects, outputUsage)
          transformΓ = Γ :+ parameterBinding :+ inputBinding.weakened
          transformUsages <- checkType(transform, outputCType.weaken(2, 0))(using transformΓ)
          transformUsages <- verifyUsages(transformUsages)(2)
          _ <- checkSubsumption(
            inputEff,
            EffectsUnion(outputEffects, eff),
            Some(EffectsType()),
          )
          // Check handler implementations
          handlerUsages <-
            def checkHandler(eff: Eff): Either[IrError, Usages] =
              val (qn, args) = eff
              for
                effect <- Σ.getEffectOption(qn).toRight(MissingDeclaration(qn))
                operators <- Σ.getOperatorsOption(qn).toRight(MissingDeclaration(qn))
                _ <-
                  if handlers.size == operators.size && handlers.keySet == operators
                      .map(_.name)
                      .toSet
                  then Right(())
                  else Left(UnmatchedHandlerImplementation(qn, handlers.keys))
                handlerUsages <- transpose(
                  operators.map { opDecl =>
                    val handlerBody = handlers(qn / opDecl.name)
                    val (argNames, resumeNameOption) = h.handlersBoundNames(qn / opDecl.name)
                    // All of the following opXXX are weakened for handler parameter
                    val opResultTy = opDecl.resultTy.substLowers(args: _*).weakened
                    val opResultUsage = opDecl.resultUsage.substLowers(args: _*).weakened
                    val opParamTys = parameterBinding +: opDecl.paramTys
                      .substLowers(args: _*)
                      .zip(argNames)
                      .map { case (binding, argName) =>
                        Binding(binding.ty, binding.usage)(argName)
                      }
                      .weakened
                    for
                      opResultTyLevel <- inferLevel(opResultTy)
                      opResultTyLevel <- opResultTyLevel match
                        case ULevel.USimpleLevel(l) => Right(l)
                        case _                      => Left(LevelTooBig(opResultTyLevel))
                      case (opParamTys, opOutputTy) <- opDecl.continuationUsage match
                        case Some(continuationUsage) =>
                          resumeNameOption match
                            case Some(resumeName) =>
                              for
                                outputTypeLevel <- inferLevel(outputType)
                                level <- outputTypeLevel match
                                  case ULevel.USimpleLevel(o) =>
                                    Right(LevelMax(parameterTypeLevel, opResultTyLevel, o))
                                  case l: ULevel.UωLevel => Left(LevelTooBig(l))
                              yield (
                                opParamTys :+
                                  Binding(
                                    U(
                                      RecordType(
                                        Builtins.ContinuationQn,
                                        List(
                                          level,
                                          UsageLiteral(continuationUsage),
                                          parameterBinding.usage,
                                          parameterBinding.ty,
                                          opResultUsage,
                                          opResultTy,
                                          parameterOpsEffects,
                                          outputEffects,
                                          outputUsage,
                                          outputType,
                                        ),
                                      ).weaken(opDecl.paramTys.size + 1, 0),
                                    ),
                                  )(resumeName),
                                outputCType.weaken(opParamTys.size + 1, 0),
                              )
                            case None =>
                              throw IllegalArgumentException("missing name for continuation")
                        case None =>
                          Right(
                            (
                              opParamTys,
                              F(
                                DataType(
                                  Builtins.PairQn,
                                  List(
                                    opResultTyLevel,
                                    EqDecidabilityLiteral(EqDecidability.EqUnknown),
                                    parameterBinding.usage,
                                    parameterBinding.ty,
                                    opResultUsage,
                                    opResultTy,
                                  ),
                                ),
                                outputEffects,
                                opResultUsage,
                              ).weaken(opDecl.paramTys.size, 0),
                            ),
                          )
                      bodyUsages <- checkType(handlerBody, opOutputTy)(using Γ ++ opParamTys)
                      bodyUsages <- verifyUsages(bodyUsages)(opParamTys.size)(using Γ ++ opParamTys)
                    yield bodyUsages
                  },
                )
              yield handlerUsages.reduce(_ + _)
            eff match
              case Effects(effs, s) if s.isEmpty => transpose(effs.map(checkHandler(_)))
              case _                             => Left(EffectTermToComplex(eff))
        yield (
          outputCType,
          // usages in handlers are multiplied by UUnres because handlers may be invoked any number of times.
          (handlerUsages.reduce(_ + _) + transformUsages
            .dropRight(1)
            .map(_.strengthened) + effUsages) * UUnres + inputUsages,
        )
      case AllocOp(heap, vTy) =>
        for
          heapUsages <- checkType(heap, HeapType())
          _ <- checkIsType(vTy)
        yield (
          F(
            CellType(heap, vTy, CellStatus.Uninitialized),
            EffectsLiteral(Set((Builtins.HeapEffQn, heap :: Nil))),
          ),
          heapUsages,
        )
      case SetOp(cell, value) =>
        for
          case (cellTy, cellUsages) <- inferType(cell)
          r <- cellTy match
            case CellType(heap, vTy, _) =>
              for valueUsages <- checkType(value, vTy)
              yield (
                F(
                  CellType(heap, vTy, CellStatus.Initialized),
                  EffectsLiteral(Set((Builtins.HeapEffQn, heap :: Nil))),
                ),
                cellUsages + valueUsages,
              )
            case _ => Left(ExpectCell(cell))
        yield r
      case GetOp(cell) =>
        for
          case (cellTy, cellUsages) <- inferType(cell)
          r <- cellTy match
            case CellType(heap, vTy, status) if status == CellStatus.Initialized =>
              Right(
                F(
                  vTy,
                  EffectsLiteral(Set((Builtins.HeapEffQn, heap :: Nil))),
                ),
              )
            case _: CellType => Left(UninitializedCell(tm))
            case _           => Left(ExpectCell(cell))
        yield (r, cellUsages)
      case h @ HeapHandler(outputEffects, _, _, input) =>
        val heapVarBinding =
          Binding[VTerm](HeapType(), UsageLiteral(UUnres))(h.boundName)

        given Context = Γ :+ heapVarBinding

        for
          case (inputCTy, inputUsages) <- inferType(input)
          r <- inputCTy match
            case F(inputTy, eff, _) =>
              for
                _ <- checkSubsumption(
                  eff,
                  EffectsUnion(
                    EffectsLiteral(Set((Builtins.HeapEffQn, Var(0) :: Nil))),
                    outputEffects.weakened,
                  ),
                  Some(EffectsType()),
                )(using SUBSUMPTION)
                // TODO[P2]: Use more sophisticated check here to catch leak through wrapping heap
                //  variable inside things. If it's leaked, there is no point using this handler at
                //  all. Simply using GlobalHeapKey is the right thing to do. This is because a
                //  creating a leaked heap key itself is performing a side effect with global heap.
                _ <- checkVar0Leak(
                  inputTy,
                  LeakedReferenceToHeapVariable(input),
                )
              yield F(inputTy.strengthened, outputEffects)
            case _ => Left(ExpectFType(inputCTy))
        yield (r, inputUsages),
  )

private def getEffVarContinuationUsage(v: Var)(using Γ: Context)(using Signature): Option[Usage] =
  Γ.resolve(v) match
    case Binding(EffectsType(usage), _) => usage
    case _ =>
      throw IllegalStateException("typing exception")

def checkType
  (tm: CTerm, ty: CTerm)
  (using Γ: Context)
  (using Σ: Signature)
  (using ctx: TypingContext)
  : Either[IrError, Usages] = debugCheck(
  tm,
  ty,
  for
    case (tmTy, usages) <- inferType(tm)
    ty <- reduceCType(ty)
    _ <- checkSubsumption(tmTy, ty, None)
  yield usages,
)

enum CheckSubsumptionMode:
  case SUBSUMPTION, CONVERSION

import CheckSubsumptionMode.*

given CheckSubsumptionMode = SUBSUMPTION

/** @param ty
  *   can be [[None]] if `a` and `b` are types
  */
// Precondition: terms are already type-checked
def checkSubsumption
  (rawSub: VTerm, rawSup: VTerm, rawTy: Option[VTerm])
  (using mode: CheckSubsumptionMode)
  (using Γ: Context)
  (using Σ: Signature)
  (using ctx: TypingContext)
  : Either[IrError, Unit] =
  def impl: Either[IrError, Unit] =
    if rawSub == rawSup then return Right(())
    val ty = rawTy.map(_.normalized) match
      case None           => None
      case Some(Right(v)) => Some(v)
      case Some(Left(e))  => return Left(e)
    (rawSub.normalized, rawSup.normalized) match
      case (Left(e), _) => Left(e)
      case (_, Left(e)) => Left(e)
      case (Right(sub), Right(sup)) =>
        (sub, sup, ty) match
          case (Type(upperBound1), Type(upperBound2), _) =>
            checkSubsumption(upperBound1, upperBound2, None)
          case (ty, Top(ul2, eqD2), _) =>
            for
              ul1 <- inferLevel(ty)
              _ <- checkULevelSubsumption(ul1, ul2)
              eqD1 <- deriveTypeInherentEqDecidability(ty)
              _ <- checkEqDecidabilitySubsumption(eqD1, eqD2)
            yield ()
          case (U(cty1), U(cty2), _) => checkSubsumption(cty1, cty2, None)
          case (Thunk(c1), Thunk(c2), Some(U(ty))) =>
            checkSubsumption(c1, c2, Some(ty))
          case (DataType(qn1, args1), DataType(qn2, args2), _) if qn1 == qn2 =>
            Σ.getDataOption(qn1) match
              case None => Left(MissingDeclaration(qn1))
              case Some(data) =>
                var args = IndexedSeq[VTerm]()
                allRight(
                  args1
                    .zip(args2)
                    .zip(data.tParamTys ++ data.tIndexTys.map((_, Variance.INVARIANT)))
                    .map { case ((arg1, arg2), (binding, variance)) =>
                      variance match
                        case Variance.INVARIANT =>
                          val r = checkSubsumption(
                            arg1,
                            arg2,
                            Some(binding.ty.substLowers(args: _*)),
                          )(
                            using CONVERSION,
                          )
                          args = args :+ arg1
                          r
                        case Variance.COVARIANT =>
                          val r = checkSubsumption(
                            arg1,
                            arg2,
                            Some(binding.ty.substLowers(args: _*)),
                          )
                          args = args :+ arg1
                          r
                        case Variance.CONTRAVARIANT =>
                          val r = checkSubsumption(
                            arg2,
                            arg1,
                            Some(binding.ty.substLowers(args: _*)),
                          )
                          args = args :+ arg2
                          r
                    },
                )
          case (Con(name1, args1), Con(name2, args2), Some(DataType(qn, _))) if name1 == name2 =>
            Σ.getConstructorOption(qn, name1) match
              case None => Left(MissingConstructor(name1, qn))
              case Some(con) =>
                var args = IndexedSeq[VTerm]()
                allRight(
                  args1
                    .zip(args2)
                    .zip(con.paramTys)
                    .map { case ((arg1, arg2), binding) =>
                      val r = checkSubsumption(
                        arg1,
                        arg2,
                        Some(binding.ty.substLowers(args: _*)),
                      )
                      args = args :+ arg1
                      r
                    },
                )
          case (EffectsType(continuationUsage1), EffectsType(continuationUsage2), _) =>
            // Note that subsumption checking is reversed because the effect of the computation
            // marks how the continuation can be invoked. Normally, checking usage is checking
            // how a resource is *consumed*. But here, checking usage is checking how the
            // continuation (as a resource) is provided.
            checkContinuationUsageSubsumption(continuationUsage2, continuationUsage1)
          case (UsageType(Some(u1)), UsageType(Some(u2)), _) if mode == SUBSUMPTION =>
            checkUsageSubsumption(u1, u2)
          case (UsageType(Some(_)), UsageType(None), _) if mode == SUBSUMPTION =>
            Right(())
          case (EqualityType(ty1, a1, b1), EqualityType(ty2, a2, b2), _) =>
            checkSubsumption(ty1, ty2, None) >>
              checkSubsumption(a1, a2, Some(ty1)) >>
              checkSubsumption(b1, b2, Some(ty1))
          case (
              CellType(heap1, ty1, status1),
              CellType(heap2, ty2, status2),
              _,
            ) =>
            for r <- checkSubsumption(heap1, heap2, Some(HeapType())) >>
                checkSubsumption(ty1, ty2, None)(using CONVERSION) >>
                (if status1 == status2 || status1 == CellStatus.Initialized then Right(())
                 else
                   Left(
                     NotVSubsumption(sub, sup, ty, mode),
                   )
                )
            yield r
          case (_, Heap(GlobalHeapKey), Some(HeapType())) if mode == SUBSUMPTION =>
            Right(())
          case (v: Var, ty2, _) if mode == CheckSubsumptionMode.SUBSUMPTION =>
            Γ.resolve(v).ty match
              case Type(upperBound) =>
                checkSubsumption(upperBound, ty2, None)
              case _ => Left(NotVSubsumption(sub, sup, ty, mode))
          case (Collapse(c), v, ty) =>
            checkSubsumption(c, Return(v), ty.map(F(_)))
          case (v, Collapse(c), ty) =>
            checkSubsumption(Return(v), c, ty.map(F(_)))
          case _ => Left(NotVSubsumption(sub, sup, ty, mode))

  debugSubsumption(rawSub, rawSup, rawTy, impl)

/** @param ty
  *   can be [[None]] if `a` and `b` are types
  */
// Precondition: terms are already type-checked
def checkSubsumption
  (sub: CTerm, sup: CTerm, ty: Option[CTerm])
  (using mode: CheckSubsumptionMode)
  (using Γ: Context)
  (using Σ: Signature)
  (using ctx: TypingContext)
  : Either[IrError, Unit] = debugSubsumption(
  sub,
  sup,
  ty, {
    val isTotal = ty.forall(_.asInstanceOf[IType].effects == Total)
    for
      sub <- if isTotal then reduce(sub) else Right(sub)
      sub <- simplifyLet(sub)
      sup <- if isTotal then reduce(sup) else Right(sup)
      sup <- simplifyLet(sup)
      r <- (sub, sup, ty) match
        case (_, _, _) if sub == sup => Right(())
        case (_, _, Some(FunctionType(binding, bodyTy, _))) =>
          checkSubsumption(
            Application(sub.weakened, Var(0)),
            Application(sup.weakened, Var(0)),
            Some(bodyTy),
          )(using CONVERSION)(using Γ :+ binding)
        case (_, _, Some(RecordType(qn, _, _))) =>
          Σ.getFieldsOption(qn) match
            case None => Left(MissingDefinition(qn))
            case Some(fields) =>
              allRight(
                fields.map { field =>
                  checkSubsumption(
                    Projection(sub, field.name),
                    Projection(sup, field.name),
                    Some(field.ty),
                  )(using CONVERSION)
                },
              )
        case (CType(upperBound1, eff1), CType(upperBound2, eff2), _) =>
          checkEffSubsumption(eff1, eff2) >>
            checkSubsumption(upperBound1, upperBound2, Some(sup))
        case (ty: IType, CTop(ul2, eff2), _) =>
          for
            ul1 <- inferLevel(ty)
            _ <- checkULevelSubsumption(ul1, ul2)
            _ <- checkEffSubsumption(ty.effects, eff2)
          yield ()
        case (F(vTy1, eff1, u1), F(vTy2, eff2, u2), _) =>
          for
            _ <- checkEffSubsumption(eff1, eff2)
            _ <- checkUsageSubsumption(u1, u2)
            r <- checkSubsumption(vTy1, vTy2, None)
          yield r
        case (Return(v1, u1), Return(v2, u2), Some(F(ty, _, _))) =>
          checkSubsumption(v1, v2, Some(ty))(using CONVERSION) >>
            checkSubsumption(u1, u2, Some(UsageType(None)))(using CONVERSION)
        case (Let(t1, ctx1), Let(t2, ctx2), ty) =>
          for
            case (t1CTy, _) <- inferType(t1)
            r <- t1CTy match
              case F(t1Ty, _, _) =>
                for
                  case (t2CTy, _) <- inferType(t2)
                  _ <- checkSubsumption(t1CTy, t2CTy, None)(using CONVERSION)
                  _ <- checkSubsumption(t1, t2, Some(t2CTy))(using CONVERSION)
                  r <- checkSubsumption(ctx1, ctx2, ty.map(_.weakened))(using CONVERSION)(using
                    Γ :+ Binding(t1Ty, UsageLiteral(UUnres))(gn"v"),
                  )
                yield r
              case _ => Left(ExpectFType(t1CTy))
          yield r
        case (
            FunctionType(binding1, bodyTy1, eff1),
            FunctionType(binding2, bodyTy2, eff2),
            _,
          ) =>
          checkSubsumption(eff1, eff2, Some(EffectsType())) >>
            checkSubsumption(binding2.ty, binding1.ty, None) >>
            checkSubsumption(bodyTy1, bodyTy2, None)(using mode)(using Γ :+ binding2)
        case (Application(fun1, arg1), Application(fun2, arg2), _) =>
          for
            case (fun1Ty, _) <- inferType(fun1)
            case (fun2Ty, _) <- inferType(fun2)
            _ <- checkSubsumption(fun1Ty, fun2Ty, None)(using CONVERSION)
            _ <- checkSubsumption(fun1, fun2, Some(fun1Ty))(using CONVERSION)
            r <- fun1Ty match
              case FunctionType(binding, _, _) =>
                checkSubsumption(
                  arg1,
                  arg2,
                  Some(binding.ty),
                )(using CONVERSION)
              case _ => Left(NotCSubsumption(sub, sup, ty, mode))
          yield r
        case (RecordType(qn1, args1, eff1), RecordType(qn2, args2, eff2), _) if qn1 == qn2 =>
          Σ.getRecordOption(qn1) match
            case None => Left(MissingDeclaration(qn1))
            case Some(record) =>
              var args = IndexedSeq[VTerm]()
              checkSubsumption(eff1, eff2, Some(EffectsType())) >>
                allRight(
                  args1
                    .zip(args2)
                    .zip(record.tParamTys)
                    .map { case ((arg1, arg2), (binding, variance)) =>
                      variance match
                        case Variance.INVARIANT =>
                          val r = checkSubsumption(
                            arg1,
                            arg2,
                            Some(binding.ty.substLowers(args: _*)),
                          )(using CONVERSION)
                          args = args :+ arg1
                          r
                        case Variance.COVARIANT =>
                          val r = checkSubsumption(
                            arg1,
                            arg2,
                            Some(binding.ty.substLowers(args: _*)),
                          )
                          args = args :+ arg1
                          r
                        case Variance.CONTRAVARIANT =>
                          val r = checkSubsumption(
                            arg2,
                            arg1,
                            Some(binding.ty.substLowers(args: _*)),
                          )
                          args = args :+ arg2
                          r
                    },
                )
        case (Projection(rec1, name1), Projection(rec2, name2), _) if name1 == name2 =>
          for
            case (rec1Ty, _) <- inferType(rec1)
            case (rec2Ty, _) <- inferType(rec2)
            r <- checkSubsumption(rec1Ty, rec2Ty, None)(using CONVERSION)
          yield r
        case (
            OperatorCall((qn1, tArgs1), name1, args1),
            OperatorCall((qn2, tArgs2), name2, args2),
            _,
          ) if qn1 == qn2 && name1 == name2 =>
          Σ.getOperatorOption(qn1, name1) match
            case None => Left(MissingOperator(name1, qn1))
            case Some(operator) =>
              var args = IndexedSeq[VTerm]()
              Σ.getEffectOption(qn1) match
                case None => Left(MissingDeclaration(qn1))
                case Some(effect) =>
                  allRight(
                    tArgs1.zip(tArgs2).zip(effect.tParamTys).map { case ((tArg1, tArg2), binding) =>
                      val r =
                        checkSubsumption(tArg1, tArg2, Some(binding.ty))(using CONVERSION)
                      args = args :+ tArg1
                      r
                    },
                  ) >> allRight(
                    args1.zip(args2).zip(operator.paramTys).map { case ((arg1, arg2), binding) =>
                      val r = checkSubsumption(arg1, arg2, Some(binding.ty))(
                        using CONVERSION,
                      )
                      args = args :+ arg1
                      r
                    },
                  )
        // For now, we skip the complex logic checking subsumption of handler and continuations. It
        // seems not all that useful to keep those. But we can always add them later if it's deemed
        // necessary.
        case _ => Left(NotCSubsumption(sub, sup, ty, mode))
    yield r
  },
)

private def simplifyLet
  (t: CTerm)
  (using Γ: Context)
  (using Σ: Signature)
  (using ctx: TypingContext)
  : Either[IrError, CTerm] = ctx.trace[IrError, CTerm](
  s"simplify",
  s"${yellow(t.sourceInfo)} ${pprint(t)}",
  successMsg = tm => s"${yellow(tm.sourceInfo)} ${green(pprint(tm))}",
) {
  t match
    case Let(t, ctx) =>
      for
        case (tTy, _) <- inferType(t)
        r <- tTy match
          case F(_, eff, _) if eff == Total =>
            simplifyLet(ctx.substLowers(Collapse(t))).flatMap(reduce)
          case _ => Right(t)
      yield r
    case _ => Right(t)
}

// private def checkInherentUsage
//   (data: Data, constructor: Constructor)
//   (using Σ: Signature)
//   (using ctx: TypingContext)
//   : Either[IrError, Unit] =
//   data.inherentUsage match
//     case UsageLiteral(U1) => Right(())
//     case _ =>
//       given Γ: Context = data.tParamTys.map(_._1) ++ data.tIndexTys

//       def checkTelescope
//         (telescope: Telescope, dataInherentUsage: VTerm)
//         (using Γ: Context)
//         : Either[IrError, Unit] = telescope match
//         case Nil => Right(())
//         case (b @ Binding(ty, declaredUsage)) :: telescope =>
//           for
//             inherentUsage <- deriveTypeInherentUsage(ty)
//             providedUsage = UsageProd(inherentUsage, declaredUsage)
//             consumedUsage = UsageProd(
//               inherentUsage,
//               declaredUsage,
//               dataInherentUsage,
//             )
//             _ <- checkSubsumption(
//               providedUsage,
//               consumedUsage,
//               Some(UsageType(None)(using SiEmpty)),
//             )(using SUBSUMPTION)
//             _ <- checkTelescope(telescope, dataInherentUsage.weakened)(using Γ :+ b)
//           yield ()
//       checkTelescope(constructor.paramTys, data.inherentUsage)
// end checkInherentUsage

// private def deriveTypeInherentUsage
//   (ty: VTerm)
//   (using Γ: Context)
//   (using Σ: Signature)
//   (using ctx: TypingContext)
//   : Either[IrError, VTerm] = ty match
//   case _: LevelType => Right(UsageLiteral(U0))
//   case _: Type | _: UsageType | _: EffectsType | _: HeapType | _: CellType =>
//     Right(UsageLiteral(UUnres))
//   case _: EqualityType => Right(UsageLiteral(U0))
//   case _: U            => Right(UsageLiteral(U1))
//   case Top(_, u, _)    => Right(u)
//   case _: Var | _: Collapse =>
//     for
//       case (tyTy, _) <- inferType(ty)
//       r <- tyTy match
//         case Type(upperBound) => deriveTypeInherentUsage(upperBound)
//         case _                => Left(ExpectVType(ty))
//     yield r
//   case d: DataType =>
//     Σ.getDataOption(d.qn) match
//       case Some(data) => Right(data.inherentUsage.substLowers(d.args: _*))
//       case _          => Left(MissingDeclaration(d.qn))
//   case _ => Left(ExpectVType(ty))
// end deriveTypeInherentUsage

private def checkInherentEqDecidable
  (data: Data, constructor: Constructor)
  (using Σ: Signature)
  (using ctx: TypingContext)
  : Either[IrError, Unit] =
  given Γ: Context = data.tParamTys.map(_._1) ++ data.tIndexTys

  // 1. check that eqD of component type ⪯ eqD of data
  def checkComponentTypes(tys: Telescope, dataEqD: VTerm)(using Γ: Context): Either[IrError, Unit] =
    tys match
      case Nil => Right(())
      case binding :: rest =>
        for
          eqD <- deriveTypeInherentEqDecidability(binding.ty)
          _ <- checkSubsumption(eqD, dataEqD, Some(EqDecidabilityType()))(using SUBSUMPTION)
          _ <- checkComponentTypes(rest, dataEqD.weakened)(using Γ :+ binding)
        yield ()

  // 2. inductively define a set of constructor params and this set must contain all constructor
  //    params in order for the data to be non-EqUnknown
  //  base: constructor type and component types whose binding has non-0 usage (component usage is
  //        calculated by product of declared usage in binding and data.inherentUsage).
  //  inductive: bindings that are referenced (not through Collapse to root of the term) inductively
  def checkComponentUsage(constructor: Constructor) =
    val numParams = constructor.paramTys.size
    // all paramTys and usages are weakened to be in the same context with constructor.tArgs
    val allParams: Map[ /* dbIndex */ Nat, ( /* ty */ VTerm, /* usage */ VTerm)] =
      constructor.paramTys.zipWithIndex.map { (binding, i) =>
        (
          numParams - i,
          (
            binding.ty.weaken(numParams - i, 0),
            binding.usage.weaken(
              numParams - i,
              0,
            ),
          ),
        )
      }.toMap

    val validatedParams = allParams.filter { case (_, (_, usage)) =>
      checkSubsumption(
        usage,
        UsageLiteral(U1),
        Some(UsageType(None)),
      )(
        using SUBSUMPTION,
      ) match
        case Right(_) => true
        case _        => false
    }

    def getReferencedConstructorArgs(tm: VTerm): Set[Nat] =
      val (positive, negative) =
        SkippingCollapseFreeVarsVisitor.visitVTerm(tm)(using 0)
      (positive ++ negative).filter(_ < numParams)

    val startingValidatedParamIndices: Set[Int] =
      validatedParams.map(numParams - _._1).to(Set) ++ constructor.tArgs
        .flatMap(
          getReferencedConstructorArgs,
        )

    // Note that we do not add usage because the usage of a component is not present at runtime
    val allValidatedParamIndices = startingValidatedParamIndices
      .bfs(dbIndex =>
        getReferencedConstructorArgs(
          allParams(dbIndex)._1,
        ),
      )
      .iterator
      .to(Set)
    if allValidatedParamIndices.size == constructor.paramTys.size then Right(())
    else Left(NotEqDecidableDueToConstructor(data.qn, constructor.name))

  checkSubsumption(
    data.inherentEqDecidability,
    EqDecidabilityLiteral(EqUnknown),
    Some(EqDecidabilityType()),
  )(using CONVERSION) match
    // short circuit since there is no need to do any check
    case Right(_) => Right(())
    // Call 1, 2, 3
    case _ =>
      checkComponentTypes(
        constructor.paramTys,
        data.inherentEqDecidability,
      ) >>
        checkComponentUsage(constructor)

private object SkippingCollapseFreeVarsVisitor extends FreeVarsVisitor:
  override def visitCollapse
    (collapse: Collapse)
    (using bar: Nat)
    (using Σ: Signature)
    : ( /* positive */ Set[Nat], /* negative */ Set[Nat]) = this.combine()

private def deriveTypeInherentEqDecidability
  (ty: VTerm)
  (using Γ: Context)
  (using Σ: Signature)
  (using ctx: TypingContext)
  : Either[IrError, VTerm] = ty match
  case _: Type | _: EqualityType | _: UsageType | _: EqDecidabilityType | _: EffectsType |
    _: LevelType | _: HeapType | _: CellType =>
    Right(EqDecidabilityLiteral(EqDecidable))
  case Top(_, eqDecidability) => Right(eqDecidability)
  case _: Var | _: Collapse =>
    for
      case (tyTy, _) <- inferType(ty)
      r <- tyTy match
        case Type(upperBound) => deriveTypeInherentEqDecidability(upperBound)
        case _                => Left(ExpectVType(ty))
    yield r
  case _: U => Right(EqDecidabilityLiteral(EqUnknown))
  case d: DataType =>
    Σ.getDataOption(d.qn) match
      case Some(data) =>
        Right(data.inherentEqDecidability.substLowers(d.args: _*))
      case _ => Left(MissingDeclaration(d.qn))
  case _ => Left(ExpectVType(ty))

private def checkIsEqDecidableTypes
  (ty: VTerm)
  (using Γ: Context)
  (using Σ: Signature)
  (using ctx: TypingContext)
  : Either[IrError, Unit] =
  for
    eqD <- deriveTypeInherentEqDecidability(ty)
    _ <- checkSubsumption(
      eqD,
      EqDecidabilityLiteral(EqDecidable),
      Some(EqDecidabilityType()),
    )(using CONVERSION)
  yield ()

private def checkAreEqDecidableTypes
  (telescope: Telescope)
  (using Γ: Context)
  (using Σ: Signature)
  (using ctx: TypingContext)
  : Either[IrError, Unit] = telescope match
  case Nil => Right(())
  case binding :: telescope =>
    for
      _ <- checkIsEqDecidableTypes(binding.ty)
      _ <- checkAreEqDecidableTypes(telescope)(using Γ :+ binding)
    yield ()

private def checkEqDecidabilitySubsumption
  (eqD1: VTerm, eqD2: VTerm)
  (using mode: CheckSubsumptionMode)
  (using Γ: Context)
  (using Σ: Signature)
  (using
    ctx: TypingContext,
  )
  : Either[IrError, Unit] = (eqD1.normalized, eqD2.normalized) match
  case (Left(e), _)                               => Left(e)
  case (_, Left(e))                               => Left(e)
  case (Right(eqD1), Right(eqD2)) if eqD1 == eqD2 => Right(())
  case (Right(EqDecidabilityLiteral(EqDecidability.EqDecidable)), _) |
    (_, Right(EqDecidabilityLiteral(EqDecidability.EqUnknown))) if mode == SUBSUMPTION =>
    Right(())
  case _ => Left(NotEqDecidabilitySubsumption(eqD1, eqD2, mode))

/** @param usages
  *   usage terms should live in Γ
  * @param count
  *   number of usages to verify, counting from the end (right)
  * @return
  *   unverified usages
  */
private def verifyUsages
  (usages: Usages)
  (count: Nat = usages.size)
  (using Γ: Context)
  (using Σ: Signature)
  (using ctx: TypingContext)
  : Either[IrError, Usages] =
  transpose(usages.takeRight(count).reverse.zipWithIndex.map { (v, i) =>
    checkUsageSubsumption(v, Γ.resolve(i).usage)(using SUBSUMPTION)
  }) >> Right(usages.drop(count).map { v =>
    try v.strengthen(count, 0)
    catch
      // It's possible for a term's usage to reference a usage term after it. For example consider
      // functino `f: u: Usage -> [u] Nat -> Nat` and context `{i: Nat, u: Usage}`, then `f u i`
      // has usage `[u, U1]`. In this case, strengthen usage of `i` is approximated by UUnres.
      case _: StrengthenException => UsageLiteral(Usage.UUnres)
  })

/** @param invert
  *   useful when checking patterns where the consumed usages are actually provided usages because
  *   lhs patterns are multiplied by declared usages in function
  */
private def checkUsagesSubsumption
  (usages: Usages, invert: Boolean = false)
  (using Γ: Context)
  (using Σ: Signature)
  (using ctx: TypingContext)
  : Either[IrError, Unit] =
  assert(usages.size == Γ.size)
  allRight((0 until Γ.size).map { i =>
    given Γ2: Context = Γ.take(i)
    val binding = Γ(i)
    val providedUsage = binding.usage
    val consumedUsage = usages(i).strengthen(Γ.size - i, 0)
    if invert then checkUsageSubsumption(consumedUsage, providedUsage)(using SUBSUMPTION)
    else checkUsageSubsumption(providedUsage, consumedUsage)(using SUBSUMPTION)
  })

private def checkContinuationUsageSubsumption
  (usage1: Option[Usage], usage2: Option[Usage])
  (using mode: CheckSubsumptionMode)
  (using Γ: Context)
  (using Σ: Signature)
  (using ctx: TypingContext)
  : Either[IrError, Unit] = (usage1, usage2) match
  case (None, None) => Right(())
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
  : Either[IrError, Unit] = (usage1.normalized, usage2.normalized) match
  case (Left(e), _)                                       => Left(e)
  case (_, Left(e))                                       => Left(e)
  case (Right(usage1), Right(usage2)) if usage1 == usage2 => Right(())
  // Note on direction of usage comparison: UUnres > U1 but UUnres subsumes U1 when counting usage
  case (Right(UsageLiteral(u1)), Right(UsageLiteral(u2))) if u1 >= u2 && mode == SUBSUMPTION =>
    Right(())
  case (Right(UsageLiteral(UUnres)), _) if mode == SUBSUMPTION => Right(())
  case (Right(v @ Var(_)), Right(UsageLiteral(u2))) =>
    Γ.resolve(v).ty match
      // Only UUnres subsumes UUnres and UUnres is also convertible with itself.
      case UsageType(Some(UsageLiteral(Usage.UUnres))) if u2 == Usage.UUnres => Right(())
      case UsageType(Some(u1Bound)) if mode == SUBSUMPTION =>
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
  : Either[IrError, Unit] =
  (eff1.normalized, eff2.normalized) match
    case (Left(e), _)                               => Left(e)
    case (_, Left(e))                               => Left(e)
    case (Right(eff1), Right(eff2)) if eff1 == eff2 => Right(())
    case (
        Right(Effects(literals1, unionOperands1)),
        Right(Effects(literals2, unionOperands2)),
      )
      if mode == CheckSubsumptionMode.SUBSUMPTION &&
        literals1.subsetOf(literals2) && unionOperands1.subsetOf(unionOperands2) =>
      Right(())
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
  : Either[IrError, Unit] =
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
    case _ if ul1Normalized == ul2Normalized => Right(())
    case _ if mode == CONVERSION =>
      Left(NotLevelSubsumption(ul1Normalized, ul2Normalized, mode))
    case (
        USimpleLevel(Level(l1, maxOperands1)),
        USimpleLevel(Level(l2, maxOperands2)),
      )
      if l1 <= l2 &&
        maxOperands1.forall { (k, v) =>
          maxOperands2.getOrElse(k, -1) >= v
        } =>
      Right(())
    case (USimpleLevel(_), UωLevel(_))          => Right(())
    case (UωLevel(l1), UωLevel(l2)) if l1 <= l2 => Right(())
    case _ => Left(NotLevelSubsumption(ul1Normalized, ul2Normalized, mode))

def checkTypes
  (tms: Seq[VTerm], tys: Telescope)
  (using Γ: Context)
  (using Σ: Signature)
  (using ctx: TypingContext)
  : Either[IrError, Usages] =
  ctx.trace("checking multiple terms") {
    if tms.length != tys.length then Left(TelescopeLengthMismatch(tms, tys))
    else
      transpose(
        tms.zip(tys).zipWithIndex.map { case ((tm, binding), index) =>
          checkType(tm, binding.ty.substLowers(tms.take(index): _*))
        },
      ).map(_.reduce(_ + _))
  }

def checkIsType
  (vTy: VTerm, levelBound: Option[ULevel] = None)
  (using Γ: Context)
  (using Σ: Signature)
  (using ctx: TypingContext)
  : Either[IrError, Unit] =
  ctx.trace("checking is type") {
    for
      case (vTyTy, _) <- inferType(vTy) // inferType also checks term is correctly constructed
      r <- vTyTy match
        case Type(_) =>
          levelBound match
            case Some(bound) =>
              for
                ul <- inferLevel(vTy)
                _ <- checkULevelSubsumption(ul, bound)
              yield ()
            case _ => Right(())
        case _ => Left(NotTypeError(vTy))
    yield ()
  }

def checkIsCType
  (cTy: CTerm, levelBound: Option[ULevel] = None)
  (using Γ: Context)
  (using Σ: Signature)
  (using ctx: TypingContext)
  : Either[IrError, Unit] =
  ctx.trace("checking is C type") {
    for
      case (cTyTy, _) <- inferType(cTy)
      r <- cTyTy match
        case CType(_, eff) if eff == Total =>
          levelBound match
            case Some(bound) =>
              for
                ul <- inferLevel(cTy)
                _ <- checkULevelSubsumption(ul, bound)
              yield ()
            case _ => Right(())
        case _: CType => Left(EffectfulCTermAsType(cTy))
        case _        => Left(NotCTypeError(cTy))
    yield r
  }

def reduceUsage
  (usage: CTerm)
  (using Γ: Context)
  (using Σ: Signature)
  (using ctx: TypingContext)
  : Either[IrError, VTerm] =
  ctx.trace("reduce usage", Block(yellow(usage.sourceInfo), pprint(usage))) {
    for
      _ <- checkType(usage, F(UsageType()))
      reduced <- reduce(usage)
      usage <- reduced match
        case Return(u, _) => Right(u)
        case _ =>
          throw IllegalStateException(
            "type checking has bugs: reduced value of type `F(UsageType())` must be `Return(u)`.",
          )
    yield usage
  }

def reduceVType
  (vTy: CTerm)
  (using Γ: Context)
  (using Σ: Signature)
  (using ctx: TypingContext)
  : Either[IrError, VTerm] =
  ctx.trace("reduce V type", Block(yellow(vTy.sourceInfo), pprint(vTy))) {
    for
      case (tyTy, _) <- inferType(vTy)
      r <- tyTy match
        case F(Type(_), effect, _) if effect == Total =>
          for
            reducedTy <- reduce(vTy)
            r <- reducedTy match
              case Return(vTy, _) => Right(vTy)
              case _ =>
                throw IllegalStateException(
                  "type checking has bugs: reduced value of type `F ...` must be `Return ...`.",
                )
          yield r
        case F(_, _, _) => Left(EffectfulCTermAsType(vTy))
        case _          => Left(ExpectFType(vTy))
    yield r
  }

def reduceCType
  (cTy: CTerm)
  (using Γ: Context)
  (using Σ: Signature)
  (using ctx: TypingContext)
  : Either[IrError, CTerm] =
  ctx.trace("reduce C type", Block(yellow(cTy.sourceInfo), pprint(cTy))) {
    cTy match
      case _: CType | _: F | _: FunctionType | _: RecordType | _: CTop =>
        Right(cTy)
      case _ =>
        for
          case (cTyTy, _) <- inferType(cTy)
          r <- cTyTy match
            case CType(_, eff) if eff == Total => reduce(cTy)
            case F(_, eff, _) if eff == Total =>
              def unfoldLet(cTy: CTerm): Either[IrError, CTerm] = cTy match
                // Automatically promote a SomeVType to F(SomeVType).
                case Return(vty, _) => Right(F(vty)(using cTy.sourceInfo))
                case Let(t, ctx) =>
                  reduce(ctx.substLowers(Collapse(t))).flatMap(unfoldLet)
                case c =>
                  throw IllegalStateException(
                    s"type checking has bugs: $c should be of form `Return(...)`",
                  )

              reduce(cTy).flatMap(unfoldLet)
            case _: CType => Left(EffectfulCTermAsType(cTy))
            case _        => Left(NotCTypeError(cTy))
        yield r
  }

private def augmentEffect(eff: VTerm, cty: CTerm): CTerm = cty match
  case CType(upperBound, effects) =>
    CType(upperBound, EffectsUnion(eff, effects))
  case CTop(ul, effects)      => CTop(ul, EffectsUnion(eff, effects))
  case F(vTy, effects, usage) => F(vTy, EffectsUnion(eff, effects), usage)
  case FunctionType(binding, bodyTy, effects) =>
    FunctionType(
      binding,
      bodyTy,
      EffectsUnion(eff, effects),
    )
  case RecordType(qn, args, effects) =>
    RecordType(qn, args, EffectsUnion(eff, effects))
  case _ => throw IllegalArgumentException(s"trying to augment $cty with $eff")

private def checkVar0Leak
  (ty: CTerm | VTerm, error: => IrError)
  (using Σ: Signature)
  : Either[IrError, Unit] =
  val (positiveFreeVars, negativeFreeVars) = ty match
    case ty: CTerm => getFreeVars(ty)(using 0)
    case ty: VTerm => getFreeVars(ty)(using 0)
  if positiveFreeVars(0) || negativeFreeVars(0) then Left(error)
  else Right(())

def allRight[L](es: Iterable[Either[L, ?]]): Either[L, Unit] =
  es.first {
    case Left(l) => Some(l)
    case _       => None
  } match
    case Some(l) => Left(l)
    case _       => Right(())

extension [L, R1](e1: Either[L, R1])
  private inline infix def >>[R2](e2: => Either[L, R2]): Either[L, R2] =
    e1.flatMap(_ => e2)

private def debugCheck[L, R]
  (tm: CTerm | VTerm, ty: CTerm | VTerm, result: => Either[L, R])
  (using Context)
  (using Signature)
  (using ctx: TypingContext)
  : Either[L, R] =
  ctx.trace(
    s"checking",
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

private inline def debugInfer[L, R <: (CTerm | VTerm)]
  (tm: R, result: => Either[L, (R, Usages)])
  (using Context)
  (using Signature)
  (using ctx: TypingContext)
  : Either[L, (R, Usages)] =
  ctx.trace[L, (R, Usages)](
    s"inferring type",
    Block(ChopDown, Aligned, yellow(tm.sourceInfo), pprint(tm)),
    ty => Block(ChopDown, Aligned, yellow(ty._1.sourceInfo), green(pprint(ty._1))),
  )(result.map { case (r, u) =>
    (r.withSourceInfo(SiTypeOf(tm.sourceInfo)).asInstanceOf[R], u)
  })

private inline def debugSubsumption[L, R]
  (
    rawSub: CTerm | VTerm,
    rawSup: CTerm | VTerm,
    rawTy: Option[CTerm | VTerm],
    result: => Either[L, R],
  )
  (using mode: CheckSubsumptionMode)
  (using Context)
  (using Signature)
  (using ctx: TypingContext)
  : Either[L, R] =
  val modeString = mode match
    case CheckSubsumptionMode.SUBSUMPTION => "⪯"
    case CheckSubsumptionMode.CONVERSION  => "≡"
  ctx.trace(
    s"deciding",
    Block(
      ChopDown,
      Aligned,
      yellow(rawSub.sourceInfo),
      pprint(rawSub),
      modeString,
      yellow(rawSup.sourceInfo),
      pprint(rawSup),
      ":",
      yellow(rawTy.map(_.sourceInfo).getOrElse(SiEmpty)),
      rawTy.map(pprint),
    ),
  )(result)
