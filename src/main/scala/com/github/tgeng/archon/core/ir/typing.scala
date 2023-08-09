package com.github.tgeng.archon.core.ir

import scala.collection.immutable.{Map, Set}
import scala.collection.mutable
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

case class Constraint(context: Context, lhs: List[VTerm], rhs: List[VTerm], tys: Telescope)

/** @param context:
  *   context of this meta-variable
  * @param ty:
  *   type of this meta-variable living in the context above
  */
enum MetaVariable(val context: Context, val ty: CTerm):
  case Unsolved(override val context: Context, override val ty: CTerm)
    extends MetaVariable(context, ty)

  /** @param value:
    *   the solved value of this meta variable
    */
  case Solved(override val context: Context, override val ty: CTerm, value: CTerm)
    extends MetaVariable(context, ty)

  /** @param constraints:
    *   must be non-empty since otherwise the meta variable would be solved.
    */
  case Guarded
    (
      override val context: Context,
      override val ty: CTerm,
      value: CTerm,
      constraints: Set[Constraint],
    ) extends MetaVariable(context, ty)

  require(this match
    case Guarded(_, _, _, constraints) => constraints.nonEmpty
    case _                             => true,
  )

extension(mv: MetaVariable)
  def contextFreeType: CTerm = mv.context.foldRight[CTerm](mv.ty) { (elem, acc) =>
    FunctionType(elem, acc)
  }

trait TypingContext
  (
    var traceLevel: Int,
    var enableDebugging: Boolean,
    val metaVars: mutable.ArrayBuffer[MetaVariable],
  ):

  def addMetaVar(mv: MetaVariable): Meta =
    val index = metaVars.size
    metaVars += mv
    Meta(index)

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

    checkIsCType(definition.ty) >> Right(())
  }

def checkClause
  (qn: QualifiedName, clause: Clause)
  (using Σ: Signature)
  (using ctx: TypingContext)
  : Either[IrError, Clause] = ctx.trace(s"checking def clause $qn") {
  val lhs = clause.lhs.foldLeft(Some(Def(qn)): Option[CTerm]) {
    case (Some(f), p) =>
      p.toElimination match
        case Some(ETerm(t))    => Some(Application(f, t))
        case Some(EProj(name)) => Some(Projection(f, name))
        case None              => None
    case (None, _) => None
  }
  lhs match
    case None => Right(clause) // skip checking absurd clauses
    case Some(lhs) =>
      given Context = clause.bindings
      for
        (_, lhsUsages) <- checkType(lhs, clause.ty)
        _ <- checkUsagesSubsumption(lhsUsages, true)
        (rhs, rhsUsages) <- checkType(clause.rhs, clause.ty)
        _ <- checkUsagesSubsumption(rhsUsages)
      yield clause.copy(rhs = rhs)
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

def checkOperation
  (qn: QualifiedName, operation: Operation)
  (using Σ: Signature)
  (using ctx: TypingContext)
  : Either[IrError, Unit] =
  ctx.trace(s"checking effect operation $qn.${operation.name}") {
    Σ.getEffectOption(qn) match
      case None => Left(MissingDeclaration(qn))
      case Some(effect) =>
        val Γ = effect.tParamTys.toIndexedSeq

        checkParameterTypeDeclarations(operation.paramTys)(using Γ) >>
          checkIsType(operation.resultTy)(using Γ ++ operation.paramTys) >> Right(())
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
  : Either[IrError, (ULevel, Usages)] = ul match
  case ULevel.USimpleLevel(l) =>
    for
      (l, usages) <- checkType(l, LevelType())
      l <- l.normalized
    yield (ULevel.USimpleLevel(l), usages)
  case ULevel.UωLevel(_) => Right(ul, Usages.zero)

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
    case Collapse(cTm)      => inferLevel(cTm)
    case U(cty)             => inferLevel(cty)
    case DataType(qn, args) => Right(Σ.getData(qn).ul.substLowers(args: _*))
    case _: UsageType | _: EqDecidabilityType | _: EffectsType | _: HeapType =>
      Right(ULevel.USimpleLevel(LevelLiteral(0)))
    case _: LevelType    => Right(ULevel.UωLevel(0))
    case CellType(_, ty) => inferLevel(ty)
    case _ => throw IllegalArgumentException(s"should have been checked to be a type: $tm")

def inferType
  (tm: VTerm)
  (using Γ: Context)
  (using Σ: Signature)
  (using ctx: TypingContext)
  : Either[IrError, (VTerm, VTerm, Usages)] =
  debugInfer(
    tm,
    tm match
      case Type(upperBound) =>
        for
          (upperBound, upperBoundUsages) <- checkIsType(upperBound)
          upperBound <- upperBound.normalized
          newTm = Type(upperBound)(using tm.sourceInfo)
        yield (newTm, Type(newTm), upperBoundUsages)
      case Top(ul, eqD) =>
        for
          (ul, ulUsage) <- checkULevel(ul)
          (eqD, eqDUsage) <- checkType(eqD, EqDecidabilityType())
          eqD <- eqD.normalized
          newTm = Top(ul, eqD)(using tm.sourceInfo)
        yield (newTm, Type(newTm), (ulUsage + eqDUsage))
      case r: Var => Right(r, Γ.resolve(r).ty, Usages.single(r))
      case Collapse(cTm) =>
        for
          case (cTm, cTy, usage) <- inferType(cTm)
          case (vTy, u) <- cTy match
            case F(vTy, eff, u) if eff == Total => Right((vTy, u))
            case F(_, _, _)                     => Left(CollapsingEffectfulTerm(cTm))
            case _                              => Left(NotCollapsable(cTm))
        yield (Collapse(cTm), vTy, usage)
      case U(cty) =>
        for
          case (cty, ctyTy, usage) <- inferType(cty)
          newTm <- Collapse(cty)(using tm.sourceInfo).normalized
          r <- ctyTy match
            case CType(_, eff) if eff == Total => Right(Type(newTm))
            // Automatically promote SomeVType to F(SomeVType)
            case F(Type(_), eff, _) if eff == Total => Right(Type(newTm))
            case CType(_, _) | F(Type(_), _, _) =>
              Left(EffectfulCTermAsType(cty))
            case _ => Left(NotTypeError(tm))
        yield (newTm, r, usage)
      case Thunk(c) =>
        for case (c, cty, usage) <- inferType(c)
        yield (Thunk(c), U(cty), usage)
      case DataType(qn, args) =>
        Σ.getDataOption(qn) match
          case None => Left(MissingDeclaration(qn))
          case Some(data) =>
            for
              (args, usage) <- checkTypes(args, (data.tParamTys.map(_._1) ++ data.tIndexTys).toList)
              args <- transpose(args.map(_.normalized))
              newTm = DataType(qn, args)(using tm.sourceInfo)
            yield (newTm, Type(newTm), usage)
      case _: Con          => throw IllegalArgumentException("cannot infer type")
      case u: UsageLiteral => Right(u, UsageType(Some(u)), Usages.zero)
      case UsageCompound(op, operands) =>
        for
          (operands, usages) <- transposeCheckTypeResults(
            operands.multiToSeq.map(o => checkType(o, UsageType(None))),
          )
          newTm = UsageCompound(op, operands.toMultiset)(using tm.sourceInfo)
          bound <- newTm.normalized match
            case Right(u) => Right(Some(u))
            case _        => Right(None)
        yield (newTm, UsageType(bound), usages)
      case u: UsageType               => 
        for
          result <- transpose(u.upperBound.map(upperBound => checkType(upperBound, UsageType(None))))
        yield result match
          case Some(upperBound, usages) => (u, Type(UsageType(Some(upperBound))), usages)
          case _ => (u, Type(u), Usages.zero)
      case eqD: EqDecidabilityType    => Right(eqD, Type(eqD), Usages.zero)
      case eqD: EqDecidabilityLiteral => Right(eqD, EqDecidabilityType(), Usages.zero)
      case e: EffectsType             => Right(e, Type(e), Usages.zero)
      case Effects(literal, operands) =>
        for
          (_, literalUsages) <- transposeCheckTypeResults(
            literal.map { (qn, args) =>
              Σ.getEffectOption(qn) match
                case None         => Left(MissingDeclaration(qn))
                case Some(effect) => checkTypes(args, effect.tParamTys.toList)
            },
          )
          (operands, operandsUsages) <- transposeCheckTypeResults(
            operands.map { ref => checkType(ref, EffectsType()) }.toList,
          )
          newTm: Effects = Effects(literal, operands.toSet)(using tm.sourceInfo)
          usage <- getEffectsContinuationUsage(newTm)
        yield (
          newTm,
          EffectsType(usage),
          literalUsages + operandsUsages,
        )
      case LevelType() => Right(LevelType(), (Type(LevelType())), Usages.zero)
      case Level(op, maxOperands) =>
        for
          (operands, usages) <- transposeCheckTypeResults(maxOperands.map { (ref, _) =>
            checkType(ref, LevelType())
          })
          newTm = Level(op, operands.toMultiset)(using tm.sourceInfo)
        yield (newTm, LevelType(), usages)
      case HeapType() => Right(HeapType(), (Type(HeapType())), Usages.zero)
      case h: Heap    => Right(h, HeapType(), Usages.zero)
      case CellType(heap, ty) =>
        for
          (heap, heapUsages) <- checkType(heap, HeapType())
          case (ty, tyTy, tyUsages) <- inferType(ty)
          heap <- heap.normalized
          ty <- ty.normalized
          newTm = CellType(heap, ty)(using tm.sourceInfo)
          r <- tyTy match
            case Type(_) => Right(Type(newTm))
            case _       => Left(NotTypeError(ty))
        yield (newTm, r, (heapUsages + tyUsages))
      case Cell(_, _) => throw IllegalArgumentException("cannot infer type")
      case Auto()     => throw IllegalArgumentException("cannot infer type"),
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
  : Either[IrError, (VTerm, Usages)] = debugCheck(
  tm,
  ty,
  tm match
    case Collapse(c) => checkType(c, F(ty)).map((tm, usages) => (Collapse(tm), usages))
    case Thunk(c) =>
      ty match
        case U(cty) => checkType(c, cty).map((tm, usages) => (Thunk(tm), usages))
        case _      => Left(ExpectUType(ty))
    case Con(name, args) =>
      ty match
        case DataType(qn, tArgs) =>
          Σ.getConstructorOption(qn, name) match
            case None => Left(MissingConstructor(name, qn))
            case Some(con) =>
              val data = Σ.getData(qn)
              val tParamArgs = tArgs.take(data.tParamTys.size)
              val tIndexArgs = tArgs.drop(data.tParamTys.size)
              for
                (args, usages) <- checkTypes(args, con.paramTys.substLowers(tParamArgs: _*))
                _ <- checkSubsumptions(
                  con.tArgs.map(_.substLowers(tParamArgs ++ args: _*)),
                  tIndexArgs,
                  data.tIndexTys.substLowers(tParamArgs: _*),
                )(using CONVERSION)
              yield (DataType(qn, args), usages)
        case _ => Left(ExpectDataType(ty))
    case Cell(heapKey, _) =>
      ty match
        case CellType(heap, _) if Heap(heapKey) == heap => Right(tm, Usages.zero)
        case _: CellType                                => Left(ExpectCellTypeWithHeap(heapKey))
        case _                                          => Left(ExpectCellType(ty))
    case Auto() =>
      val meta = ctx.addMetaVar(MetaVariable.Unsolved(Γ, F(ty)))
      Right(
        (
          Collapse(vars(Γ.size - 1).foldLeft[CTerm](meta)(Application(_, _))),
          Usages.zero,
        ),
      )
    case _ =>
      for
        case (newTm, inferred, usages) <- inferType(tm)
        _ <- checkSubsumption(inferred, ty, None)
      yield (newTm, usages),
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
  : Either[IrError, (CTerm, CTerm, Usages)] =
  debugInfer(
    tm,
    tm match
      case Hole =>
        throw IllegalArgumentException(
          "hole should only be present during reduction",
        )
      case CType(upperBound, effects) =>
        for
          (effects, effUsages) <- checkType(effects, EffectsType())
          (upperBound, upperBoundTy, upperBoundUsages) <- inferType(upperBound)
        yield (
          CType(upperBound, effects),
          CType(tm, Total),
          (effUsages + upperBoundUsages),
        )
      case CTop(ul, effects) =>
        for
          (effects, uUsages) <- checkType(effects, EffectsType())
          (ul, ulUsages) <- checkULevel(ul)
          newTm = CTop(ul, effects)(using tm.sourceInfo)
        yield (newTm, CType(newTm, Total), (uUsages + ulUsages))
      case m @ Meta(index) => Right(m, ctx.metaVars(index).contextFreeType, Usages.zero)
      case d @ Def(qn) =>
        Σ.getDefinitionOption(qn) match
          case None             => Left(MissingDeclaration(qn))
          case Some(definition) => Right((d, definition.ty, Usages.zero))
      case Force(v) =>
        for
          (v, vTy, vUsages) <- inferType(v)
          cTy <- vTy match
            // TODO: think about whether this is good enough.
            // Annotating all force as maybe-divergent because the computations may be dynamically
            // loaded from handlers and hence there is no way to statically detect cyclic references
            // between computations (functions, etc) unless I make the type system even more
            // complicated to somehow tracking possible call-hierarchy.
            case U(cty) => Right(augmentEffect(MaybeDiv, cty))
            case _      => Left(ExpectUType(vTy))
        yield (Force(v), cTy, vUsages)
      case F(vTy, effects, usage) =>
        for
          (effects, effUsages) <- checkType(effects, EffectsType())
          (usage, uUsages) <- checkType(usage, UsageType(None))
          // Prevent returning value of U0 usage, which does not make sense.
          _ <- checkUsageSubsumption(usage, UsageLiteral(Usage.U1))
          case (vTy, vTyTy, vTyUsages) <- inferType(vTy)
          newTm = F(vTy, effects, usage)(using tm.sourceInfo)
          cTyTy <- vTyTy match
            case Type(_) => Right(CType(newTm, Total))
            case _       => Left(NotTypeError(vTy))
        yield (newTm, cTyTy, (effUsages + uUsages + vTyUsages))
      case Return(v) =>
        for case (v, vTy, vUsages) <- inferType(v)
        yield (Return(v), F(vTy, Total), vUsages)
      case tm: Let => checkLet(tm, None)
      case FunctionType(binding, bodyTy, effects) =>
        for
          (effects, effUsages) <- checkType(effects, EffectsType())
          (ty, tyTy, tyUsages) <- inferType(binding.ty)
          (bindingUsage, bindingUsageUsages) <- checkType(binding.usage, UsageType(None))
          (newTm, funTyTy, bodyTyUsages) <- tyTy match
            case Type(_) =>
              for
                (bodyTy, bodyTyTy, bodyTyUsages) <- inferType(bodyTy)(using Γ :+ binding)
                newTm = FunctionType(Binding(ty, bindingUsage)(binding.name), bodyTy, effects)(using
                  tm.sourceInfo,
                )
                r <- bodyTyTy match
                  case CType(_, eff) if eff == Total =>
                    // Strengthen is safe here because if it references the binding, then the
                    // binding must be at level ω and hence ULevelMax would return big type.
                    // Also, there is no need to check the dropped usage because usages in types
                    // is always multiplied by U0.
                    Right(
                      newTm,
                      CType(newTm, Total),
                      bodyTyUsages.dropRight(1).map(_.strengthened),
                    )
                  // TODO[P3]: think about whether the following is actually desirable
                  // Automatically promote Return(SomeVType) to F(SomeVType) and proceed type
                  // inference.
                  case F(Type(_), eff, _) if eff == Total =>
                    Right(
                      newTm,
                      CType(newTm, Total),
                      bodyTyUsages.dropRight(1).map(_.strengthened),
                    )
                  case CType(_, _) | F(Type(_), _, _) =>
                    Left(EffectfulCTermAsType(bodyTy))
                  case _ => Left(NotCTypeError(bodyTy))
              yield r
            case _ => Left(NotTypeError(binding.ty))
        yield (newTm, funTyTy, (effUsages + tyUsages + bodyTyUsages + bindingUsageUsages))
      case Application(fun, arg) =>
        for
          case (fun, funTy, funUsages) <- inferType(fun)
          r <- funTy match
            case FunctionType(binding, bodyTy, effects) =>
              for
                (arg, argUsages) <- checkType(arg, binding.ty)
                bodyTy <- reduceCType(bodyTy.substLowers(arg))
              yield (
                Application(fun, arg),
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
              (effects, effUsages) <- checkType(effects, EffectsType())
              (args, argsUsages) <- checkTypes(args, record.tParamTys.map(_._1).toList)
            yield (RecordType(qn, args, effects), CType(tm, Total), (effUsages + argsUsages))
      case Projection(rec, name) =>
        for
          (rec, recTy, recUsages) <- inferType(rec)
          newTm = Projection(rec, name)(using tm.sourceInfo)
          ty <- recTy match
            case RecordType(qn, args, effects) =>
              Σ.getFieldOption(qn, name) match
                case None => Left(MissingField(name, qn))
                case Some(f) =>
                  Right(augmentEffect(effects, f.ty.substLowers(args :+ Thunk(rec): _*)))
            case _ => Left(ExpectRecord(rec))
        yield (newTm, ty, recUsages)
      case OperationCall((qn, tArgs), name, args) =>
        Σ.getEffectOption(qn) match
          case None => Left(MissingDeclaration(qn))
          case Some(effect) =>
            Σ.getOperationOption(qn, name) match
              case None => Left(MissingDefinition(qn))
              case Some(op) =>
                for
                  (tArgs, effUsages) <- checkTypes(tArgs, effect.tParamTys.toList)
                  (args, argsUsages) <- checkTypes(args, op.paramTys.substLowers(tArgs: _*))
                  newEff = (qn, tArgs)
                  newTm = OperationCall(newEff, name, args)(using tm.sourceInfo)
                yield (
                  newTm,
                  F(
                    op.resultTy.substLowers(tArgs ++ args: _*),
                    // TODO[p4]: figure out if there is way to better manage divergence for handler
                    // operations. The dynamic nature of handler dispatching makes it impossible to
                    // know at compile time whether this would lead to a cyclic reference in
                    // computations.
                    EffectsLiteral(Set(newEff, (Builtins.MaybeDivQn, Nil))),
                  ),
                  effUsages + argsUsages,
                )
      case _: Continuation | _: ContinuationReplicationState |
        _: ContinuationReplicationStateAppender =>
        throw IllegalArgumentException(
          "continuation is only created in reduction and hence should not be type checked.",
        )
      case h: Handler => checkHandler(h, None)
      case AllocOp(heap, vTy, value) =>
        for
          (heap, heapUsages) <- checkType(heap, HeapType())
          (value, valueUsages) <- checkType(value, vTy)
          (vTy, _) <- checkIsType(vTy)
        yield (
          AllocOp(heap, vTy, value),
          F(
            CellType(heap, vTy),
            EffectsLiteral(Set((Builtins.HeapEffQn, heap :: Nil))),
          ),
          heapUsages + valueUsages,
        )
      case SetOp(cell, value) =>
        for
          (cell, cellTy, cellUsages) <- inferType(cell)
          r <- cellTy match
            case CellType(heap, vTy) =>
              for (value, valueUsages) <- checkType(value, vTy)
              yield (
                SetOp(cell, value),
                F(
                  CellType(heap, vTy),
                  EffectsLiteral(Set((Builtins.HeapEffQn, heap :: Nil))),
                ),
                cellUsages + valueUsages,
              )
            case _ => Left(ExpectCell(cell))
        yield r
      case GetOp(cell) =>
        for
          case (cell, cellTy, cellUsages) <- inferType(cell)
          r <- cellTy match
            case CellType(heap, vTy) =>
              Right(F(vTy, EffectsLiteral(Set((Builtins.HeapEffQn, heap :: Nil)))))
            case _ => Left(ExpectCell(cell))
        yield (GetOp(cell), r, cellUsages)
      case h: HeapHandler => checkHeapHandler(h, None),
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
  : Either[IrError, (CTerm, Usages)] = debugCheck(
  tm,
  ty,
  tm match
    case Force(v) => checkType(v, U(ty)).map((v, usages) => (Force(v), usages))
    case Return(v) =>
      ty match
        case F(ty, _, usage) => checkType(v, ty).map((v, usages) => (Return(v), usages * usage))
        case _               => Left(ExpectFType(ty))
    case l: Let         => checkLet(l, Some(ty)).map((v, _, usages) => (v, usages))
    case h: Handler     => checkHandler(h, Some(ty)).map((v, _, usages) => (v, usages))
    case h: HeapHandler => checkHeapHandler(h, Some(ty)).map((v, _, usages) => (v, usages))
    case _ =>
      for
        case (tm, tmTy, usages) <- inferType(tm)
        ty <- reduceCType(ty)
        _ <- checkSubsumption(tmTy, ty, None)
      yield (tm, usages),
)

enum CheckSubsumptionMode:
  case SUBSUMPTION, CONVERSION

import CheckSubsumptionMode.*

given CheckSubsumptionMode = SUBSUMPTION

def checkSubsumptions
  (subs: List[VTerm], sups: List[VTerm], tys: Telescope)
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
        headConstraints <- checkSubsumption(sub, sup, Some(ty.ty))
        r <-
          if headConstraints.isEmpty
          then checkSubsumptions(tailSubs, tailSups, tys.substLowers(sub))
          else
            val (a, b) = getFreeVars(tys)(using 0)
            if a(0) || b(0)
              // if the head term is referenced in the tail, add the whole thing as a constraint
            then Right(Set(Constraint(Γ, subs, sups, tys)))
            // the head term is not referenced in the tail, add the tail constraint in addition to the head
            // constraints
            else checkSubsumptions(tailSubs, tailSups, tys.strengthened).map(headConstraints ++ _)
      yield r
    case _ => throw IllegalArgumentException("length mismatch")

/** @param ty
  *   can be [[None]] if `rawSub` and `rawSup` are types
  */
// Precondition: terms are already type-checked
def checkSubsumption
  (rawSub: VTerm, rawSup: VTerm, rawTy: Option[VTerm])
  (using mode: CheckSubsumptionMode)
  (using Γ: Context)
  (using Σ: Signature)
  (using ctx: TypingContext)
  : Either[IrError, Set[Constraint]] =
  def impl: Either[IrError, Set[Constraint]] =
    if rawSub == rawSup then return Right(Set.empty)
    val ty = rawTy.map(_.normalized) match
      case None           => None
      case Some(Right(v)) => Some(v)
      case Some(Left(e))  => return Left(e)
    (rawSub.normalized, rawSup.normalized) match
      case (Left(e), _)             => Left(e)
      case (_, Left(e))             => Left(e)
      case (Right(sub), Right(sup)) =>
        // TODO: handle meta variables
        (sub, sup, ty) match
          case (Type(upperBound1), Type(upperBound2), _) =>
            checkSubsumption(upperBound1, upperBound2, None)
          case (ty, Top(ul2, eqD2), _) =>
            for
              ul1 <- inferLevel(ty)
              levelConstraints <- checkULevelSubsumption(ul1, ul2)
              eqD1 <- deriveTypeInherentEqDecidability(ty)
              eqDecidabilityConstraints <- checkEqDecidabilitySubsumption(eqD1, eqD2)
            yield levelConstraints ++ eqDecidabilityConstraints
          case (U(cty1), U(cty2), _) => checkSubsumption(cty1, cty2, None)
          case (Thunk(c1), Thunk(c2), Some(U(ty))) =>
            checkSubsumption(c1, c2, Some(ty))
          case (DataType(qn1, args1), DataType(qn2, args2), _) if qn1 == qn2 =>
            Σ.getDataOption(qn1) match
              case None => Left(MissingDeclaration(qn1))
              case Some(data) =>
                var args = IndexedSeq[VTerm]()
                transpose(
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
                    .map { case ((arg1, arg2), binding) =>
                      val r = checkSubsumption(
                        arg1,
                        arg2,
                        Some(binding.ty.substLowers(args: _*)),
                      )
                      args = args :+ arg1
                      r
                    },
                ).map(_.flatten.toSet)
          case (EffectsType(continuationUsage1), EffectsType(continuationUsage2), _) =>
            // Note that subsumption checking is reversed because the effect of the computation
            // marks how the continuation can be invoked. Normally, checking usage is checking
            // how a resource is *consumed*. But here, checking usage is checking how the
            // continuation (as a resource) is provided.
            checkContinuationUsageSubsumption(continuationUsage2, continuationUsage1)
          case (UsageType(Some(u1)), UsageType(Some(u2)), _) if mode == SUBSUMPTION =>
            checkUsageSubsumption(u1, u2)
          case (UsageType(Some(_)), UsageType(None), _) if mode == SUBSUMPTION =>
            Right(Set.empty)
          case (
              CellType(heap1, ty1),
              CellType(heap2, ty2),
              _,
            ) =>
            for
              heapConstraints <- checkSubsumption(heap1, heap2, Some(HeapType()))
              tyConstraints <- checkSubsumption(ty1, ty2, None)(using CONVERSION)
            yield heapConstraints ++ tyConstraints
          case (_, Heap(GlobalHeapKey), Some(HeapType())) if mode == SUBSUMPTION =>
            Right(Set.empty)
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
  : Either[IrError, Set[Constraint]] = debugSubsumption(
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
        case (_, _, _) if sub == sup => Right(Set.empty)
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
              transpose(
                fields.map { field =>
                  checkSubsumption(
                    Projection(sub, field.name),
                    Projection(sup, field.name),
                    Some(field.ty),
                  )(using CONVERSION)
                },
              ).map(_.flatten.toSet)
        case (CType(upperBound1, eff1), CType(upperBound2, eff2), _) =>
          for
            effConstraint <- checkEffSubsumption(eff1, eff2)
            upperBoundConstraint <- checkSubsumption(upperBound1, upperBound2, Some(sup))
          yield effConstraint ++ upperBoundConstraint
        case (ty: IType, CTop(ul2, eff2), _) =>
          for
            ul1 <- inferLevel(ty)
            levelConstraint <- checkULevelSubsumption(ul1, ul2)
            effConstraint <- checkEffSubsumption(ty.effects, eff2)
          yield levelConstraint ++ effConstraint
        case (F(vTy1, eff1, u1), F(vTy2, eff2, u2), _) =>
          for
            effConstraint <- checkEffSubsumption(eff1, eff2)
            usageConstraint <- checkUsageSubsumption(u1, u2)
            tyConstraint <- checkSubsumption(vTy1, vTy2, None)
          yield effConstraint ++ usageConstraint ++ tyConstraint
        case (Return(v1), Return(v2), Some(F(ty, _, _))) =>
          checkSubsumption(v1, v2, Some(ty))(using CONVERSION)
        case (Let(t1, ty1, eff1, usage1, ctx1), Let(t2, ty2, eff2, usage2, ctx2), ty) =>
          for
            tyConstraint <- checkSubsumption(ty1, ty2, None)(using CONVERSION)
            effConstraint <- checkSubsumption(eff1, eff2, Some(EffectsType()))(using CONVERSION)
            usageConstraint <- checkSubsumption(usage1, usage2, Some(UsageType()))(using CONVERSION)
            combinedEffects <-
              if effConstraint.isEmpty then Right(eff1) else EffectsUnion(eff1, eff2).normalized
            tConstraint <- checkSubsumption(
              t1,
              t2,
              // Note on type used heres
              // * The concrete type passed here does not affect correctness of type checking.
              // * A combined effect is used to be safe (e.g. we don't want to normalize potentially diverging terms)
              // * Usage is not important during subsumption checking, hence we just pass UUnres.
              Some(F(ty1, combinedEffects, UsageLiteral(UUnres))),
            )(using CONVERSION)
            ctxConstraint <- checkSubsumption(ctx1, ctx2, ty.map(_.weakened))(using mode)(
              // Using ty1 or ty2 doesn't really matter here. We don't need to do any lambda substitution because ty1 or
              // ty2 are not referenced by anything in ctx1 or ctx2 or ty.
              using Γ :+ Binding(ty1, UsageLiteral(UUnres))(gn"v"),
            )
          yield tyConstraint ++ effConstraint ++ usageConstraint ++ tConstraint ++ ctxConstraint
        case (
            FunctionType(binding1, bodyTy1, eff1),
            FunctionType(binding2, bodyTy2, eff2),
            _,
          ) =>
          for
            effConstraint <- checkSubsumption(eff1, eff2, Some(EffectsType()))
            tyConstraint <- checkSubsumption(binding2.ty, binding1.ty, None)
            bodyConstraint <-
              if tyConstraint.isEmpty
              then checkSubsumption(bodyTy1, bodyTy2, None)(using mode)(using Γ :+ binding2)
              else
                val meta = ctx.addMetaVar(
                  Guarded(
                    Γ :+ binding2,
                    F(binding1.ty.weakened, Total, binding1.usage.weakened),
                    Return(Var(0)),
                    tyConstraint,
                  ),
                )
                checkSubsumption(
                  bodyTy1,
                  bodyTy2.subst {
                    case 0 => Some(Collapse(vars(Γ.size).foldLeft[CTerm](meta)(Application(_, _))))
                    case _ => None
                  },
                  None,
                )(using mode)(using Γ :+ binding2)
          yield effConstraint ++ tyConstraint ++ bodyConstraint
        case (Application(fun1, arg1), Application(fun2, arg2), _) =>
          for
            case (fun1, fun1Ty, _) <- inferType(fun1)
            case (fun2, fun2Ty, _) <- inferType(fun2)
            funTyConstraint <- checkSubsumption(fun1Ty, fun2Ty, None)(using CONVERSION)
            funConstraint <- checkSubsumption(fun1, fun2, Some(fun1Ty))(using CONVERSION)
            argConstraint <- fun1Ty match
              case FunctionType(binding, _, _) =>
                checkSubsumption(
                  arg1,
                  arg2,
                  Some(binding.ty),
                )(using CONVERSION)
              case _ => Left(NotCSubsumption(sub, sup, ty, mode))
          yield funTyConstraint ++ funConstraint ++ argConstraint
        case (RecordType(qn1, args1, eff1), RecordType(qn2, args2, eff2), _) if qn1 == qn2 =>
          Σ.getRecordOption(qn1) match
            case None => Left(MissingDeclaration(qn1))
            case Some(record) =>
              var args = IndexedSeq[VTerm]()
              for
                effConstraint <- checkSubsumption(eff1, eff2, Some(EffectsType()))
                argConstraint <- transpose(
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
                ).map(_.flatten.toSet)
              yield effConstraint ++ argConstraint
        case (Projection(rec1, name1), Projection(rec2, name2), _) if name1 == name2 =>
          for
            case (rec1, rec1Ty, _) <- inferType(rec1)
            case (rec2, rec2Ty, _) <- inferType(rec2)
            r <- checkSubsumption(rec1Ty, rec2Ty, None)(using CONVERSION)
          yield r
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
                          val r =
                            checkSubsumption(tArg1, tArg2, Some(binding.ty))(using CONVERSION)
                          args = args :+ tArg1
                          r
                      },
                    ).map(_.flatten.toSet)
                    argConstraint <- transpose(
                      args1.zip(args2).zip(operation.paramTys).map { case ((arg1, arg2), binding) =>
                        val r = checkSubsumption(arg1, arg2, Some(binding.ty))(
                          using CONVERSION,
                        )
                        args = args :+ arg1
                        r
                      },
                    ).map(_.flatten.toSet)
                  yield tArgConstraint ++ argConstraint
        // For now, we skip the complex logic checking subsumption of handler and continuations. It
        // seems not all that useful to keep those. But we can always add them later if it's deemed
        // necessary.
        case _ => Left(NotCSubsumption(sub, sup, ty, mode))
    yield r
  },
)

private def assignMeta
  (meta: Meta, term: CTerm)
  (using Γ: Context)
  (using Σ: Signature)
  (using ctx: TypingContext) = ???

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
    case Let(t, ty, eff, usage, ctx) =>
      for
        eff <- eff.normalized
        r <-
          if eff == Total then simplifyLet(ctx.substLowers(Collapse(t))).flatMap(reduce)
          else Right(t)
      yield r
    case _ => Right(t)
}

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
  case _: Type | _: UsageType | _: EqDecidabilityType | _: EffectsType | _: LevelType |
    _: HeapType | _: CellType =>
    Right(EqDecidabilityLiteral(EqDecidable))
  case Top(_, eqDecidability) => Right(eqDecidability)
  case _: Var | _: Collapse =>
    for
      case (ty, tyTy, _) <- inferType(ty)
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
  : Either[IrError, Set[Constraint]] = (eqD1.normalized, eqD2.normalized) match
  // TODO: handle meta variables
  case (Left(e), _)                               => Left(e)
  case (_, Left(e))                               => Left(e)
  case (Right(eqD1), Right(eqD2)) if eqD1 == eqD2 => Right(Set.empty)
  case (Right(EqDecidabilityLiteral(EqDecidability.EqDecidable)), _) |
    (_, Right(EqDecidabilityLiteral(EqDecidability.EqUnknown))) if mode == SUBSUMPTION =>
    Right(Set.empty)
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
  case (Right(UsageLiteral(u1)), Right(UsageLiteral(u2))) if u1 >= u2 && mode == SUBSUMPTION =>
    Right(Set.empty)
  case (Right(UsageLiteral(UUnres)), _) if mode == SUBSUMPTION => Right(Set.empty)
  case (Right(v @ Var(_)), Right(UsageLiteral(u2))) =>
    Γ.resolve(v).ty match
      // Only UUnres subsumes UUnres and UUnres is also convertible with itself.
      case UsageType(Some(UsageLiteral(Usage.UUnres))) if u2 == Usage.UUnres => Right(Set.empty)
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
      Right(Set.empty)
    case (USimpleLevel(_), UωLevel(_))          => Right(Set.empty)
    case (UωLevel(l1), UωLevel(l2)) if l1 <= l2 => Right(Set.empty)
    case _ => Left(NotLevelSubsumption(ul1Normalized, ul2Normalized, mode))

def checkTypes
  (tms: Seq[VTerm], tys: Telescope)
  (using Γ: Context)
  (using Σ: Signature)
  (using ctx: TypingContext)
  : Either[IrError, (List[VTerm], Usages)] =
  ctx.trace("checking multiple terms") {
    if tms.length != tys.length then Left(TelescopeLengthMismatch(tms, tys))
    else
      transposeCheckTypeResults(
        tms.zip(tys).zipWithIndex.map { case ((tm, binding), index) =>
          checkType(tm, binding.ty.substLowers(tms.take(index): _*))
        },
      )
  }

private def transposeCheckTypeResults[R]
  (
    resultsAndUsages: Iterable[Either[IrError, (R, Usages)]],
  )
  : Either[IrError, (List[R], Usages)] =
  transpose(resultsAndUsages).map(resultsAndUsages =>
    (resultsAndUsages.map(_._1).toList, resultsAndUsages.map(_._2).reduce(_ + _)),
  )

private def checkLet
  (tm: Let, bodyTy: Option[CTerm])
  (using Γ: Context)
  (using Σ: Signature)
  (using ctx: TypingContext)
  : Either[IrError, (CTerm, CTerm, Usages)] =
  val t = tm.t
  val ty = tm.ty
  val effects = tm.eff
  val usage = tm.usage
  val body = tm.ctx
  for
    (ty, _) <- checkIsType(ty)
    (effects, _) <- checkType(effects, EffectsType())
    (usage, _) <- checkType(usage, UsageType())
    (t, tUsages) <- checkType(t, F(ty, effects, usage))
    effects <- effects.normalized
    tUsages <- transpose(tUsages.map(_.normalized))
    (newTm, bodyTy, usages) <-
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
          newBody = t match
            case Return(v) => body.substLowers(v)
            case c         => body.substLowers(Collapse(c))
          r <- bodyTy match
            case Some(bodyTy) =>
              checkType(newBody, bodyTy).map((newBody, usages) => (newBody, bodyTy, usages))
            case None => inferType(newBody)
        yield r
      // Otherwise, just add the binding to the context and continue type checking.
      else
        for
          case (body, bodyTy, usagesInBody) <- bodyTy match
            case None => inferType(body)(using Γ :+ Binding(ty, usage)(gn"v"))
            case Some(bodyTy) =>
              checkType(body, bodyTy.weakened)(using Γ :+ Binding(ty, usage)(gn"v"))
                .map((body, usages) => (body, bodyTy, usages))
          // Report an error if the type of `body` needs to reference the effectful
          // computation. User should use a dependent sum type to wrap such
          // references manually to avoid the leak.
          // TODO[P3]: in case weakened failed, provide better error message: ctxTy cannot depend on
          //  the bound variable
          _ <- checkVar0Leak(
            bodyTy,
            LeakedReferenceToEffectfulComputationResult(t),
          )
          _ <- checkUsageSubsumption(usagesInBody.last.strengthened, usage)(using SUBSUMPTION)
          usagesInContinuation <- effects match
            // Join with U1 for normal execution without any call to effect handlers
            case v: Var                           => Right(getEffVarContinuationUsage(v))
            case eff @ Effects(literal, operands) => getEffectsContinuationUsage(eff)
            case _ =>
              throw IllegalStateException(s"expect to be of Effects type: $tm")
        yield (
          Let(t, ty, effects, usage, body)(tm.boundName)(using tm.sourceInfo),
          bodyTy.strengthened,
          usagesInBody
            .dropRight(1) // drop this binding
            .map(_.strengthened) *
            (UsageLiteral(usagesInContinuation.getOrElse(Usage.U1) | Usage.U1)),
        )
  yield (newTm, augmentEffect(effects, bodyTy), usages)

def checkHandler
  (h: Handler, inputTy: Option[CTerm])
  (using Γ: Context)
  (using Σ: Signature)
  (using ctx: TypingContext)
  : Either[IrError, (CTerm, CTerm, Usages)] =
  val eff = h.eff
  val parameter = h.parameter
  val parameterBinding = h.parameterBinding
  val parameterDisposer = h.parameterDisposer
  val parameterReplicator = h.parameterReplicator
  val outputEffects = h.outputEffects
  val outputUsage = h.outputUsage
  val outputType = h.outputType
  val transform = h.transform
  val handlers = h.handlers
  val input = h.input
  def filterSimpleEffects(normalizedEffects: VTerm): Either[IrError, VTerm] =
    normalizedEffects match
      case v: Var => filterSimpleEffects(Effects(Set.empty, Set(v)))
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
    (eff, effUsages) <- checkType(eff, EffectsType())
    (parameterBindingTy, _) <- checkIsType(parameterBinding.ty)
    (parameterBindingUsage, _) <- checkType(parameterBinding.usage, UsageType(None))
    newParameterBinding = Binding(parameterBindingTy, parameterBindingUsage)(parameterBinding.name)
    (parameter, singleParameterUsages) <- checkType(parameter, parameterBindingTy)
    parameterUsages = singleParameterUsages * parameterBindingUsage
    (outputEffects, _) <- parameterReplicator match
      case Some(_) => checkType(outputEffects, EffectsType())
      // parameterReplicator is not specified, in this case, the outputEffects must not be
      // re-entrant.
      case None => checkType(outputEffects, EffectsType(Some(Usage.UAff)))
    outputEffects <- outputEffects.normalized
    parameterOpsEffects <- filterSimpleEffects(outputEffects)
    parameterOpsΓ = Γ :+ newParameterBinding
    (parameterDisposer, parameterDisposerUsages) <- checkType(
      parameterDisposer,
      F(DataType(Builtins.UnitQn), parameterOpsEffects),
    )(using parameterOpsΓ)
    parameterTypeLevel <- inferLevel(newParameterBinding.ty)
    parameterTypeLevel <- parameterTypeLevel match
      case ULevel.USimpleLevel(l) => Right(l)
      case _                      => Left(LevelTooBig(parameterTypeLevel))
    parameterDisposerUsages <- verifyUsages(parameterDisposerUsages)(1)(using parameterOpsΓ)
    (parameterReplicator, parameterReplicatorUsages) <- parameterReplicator match
      case Some(parameterReplicator) =>
        for
          (parameterReplicator, parameterReplicatorUsages) <- checkType(
            parameterReplicator,
            F(
              DataType(
                Builtins.PairQn,
                List(
                  parameterTypeLevel,
                  EqDecidabilityLiteral(EqDecidability.EqUnknown),
                  newParameterBinding.usage,
                  newParameterBinding.ty,
                  newParameterBinding.usage,
                  newParameterBinding.ty,
                ),
              ),
              parameterOpsEffects,
            ).weakened,
          )(using parameterOpsΓ)
          parameterReplicatorUsages <- verifyUsages(parameterReplicatorUsages)(1)(using
            parameterOpsΓ,
          )
        yield (Some(parameterReplicator), parameterReplicatorUsages)
      case None => Right(None, List.fill(Γ.size)(UsageLiteral(Usage.U0)))
    case (input, inputCTy, inputUsages) <- inputTy match
      case None => inferType(input)
      case Some(inputTy) =>
        checkType(input, inputTy).map((input, usages) => (input, inputTy, usages))
    case (inputTy, inputEff, inputUsage) <- inputCTy match
      case F(inputTy, inputEff, inputUsage) => Right((inputTy, inputEff, inputUsage))
      case _                                => Left(ExpectFType(inputCTy))
    inputBinding = Binding(inputTy, inputUsage)(gn"v")
    (outputType, _) <- checkIsType(outputType)
    outputCType = F(outputType, outputEffects, outputUsage)
    transformΓ = Γ :+ newParameterBinding :+ inputBinding.weakened
    (outputUsage, _) <- checkType(outputUsage, UsageType(None))
    (transform, transformUsages) <- checkType(transform, outputCType.weaken(2, 0))(using transformΓ)
    transformUsages <- verifyUsages(transformUsages)(2)
    _ <- checkSubsumption(
      inputEff,
      EffectsUnion(outputEffects, eff),
      Some(EffectsType()),
    )
    // Check handler implementations
    (handlerEntries, handlerUsages) <-
      def checkHandler(eff: Eff): Either[IrError, (List[(QualifiedName, CTerm)], Usages)] =
        val (qn, args) = eff
        for
          effect <- Σ.getEffectOption(qn).toRight(MissingDeclaration(qn))
          operations <- Σ.getOperationsOption(qn).toRight(MissingDeclaration(qn))
          _ <-
            val missingOperationQn =
              operations.map(qn / _.name).filter(qn => !handlers.contains(qn)).toSet
            if missingOperationQn.isEmpty then Right(())
            else Left(MissingHandlerImplementation(missingOperationQn, h.sourceInfo))
          (handlerEntries, handlerUsages) <- transposeCheckTypeResults(
            operations.map { opDecl =>
              val handlerQn = qn / opDecl.name
              val handlerBody = handlers(handlerQn)
              val (argNames, resumeNameOption) = h.handlersBoundNames(handlerQn)
              // All of the following opXXX are weakened for handler parameter
              val opResultTy = opDecl.resultTy.substLowers(args: _*).weakened
              val opResultUsage = opDecl.resultUsage.substLowers(args: _*).weakened
              val opParamTys = newParameterBinding +: opDecl.paramTys
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
                                    newParameterBinding.usage,
                                    newParameterBinding.ty,
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
                              newParameterBinding.usage,
                              newParameterBinding.ty,
                              opResultUsage,
                              opResultTy,
                            ),
                          ),
                          outputEffects,
                          opResultUsage,
                        ).weaken(opDecl.paramTys.size, 0),
                      ),
                    )
                (handlerBody, bodyUsages) <- checkType(handlerBody, opOutputTy)(using
                  Γ ++ opParamTys,
                )
                bodyUsages <- verifyUsages(bodyUsages)(opParamTys.size)(using Γ ++ opParamTys)
              yield ((handlerQn -> handlerBody), bodyUsages)
            },
          )
        yield (handlerEntries, handlerUsages)
      eff match
        case Effects(effs, s) if s.isEmpty =>
          val effQns = effs.map(_._1)
          for
            _ <-
              val unknownOperationQns = handlers.keySet
                .filter {
                  case QualifiedName.Node(parent, _) => !effQns.contains(parent)
                  case qn => throw IllegalStateException(s"bad operation name $qn")
                }
              if unknownOperationQns.isEmpty
              then Right(())
              else Left(UnknownHandlerImplementation(unknownOperationQns, h.sourceInfo))
            r <- transposeCheckTypeResults(effs.map(checkHandler(_)))
          yield r

        case _ => Left(EffectTermToComplex(eff))
  yield (
    Handler(
      eff,
      parameter,
      newParameterBinding,
      parameterDisposer,
      parameterReplicator,
      outputEffects,
      outputUsage,
      outputType,
      transform,
      Map(handlerEntries.flatten: _*),
      input,
    )(h.transformBoundName, h.handlersBoundNames)(using h.sourceInfo),
    outputCType,
    // usages in handlers are multiplied by UUnres because handlers may be invoked any number of times.
    (handlerUsages + transformUsages
      .dropRight(1)
      .map(_.strengthened) + effUsages) * UUnres + inputUsages,
  )

def checkHeapHandler
  (h: HeapHandler, inputTy: Option[CTerm])
  (using Γ: Context)
  (using Σ: Signature)
  (using ctx: TypingContext)
  : Either[IrError, (CTerm, CTerm, Usages)] =
  val input = h.input
  val heapVarBinding =
    Binding[VTerm](HeapType(), UsageLiteral(UUnres))(h.boundName)

  given Context = Γ :+ heapVarBinding

  for
    case (input, inputCTy, inputUsages) <- inputTy match
      case None          => inferType(input)
      case Some(inputTy) => checkType(input, inputTy).map((inputTy, _))
    r <- inputCTy match
      case F(inputTy, eff, _) =>
        for
          // TODO[P2]: Use more sophisticated check here to catch leak through wrapping heap
          //  variable inside things. If it's leaked, there is no point using this handler at
          //  all. Simply using GlobalHeapKey is the right thing to do. This is because a
          //  creating a leaked heap key itself is performing a side effect with global heap.
          _ <- checkVar0Leak(
            inputTy,
            LeakedReferenceToHeapVariable(input),
          )
          outputEff = eff match
            case Effects(literal, vars) =>
              Effects(
                literal.filter {
                  // Filter out current heap effect. `Var(0)` binds to the heap key of this
                  // handler.
                  case (qn, args) => qn != Builtins.HeapEffQn && args != List(Var(0))
                },
                vars,
              )
            case _ => eff
        yield F(inputTy.strengthened, outputEff)
      case _ => Left(ExpectFType(inputCTy))
  yield (input, r, inputUsages)

def checkIsType
  (vTy: VTerm, levelBound: Option[ULevel] = None)
  (using Γ: Context)
  (using Σ: Signature)
  (using ctx: TypingContext)
  : Either[IrError, (VTerm, Usages)] =
  ctx.trace("checking is type") {
    for
      (vTy, vTyTy, usages) <- inferType(vTy) // inferType also checks term is correctly constructed
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
    yield (vTy, usages)
  }

def checkIsCType
  (cTy: CTerm, levelBound: Option[ULevel] = None)
  (using Γ: Context)
  (using Σ: Signature)
  (using ctx: TypingContext)
  : Either[IrError, CTerm] =
  ctx.trace("checking is C type") {
    for
      case (cty, cTyTy, _) <- inferType(cTy)
      _ <- cTyTy match
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
    yield cty
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
        case Return(u) => Right(u)
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
      case (vTy, tyTy, _) <- inferType(vTy)
      r <- tyTy match
        case F(Type(_), effect, _) if effect == Total =>
          for
            reducedTy <- reduce(vTy)
            r <- reducedTy match
              case Return(vTy) => Right(vTy)
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
          case (cTy, cTyTy, _) <- inferType(cTy)
          r <- cTyTy match
            case CType(_, eff) if eff == Total => reduce(cTy)
            case F(_, eff, _) if eff == Total =>
              def unfoldLet(cTy: CTerm): Either[IrError, CTerm] = cTy match
                // Automatically promote a SomeVType to F(SomeVType).
                case Return(vty) => Right(F(vty)(using cTy.sourceInfo))
                case Let(t, _, _, _, ctx) =>
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
  // TODO[P1]: remove this since it hides typing issues
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
  (tm: R, result: => Either[L, (R, R, Usages)])
  (using Context)
  (using Signature)
  (using ctx: TypingContext)
  : Either[L, (R, R, Usages)] =
  ctx.trace[L, (R, R, Usages)](
    s"inferring type",
    Block(ChopDown, Aligned, yellow(tm.sourceInfo), pprint(tm)),
    ty => Block(ChopDown, Aligned, yellow(ty._1.sourceInfo), green(pprint(ty._1))),
  )(result.map { case (v, r, u) =>
    (v, r.withSourceInfo(SiTypeOf(tm.sourceInfo)).asInstanceOf[R], u)
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

/* References
 [0]  Norell, Ulf. “Towards a practical programming language based on dependent type theory.” (2007).
 */
