package com.github.tgeng.archon.core.ir

import scala.util.boundary, boundary.break;
import scala.collection.immutable.{Map, Set}
import scala.collection.mutable
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

import scala.annotation.tailrec
import PrettyPrinter.pprint
import WrapPolicy.*
import IndentPolicy.*
import DelimitPolicy.*
import scala.collection.immutable.LazyList.cons
import UnsolvedMetaVariableConstraint.*

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

enum Constraint:
  case Conversions(context: Context, lhs: List[VTerm], rhs: List[VTerm], tys: Telescope)
  case VConversion(context: Context, lhs: VTerm, rhs: VTerm, ty: Option[VTerm])
  case CConversion(context: Context, lhs: CTerm, rhs: CTerm, ty: Option[CTerm])
  case VSubType(context: Context, sub: VTerm, sup: VTerm)
  case CSubType(context: Context, sub: CTerm, sup: CTerm)
  case EffSubsumption(context: Context, sub: VTerm, sup: VTerm)
  case LevelSubsumption(context: Context, sub: VTerm, sup: VTerm)
  case UsageSubsumption(context: Context, sub: VTerm, sup: VTerm)
  case EqDecidabilitySubsumption(context: Context, sub: VTerm, sup: VTerm)

enum UnsolvedMetaVariableConstraint:
  case UmcNothing
  case UmcCSubtype(lowerBound: CTerm)
  case UmcVSubtype(lowerBound: VTerm)
  case UmcEffSubsumption(lowerBound: VTerm)
  case UmcLevelSubsumption(lowerBound: VTerm)
  case UmcUsageSubsumption(upperBound: VTerm)

  def substLowers(args: VTerm*)(using Signature): UnsolvedMetaVariableConstraint = this match
    case UmcNothing => UmcNothing
    case UmcCSubtype(lowerBound) =>
      UmcCSubtype(lowerBound.substLowers(args: _*))
    case UmcVSubtype(lowerBound) =>
      UmcVSubtype(lowerBound.substLowers(args: _*))
    case UmcEffSubsumption(lowerBound) =>
      UmcEffSubsumption(lowerBound.substLowers(args: _*))
    case UmcLevelSubsumption(lowerBound) =>
      UmcLevelSubsumption(lowerBound.substLowers(args: _*))
    case UmcUsageSubsumption(upperBound) =>
      UmcUsageSubsumption(upperBound.substLowers(args: _*))

/** @param context:
  *   context of this meta-variable
  * @param ty:
  *   type of this meta-variable living in the context above
  */
enum MetaVariable(val context: Context, val ty: CTerm):
  case Unsolved
    (
      override val context: Context,
      override val ty: CTerm,
      constraint: UnsolvedMetaVariableConstraint,
    ) extends MetaVariable(context, ty)

  /** @param value:
    *   the solved value of this meta variable
    */
  case Solved(override val context: Context, override val ty: CTerm, value: CTerm) extends MetaVariable(context, ty)

  /** @param preconditions:
    *   must be non-empty since otherwise the meta variable would be solved.
    */
  case Guarded
    (
      override val context: Context,
      override val ty: CTerm,
      value: CTerm,
      preconditions: Set[Constraint],
    ) extends MetaVariable(context, ty)

  require(this match
    case Guarded(_, _, _, preconditions) => preconditions.nonEmpty
    case _                               => true,
  )

  def substLowers(args: VTerm*)(using Signature): MetaVariable =
    require(context.size >= args.size)
    this match
      case Unsolved(context, ty, constraint) =>
        Unsolved(context.drop(args.size), ty.substLowers(args: _*), constraint)
      case Solved(context, ty, value) =>
        Solved(context.drop(args.size), ty.substLowers(args: _*), value.substLowers(args: _*))
      case Guarded(context, ty, value, preconditions) =>
        Guarded(
          context.drop(args.size),
          ty.substLowers(args: _*),
          value.substLowers(args: _*),
          preconditions,
        )

  def contextFreeType: CTerm = context.foldRight[CTerm](ty) { (elem, acc) =>
    FunctionType(elem, acc)
  }

enum ResolvedMetaVariable:
  /** @param substitution:
    *   substitution that converts a term in the context in which this resolution happens to the context of this meta
    *   variable. That is, a term after this substitution can be assigned to the meta variable. Note that, caller must
    *   check to make sure all variables are mapped by this substitution, otherwise, the substituted variable can
    *   contain (unresolved) free variables. Note that, this value is none if a substitution map cannot be obtained (due
    *   to redex containing eliminations that are not distinct variables)
    * @param resolved:
    *   the resolved meta variable where types are already substituted with the current arguments in the given redex.
    */
  case RUnsolved
    (
      index: Nat,
      substitution: Map[Int, VTerm],
      constraint: UnsolvedMetaVariableConstraint,
      tm: CTerm,
      ty: CTerm,
    )
  case RGuarded()
  case RSolved()
import ResolvedMetaVariable.*

class TypingContext
  (
    var traceLevel: Int,
    var enableDebugging: Boolean,
  ):

  private val metaVars: mutable.ArrayBuffer[MetaVariable] = mutable.ArrayBuffer()
  private var version: Int = 0
  private var solvedVersion: Int = 0
  given TypingContext = this

  // TODO[P0]: check usage of this method. Normally the following `resolve` should be used instead.
  def resolveMeta(m: Meta) = metaVars(m.index)

  def withMetaResolved[R]
    (input: CTerm)
    (action: ((ResolvedMetaVariable, List[Elimination[VTerm]]) | CTerm) => R)
    (using Signature)
    : R =
    resolve(input) match
      case Some(r) => action(r)
      case None    => action(input)

  def withMetaResolved2[R]
    (input1: CTerm, input2: CTerm)
    (
      action: (
        (ResolvedMetaVariable, List[Elimination[VTerm]]) | CTerm,
        (ResolvedMetaVariable, List[Elimination[VTerm]]) | CTerm,
      ) => R,
    )
    (using Signature)
    : R =
    withMetaResolved(input1):
      case input1 =>
        withMetaResolved(input2):
          case input2 =>
            action(input1, input2)

  def withMetaResolved[R](input: VTerm)(action: (ResolvedMetaVariable | VTerm) => R)(using Signature): R =
    input match
      case Collapse(c) =>
        withMetaResolved(c) {
          case (r, Nil) => action((r))
          case (_, _) =>
            throw IllegalStateException(
              "type error: extra elims for vterm which should never happen",
            )
          case _: CTerm => action(input)
        }
      case _ => action(input)

  def withMetaResolved2[R]
    (input1: VTerm, input2: VTerm)
    (action: (ResolvedMetaVariable | VTerm, ResolvedMetaVariable | VTerm) => R)
    (using Signature)
    : R =
    withMetaResolved(input1):
      case input1 =>
        withMetaResolved(input2):
          case input2 =>
            action(input1, input2)

  def resolve(c: CTerm)(using Signature): Option[(ResolvedMetaVariable, List[Elimination[VTerm]])] =
    val (index, elims) = c match
      case Meta(index)                   => (index, Nil)
      case r @ Redex(Meta(index), elims) => (index, elims)
      case _                             => return None
    metaVars(index) match
      case Unsolved(context, ty, constraints) =>
        if context.size > elims.size then return None
        val args = elims.take(context.size).collect { case Elimination.ETerm(t) =>
          t
        }
        val substitutionCandidate = args.zipWithIndex.collect { case (Var(v), i) =>
          (v, Var(context.size - 1 - i))
        }.toMap
        val substitution =
          if substitutionCandidate.size == context.size
          then substitutionCandidate
          else return None

        val extraElims = elims.drop(context.size)
        Some(
          ResolvedMetaVariable.RUnsolved(
            index,
            substitution,
            constraints.substLowers(args: _*),
            c,
            ty.substLowers(args: _*),
          ),
          extraElims,
        )
      case Solved(context, _, _)     => Some(RSolved(), elims.drop(context.size))
      case Guarded(context, _, _, _) => Some(RGuarded(), elims.drop(context.size))

  def resolveMetaVariableType(c: CTerm)(using Signature): Option[CTerm] = c match
    case m @ Meta(index) =>
      val resolved = metaVars(index)
      if resolved.context.isEmpty then Some(resolved.ty)
      else None
    case Redex(m @ Meta(index), elims) =>
      val resolved = metaVars(index)
      if resolved.context.size <= elims.size
      then
        val args = elims.take(resolved.context.size).collect { case Elimination.ETerm(t) =>
          t
        }
        Some(resolved.ty.substLowers(args: _*))
      else None
    case _ => None

  def addUnsolved(ty: CTerm)(using Γ: Context): CTerm =
    val meta = addMetaVar(Unsolved(Γ, ty, UmcNothing))
    redex(meta, vars(Γ.size - 1))

  def addGuarded(ty: CTerm, value: CTerm, constraints: Set[Constraint])(using Γ: Context): CTerm =
    val meta = addMetaVar(Guarded(Γ, ty, value, constraints))
    redex(meta, vars(Γ.size - 1))

  private def addMetaVar(mv: MetaVariable): Meta =
    val index = metaVars.size
    metaVars += mv
    Meta(index)

  /** @param value:
    *   value must be in the context of the meta variable. That is, value must be from a call of `adaptForMetaVariable`
    */
  def assignUnsolved
    (m: RUnsolved, value: CTerm)
    (using Γ: Context)
    (using Σ: Signature)
    : Either[IrError, Set[Constraint]] =
    assignValue(m.index, value)
    m.constraint match
      case UmcNothing                    => Right(Set.empty)
      case UmcCSubtype(lowerBound)       => checkIsSubtype(lowerBound, value)
      case UmcVSubtype(lowerBound)       => checkIsSubtype(lowerBound, Collapse(value))
      case UmcEffSubsumption(lowerBound) => checkEffSubsumption(lowerBound, Collapse(value))
      case UmcLevelSubsumption(lowerBound) =>
        checkLevelSubsumption(lowerBound, Collapse(value))
      case UmcUsageSubsumption(upperBound) =>
        checkUsageSubsumption(Collapse(value), upperBound)

  def alignElims(t: CTerm, elims: List[Elimination[VTerm]])(using Signature): Option[CTerm] =
    elims match
      case Nil => Some(t)
      case elims =>
        t match
          case Redex(t, elims2) if elims2.takeRight(elims.size) == elims =>
            Some(redex(t, elims2.dropRight(elims.size)))
          case _ => None

  def adaptForMetaVariable(m: RUnsolved, value: CTerm)(using Signature): Option[CTerm] =
    // Make sure meta variable assignment won't cause cyclic meta variable references.
    if MetaVarVisitor.visitCTerm(value)(m.index) then return None
    val (a, b) = getFreeVars(value)(using 0)
    if (a ++ b -- m.substitution.keySet).nonEmpty then return None
    Some(value.subst(m.substitution.lift))

  def adaptForMetaVariable(m: RUnsolved, value: VTerm)(using Signature): Option[VTerm] =
    // Make sure meta variable assignment won't cause cyclic meta variable references.
    if MetaVarVisitor.visitVTerm(value)(m.index) then return None
    val (a, b) = getFreeVars(value)(using 0)
    if (a ++ b -- m.substitution.keySet).nonEmpty then return None
    Some(value.subst(m.substitution.lift))

  def updateConstraint(u: RUnsolved, constraint: UnsolvedMetaVariableConstraint): Unit =
    metaVars(u.index) match
      case Unsolved(context, ty, _) =>
        metaVars(u.index) = Unsolved(context, ty, constraint)
      case _ => throw IllegalStateException("updateConstraint called on non-unsolved meta variable")

  private def assignValue(index: Nat, value: CTerm): Unit =
    version += 1
    val existing = metaVars(index)
    metaVars(index) = Solved(existing.context, existing.ty, value)

  private def updateGuarded(index: Nat, guarded: Guarded): Unit =
    metaVars(index) = guarded

  def solve(constraints: Set[Constraint])(using Σ: Signature): Either[IrError, Set[Constraint]] =
    var currentConstraints = constraints
    while (solvedVersion != version) {
      solvedVersion = version
      solveOnce(currentConstraints) match
        case Right(newConstraints) => currentConstraints = newConstraints
        case Left(e)               => return Left(e)
    }
    Right(currentConstraints)

  private def solveOnce(constraints: Set[Constraint])(using Σ: Signature): Either[IrError, Set[Constraint]] = boundary:
    val metaVarIndexes = MetaVarCollector.visitConstraints(constraints)
    for index <- metaVarIndexes.toSeq.sorted do
      metaVars(index) match
        case Guarded(context, ty, value, constraints) =>
          solveConstraints(constraints) match
            case Right(newConstraints) =>
              if newConstraints.isEmpty then assignValue(index, value)
              else updateGuarded(index, new Guarded(context, ty, value, newConstraints))
            case Left(e) => break(Left(e))
        case _ => // do nothing
    solveConstraints(constraints)

  private object MetaVarCollector extends Visitor[TypingContext, Set[Nat]]:
    override def visitMeta(m: Meta)(using ctx: TypingContext)(using Σ: Signature): Set[Nat] =
      Set(m.index) ++ {
        ctx.resolveMeta(m) match
          // Include all meta varialbles in the constraints of guarded meta variables so that solving these can potentially
          // turn guarded meta variables to solved ones.
          case Guarded(_, _, _, constraints) => visitConstraints(constraints)
          case _                             => Set[Nat]()
      }

    override def combine(freeVars: Set[Nat]*)(using ctx: TypingContext)(using Σ: Signature): Set[Nat] =
      freeVars.flatten.toSet

    def visitConstraints(constraints: Set[Constraint])(using ctx: TypingContext)(using Σ: Signature): Set[Nat] =
      constraints.flatMap {
        case Constraint.Conversions(_, lhs, rhs, _) =>
          lhs.flatMap(visitVTerm) ++ rhs.flatMap(visitVTerm)
        // TODO[P0]: handle other constraints
        case _ => ???
      }

  private def solveConstraints(constraints: Set[Constraint])(using Σ: Signature): Either[IrError, Set[Constraint]] =
    boundary:
      val result = mutable.Set[Constraint]()
      for constraint <- constraints do
        constraint match
          case Constraint.Conversions(context, lhs, rhs, tys) =>
            checkAreConvertible(lhs, rhs, tys)(using context) match
              case Right(constraints) => result ++= constraints
              case Left(e)            => break(Left(e))
          case Constraint.VConversion(context, lhs, rhs, ty) =>
            checkIsConvertible(lhs, rhs, ty)(using context) match
              case Right(constraints) => result ++= constraints
              case Left(e)            => break(Left(e))
          case Constraint.CConversion(context, lhs, rhs, ty) =>
            checkIsConvertible(lhs, rhs, ty)(using context) match
              case Right(constraints) => result ++= constraints
              case Left(e)            => break(Left(e))
          case Constraint.VSubType(context, sub, sup) =>
            checkIsSubtype(sub, sup)(using context) match
              case Right(constraints) => result ++= constraints
              case Left(e)            => break(Left(e))
          case Constraint.CSubType(context, sub, sup) =>
            checkIsSubtype(sub, sup)(using context) match
              case Right(constraints) => result ++= constraints
              case Left(e)            => break(Left(e))
          case Constraint.EffSubsumption(context, sub, sup) =>
            checkEffSubsumption(sub, sup)(using context) match
              case Right(constraints) => result ++= constraints
              case Left(e)            => break(Left(e))

          case _ => ???
      Right(result.toSet)

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

extension (us1: Usages)
  infix def +(us2: Usages): Usages =
    if us1.size != us2.size then throw IllegalArgumentException("mismatched size")
    else us1.zip(us2).map { (u1, u2) => UsageSum(u1, u2) }

  infix def *(scalar: VTerm): Usages = us1.map(u => UsageProd(u, scalar))
  infix def *(scalar: Usage)(using SourceInfo): Usages =
    us1.map(u => UsageProd(u, UsageLiteral(scalar)))

def checkData(data: Data)(using Σ: Signature)(using ctx: TypingContext): Either[IrError, Data] =
  ctx.trace(s"checking data signature ${data.qn}") {
    given Context = IndexedSeq()

    for
      tParamsTysTelescope <- checkParameterTypeDeclarations(data.tParamTys.map(_._1).toTelescope)
      tParamTys = Context.fromTelescope(tParamsTysTelescope)
      tIndexTys <- checkParameterTypeDeclarations(data.tIndexTys)(using tParamTys)
      tContext = tParamTys ++ tIndexTys
      (level, _) <- checkLevel(data.level)(using tContext)
      (inherentEqDecidability, _) <- checkType(data.inherentEqDecidability, EqDecidabilityType())(using
        tContext,
      )
      _ <- checkTParamsAreUnrestricted(tContext.toTelescope)
    yield Data(data.qn)(
      tParamTys.zip(data.tParamTys.map(_._2)),
      tIndexTys,
      level,
      inherentEqDecidability,
    )
  }

def checkDataConstructor
  (qn: QualifiedName, con: Constructor)
  (using Σ: Signature)
  (using ctx: TypingContext)
  : Either[IrError, Constructor] =
  ctx.trace(s"checking data constructor $qn.${con.name}") {
    Σ.getDataOption(qn) match
      case None => Left(MissingDeclaration(qn))
      case Some(data) =>
        given Γ: Context = data.tParamTys.map(_._1)
        for
          paramTys <- checkParameterTypeDeclarations(con.paramTys, Some(data.level))
          (tArgs, _) <- checkTypes(con.tArgs, data.tIndexTys.weaken(con.paramTys.size, 0))(using
            Γ ++ paramTys,
          )
          _ <- checkInherentEqDecidable(Σ.getData(qn), con)
          _ <- {
            // binding of positiveVars must be either covariant or invariant
            // binding of negativeVars must be either contravariant or invariant
            val (positiveVars, negativeVars) = getFreeVars(con.paramTys)(using 0)
            val tParamTysSize = data.tParamTys.size
            val bindingWithIncorrectUsage = data.tParamTys.zipWithIndex.filter { case ((_, variance), reverseIndex) =>
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
        yield Constructor(con.name, paramTys, tArgs)
  }

def checkRecord(record: Record)(using Σ: Signature)(using ctx: TypingContext): Either[IrError, Record] =
  ctx.trace(s"checking record signature ${record.qn}") {
    given Context = IndexedSeq()

    val tParams = record.tParamTys.map(_._1)
    for
      tParamTysTelescope <- checkParameterTypeDeclarations(tParams.toList)
      tParamTys = Context.fromTelescope(tParamTysTelescope)
      _ <- checkTParamsAreUnrestricted(tParams.toList)
      (level, _) <- checkLevel(record.level)(using tParams.toIndexedSeq)
    yield Record(record.qn)(tParamTys.zip(record.tParamTys.map(_._2)), level, record.selfName)
  }

def checkRecordField
  (qn: QualifiedName, field: Field)
  (using Σ: Signature)
  (using ctx: TypingContext)
  : Either[IrError, Field] =
  ctx.trace(s"checking record field $qn.${field.name}") {
    Σ.getRecordOption(qn) match
      case None => Left(MissingDeclaration(qn))
      case Some(record) =>
        given Context =
          record.tParamTys.map(_._1).toIndexedSeq :+ getRecordSelfBinding(
            record,
          )

        for
          (ty, _) <- checkIsCType(field.ty, Some(record.level.weakened))
          _ <-
            // binding of positiveVars must be either covariant or invariant
            // binding of negativeVars must be either contravariant or invariant
            val (positiveVars, negativeVars) = getFreeVars(field.ty)(using 0)
            val tParamTysSize = record.tParamTys.size
            val bindingWithIncorrectUsage = record.tParamTys.zipWithIndex.filter { case ((_, variance), reverseIndex) =>
              val index =
                tParamTysSize - reverseIndex // Offset by 1 to accommodate self reference
              variance match
                case Variance.INVARIANT     => false
                case Variance.COVARIANT     => negativeVars(index)
                case Variance.CONTRAVARIANT => positiveVars(index)
            }
            if bindingWithIncorrectUsage.isEmpty then Right(())
            else
              Left(
                IllegalVarianceInRecord(
                  record.qn,
                  bindingWithIncorrectUsage.map(_._2),
                ),
              )
        yield Field(field.name, ty)
  }

def getRecordSelfBinding(record: Record): Binding[VTerm] = Binding(
  U(
    RecordType(
      record.qn,
      (record.tParamTys.size - 1).to(0, -1).map(Var(_)).toList,
      Total(),
    ),
  ),
  U1,
)(record.selfName)

def checkDef(definition: Definition)(using Σ: Signature)(using ctx: TypingContext): Either[IrError, Definition] =
  ctx.trace(s"checking def signature ${definition.qn}") {
    given Context = IndexedSeq()

    for (ty, _) <- checkIsCType(definition.ty)
    yield Definition(definition.qn)(ty)
  }

def checkEffect(effect: Effect)(using Σ: Signature)(using ctx: TypingContext): Either[IrError, Effect] =
  ctx.trace(s"checking effect signature ${effect.qn}") {
    given Context = IndexedSeq()

    for
      telescope <- checkParameterTypeDeclarations(effect.tParamTys.toTelescope)
      _ <- checkTParamsAreUnrestricted(telescope)
      _ <- checkAreEqDecidableTypes(telescope)
    yield Effect(effect.qn)(telescope.reverse.toIndexedSeq, effect.continuationUsage)
  }

def checkOperation
  (qn: QualifiedName, operation: Operation)
  (using Σ: Signature)
  (using ctx: TypingContext)
  : Either[IrError, Operation] =
  ctx.trace(s"checking effect operation $qn.${operation.name}") {
    Σ.getEffectOption(qn) match
      case None => Left(MissingDeclaration(qn))
      case Some(effect) =>
        val Γ = effect.tParamTys.toIndexedSeq

        for
          paramTys <- checkParameterTypeDeclarations(operation.paramTys)(using Γ)
          (resultTy, _) <- checkIsType(operation.resultTy)(using Γ ++ operation.paramTys)
          (resultUsage, _) <- checkType(operation.resultUsage, UsageType(None))
        yield operation.copy(paramTys = paramTys, resultTy = resultTy, resultUsage = resultUsage)
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
      constarints <- checkUsageSubsumption(binding.usage, UsageLiteral(UUnres)).flatMap(ctx.solve)
      _ <- constarints.isEmpty match
        case true  => Right(())
        case false => Left(ExpectUnrestrictedTypeParameterBinding(binding))
      _ <- checkTParamsAreUnrestricted(rest)(using Γ :+ binding)
    yield ()

private def checkParameterTypeDeclarations
  (tParamTys: Telescope, levelBound: Option[VTerm] = None)
  (using Γ: Context)
  (using Σ: Signature)
  (using ctx: TypingContext)
  : Either[IrError, Telescope] = tParamTys match
  case Nil => Right(Nil)
  case binding :: rest =>
    for
      (ty, _) <- checkIsType(binding.ty, levelBound)
      _ <- checkIsEqDecidableTypes(ty)
      (usage, _) <- checkType(binding.usage, UsageType(None))
      rest <- checkParameterTypeDeclarations(rest)(using Γ :+ binding)
    yield Binding(ty, usage)(binding.name) :: rest

private def checkLevel
  (level: VTerm)
  (using Γ: Context)
  (using Σ: Signature)
  (using ctx: TypingContext)
  : Either[IrError, (VTerm, Usages)] = checkType(level, LevelType(LevelUpperBound()))

// Precondition: tm is already type-checked and is normalized
private def inferLevel
  (tm: VTerm)
  (using Γ: Context)
  (using Σ: Signature)
  (using ctx: TypingContext)
  : Either[IrError, VTerm] =
  tm match
    case Type(upperBound) => inferLevel(upperBound).map(LevelSuc(_))
    case Top(level, eqD)  => Right(level)
    case r: Var =>
      Γ.resolve(r).ty match
        case Type(upperBound) => inferLevel(upperBound)
        case _                => Left(NotTypeError(tm))
    // TODO[P0]: this is not right, we need to handle collapse of redux here.
    case Collapse(cTm)      => inferLevel(cTm)
    case U(cty)             => inferLevel(cty)
    case DataType(qn, args) => Right(Σ.getData(qn).level.substLowers(args: _*))
    case _: UsageType | _: EqDecidabilityType | _: EffectsType | _: HeapType =>
      Right(LevelLiteral(0))
    case LevelType(upperBound) =>
      for (upperBound, _) <- checkLevel(upperBound)
      yield LevelSuc(upperBound)
    case CellType(_, ty) => inferLevel(ty)
    case _               => throw IllegalArgumentException(s"should have been checked to be a type: $tm")

def inferType
  (tm: VTerm)
  (using Γ: Context)
  (using Σ: Signature)
  (using ctx: TypingContext)
  : Either[IrError, (VTerm, VTerm, Usages)] = debugInfer(tm):
  tm match
    case Type(upperBound) =>
      for
        (upperBound, upperBoundUsages) <- checkIsType(upperBound)
        upperBound <- upperBound.normalized
        newTm = Type(upperBound)(using tm.sourceInfo)
      yield (newTm, Type(newTm), upperBoundUsages)
    case Top(level, eqD) =>
      for
        (level, ulUsage) <- checkLevel(level)
        (eqD, eqDUsage) <- checkType(eqD, EqDecidabilityType())
        eqD <- eqD.normalized
        newTm = Top(level, eqD)(using tm.sourceInfo)
      yield (newTm, Type(newTm), (ulUsage + eqDUsage))
    case r: Var => Right(r, Γ.resolve(r).ty, Usages.single(r))
    case Collapse(cTm) =>
      for
        case (cTm, cTy, usage) <- inferType(cTm)
        case (vTy, u) <- cTy match
          case F(vTy, eff, u) if isTotal(cTm, Some(cTy)) => Right((vTy, u))
          case F(_, _, _)                                => Left(CollapsingEffectfulTerm(cTm))
          case _                                         => Left(NotCollapsable(cTm))
      yield (Collapse(cTm), vTy, usage)
    case U(cty) =>
      for
        case (cty, ctyTy, usage) <- inferType(cty)
        newTm <- Collapse(cty)(using tm.sourceInfo).normalized
        r <- ctyTy match
          case CType(_, eff) if isTotal(cty, Some(ctyTy)) => Right(Type(newTm))
          // Automatically promote SomeVType to F(SomeVType)
          case F(Type(_), eff, _) if isTotal(cty, Some(ctyTy)) => Right(Type(newTm))
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
    case u: UsageType =>
      for result <- transpose(
          u.upperBound.map(upperBound => checkType(upperBound, UsageType(None))),
        )
      yield result match
        case Some(upperBound, usages) => (u, Type(UsageType(Some(upperBound))), usages)
        case _                        => (u, Type(u), Usages.zero)
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
    case LevelType(order) => Right(LevelType(order), (Type(LevelType(order))), Usages.zero)
    case Level(op, maxOperands) =>
      for
        (operands, usages) <- transposeCheckTypeResults(maxOperands.map { (ref, _) =>
          checkLevel(ref)
        })
        newTm = Level(op, operands.toMultiset)(using tm.sourceInfo)
      yield (newTm, LevelType(newTm), usages)
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
    case Auto()     => throw IllegalArgumentException("cannot infer type")

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
    case c @ Con(name, args) =>
      ty match
        case dataType @ DataType(qn, tArgs) =>
          Σ.getConstructorOption(qn, name) match
            case None => Left(MissingConstructor(name, qn))
            case Some(con) =>
              val data = Σ.getData(qn)
              val tParamArgs = tArgs.take(data.tParamTys.size)
              val tIndexArgs = tArgs.drop(data.tParamTys.size)
              for
                (args, usages) <- checkTypes(args, con.paramTys.substLowers(tParamArgs: _*))
                constraints <- checkAreConvertible(
                  con.tArgs.map(_.substLowers(tParamArgs ++ args: _*)),
                  tIndexArgs,
                  data.tIndexTys.substLowers(tParamArgs: _*),
                ).flatMap(ctx.solve)
                _ <-
                  if constraints.isEmpty then Right(())
                  else Left(UnmatchedDataIndex(c, dataType))
              yield (DataType(qn, args), usages)
        case _ => Left(ExpectDataType(ty))
    case Cell(heapKey, _) =>
      ty match
        case CellType(heap, _) if Heap(heapKey) == heap => Right(tm, Usages.zero)
        case _: CellType                                => Left(ExpectCellTypeWithHeap(heapKey))
        case _                                          => Left(ExpectCellType(ty))
    case Auto() =>
      Right(
        (
          Collapse(ctx.addUnsolved(F(ty))),
          Usages.zero,
        ),
      )
    case _ =>
      for
        case (newTm, inferred, usages) <- inferType(tm)
        constraints <- checkIsSubtype(inferred, ty)
        _ <-
          if constraints.isEmpty then Right(())
          else Left(NotVSubsumption(inferred, ty, None))
      yield (newTm, usages),
)

// Precondition: tm is already type-checked
private def inferLevel
  (tm: CTerm)
  (using Γ: Context)
  (using Σ: Signature)
  (using ctx: TypingContext)
  : Either[IrError, VTerm] =
  for
    tm <- Reducible.reduce(tm)
    level <- tm match
      case CType(upperBound, effects) => inferLevel(upperBound).map(LevelSuc(_))
      case CTop(level, effects)       => Right(level)
      case F(vTy, effects, usage)     => inferLevel(vTy)
      case FunctionType(binding, bodyTy, effects) =>
        for
          argLevel <- inferLevel(binding.ty)
          bodyLevel <- inferLevel(bodyTy)(using Γ :+ binding)
        // strengthen is always safe because the only case that bodyLevel would reference 0 is when
        // arg is of type Level. But in that case the overall level would be ω.
        yield LevelMax(argLevel.weakened, bodyLevel).strengthened
      case RecordType(qn, args, effects) => Right(Σ.getRecord(qn).level.substLowers(args: _*))
      case tm =>
        ctx.resolveMetaVariableType(tm) match
          case Some(ty) =>
            ty match
              // TODO[P1]: consider refactor this to use some helper function for such common patterns where we create a
              // stub term when expecting the meta variable to match certain structure.
              case CType(upperBound, _) => inferLevel(upperBound)
              case cty =>
                val level = ctx.addUnsolved(F(LevelType(LevelUpperBound())))
                val usage = ctx.addUnsolved(F(UsageType()))
                for
                  constraints <- checkIsConvertible(
                    cty,
                    CType(CTop(Collapse(level)), Collapse(usage)),
                    None,
                  )
                  constraints <- ctx.solve(constraints)
                  l <-
                    if constraints.isEmpty then Collapse(level).normalized
                    else Left(NotCTypeError(tm))
                yield l
          case _ => Left(NotCTypeError(tm))
  yield level

def inferType
  (tm: CTerm)
  (using Γ: Context)
  (using Σ: Signature)
  (using ctx: TypingContext)
  : Either[IrError, (CTerm, CTerm, Usages)] = debugInfer(tm):
  for
    tm <- tm.normalized
    r <- tm match
      case Hole =>
        throw IllegalArgumentException(
          "hole should only be present during reduction",
        )
      case CType(upperBound, effects) =>
        for
          (effects, effUsages) <- checkType(effects, EffectsType())
          (upperBound, upperBoundUsages) <- checkIsCType(upperBound)
          upperBound <- reduceCType(upperBound)
          effects <- effects.normalized
          newTm = CType(upperBound, effects)
        yield (
          newTm,
          CType(newTm, Total()),
          (effUsages + upperBoundUsages),
        )
      case CTop(level, effects) =>
        for
          (effects, uUsages) <- checkType(effects, EffectsType())
          (level, ulUsages) <- checkLevel(level)
          effects <- effects.normalized
          newTm = CTop(level, effects)(using tm.sourceInfo)
        yield (newTm, CType(newTm, Total()), (uUsages + ulUsages))
      case m: Meta => Right(m, ctx.resolveMeta(m).contextFreeType, Usages.zero)
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
            case U(cty) => Right(augmentEffect(MaybeDiv(), cty))
            case _      => Left(ExpectUType(vTy))
        yield (Force(v), cTy, vUsages)
      case F(vTy, effects, usage) =>
        for
          (effects, effUsages) <- checkType(effects, EffectsType())
          (usage, uUsages) <- checkType(usage, UsageType(None))
          // Prevent returning value of U0 usage, which does not make sense.
          usageConstraints <- checkUsageSubsumption(usage, UsageLiteral(Usage.U1))
            .flatMap(ctx.solve)
          _ <-
            if usageConstraints.isEmpty then Right(())
            else Left(NotVSubsumption(usage, UsageLiteral(Usage.U1), Some(UsageType())))
          case (vTy, vTyTy, vTyUsages) <- inferType(vTy)
          vTy <- vTy.normalized
          usage <- usage.normalized
          newTm = F(vTy, effects, usage)(using tm.sourceInfo)
          cTyTy <- vTyTy match
            case Type(_) => Right(CType(newTm, Total()))
            case _       => Left(NotTypeError(vTy))
        yield (newTm, cTyTy, (effUsages + uUsages + vTyUsages))
      case Return(v) =>
        for case (v, vTy, vUsages) <- inferType(v)
        yield (Return(v), F(vTy, Total()), vUsages)
      case tm: Let => checkLet(tm, None)
      case FunctionType(binding, bodyTy, effects) =>
        for
          (effects, effUsages) <- checkType(effects, EffectsType())
          effects <- effects.normalized
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
                  case CType(_, eff) if isTotal(bodyTy, Some(bodyTyTy)) =>
                    // Strengthen is safe here because if it references the binding, then the
                    // binding must be at level ω and hence ULevelMax would return big type.
                    // Also, there is no need to check the dropped usage because usages in types
                    // is always multiplied by U0.
                    Right(
                      newTm,
                      CType(newTm, Total()),
                      bodyTyUsages.dropRight(1).map(_.strengthened),
                    )
                  // TODO[P3]: think about whether the following is actually desirable
                  // Automatically promote Return(SomeVType) to F(SomeVType) and proceed type
                  // inference.
                  case F(Type(_), eff, _) if isTotal(bodyTy, Some(bodyTyTy)) =>
                    Right(
                      newTm,
                      CType(newTm, Total()),
                      bodyTyUsages.dropRight(1).map(_.strengthened),
                    )
                  case CType(_, _) | F(Type(_), _, _) =>
                    Left(EffectfulCTermAsType(bodyTy))
                  case _ => Left(NotCTypeError(bodyTy))
              yield r
            case _ => Left(NotTypeError(binding.ty))
        yield (newTm, funTyTy, (effUsages + tyUsages + bodyTyUsages + bindingUsageUsages))
      case Redex(c, elims) =>
        def checkElims
          (checkedElims: List[Elimination[VTerm]], cty: CTerm, elims: List[Elimination[VTerm]])
          : Either[IrError, (List[Elimination[VTerm]], CTerm, Usages)] =
          elims match
            case Nil => Right(Nil, cty, Usages.zero)
            case (e @ ETerm(arg)) :: rest =>
              cty match
                case FunctionType(binding, bodyTy, effects) =>
                  for
                    (arg, argUsages) <- checkType(arg, binding.ty)
                    cty <- reduceCType(bodyTy.substLowers(arg))
                    (rest, cty, restUsages) <- checkElims(e :: checkedElims, cty, rest)
                  yield (ETerm(arg) :: rest, augmentEffect(effects, cty), (argUsages + restUsages))
                case _ => Left(ExpectFunction(redex(c, checkedElims.reverse)))
            case (e @ EProj(name)) :: rest =>
              cty match
                case RecordType(qn, args, effects) =>
                  Σ.getFieldOption(qn, name) match
                    case None => Left(MissingField(name, qn))
                    case Some(f) =>
                      for
                        cty <- reduceCType(
                          f.ty.substLowers(args :+ Thunk(redex(c, checkedElims)): _*),
                        )
                        (rest, cty, restUsages) <- checkElims(e :: checkedElims, cty, rest)
                      yield (EProj(name) :: rest, augmentEffect(effects, cty), restUsages)
                case _ => Left(ExpectRecord(redex(c, checkedElims.reverse)))
        for
          (c, cty, usages) <- inferType(c)
          (elims, cty, argUsages) <- checkElims(Nil, cty, elims)
        yield (redex(c, elims), cty, (usages + argUsages))
      case RecordType(qn, args, effects) =>
        Σ.getRecordOption(qn) match
          case None => Left(MissingDeclaration(qn))
          case Some(record) =>
            for
              (effects, effUsages) <- checkType(effects, EffectsType())
              (args, argsUsages) <- checkTypes(args, record.tParamTys.map(_._1).toList)
            yield (RecordType(qn, args, effects), CType(tm, Total()), (effUsages + argsUsages))
      case OperationCall((qn, tArgs), name, args) =>
        Σ.getEffectOption(qn) match
          case None => Left(MissingDeclaration(qn))
          case Some(effect) =>
            Σ.getOperationOption(qn, name) match
              case None => Left(MissingDefinition(qn))
              case Some(op) =>
                for
                  (tArgs, effUsages) <- checkTypes(tArgs, effect.tParamTys.toList)
                  tArgs <- transpose(tArgs.map(_.normalized))
                  (args, argsUsages) <- checkTypes(args, op.paramTys.substLowers(tArgs: _*))
                  newEff = (qn, tArgs)
                  newTm = OperationCall(newEff, name, args)(using tm.sourceInfo)
                  ty <- op.resultTy.substLowers(tArgs ++ args: _*).normalized
                yield (
                  newTm,
                  F(
                    ty,
                    // TODO[p4]: figure out if there is way to better manage divergence for handler
                    // operations. The dynamic nature of handler dispatching makes it impossible to
                    // know at compile time whether this would lead to a cyclic reference in
                    // computations.
                    EffectsLiteral(Set(newEff, (Builtins.MaybeDivQn, Nil))),
                  ),
                  effUsages + argsUsages,
                )
      case _: Continuation | _: ContinuationReplicationState | _: ContinuationReplicationStateAppender =>
        throw IllegalArgumentException(
          "continuation is only created in reduction and hence should not be type checked.",
        )
      case h: Handler => checkHandler(h, None)
      case AllocOp(heap, vTy, value) =>
        for
          (heap, heapUsages) <- checkType(heap, HeapType())
          heap <- heap.normalized
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
      case h: HeapHandler => checkHeapHandler(h, None)
  yield r

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
        constraints <- checkIsSubtype(tmTy, ty).flatMap(ctx.solve)
        _ <-
          if constraints.isEmpty then Right(())
          else Left(NotCSubsumption(tmTy, ty, None))
      yield (tm, usages),
)
private object MetaVarVisitor extends Visitor[TypingContext, Set[Int]]() {
  override def combine(rs: Set[Int]*)(using ctx: TypingContext)(using Σ: Signature): Set[Int] =
    rs.flatten.to(Set)
  override def visitMeta(m: Meta)(using ctx: TypingContext)(using Σ: Signature): Set[Int] =
    Set(m.index) ++ (ctx.resolveMeta(m) match
      // bounds in unsolved doesn't need to be checked now. They will be checked when they become solved.
      case _: Unsolved             => Set.empty
      case Guarded(_, _, value, _) => visitCTerm(value)
      case Solved(_, _, value)     => visitCTerm(value)
    )
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
          constraints <- checkEqDecidabilitySubsumption(eqD, dataEqD)
          _ <- constraints.isEmpty match
            case true  => Right(())
            case false => Left(NotEqDecidableType(binding.ty))
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
      checkUsageSubsumption(usage, UsageLiteral(U1)) match
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

  checkIsConvertible(
    data.inherentEqDecidability,
    EqDecidabilityLiteral(EqUnknown),
    Some(EqDecidabilityType()),
  ) match
    // short circuit since there is no need to do any check
    case Right(_) => Right(())
    // Call 1, 2, 3
    case _ =>
      for
        _ <- checkComponentTypes(
          constructor.paramTys,
          data.inherentEqDecidability,
        )
        _ <- checkComponentUsage(constructor)
      yield ()

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
  case _: Type | _: UsageType | _: EqDecidabilityType | _: EffectsType | _: LevelType | _: HeapType | _: CellType =>
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
    constraints <- checkIsConvertible(
      eqD,
      EqDecidabilityLiteral(EqDecidable),
      Some(EqDecidabilityType()),
    )
    r <- constraints.isEmpty match
      case true  => Right(())
      case false => Left(NotEqDecidableType(ty))
  yield r

private def checkAreEqDecidableTypes
  (telescope: Telescope)
  (using Γ: Context)
  (using Σ: Signature)
  (using ctx: TypingContext)
  : Either[IrError, Telescope] = telescope match
  case Nil => Right(Nil)
  case binding :: telescope =>
    for
      ty <- checkIsEqDecidableTypes(binding.ty)
      rest <- checkAreEqDecidableTypes(telescope)(using Γ :+ binding)
    yield telescope

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
  for _ <- transpose(usages.takeRight(count).reverse.zipWithIndex.map { (v, i) =>
      for
        constraint <- checkUsageSubsumption(v, Γ.resolve(i).usage)
        r <-
          if constraint.isEmpty then Right(())
          else Left(NotUsageSubsumption(v, Γ.resolve(i).usage))
      yield ()
    })
  yield usages.drop(count).map { v =>
    try v.strengthen(count, 0)
    catch
      // It's possible for a term's usage to reference a usage term after it. For example consider
      // functino `f: u: Usage -> [u] Nat -> Nat` and context `{i: Nat, u: Usage}`, then `f u i`
      // has usage `[u, U1]`. In this case, strengthen usage of `i` is approximated by UUnres.
      case _: StrengthenException => UsageLiteral(Usage.UUnres)
  }

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
  (resultsAndUsages: Iterable[Either[IrError, (R, Usages)]])
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
      // TODO[P0]: this is not safe!! conversion check could instantiate meta varaibles!!
      def areTUsagesZeroOrUnrestricted: Boolean =
        tUsages.forall { usage =>
          toBoolean(
            checkIsConvertible(usage, UsageLiteral(Usage.UUnres), Some(UsageType())),
          ) ||
          toBoolean(
            checkIsConvertible(usage, UsageLiteral(Usage.U0), Some(UsageType())),
          )
        }
      if isTotal(t, Some(F(ty, effects, usage))) && areTUsagesZeroOrUnrestricted then
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
              for
                (bodyTy, _) <- checkIsCType(bodyTy)
                (newBody, usages) <- checkType(newBody, bodyTy)
              yield (newBody, bodyTy, usages)
            case None => inferType(newBody)
        yield r
      // Otherwise, just add the binding to the context and continue type checking.
      else
        for
          case (body, bodyTy, usagesInBody) <- bodyTy match
            case None => inferType(body)(using Γ :+ Binding(ty, usage)(gn"v"))
            case Some(bodyTy) =>
              for
                (bodyTy, _) <- checkIsCType(bodyTy)
                (body, usages) <- checkType(body, bodyTy.weakened)(using
                  Γ :+ Binding(ty, usage)(gn"v"),
                )
              yield (body, bodyTy, usages)
          // Report an error if the type of `body` needs to reference the effectful
          // computation. User should use a dependent sum type to wrap such
          // references manually to avoid the leak.
          // TODO[P3]: in case weakened failed, provide better error message: ctxTy cannot depend on
          //  the bound variable
          _ <- checkVar0Leak(
            bodyTy,
            LeakedReferenceToEffectfulComputationResult(t),
          )
          constraints <- checkUsageSubsumption(usagesInBody.last.strengthened, usage)
          _ <-
            if constraints.isEmpty then Right(())
            else Left(NotVSubsumption(usagesInBody.last.strengthened, usage, Some(UsageType())))
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
    outputUsage <- outputUsage.normalized
    outputCType = F(outputType, outputEffects, outputUsage)
    transformΓ = Γ :+ newParameterBinding :+ inputBinding.weakened
    (outputUsage, _) <- checkType(outputUsage, UsageType(None))
    (transform, transformUsages) <- checkType(transform, outputCType.weaken(2, 0))(using transformΓ)
    transformUsages <- verifyUsages(transformUsages)(2)
    effConstraints <- checkEffSubsumption(
      inputEff,
      EffectsUnion(outputEffects, eff),
    )
    _ <-
      if effConstraints.isEmpty then Right(())
      else Left(NotVSubsumption(inputEff, EffectsUnion(outputEffects, eff), Some(EffectsType())))
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
                case (opParamTys, opOutputTy) <- opDecl.continuationUsage match
                  case Some(continuationUsage) =>
                    resumeNameOption match
                      case Some(resumeName) =>
                        for outputTypeLevel <- inferLevel(outputType)
                        yield (
                          opParamTys :+
                            Binding(
                              U(
                                RecordType(
                                  Builtins.ContinuationQn,
                                  List(
                                    outputTypeLevel,
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
                  case qn                            => throw IllegalStateException(s"bad operation name $qn")
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
  (vTy: VTerm, levelBound: Option[VTerm] = None)
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
                level <- inferLevel(vTy)
                _ <- checkLevelSubsumption(level, bound)
              yield ()
            case _ => Right(())
        case _ => Left(NotTypeError(vTy))
    yield (vTy, usages)
  }

def checkIsCType
  (cTy: CTerm, levelBound: Option[VTerm] = None)
  (using Γ: Context)
  (using Σ: Signature)
  (using ctx: TypingContext)
  : Either[IrError, (CTerm, Usages)] =
  ctx.trace("checking is C type") {
    for
      case (cty, cTyTy, usages) <- inferType(cTy)
      _ <- cTyTy match
        case CType(_, eff) if isTotal(cty, Some(cTyTy)) =>
          levelBound match
            case Some(bound) =>
              for
                level <- inferLevel(cTy)
                _ <- checkLevelSubsumption(level, bound)
              yield ()
            case _ => Right(())
        case _: CType => Left(EffectfulCTermAsType(cTy))
        case _        => Left(NotCTypeError(cTy))
      cty <- reduceCType(cty)
    yield (cty, usages)
  }

def reduceUsage(usage: CTerm)(using Γ: Context)(using Σ: Signature)(using ctx: TypingContext): Either[IrError, VTerm] =
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

def reduceVType(vTy: CTerm)(using Γ: Context)(using Σ: Signature)(using ctx: TypingContext): Either[IrError, VTerm] =
  ctx.trace("reduce V type", Block(yellow(vTy.sourceInfo), pprint(vTy))) {
    for
      case (vTy, tyTy, _) <- inferType(vTy)
      r <- tyTy match
        case F(Type(_), effect, _) if isTotal(vTy, Some(tyTy)) =>
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

def reduceCType(cTy: CTerm)(using Γ: Context)(using Σ: Signature)(using ctx: TypingContext): Either[IrError, CTerm] =
  ctx.trace("reduce C type", Block(yellow(cTy.sourceInfo), pprint(cTy))) {
    cTy match
      case _: CType | _: F | _: FunctionType | _: RecordType | _: CTop =>
        Right(cTy)
      case _ =>
        for
          case (cTy, cTyTy, _) <- inferType(cTy)
          r <- cTyTy match
            case CType(_, eff) if isTotal(cTy, Some(cTyTy)) => reduce(cTy)
            case F(_, eff, _) if isTotal(cTy, Some(cTyTy)) =>
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
  case CTop(level, effects)   => CTop(level, EffectsUnion(eff, effects))
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

private def checkVar0Leak(ty: CTerm | VTerm, error: => IrError)(using Σ: Signature): Either[IrError, Unit] =
  val (positiveFreeVars, negativeFreeVars) = ty match
    case ty: CTerm => getFreeVars(ty)(using 0)
    case ty: VTerm => getFreeVars(ty)(using 0)
  if positiveFreeVars(0) || negativeFreeVars(0) then Left(error)
  else Right(())

// TODO: delete this.
def allRight[L](es: Iterable[Either[L, ?]]): Either[L, Unit] =
  es.first {
    case Left(l) => Some(l)
    case _       => None
  } match
    case Some(l) => Left(l)
    case _       => Right(())

private object CollapseFinder extends Visitor[Unit, Boolean]:
  override def combine(rs: Boolean*)(using ctx: Unit)(using Σ: Signature): Boolean =
    rs.exists(b => b)
  override def visitCollapse(collapse: Collapse)(using ctx: Unit)(using Σ: Signature): Boolean =
    true

def hasCollapse(t: VTerm)(using Σ: Signature): Boolean = CollapseFinder.visitVTerm(t)(using ())

private def extractDistinctArgVars(args: Seq[VTerm]): Option[List[Nat]] =
  val argVars = args.collect { case v: Var => v.idx }
  if argVars.distinct.length == argVars.length then Some(argVars.toList)
  else None

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
  (tm: R)
  (result: => Either[L, (R, R, Usages)])
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
