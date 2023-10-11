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
import z3.scala.dsl.Eq
import scala.annotation.meta.param

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
  case UmcCSubtype(lowerBounds: Set[CTerm])
  case UmcVSubtype(lowerBounds: Set[VTerm])
  case UmcEffSubsumption(lowerBound: VTerm)
  case UmcLevelSubsumption(lowerBound: VTerm)
  case UmcUsageSubsumption(upperBound: VTerm)

  def substLowers(args: VTerm*)(using Signature): UnsolvedMetaVariableConstraint = this match
    case UmcNothing => UmcNothing
    case UmcCSubtype(lowerBounds) =>
      UmcCSubtype(lowerBounds.map(_.substLowers(args: _*)))
    case UmcVSubtype(lowerBounds) =>
      UmcVSubtype(lowerBounds.map(_.substLowers(args: _*)))
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
  def ty: CTerm

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
  case RGuarded(ty: CTerm)
  case RSolved(ty: CTerm)
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
        val args = elims.take(context.size).collect { case Elimination.ETerm(t) => t }
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
      case Solved(context, ty, _) =>
        val args = elims.take(context.size).collect { case Elimination.ETerm(t) => t }
        Some(RSolved(ty.substLowers(args: _*)), elims.drop(context.size))
      case Guarded(context, ty, _, _) =>
        val args = elims.take(context.size).collect { case Elimination.ETerm(t) => t }
        Some(RGuarded(ty.substLowers(args: _*)), elims.drop(context.size))

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
      case UmcNothing               => Right(Set.empty)
      case UmcCSubtype(lowerBounds) => transpose(lowerBounds.map(checkIsSubtype(_, value))).map(_.flatten)
      case UmcVSubtype(lowerBounds) => transpose(lowerBounds.map(checkIsSubtype(_, Collapse(value)))).map(_.flatten)
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

  def checkSolved
    (constraints: Either[IrError, Set[Constraint]], error: => IrError)
    (using Σ: Signature)
    : Either[IrError, Unit] =
    for
      constraints <- constraints
      r <- solve(constraints).flatMap { constraints =>
        if constraints.isEmpty then Right(())
        else Left(error)
      }
    yield r

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
        // TODO[P0]: we probably want to also assign values to bounded unsolved meta variables. Also, it may make sense
        // to pass in a variable that controls when to solve those to allow more fined-grained controls.
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
        case Constraint.Conversions(_, lhs, rhs, _)            => lhs.flatMap(visitVTerm) ++ rhs.flatMap(visitVTerm)
        case Constraint.VConversion(_, lhs, rhs, _)            => visitVTerm(lhs) ++ visitVTerm(rhs)
        case Constraint.CConversion(_, lhs, rhs, _)            => visitCTerm(lhs) ++ visitCTerm(rhs)
        case Constraint.VSubType(_, sub, sup)                  => visitVTerm(sub) ++ visitVTerm(sup)
        case Constraint.CSubType(_, sub, sup)                  => visitCTerm(sub) ++ visitCTerm(sup)
        case Constraint.EffSubsumption(_, sub, sup)            => visitVTerm(sub) ++ visitVTerm(sup)
        case Constraint.LevelSubsumption(_, sub, sup)          => visitVTerm(sub) ++ visitVTerm(sup)
        case Constraint.UsageSubsumption(_, sub, sup)          => visitVTerm(sub) ++ visitVTerm(sup)
        case Constraint.EqDecidabilitySubsumption(_, sub, sup) => visitVTerm(sub) ++ visitVTerm(sup)
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
          case Constraint.LevelSubsumption(context, sub, sup) =>
            checkLevelSubsumption(sub, sup)(using context) match
              case Right(constraints) => result ++= constraints
              case Left(e)            => break(Left(e))
          case Constraint.UsageSubsumption(context, sub, sup) =>
            checkUsageSubsumption(sub, sup)(using context) match
              case Right(constraints) => result ++= constraints
              case Left(e)            => break(Left(e))
          case Constraint.EqDecidabilitySubsumption(context, sub, sup) =>
            checkEqDecidabilitySubsumption(sub, sup)(using context) match
              case Right(constraints) => result ++= constraints
              case Left(e)            => break(Left(e))
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

  infix def |(us2: Usages): Usages =
    if us1.size != us2.size then throw IllegalArgumentException("mismatched size")
    else us1.zip(us2).map { (u1, u2) => UsageJoin(u1, u2) }

  infix def *(scalar: VTerm): Usages = us1.map(u => UsageProd(u, scalar))
  infix def *(scalar: Usage)(using SourceInfo): Usages =
    us1.map(u => UsageProd(u, UsageLiteral(scalar)))

def checkData(data: Data)(using Σ: Signature)(using ctx: TypingContext): Either[IrError, Data] =
  ctx.trace(s"checking data signature ${data.qn}") {
    given Context = IndexedSeq()

    for
      tParamsTysTelescope <- checkparameterTyDeclarations(data.tParamTys.map(_._1).toTelescope)
      tParamTys = Context.fromTelescope(tParamsTysTelescope)
      tIndexTys <- checkparameterTyDeclarations(data.tIndexTys)(using tParamTys)
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
          paramTys <- checkparameterTyDeclarations(con.paramTys, Some(data.level))
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
      tParamTysTelescope <- checkparameterTyDeclarations(tParams.toList)
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
        given Context = record.tParamTys.map(_._1).toIndexedSeq :+ getRecordSelfBinding(record)
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
      telescope <- checkparameterTyDeclarations(effect.tParamTys.toTelescope)
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
          paramTys <- checkparameterTyDeclarations(operation.paramTys)(using Γ)
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
      constarints <- checkUsageSubsumption(binding.usage, UsageLiteral(UAny)).flatMap(ctx.solve)
      _ <- constarints.isEmpty match
        case true  => Right(())
        case false => Left(ExpectUnrestrictedTypeParameterBinding(binding))
      _ <- checkTParamsAreUnrestricted(rest)(using Γ :+ binding)
    yield ()

private def checkparameterTyDeclarations
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
      rest <- checkparameterTyDeclarations(rest)(using Γ :+ binding)
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
    case _: UsageType | _: EqDecidabilityType | _: EffectsType =>
      Right(LevelLiteral(0))
    case LevelType(upperBound) =>
      for (upperBound, _) <- checkLevel(upperBound)
      yield LevelSuc(upperBound)
    case _ => throw IllegalArgumentException(s"should have been checked to be a type: $tm")

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
        case vTy <- cTy match
          case F(vTy, eff, u) if isTotal(cTm, Some(cTy)) =>
            checkUsageSubsumption(u, u1).flatMap(ctx.solve) match
              case Right(constraints) if constraints.isEmpty => Right(vTy)
              case _                                         => Left(CollapsingU0Term(cTm))
          case F(_, _, _) => Left(CollapsingEffectfulTerm(cTm))
          case _          => Left(NotCollapsable(cTm))
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
    case UsageProd(operands) =>
      for
        (operands, usages) <- transposeCheckTypeResults(
          operands.map(o => checkType(o, UsageType(None))),
        )
        newTm <- UsageProd(operands.toSet)(using tm.sourceInfo).normalized
      yield (newTm, UsageType(Some(newTm)), usages)
    case UsageSum(operands) =>
      for
        (operands, usages) <- transposeCheckTypeResults(
          operands.multiToSeq.map(o => checkType(o, UsageType(None))),
        )
        newTm <- UsageSum(operands.toMultiset)(using tm.sourceInfo).normalized
      yield (newTm, UsageType(Some(newTm)), usages)
    case UsageJoin(operands) =>
      for
        (operands, usages) <- transposeCheckTypeResults(
          operands.map(o => checkType(o, UsageType(None))),
        )
        newTm <- UsageJoin(operands.toSet)(using tm.sourceInfo).normalized
      yield (newTm, UsageType(Some(newTm)), usages)
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
    case Auto() => throw IllegalArgumentException("cannot infer type")

def getLiteralEffectsContinuationUsage(effs: Set[Eff])(using Σ: Signature): ContinuationUsage =
  effs
    .map { (qn, _) => Σ.getEffect(qn).continuationUsage }
    .foldLeft(ContinuationUsage.Cu1) { _ | _ }

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
      case cct @ CapturedContinuationTip(ty) => Right(cct, ty, Usages.zero)
      case CType(upperBound, effects) =>
        for
          (effects, effUsages) <- checkType(effects, EffectsType())
          (upperBound, upperBoundUsages) <- checkIsCType(upperBound)
          upperBound <- upperBound.normalized(None)
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
      case Return(v, usage) =>
        for case (v, vTy, vUsages) <- inferType(v)
        yield (Return(v, usage), F(vTy, Total(), usage), vUsages * usage)
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
                    (bodyTy, _) <- checkIsCType(bodyTy)(using Γ :+ binding)
                    cty <- bodyTy.substLowers(arg).normalized(None)
                    (rest, cty, restUsages) <- checkElims(e :: checkedElims, cty, rest)
                    continuationUsage <- getEffectsContinuationUsage(effects)
                  yield (ETerm(arg) :: rest, augmentEffect(effects, cty), (argUsages + restUsages * continuationUsage))
                case _ => Left(ExpectFunction(redex(c, checkedElims.reverse)))
            case (e @ EProj(name)) :: rest =>
              cty match
                case RecordType(qn, args, effects) =>
                  Σ.getFieldOption(qn, name) match
                    case None => Left(MissingField(name, qn))
                    case Some(f) =>
                      for
                        _ <- checkTypes(args, Σ.getRecord(qn).tParamTys.map(_._1).toList)
                        cty <- f.ty.substLowers(args :+ Thunk(redex(c, checkedElims)): _*).normalized(None)
                        (rest, cty, restUsages) <- checkElims(e :: checkedElims, cty, rest)
                        continuationUsage <- getEffectsContinuationUsage(effects)
                        // TODO[P0]: think about how to check self reference in record.
                      yield (EProj(name) :: rest, augmentEffect(effects, cty), restUsages * continuationUsage)
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
      case c @ Continuation(handler, continuationUsage) =>
        def findTip(c: CTerm): CapturedContinuationTip = c match
          case c: CapturedContinuationTip => c
          case l: Let                     => findTip(l)
          case h: Handler                 => findTip(h.input)
          case r: Redex                   => findTip(r.t)
          case _                          => throw IllegalStateException("impossible term")
        val CapturedContinuationTip(F(resultTy, _, resultUsage)) = findTip(handler)
        for
          (checkedHandler, outputTy, handlerUsages) <- inferType(handler)
          handler = checkedHandler.asInstanceOf[Handler]
          paramLevel <- inferLevel(handler.parameterBinding.ty)
          resultLevel <- inferLevel(resultTy)
          outputLevel <- inferLevel(outputTy)
          continuationLevel <- LevelMax(paramLevel, resultLevel, outputLevel).normalized
        yield (
          Continuation(handler, continuationUsage),
          RecordType(
            Builtins.ContinuationQn,
            List(
              continuationLevel,
              UsageLiteral(continuationUsage),
              handler.parameterBinding.usage,
              handler.parameterBinding.ty,
              resultUsage,
              resultTy,
              handler.outputEffects,
              handler.outputUsage,
              handler.outputTy,
            ),
          ),
          handlerUsages,
        )
      case h: Handler => checkHandler(h, None)
  yield r

private def getEffVarContinuationUsage(v: Var)(using Γ: Context)(using Signature): VTerm =
  Γ.resolve(v) match
    case Binding(EffectsType(usage, _), _) => usage
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
    case Return(v, usage) =>
      ty match
        case F(ty, _, expectedUsage) =>
          for
            (v, usages) <- checkType(v, ty)
            constraints <- checkUsageSubsumption(usage, expectedUsage).flatMap(ctx.solve)
            _ <- if constraints.isEmpty then Right(()) else Left(NotUsageSubsumption(usage, expectedUsage))
          yield (Return(v, usage), usages * usage)
        case _ => Left(ExpectFType(ty))
    case l: Let     => checkLet(l, Some(ty)).map((v, _, usages) => (v, usages))
    case h: Handler => checkHandler(h, Some(ty)).map((v, _, usages) => (v, usages))
    case _ =>
      for
        case (tm, tmTy, usages) <- inferType(tm)
        ty <- ty.normalized(None)
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
          eqD <- inferEqDecidability(binding.ty)
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

def inferEqDecidability
  (ty: VTerm)
  (using Γ: Context)
  (using Σ: Signature)
  (using ctx: TypingContext)
  : Either[IrError, VTerm] = ty match
  case _: Type | _: UsageType | _: EqDecidabilityType | _: EffectsType | _: LevelType =>
    Right(EqDecidabilityLiteral(EqDecidable))
  case Top(_, eqDecidability) => Right(eqDecidability)
  case _: Var | _: Collapse =>
    for
      case (ty, tyTy, _) <- inferType(ty)
      r <- tyTy match
        case Type(upperBound) => inferEqDecidability(upperBound)
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
    eqD <- inferEqDecidability(ty)
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

/** @param input
  *   input usage terms should live in Γ ++ telescope
  * @param telescope
  *   signifies which usages to verify
  * @return
  *   unverified usages
  */
private def verifyUsages
  (inputUsages: Usages, telescope: Telescope)
  (using Γ: Context)
  (using Σ: Signature)
  (using ctx: TypingContext)
  : Either[IrError, Usages] =
  val Γ2 = Γ ++ telescope
  val count = telescope.size
  for _ <- transpose(inputUsages.takeRight(count).reverse.zipWithIndex.map { (v, i) =>
      for
        constraint <- checkUsageSubsumption(v, Γ2.resolve(i).usage)
        r <-
          if constraint.isEmpty then Right(())
          else Left(NotUsageSubsumption(v, Γ2.resolve(i).usage))
      yield ()
    })
  yield inputUsages.drop(count).map { v =>
    try v.strengthen(count, 0)
    catch
      // It's possible for a term's usage to reference a usage term after it. For example consider
      // functino `f: u: Usage -> [u] Nat -> Nat` and context `{i: Nat, u: Usage}`, then `f u i`
      // has usage `[u, U1]`. In this case, strengthen usage of `i` is approximated by UAny.
      case _: StrengthenException => UsageLiteral(Usage.UAny)
  }

/** @param usages
  *   usage terms should live in Γ
  * @param count
  *   number of usages to verify, counting from the end (right)
  * @return
  *   unverified usages
  */
@deprecated("use verifyUsages above instead")
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
      // has usage `[u, U1]`. In this case, strengthen usage of `i` is approximated by UAny.
      case _: StrengthenException => UsageLiteral(Usage.UAny)
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
    // I thought about adding a check on `ty` to see if it's inhabitable. And if it's not, the usages in body can all
    // be trivialized by multiple U0 since they won't execute. But inhabitability is not decidable. Even if we only
    // do some converative checking, it's hard to check polymorphic type `A` for any `A` passed by the caller. An
    // alternative is to designate a bottom type and just check that. But to make this ergonomic we need to tweak the
    // type checker to make this designated type a subtype of everything else. But type inference becomes impossible
    // with `force t` where `t` has type bottom. If we raise a type error for `force t`, this would violate substitution
    // principle of subtypes.
    // On the other hand, if we don't check inhabitability, the usages in body would simply be multipled with UAff
    // instead of U0, which seems to be a reasonable approximation. The primary reason for such a check is just to flag
    // phantom usages of terms, but I think it's not worth all these complexity.
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
        // Note that we can't do conversion check here because doing conversion check assumes it must be the case or
        // type check would fail. But here the usage can very well not be convertible with U0 or UAny.
        tUsages.forall { usage => usage == uAny || usage == u0 }
      val tTy = F(ty, effects, usage)
      if isTotal(t, Some(tTy)) && areTUsagesZeroOrUnrestricted then
        // Do the reduction onsite so that type checking in sub terms can leverage the
        // more specific type. More importantly, this way we do not need to reference
        // the result of a computation in the inferred type.
        for
          t <- t.normalized(Some(tTy))
          newBody = t match
            case Return(v, _) => body.substLowers(v)
            case c            => body.substLowers(Collapse(c))
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
        val tBinding = Binding(ty, usage)(gn"v")
        for
          case (body, bodyTy, usagesInBody) <-
            given Context = Γ :+ tBinding
            bodyTy match
              case None => inferType(body)
              case Some(bodyTy) =>
                for
                  (bodyTy, _) <- checkIsCType(bodyTy)(using Γ)
                  (body, usages) <- checkType(body, bodyTy.weakened)
                yield (body, bodyTy, usages)
          bodyTy <- checkVar0Leak(bodyTy, LeakedReferenceToEffectfulComputationResult(t))
          usagesInBody <- verifyUsages(usagesInBody, tBinding :: Nil)
          continuationUsage <- getEffectsContinuationUsage(effects)
        yield (
          Let(t, ty, effects, usage, body)(tm.boundName)(using tm.sourceInfo),
          bodyTy.strengthened,
          usagesInBody * continuationUsage,
        )
  yield (newTm, augmentEffect(effects, bodyTy), usages)

def checkHandler
  (h: Handler, outputType: Option[CTerm])
  (using Γ: Context)
  (using Σ: Signature)
  (using ctx: TypingContext)
  : Either[IrError, (CTerm, CTerm, Usages)] =
  for
    (eff, _) <- checkType(h.eff, EffectsType())
    eff <- eff.normalized
    effs <- eff match
      case Effects(effs, s) if s.isEmpty => Right(effs)
      case _                             => Left(EffectTermTooComplex(eff))
    operations = effs.flatMap(e => Σ.getOperations(e._1).map(op => (e._1 / op.name, e._2, op)))
    _ <-
      val expectedOperatonNames = operations.map(_._1)
      val actualOperationNames = h.handlers.keySet
      if expectedOperatonNames == actualOperationNames then Right(())
      else Left(HandlerOperationsMismatch(h, expectedOperatonNames, actualOperationNames))
    (otherEffects, _) <- checkType(h.otherEffects, EffectsType())
    otherEffects <- otherEffects.normalized
    (outputEffects, _) <- checkType(h.outputEffects, EffectsType())
    outputEffects <- outputEffects.normalized
    (outputUsage, _) <- checkType(h.outputUsage, UsageType())
    outputUsage <- outputUsage.normalized
    (outputTy, _) <- checkIsType(h.outputTy)
    _ <- outputType match
      case None => Right(())
      case Some(outputType) =>
        for contraints <- checkIsSubtype(F(outputTy, outputEffects, outputUsage), outputType).flatMap(ctx.solve)
        yield contraints.isEmpty match
          case true  => Right(())
          case false => Left(NotCSubtype(F(outputTy, outputEffects, outputUsage), outputType))
    (parameterTy, _) <- checkIsType(h.parameterBinding.ty)
    // parameter binding usage dictates how much resources the handler needs when consuming the parameter
    (parameterBindingUsage, _) <- checkType(h.parameterBinding.usage, UsageType())
    _ <-
      // If the handler implements some simple exceptional operation, then this operation may throw an exception, which
      // would trigger disposers of all handlers above the current handler, which, in turn, may call operations on this
      // handler again. But this is problematic if the parameter disallows multiple usages (aka, it's linear or affine)
      // because the current operation is consuming the parameter already, which means another call to an operation of
      // this handler should not be allowed.
      // This issue is solved by requiring parameter to be URel or UAny if the handler implements any simple exceptional
      // operation. Hopefully this limitation is not a big deal in practice.
      val simpleExceptionalOperations = operations
        .filter((_, _, operation) =>
          operation.continuationUsage.controlMode == ControlMode.Simple && operation.continuationUsage.usage != Usage.U1,
        )
      if simpleExceptionalOperations.isEmpty then Right(())
      else
        ctx.checkSolved(
          checkUsageSubsumption(parameterBindingUsage, uRel),
          HandlerParameterMustBeURelOrUAnyIfHandlerImplementsSimpleExceptions(h),
        )
    parameterBinding = Binding(parameterTy, parameterBindingUsage)(h.parameterBinding.name)
    (parameter, rawParameterUsages) <- checkType(h.parameter, parameterTy)
    parameterUsages = rawParameterUsages * parameterBindingUsage
    (inputTy, _) <- checkIsType(h.inputBinding.ty)
    // Unlike parameter, input is a computation and hence only executed linearly. The input binding usage is simply a
    // requirement on the final return type of the input computation.
    (inputBindingUsage, _) <- checkType(h.inputBinding.usage, UsageType())
    inputBinding = Binding(inputTy, inputBindingUsage)(h.inputBinding.name)
    inputEffects <- EffectsUnion(eff, otherEffects).normalized
    (input, inputUsages) <- checkType(h.input, F(inputTy, inputEffects, inputBindingUsage))
    inputEffectsContinuaionUsage <- getEffectsContinuationUsage(inputEffects)
    (parameterDisposer, parameterDisposerUsages) <- h.parameterDisposer match
      case Some(parameterDisposer) =>
        for
          (parameterDisposer, parameterDisposerUsages) <- checkType(
            parameterDisposer,
            F(DataType(Builtins.UnitQn, Nil), outputEffects.weakened),
          )(using Γ :+ parameterBinding)
          parameterDisposerUsages <- verifyUsages(parameterDisposerUsages, parameterBinding :: Nil)
        yield (Some(parameterDisposer), parameterDisposerUsages)
      case None =>
        (inputEffectsContinuaionUsage, parameterBindingUsage) match
          case (UsageLiteral(effUsage), UsageLiteral(paramUsage)) if effUsage <= Usage.URel || paramUsage >= Usage.U0 =>
            Right(None, Usages.zero)
          case _ => Left(ExpectParameterDisposer(h))
    (parameterReplicator, parameterReplicatorUsages) <- h.parameterReplicator match
      case Some(parameterReplicator) =>
        for
          (parameterReplicator, parameterReplicatorUsages) <- checkType(
            parameterReplicator,
            F(
              DataType(
                Builtins.PairQn,
                List(
                  LevelUpperBound(),
                  EqDecidabilityLiteral(EqDecidability.EqUnknown),
                  parameterBindingUsage,
                  parameterTy,
                  parameterBindingUsage,
                  parameterTy,
                ),
              ),
              outputEffects,
            ).weakened,
          )(using Γ :+ parameterBinding)
          parameterReplicatorUsages <- verifyUsages(parameterReplicatorUsages, parameterBinding :: Nil)
        yield (Some(parameterReplicator), parameterReplicatorUsages)
      case None =>
        (inputEffectsContinuaionUsage, parameterBindingUsage) match
          case (UsageLiteral(effUsage), UsageLiteral(paramUsage))
            if effUsage <= Usage.UAff || paramUsage >= Usage.URel || paramUsage == Usage.U0 =>
            Right(None, Usages.zero)
          case _ => Left(ExpectParameterReplicator(h))
    (transform, transformUsages) <- checkType(
      h.transform,
      F(outputTy, outputEffects, outputUsage).weaken(2, 0),
    )(using Γ :+ parameterBinding :+ inputBinding)
    handlerAndUsages <- transpose(operations.map { (qn, effArgs, operation) =>
      val handler = h.handlers(qn)
      // The followings do not need to be weakened for handler parameter because after substituting the effect args,
      // they do not contain any free variables beyond beginning of paramTys.
      val paramTys = operation.paramTys.substLowers(effArgs: _*)
      val resultTy = operation.resultTy.substLowers(effArgs: _*)
      val resultUsage = operation.resultUsage.substLowers(effArgs: _*)
      for (impl, usages) <- operation.continuationUsage match
          case ContinuationUsage(usage, ControlMode.Simple) =>
            given implΓ: Context = Γ ++ (parameterBinding +: paramTys)
            val implOffset = implΓ.size - Γ.size
            val implTy = usage match
              case U1 =>
                F(
                  DataType(
                    Builtins.PairQn,
                    List(
                      Auto(),
                      Auto(),
                      parameterBindingUsage.weaken(implOffset, 0),
                      parameterTy.weaken(implOffset, 0),
                      resultUsage,
                      resultTy,
                    ),
                  ),
                  Auto(),
                  u1,
                )
              case U0 =>
                F(
                  DataType(
                    Builtins.PairQn,
                    List(
                      Auto(),
                      Auto(),
                      parameterBindingUsage.weaken(implOffset, 0),
                      parameterTy.weaken(implOffset, 0),
                      outputUsage.weaken(implOffset, 0),
                      outputTy.weaken(implOffset, 0),
                    ),
                  ),
                  Auto(),
                  u1,
                )
              case UAff =>
                F(
                  DataType(
                    Builtins.PairQn,
                    List(
                      Auto(),
                      Auto(),
                      parameterBindingUsage.weaken(implOffset, 0),
                      parameterTy.weaken(implOffset, 0),
                      u1,
                      DataType(
                        Builtins.EitherQn,
                        List(
                          Auto(),
                          Auto(),
                          outputUsage.weaken(implOffset, 0),
                          outputTy.weaken(implOffset, 0),
                          resultUsage,
                          resultTy,
                        ),
                      ),
                    ),
                  ),
                  Auto(),
                  u1,
                )
              case _ => throw IllegalStateException("bad continuation usage on operation")
            val implOutputEffects = outputEffects.weaken(implOffset, 0)
            for
              (implTy, _) <- checkIsCType(implTy)
              (impl, usages) <- checkType(handler, implTy)
              effects <- checkEffectsAreSimple(implTy.asInstanceOf[F].effects)
              _ <- usage match
                // Simple U1 operation can only perform U1 effects so that linear resources in the contination are
                // managed correctly.
                case U1 =>
                  for
                    continuationUsage <- getEffectsContinuationUsage(effects)
                    _ <- ctx.checkSolved(checkUsageSubsumption(continuationUsage, u1), ExpectU1Effect(qn))
                  yield ()
                case _ => Right(())
              _ <- ctx.checkSolved(
                checkEffSubsumption(effects, implOutputEffects),
                NotEffectSubsumption(effects, implOutputEffects),
              )
            yield (impl, usages)
          case ContinuationUsage(continuationUsage, ControlMode.Complex) =>
            given continuationΓ: Context = Γ ++ (parameterBinding +: paramTys)
            val continuationWeakenOffset = continuationΓ.size - Γ.size
            val continuationParameterTy = parameterTy.weaken(continuationWeakenOffset, 0)
            val continuationOutputTy = outputTy.weaken(continuationWeakenOffset, 0)
            val continuationOutputEffects = outputEffects.weaken(continuationWeakenOffset, 0)
            val continuationOutputUsage = outputUsage.weaken(continuationWeakenOffset, 0)
            val continuationType = RecordType(
              Builtins.ContinuationQn,
              List(
                Auto(),
                UsageLiteral(continuationUsage),
                parameterBindingUsage.weaken(continuationWeakenOffset, 0),
                continuationParameterTy,
                resultUsage.weaken(continuationWeakenOffset, 0),
                resultTy,
                continuationOutputEffects,
                continuationOutputUsage,
                continuationOutputTy,
              ),
            )
            for
              (continuationType, _) <- checkIsCType(continuationType)
              r <-
                given implΓ: Context =
                  continuationΓ :+ Binding(U(continuationType), UsageLiteral(Usage.U1))(gn"continuation")
                val implOffset = implΓ.size - Γ.size
                checkType(
                  handler,
                  F(
                    outputTy.weaken(implOffset, 0),
                    outputEffects.weaken(implOffset, 0),
                    outputUsage.weaken(implOffset, 0),
                  ),
                )
            yield r
      yield (qn, impl, usages)
    })
  yield (
    Handler(
      eff,
      otherEffects,
      outputEffects,
      outputUsage,
      outputTy,
      parameter,
      parameterBinding,
      parameterDisposer,
      parameterReplicator,
      transform,
      handlerAndUsages.map((qn, impl, _) => (qn, impl)).toMap,
      input,
      inputBinding,
    )(h.handlersBoundNames)(using h.sourceInfo),
    F(outputTy, outputEffects, outputUsage),
    inputUsages + parameterUsages + parameterDisposerUsages + parameterReplicatorUsages + transformUsages + handlerAndUsages
      .map((_, _, usages) => usages)
      .reduce(_ + _),
  )

// Input effects should be type-checked.
// returned effects should be normalized
private def getEffectsContinuationUsage
  (effects: VTerm)
  (using Γ: Context)
  (using Σ: Signature)
  (using ctx: TypingContext)
  : Either[IrError, VTerm] =
  for
    effects <- effects.normalized
    usage <- ctx.withMetaResolved(effects):
      case Effects(literal, operands) =>
        val literalUsages = literal.foldLeft(Usage.U1) { case (acc, (qn, _)) =>
          Σ.getEffect(qn).continuationUsage.usage | acc
        }
        for usages <- transpose(operands.map(getEffectsContinuationUsage))
        yield UsageJoin(usages + UsageLiteral(literalUsages))
      case v: Var =>
        Γ.resolve(v).ty match
          case EffectsType(continuationUsage, _) => Right(continuationUsage)
          case _                                 => throw IllegalStateException("type error")
      case r: ResolvedMetaVariable =>
        r.ty match
          case F(EffectsType(continuationUsage, _), _, _) => Right(continuationUsage)
          case _                                          => throw IllegalStateException("type error")
      case _ => Right(UsageLiteral(UAny))
    usage <- usage.normalized
  yield usage

private def checkEffectsAreSimple
  (effects: VTerm)
  (using Γ: Context)
  (using Σ: Signature)
  (using ctx: TypingContext)
  : Either[IrError, VTerm] =
  for
    effects <- effects.normalized
    _ <- ctx.withMetaResolved(effects):
      case Effects(literal, operands) =>
        if literal.exists { case (qn, _) =>
            Σ.getEffect(qn).continuationUsage.controlMode == ControlMode.Complex
          }
        then Left(ExepctSimpleEffects(effects))
        else
          for _ <- transpose(operands.map(getEffectsContinuationUsage))
          yield ()
      case v: Var =>
        Γ.resolve(v).ty match
          case EffectsType(_, ControlMode.Simple)  => Right(())
          case EffectsType(_, ControlMode.Complex) => Left(ExepctSimpleEffects(effects))
          case _                                   => throw IllegalStateException("type error")
      case r: ResolvedMetaVariable =>
        r.ty match
          case F(EffectsType(_, ControlMode.Simple), _, _)  => Right(())
          case F(EffectsType(_, ControlMode.Complex), _, _) => Left(ExepctSimpleEffects(effects))
          case _                                            => throw IllegalStateException("type error")
      case _ => Right(UsageLiteral(UAny))
  yield effects

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
      cty <- cty.normalized(None)
    yield (cty, usages)
  }

def reduceUsage(usage: CTerm)(using Γ: Context)(using Σ: Signature)(using ctx: TypingContext): Either[IrError, VTerm] =
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

def reduceVType(vTy: CTerm)(using Γ: Context)(using Σ: Signature)(using ctx: TypingContext): Either[IrError, VTerm] =
  ctx.trace("reduce V type", Block(yellow(vTy.sourceInfo), pprint(vTy))) {
    for
      case (vTy, tyTy, _) <- inferType(vTy)
      r <- tyTy match
        case F(Type(_), effect, _) if isTotal(vTy, Some(tyTy)) =>
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

// Report an error if the type of `body` needs to reference the effectful
// computation. User should use a dependent sum type to wrap such
// references manually to avoid the leak.
// TODO[P3]: in case weakened failed, provide better error message: ctxTy cannot depend on
//  the bound variable
private def checkVar0Leak[T <: CTerm | VTerm](ty: T, error: => IrError)(using Σ: Signature): Either[IrError, T] =
  val (positiveFreeVars, negativeFreeVars) = ty match
    case ty: CTerm => getFreeVars(ty)(using 0)
    case ty: VTerm => getFreeVars(ty)(using 0)
  if positiveFreeVars(0) || negativeFreeVars(0) then Left(error)
  else
    Right(ty match
      case ty: CTerm => ty.strengthened.asInstanceOf[T]
      case ty: VTerm => ty.strengthened.asInstanceOf[T],
    )

// TODO: delete this.
def allRight[L](es: Iterable[Either[L, ?]]): Either[L, Unit] =
  es.first {
    case Left(l) => Some(l)
    case _       => None
  } match
    case Some(l) => Left(l)
    case _       => Right(())

def isMeta(t: VTerm): Boolean = t match
  case Collapse(Redex(Meta(_), _)) => true
  case Collapse(Meta(_))           => true
  case _                           => false

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
