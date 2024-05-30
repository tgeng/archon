package com.github.tgeng.archon.core.ir

import _root_.pprint.Tree
import com.github.tgeng.archon.common.*
import com.github.tgeng.archon.common.IndentPolicy.*
import com.github.tgeng.archon.common.WrapPolicy.*
import com.github.tgeng.archon.core.common.*
import com.github.tgeng.archon.core.ir.CTerm.*
import com.github.tgeng.archon.core.ir.Declaration.*
import com.github.tgeng.archon.core.ir.Elimination.*
import com.github.tgeng.archon.core.ir.EqDecidability.*
import com.github.tgeng.archon.core.ir.HandlerType.Simple
import com.github.tgeng.archon.core.ir.IrError.*
import com.github.tgeng.archon.core.ir.MetaVariable.*
import com.github.tgeng.archon.core.ir.PrettyPrinter.pprint
import com.github.tgeng.archon.core.ir.Reducible.reduce
import com.github.tgeng.archon.core.ir.UnsolvedMetaVariableConstraint.*
import com.github.tgeng.archon.core.ir.Usage.*
import com.github.tgeng.archon.core.ir.VTerm.*

import scala.annotation.tailrec
import scala.collection.immutable.{SeqMap, Set}
import scala.collection.mutable

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
  case HandlerTypeSubsumption(context: Context, sub: VTerm, sup: VTerm)

enum UnsolvedMetaVariableConstraint:
  case UmcNothing
  case UmcCSubtype(lowerBounds: Set[CTerm])
  case UmcVSubtype(lowerBounds: Set[VTerm])
  // union is used to combine multiple lower bounds
  case UmcEffSubsumption(lowerBound: VTerm)
  // level max is used to combine multiple level bounds
  case UmcLevelSubsumption(lowerBound: VTerm)
  // note that lower and upper is in the sense of usage subsumption, aka reverse of usage lattice.
  // - usage join is used to combine multiple upper bounds
  // - usage meet (&) is used to combine multiple lower bounds at the end when deriving the solution
  // Note: when picking the solution proactively, we should pick the upperbound if available, then
  // fallback to meet of the lowerBounds (when possible, or just fail if there are multiple complex
  // terms), and then fallback to uAny. This is because we want to pick the least necessary usage
  // when possible. For example, if u1 is sufficient, the solution should not be uRel, uAff, or
  // uAny. This is different from the other cases where the lower bound is usually preferred. This
  // asymmetry is due to the fact that usages are usually used contravariantly.
  case UmcUsageSubsumption(lowerBounds: Set[VTerm], upperBound: Option[VTerm])

  this match
    case UmcCSubtype(lowerBounds) => assert(lowerBounds.nonEmpty)
    case UmcVSubtype(lowerBounds) => assert(lowerBounds.nonEmpty)
    case _                        =>

  def substLowers(args: VTerm*)(using Signature): UnsolvedMetaVariableConstraint = this match
    case UmcNothing => UmcNothing
    case UmcCSubtype(lowerBounds) =>
      UmcCSubtype(lowerBounds.map(_.substLowers(args*)))
    case UmcVSubtype(lowerBounds) =>
      UmcVSubtype(lowerBounds.map(_.substLowers(args*)))
    case UmcEffSubsumption(lowerBound) =>
      UmcEffSubsumption(lowerBound.substLowers(args*))
    case UmcLevelSubsumption(lowerBound) =>
      UmcLevelSubsumption(lowerBound.substLowers(args*))
    case UmcUsageSubsumption(lowerBound, upperBound) =>
      UmcUsageSubsumption(
        lowerBound.map(_.substLowers(args*)),
        upperBound.map(_.substLowers(args*)),
      )

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
  case Solved(override val context: Context, override val ty: CTerm, value: CTerm)
    extends MetaVariable(context, ty)

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
        Unsolved(context.drop(args.size), ty.substLowers(args*), constraint)
      case Solved(context, ty, value) =>
        Solved(context.drop(args.size), ty.substLowers(args*), value.substLowers(args*))
      case Guarded(context, ty, value, preconditions) =>
        Guarded(
          context.drop(args.size),
          ty.substLowers(args*),
          value.substLowers(args*),
          preconditions,
        )

  def contextFreeType: CTerm = context.foldRight[CTerm](ty) { (elem, acc) =>
    FunctionType(elem, acc)
  }

enum ResolvedMetaVariable:
  def ty: CTerm

  /** @param substitution:
    *   substitution that converts a term in the context in which this resolution happens to the
    *   context of this meta variable. That is, a term after this substitution can be assigned to
    *   the meta variable. Note that, caller must check to make sure all variables are mapped by
    *   this substitution, otherwise, the substituted variable can contain (unresolved) free
    *   variables. Note that, this value is none if a substitution map cannot be obtained (due to
    *   redex containing eliminations that are not distinct variables)
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
  case RSolved(ty: CTerm, value: CTerm)
import com.github.tgeng.archon.core.ir.ResolvedMetaVariable.*

class TypingContext
  (
    var traceLevel: Int = 0,
    var enableDebugging: Boolean = false,
  ):

  private val metaVars: mutable.ArrayBuffer[MetaVariable] = mutable.ArrayBuffer()
  private var version: Int = 0
  private var solvedVersion: Int = 0
  given TypingContext = this

  // TODO[P0]: check usage of this method. Normally the following `resolve` should be used instead.
  def resolveMeta(m: Meta): MetaVariable = metaVars(m.index)

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
    withMetaResolved(input1): input1 =>
      withMetaResolved(input2)(input2 => action(input1, input2))

  def withMetaResolved[R]
    (input: VTerm)
    (action: (ResolvedMetaVariable | VTerm) => R)
    (using Signature)
    : R =
    input match
      case Collapse(c) =>
        withMetaResolved(c):
          case (r, Nil) => action(r)
          case (_, _) =>
            throw IllegalStateException(
              "type error: extra elims for vterm which should never happen",
            )
          case _: CTerm => action(input)
      case _ => action(input)

  def withMetaResolved2[R]
    (input1: VTerm, input2: VTerm)
    (action: (ResolvedMetaVariable | VTerm, ResolvedMetaVariable | VTerm) => R)
    (using Signature)
    : R =
    withMetaResolved(input1): input1 =>
      withMetaResolved(input2)(input2 => action(input1, input2))

  def resolve(c: CTerm)(using Signature): Option[(ResolvedMetaVariable, List[Elimination[VTerm]])] =
    val (index, elims) = c match
      case Meta(index)               => (index, Nil)
      case Redex(Meta(index), elims) => (index, elims)
      case _                         => return None
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
            constraints.substLowers(args*),
            c,
            ty.substLowers(args*),
          ),
          extraElims,
        )
      case Solved(context, ty, value) =>
        val args = elims.take(context.size).collect { case Elimination.ETerm(t) => t }
        Some(RSolved(ty.substLowers(args*), value.substLowers(args*)), elims.drop(context.size))
      case Guarded(context, ty, _, _) =>
        val args = elims.take(context.size).collect { case Elimination.ETerm(t) => t }
        Some(RGuarded(ty.substLowers(args*)), elims.drop(context.size))

  def resolveMetaVariableType(c: CTerm)(using Signature): Option[CTerm] = c match
    case Meta(index) =>
      val resolved = metaVars(index)
      if resolved.context.isEmpty then Some(resolved.ty)
      else None
    case Redex(Meta(index), elims) =>
      val resolved = metaVars(index)
      if resolved.context.size <= elims.size
      then
        val args = elims.take(resolved.context.size).collect { case Elimination.ETerm(t) =>
          t
        }
        Some(resolved.ty.substLowers(args*))
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
    version += 1
    metaVars += mv
    Meta(index)

  /** @param value:
    *   value must be in the context of the meta variable. That is, value must be from a call of
    *   `adaptForMetaVariable`
    */
  @throws(classOf[IrError])
  def assignUnsolved
    (index: Nat, constraint: UnsolvedMetaVariableConstraint, value: CTerm)
    (using Signature)
    (using ctx: TypingContext)
    : Set[Constraint] =
    given Context = ctx.metaVars(index).context
    assignValue(index, value)
    constraint match
      case UmcNothing               => Set.empty
      case UmcCSubtype(lowerBounds) => lowerBounds.map(checkIsSubtype(_, value)).flatten
      case UmcVSubtype(lowerBounds) => lowerBounds.map(checkIsSubtype(_, Collapse(value))).flatten
      case UmcEffSubsumption(lowerBound)   => checkEffSubsumption(lowerBound, Collapse(value))
      case UmcLevelSubsumption(lowerBound) => checkLevelSubsumption(lowerBound, Collapse(value))
      case UmcUsageSubsumption(lowerBounds, upperBound) =>
        lowerBounds.flatMap(lb => checkUsageSubsumption(Collapse(value), lb)) ++
          upperBound.toSet.flatMap(ub => checkUsageSubsumption(Collapse(value), ub))

  /** @param value:
    *   value must be in the context of the meta variable. That is, value must be from a call of
    *   `adaptForMetaVariable`
    */
  @throws(classOf[IrError])
  def assignUnsolved
    (m: RUnsolved, value: CTerm)
    (using Signature)
    (using ctx: TypingContext)
    : Set[Constraint] =
    assignUnsolved(m.index, m.constraint, value)

  def alignElims(t: CTerm, elims: List[Elimination[VTerm]])(using Signature): Option[CTerm] =
    elims match
      case Nil => Some(t)
      case elims =>
        t match
          case Redex(t, elims2) if elims2.takeRight(elims.size) == elims =>
            Some(redex(t, elims2.dropRight(elims.size)))
          case _ => None

  def adaptForMetaVariable[T]
    (m: RUnsolved, value: CTerm)
    (using Signature)
    (using ctx: TypingContext)
    (f: Context ?=> Option[CTerm] => T)
    : T =
    given Context = metaVars(m.index).context
    // Make sure meta variable assignment won't cause cyclic meta variable references.
    if MetaVarVisitor.visitCTerm(value)(m.index) then return f(None)

    if (FreeVarsVisitor
        .visitCTerm(value)(using 0)
        .map(_.idx)
        .toSet -- m.substitution.keySet).nonEmpty
    then f(None)
    else f(Some(value.subst(m.substitution.lift)))

  def adaptForMetaVariable[T]
    (m: RUnsolved, value: VTerm)
    (using Signature)
    (using ctx: TypingContext)
    (f: Context ?=> Option[VTerm] => T)
    : T =
    given Context = metaVars(m.index).context
    // Make sure meta variable assignment won't cause cyclic meta variable references.
    if MetaVarVisitor.visitVTerm(value)(m.index) then return f(None)
    if (FreeVarsVisitor
        .visitVTerm(value)(using 0)
        .map(_.idx)
        .toSet -- m.substitution.keySet).nonEmpty
    then f(None)
    else f(Some(value.subst(m.substitution.lift)))

  def updateConstraint(u: RUnsolved, constraint: UnsolvedMetaVariableConstraint): Unit =
    metaVars(u.index) match
      case Unsolved(context, ty, _) =>
        version += 1
        metaVars(u.index) = Unsolved(context, ty, constraint)
      case _ => throw IllegalStateException("updateConstraint called on non-unsolved meta variable")

  private def assignValue(index: Nat, value: CTerm)(using Context)(using Signature): Unit =
    val existing = metaVars(index)
    version += 1
    metaVars(index) = Solved(existing.context, existing.ty, value)
    debugPrint(s"#$index := ${pprint(value)}")

  private def updateGuarded(index: Nat, guarded: Guarded): Unit =
    version += 1
    metaVars(index) = guarded

  @throws(classOf[IrError])
  def checkSolved
    (constraints: Set[Constraint], error: => IrError)
    (using Context)
    (using Σ: Signature)
    : Unit = {
    val unsolvedConstraints = solve(constraints, aggressivelySolveConstraints = true)
    if unsolvedConstraints.nonEmpty then
      throw ConstraintUnificationFailure(unsolvedConstraints, error)
  }

  @throws(classOf[IrError])
  def solve
    (constraints: Set[Constraint], aggressivelySolveConstraints: Boolean = false)
    (using Context)
    (using Σ: Signature)
    : Set[Constraint] =
    trace[Set[Constraint]](
      "solve",
      Block(ChopDown, Aligned, pprint(constraints)),
      constraints => Block(ChopDown, Aligned, pprint(constraints)),
    ):
      var currentConstraints = constraints
      while solvedVersion != version do
        solvedVersion = version
        currentConstraints = solveOnce(currentConstraints, false)
      if currentConstraints.nonEmpty && aggressivelySolveConstraints then
        currentConstraints = solveOnce(currentConstraints, true)
        while solvedVersion != version do
          solvedVersion = version
          currentConstraints = solveOnce(currentConstraints, true)
      currentConstraints

  @throws(classOf[IrError])
  private def solveOnce
    (constraints: Set[Constraint], proactivelySolveAmbiguousMetaVars: Boolean)
    (using Context)
    (using Signature)
    : Set[Constraint] =
    val metaVarIndexes = MetaVarCollector.visitConstraints(constraints)
    solveAllMetaVars(metaVarIndexes, false)
    val newConstraints = solveConstraints(constraints)
    if proactivelySolveAmbiguousMetaVars then
      val metaVarIndexes = MetaVarCollector.visitConstraints(newConstraints)
      solveAllMetaVars(metaVarIndexes, true)
      solveConstraints(newConstraints)
    else newConstraints

  private def solveAllMetaVars
    (metaVarIndexes: Set[Nat], proactivelySolveAmbiguousMetaVars: Boolean)
    (using Context)
    (using Signature)
    : Unit =
    for index <- metaVarIndexes.toSeq.sorted do
      metaVars(index) match
        case Unsolved(context, ty, constraint) if proactivelySolveAmbiguousMetaVars =>
          given Context = context

          val solution: CTerm | Unit = constraint match
            case UmcNothing =>
              ty match
                case F(LevelType(l), _, u) if l > LevelOrder.zero => Return(l0, u)
                case F(UsageType(_), _, u)                        => Return(uAny, u)
                case F(EffectsType(_, _), _, u)                   => Return(total, u)
                case F(EqDecidabilityType(), _, u)                => Return(eqDecidable, u)
                case F(HandlerTypeType(), _, u)                   => Return(handlerSimple, u)
                // TODO[P2]: implement proof/instance search here.
                case _ => ()
            case UmcCSubtype(lowerBounds)        => lowerBounds.reduce(typeUnion)
            case UmcVSubtype(lowerBounds)        => Return(lowerBounds.reduce(typeUnion), uAny)
            case UmcEffSubsumption(lowerBound)   => Return(lowerBound, uAny)
            case UmcLevelSubsumption(lowerBound) => Return(lowerBound, uAny)
            case UmcUsageSubsumption(lowerBounds, upperBound) =>
              Return(
                upperBound.getOrElse {
                  lowerBounds
                    .map(_.normalized)
                    .map:
                      case UsageLiteral(u) => Some(u)
                      case _               => None
                    .foldLeft[Option[Usage]](Some(UAny)):
                      case (Some(u1), Some(u2)) => u1 & u2
                      case (Some(uAny), o)      => o
                      case (o, Some(uAny))      => o
                      case _                    => None
                    .map(UsageLiteral(_))
                    .getOrElse(throw UnableToFindUsageMeetDuringUnification(lowerBounds))
                },
                uAny,
              )
          solution match
            case ()       =>
            case c: CTerm => assignUnsolved(index, constraint, c)
        case Guarded(context, ty, value, constraints) =>
          val newConstraints = solveConstraints(constraints)
          if newConstraints.isEmpty then assignValue(index, value)
          else updateGuarded(index, Guarded(context, ty, value, newConstraints))
        case _ =>

  private object MetaVarCollector extends Visitor[TypingContext, Set[Nat]]:
    override def visitMeta(m: Meta)(using ctx: TypingContext)(using Σ: Signature): Set[Nat] =
      val rest = ctx.resolveMeta(m) match
        // Include all meta varialbles in the constraints of guarded meta variables so that solving these can potentially
        // turn guarded meta variables to solved ones.
        case Guarded(_, _, _, constraints) => visitConstraints(constraints)
        case _                             => Set[Nat]()
      Set(m.index) ++ rest

    override def combine
      (freeVars: Set[Nat]*)
      (using ctx: TypingContext)
      (using Σ: Signature)
      : Set[Nat] =
      freeVars.flatten.toSet

    def visitConstraints
      (constraints: Set[Constraint])
      (using ctx: TypingContext)
      (using Signature)
      : Set[Nat] =
      constraints.flatMap:
        case Constraint.Conversions(_, lhs, rhs, _) =>
          lhs.flatMap(visitVTerm) ++ rhs.flatMap(visitVTerm)
        case Constraint.VConversion(_, lhs, rhs, _)            => visitVTerm(lhs) ++ visitVTerm(rhs)
        case Constraint.CConversion(_, lhs, rhs, _)            => visitCTerm(lhs) ++ visitCTerm(rhs)
        case Constraint.VSubType(_, sub, sup)                  => visitVTerm(sub) ++ visitVTerm(sup)
        case Constraint.CSubType(_, sub, sup)                  => visitCTerm(sub) ++ visitCTerm(sup)
        case Constraint.EffSubsumption(_, sub, sup)            => visitVTerm(sub) ++ visitVTerm(sup)
        case Constraint.LevelSubsumption(_, sub, sup)          => visitVTerm(sub) ++ visitVTerm(sup)
        case Constraint.UsageSubsumption(_, sub, sup)          => visitVTerm(sub) ++ visitVTerm(sup)
        case Constraint.EqDecidabilitySubsumption(_, sub, sup) => visitVTerm(sub) ++ visitVTerm(sup)
        case Constraint.HandlerTypeSubsumption(_, sub, sup)    => visitVTerm(sub) ++ visitVTerm(sup)

  @throws(classOf[IrError])
  private def solveConstraints(constraints: Set[Constraint])(using Σ: Signature): Set[Constraint] =
    constraints.flatMap:
      case Constraint.Conversions(context, lhs, rhs, tys) =>
        checkAreConvertible(lhs, rhs, tys)(using context)
      case Constraint.VConversion(context, lhs, rhs, ty) =>
        checkIsConvertible(lhs, rhs, ty)(using context)
      case Constraint.CConversion(context, lhs, rhs, ty) =>
        checkIsConvertible(lhs, rhs, ty)(using context)
      case Constraint.VSubType(context, sub, sup) =>
        checkIsSubtype(sub, sup)(using context)
      case Constraint.CSubType(context, sub, sup) =>
        checkIsSubtype(sub, sup)(using context)
      case Constraint.EffSubsumption(context, sub, sup) =>
        checkEffSubsumption(sub, sup)(using context)
      case Constraint.LevelSubsumption(context, sub, sup) =>
        checkLevelSubsumption(sub, sup)(using context)
      case Constraint.UsageSubsumption(context, sub, sup) =>
        checkUsageSubsumption(sub, sup)(using context)
      case Constraint.EqDecidabilitySubsumption(context, sub, sup) =>
        checkEqDecidabilitySubsumption(sub, sup)(using context)
      case Constraint.HandlerTypeSubsumption(context, sub, sup) =>
        checkHandlerTypeSubsumption(sub, sup)(using context)

  @throws(classOf[IrError])
  inline def trace[R]
    (
      title: => String,
      description: => Block | String = "",
      successMsg: R => Block | String = (_: R) => "",
      failureMsg: Signature ?=> IrError => Block | String = (e: IrError) =>
        val exceptionFileAndLine = e.getStackTrace
          .nn(1)
          .toString
          .split('(')
          .last
          .stripSuffix(")")
        verbosePPrinter
          .copy(
            additionalHandlers = {
              case t: (VTerm | CTerm) =>
                Tree.Literal(PrettyPrinter.pprint(t)(using e.Γ).toString)
              case x: (QualifiedName | Name | Ref[?]) => verbosePPrinter.additionalHandlers(x)
            },
          )
          .apply(e)
          .toString + "[" + exceptionFileAndLine + "]",
    )
    (action: => R)
    (using Γ: Context)
    (using Signature)
    : R =
    val indent = "│ " * traceLevel
    if enableDebugging then
      println(indent)
      println(
        indent + "   " + ANSI_BLUE + pprint(Γ.toList)(using IndexedSeq[Binding[VTerm]]()).toString
          .replaceAll("\n", "\n" + indent + "   ") + ANSI_RESET,
      )
      val stacktrace: String = Thread.currentThread().nn.getStackTrace.nn(2).toString
      val fileAndLine = stacktrace.split('(').last.stripSuffix(")")
      println(indent + "┌─ " + title + " " + ANSI_WHITE + "@ " + fileAndLine + ANSI_RESET)
      if description != "" then
        println(
          (indent + "│  " + description).replaceAll("\n", "\n" + indent + "│  "),
        )
      traceLevel += 1
      try
        val r = action
        traceLevel -= 1
        val message = "✅ " + (ANSI_GREEN + successMsg(r)).replaceAll(
          "\n",
          "\n" + indent + "     ",
        )
        println(indent + "└─ " + message + ANSI_RESET + " @ " + fileAndLine)
        r
      catch
        case e: IrError =>
          val message = "❌ " + (ANSI_RED + failureMsg(e))
            .replaceAll("\n", "\n" + indent + "     ")
          traceLevel -= 1
          println(indent + "└─ " + message + ANSI_RESET + " @ " + fileAndLine)
          throw e
    else action

  inline def debug[T](inline t: T): T =
    if enableDebugging then
      val indent = "│ " * traceLevel + " "
      println(
        indent + ANSI_CYAN + stringify(t) + " = " + verbosePPrinter
          .apply(t)
          .toString
          .replace("\n", "\n" + indent) + ANSI_RESET,
      )
    t

  inline def debugPrint[T](inline t: T): T =
    if enableDebugging then
      val indent = "│ " * traceLevel
      println(indent + " " + ANSI_CYAN + t + ANSI_RESET)
    t

  def breakpoint(): Unit =
    if enableDebugging then
      val i = 1

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

@throws(classOf[IrError])
def checkData(data: Data)(using Σ: Signature)(using ctx: TypingContext): Data =
  given Context = IndexedSeq()
  ctx.trace(s"checking data signature ${data.qn}"):

    val tParamsTysTelescope = checkParameterTyDeclarations(data.context.map(_._1).toTelescope)
    val tParamTys = Context.fromTelescope(tParamsTysTelescope)
    val tIndexTys = checkParameterTyDeclarations(data.tIndexTys)(using tParamTys)
    val tContext = tParamTys ++ tIndexTys
    checkTParamsAreUnrestricted(tContext.toTelescope)
    val (level, _) = checkLevel(data.level)(using tParamTys)
    val (inherentEqDecidability, _) =
      checkType(data.inherentEqDecidability, EqDecidabilityType())(using tParamTys)
    Data(data.qn, tParamTys.zip(data.context.map(_._2)), tIndexTys, level, inherentEqDecidability)

@throws(classOf[IrError])
def checkDataConstructor
  (qn: QualifiedName, con: Constructor)
  (using Σ: Signature)
  (using ctx: TypingContext)
  : Constructor =
  Σ.getDataOption(qn) match
    case None => throw MissingDeclaration(qn)
    case Some(data) =>
      given Γ: Context = data.context.map(_._1)
      ctx.trace(s"checking data constructor $qn.${con.name}"):
        val paramTys = checkParameterTyDeclarations(con.paramTys, Some(data.level))
        val (tArgs, _) =
          checkTypes(con.tArgs, data.tIndexTys.weaken(con.paramTys.size, 0))(using Γ ++ paramTys)
        val violatingVars =
          VarianceChecker.visitTelescope(con.paramTys)(using data.context, Variance.COVARIANT, 0)
        if violatingVars.nonEmpty then throw IllegalVarianceInData(data.qn, violatingVars.toSet)
        checkConstructorEqDecidability(data.qn, con, data.inherentEqDecidability)
        Constructor(con.name, paramTys, tArgs)

@throws(classOf[IrError])
private def checkConstructorEqDecidability
  (qn: QualifiedName, constructor: Constructor, dataEqDecidability: VTerm)
  (using Γ: Context)
  (using Σ: Signature)
  (using ctx: TypingContext)
  : Unit = ctx.trace(s"check constructor eq-decidability $qn.${constructor.name}"):
  // No need to check anything if data is declared to be eq-undecidable.
  if dataEqDecidability != EqDecidabilityLiteral(EqUnknown) then
    // When deciding equality, components that are referenced in data index (except those under
    // Collapse) arguments are guaranteed to be equal because type checker has enforced the type
    // equality at compile time. Hence, we do not need to check eqDecidability of these components.
    val dataIndexReferencedComponentIndex = constructor.tArgs
      .flatMap(IgnoreCollapseFreeVarsVisitor.visitVTerm(_)(using 0))
      .map(v => constructor.paramTys.size - 1 - v.idx)
      .filter(_ >= 0)
      .toSet

    @tailrec
    def checkComponents(components: Telescope, i: Nat)(using Γ: Context): Unit =
      components match
        case Nil =>
        case binding :: rest =>
          if !dataIndexReferencedComponentIndex(i) then
            ctx.checkSolved(
              checkEqDecidabilitySubsumption(
                inferEqDecidability(binding.ty),
                dataEqDecidability.weaken(i, 0),
              ),
              NotEqDecidableDueToConstructor(qn, constructor.name, i),
            )
            ctx.checkSolved(
              checkUsageSubsumption(binding.usage, u1),
              NotEqDecidableDueToConstructor(qn, constructor.name, i),
            )
          checkComponents(rest, i + 1)(using Γ :+ binding)
    checkComponents(constructor.paramTys, 0)

private object IgnoreCollapseFreeVarsVisitor extends FreeVarsVisitorTrait:
  override def visitCollapse(collapse: Collapse)(using ctx: Nat)(using Σ: Signature): Seq[Var] =
    Seq.empty

@throws(classOf[IrError])
def checkRecord(record: Record)(using Σ: Signature)(using ctx: TypingContext): Record =
  given Context = IndexedSeq()
  ctx.trace(s"checking record signature ${record.qn}"):
    val tParams = record.context.map(_._1)
    val tParamTysTelescope = checkParameterTyDeclarations(tParams.toList)
    val tParamTys = Context.fromTelescope(tParamTysTelescope)
    checkTParamsAreUnrestricted(tParams.toList)
    val (level, _) = checkLevel(record.level)(using tParams.toIndexedSeq)
    // There is no need to check selfBinding since it's generated by elaboration and is guaranteed
    // to be correct.
    Record(
      record.qn,
      tParamTys.zip(record.context.map(_._2)),
      level,
      record.selfBinding,
    )

@throws(classOf[IrError])
def checkRecordField
  (qn: QualifiedName, field: Field)
  (using Σ: Signature)
  (using ctx: TypingContext)
  : Field =
  Σ.getRecordOption(qn) match
    case None => throw MissingDeclaration(qn)
    case Some(record) =>
      given Context = record.context.map(_._1).toIndexedSeq :+ record.selfBinding

      ctx.trace(s"checking record field $qn.${field.name}"):
        val (ty, _) = checkIsCType(field.ty, Some(record.level.weakened))
        val violatingVars =
          // 1 is to offset self binding.
          VarianceChecker.visitCTerm(field.ty)(using record.context, Variance.COVARIANT, 1)
        if violatingVars.nonEmpty then throw IllegalVarianceInRecord(record.qn, violatingVars.toSet)
        Field(field.name, ty)

private object VarianceChecker extends Visitor[(TContext, Variance, Nat), Seq[Var]]:
  override def combine
    (violatedVars: Seq[Var]*)
    (using ctx: (TContext, Variance, Nat))
    (using Σ: Signature)
    : Seq[Var] =
    violatedVars.flatten

  override def withBindings
    (bindingNames: => Seq[Ref[Name]])
    (action: ((TContext, Variance, Nat)) ?=> Seq[Var])
    (using ctx: (TContext, Variance, Nat))
    (using Σ: Signature)
    : Seq[Var] =
    val (tContext, variance, offset) = ctx
    action(using (tContext, variance, offset + bindingNames.size))

  override def visitVar
    (v: Var)
    (using ctx: (TContext, Variance, Nat))
    (using Σ: Signature)
    : Seq[Var] =
    val (tContext, variance, offset) = ctx
    val index = v.idx - offset
    if index < 0 then return Nil
    tContext.resolve(index)._2 match
      case Variance.INVARIANT => Nil
      case declaredVariance =>
        if declaredVariance == variance then Nil
        else Seq(v.strengthen(offset, 0).asInstanceOf[Var])

  override def visitVTerm
    (tm: VTerm)
    (using ctx: (TContext, Variance, Nat))
    (using Σ: Signature)
    : Seq[Var] =
    val (tContext, _, offset) = ctx
    tm match
      case _: (Type | Var | U | DataType) => super.visitVTerm(tm)(using ctx)
      case _ => super.visitVTerm(tm)(using (tContext, Variance.INVARIANT, offset))

  override def visitDataType
    (dataType: DataType)
    (using ctx: (TContext, Variance, Nat))
    (using Σ: Signature)
    : Seq[Var] =
    val (tContext, variance, offset) = ctx
    val data = Σ.getData(dataType.qn)
    (data.context.map(_._2) ++ data.tIndexTys.map(_ => Variance.INVARIANT))
      .zip(dataType.args)
      .flatMap:
        case (Variance.INVARIANT, arg) =>
          visitVTerm(arg)(using (tContext, Variance.INVARIANT, offset))
        case (Variance.COVARIANT, arg) => visitVTerm(arg)(using ctx)
        case (Variance.CONTRAVARIANT, arg) =>
          visitVTerm(arg)(using (tContext, variance.flip, offset))
      .toSeq

  override def visitCTerm
    (tm: CTerm)
    (using ctx: (TContext, Variance, Nat))
    (using Σ: Signature)
    : Seq[Var] =
    val (tContext, _, offset) = ctx
    tm match
      case _: (CType | F | FunctionType | RecordType) => super.visitCTerm(tm)(using ctx)
      case _ => super.visitCTerm(tm)(using (tContext, Variance.INVARIANT, offset))

  override def visitCType
    (cType: CType)
    (using ctx: (TContext, Variance, Nat))
    (using Σ: Signature)
    : Seq[Var] =
    val (tContext, _, offset) = ctx
    combine(
      visitCTerm(cType.upperBound),
      visitVTerm(cType.effects)(using (tContext, Variance.INVARIANT, offset)),
    )
  override def visitF(f: F)(using ctx: (TContext, Variance, Nat))(using Σ: Signature): Seq[Var] =
    val (tContext, _, offset) = ctx
    val invariantCtx = (tContext, Variance.INVARIANT, offset)
    combine(
      visitVTerm(f.vTy),
      visitVTerm(f.effects)(using invariantCtx),
      visitVTerm(f.usage)(using invariantCtx),
    )

  override def visitFunctionType
    (functionType: FunctionType)
    (using ctx: (TContext, Variance, Nat))
    (using Σ: Signature)
    : Seq[Var] =
    val (tContext, variance, offset) = ctx
    val invariantCtx = (tContext, Variance.INVARIANT, offset)
    val contravariantCtx = (tContext, variance.flip, offset)
    combine(
      visitVTerm(functionType.binding.ty)(using contravariantCtx),
      withBindings(Seq(functionType.binding.name)) {
        visitCTerm(functionType.bodyTy)
      },
      visitVTerm(functionType.effects)(using invariantCtx),
    )
  override def visitRecordType
    (recordType: RecordType)
    (using ctx: (TContext, Variance, Nat))
    (using Σ: Signature)
    : Seq[Var] =
    val (tContext, variance, offset) = ctx
    val record = Σ.getRecord(recordType.qn)
    record.context
      .map(_._2)
      .zip(recordType.args)
      .flatMap:
        case (Variance.INVARIANT, arg) =>
          visitVTerm(arg)(using (tContext, Variance.INVARIANT, offset))
        case (Variance.COVARIANT, arg) => visitVTerm(arg)(using ctx)
        case (Variance.CONTRAVARIANT, arg) =>
          visitVTerm(arg)(using (tContext, variance.flip, offset))
      .toSeq

@throws(classOf[IrError])
def checkDef(definition: Definition)(using Signature)(using ctx: TypingContext): Definition =
  given Context = definition.context
  ctx.trace(s"checking def signature ${definition.qn}"):
    val (ty, _) = checkIsCType(definition.ty)
    Definition(definition.qn, definition.context, ty)

@throws(classOf[IrError])
def checkEffect(effect: Effect)(using Signature)(using ctx: TypingContext): Effect =
  given Context = IndexedSeq()
  ctx.trace(s"checking effect signature ${effect.qn}"):

    val telescope = checkParameterTyDeclarations(effect.context.toTelescope)
    checkTParamsAreUnrestricted(telescope)
    checkAreEqDecidableTypes(telescope)
    val Γ = telescope.reverse.toIndexedSeq
    val (continuationUsage, _) = checkType(effect.continuationUsage, UsageType())(using Γ)
    val (handlerType, _) = checkType(effect.handlerType, HandlerTypeType())(using Γ)
    Effect(effect.qn, Γ, continuationUsage, handlerType)

@throws(classOf[IrError])
def checkOperation
  (qn: QualifiedName, operation: Operation)
  (using Σ: Signature)
  (using ctx: TypingContext)
  : Operation =
  Σ.getEffectOption(qn) match
    case None => throw MissingDeclaration(qn)
    case Some(effect) =>
      given Γ: Context = effect.context

      ctx.trace(s"checking effect operation $qn.${operation.name}"):
        val paramTys = checkParameterTyDeclarations(operation.paramTys)
        val (resultTy, _) = checkIsType(operation.resultTy)(using Γ ++ operation.paramTys)
        val (resultUsage, _) =
          checkType(operation.resultUsage, UsageType(None))(using Γ ++ operation.paramTys)
        operation.copy(paramTys = paramTys, resultTy = resultTy, resultUsage = resultUsage)

@tailrec
@throws(classOf[IrError])
private def checkTParamsAreUnrestricted
  (tParamTys: Telescope)
  (using Γ: Context)
  (using Σ: Signature)
  (using ctx: TypingContext)
  : Unit = tParamTys match
  case Nil =>
  case binding :: rest =>
    ctx.checkSolved(
      checkUsageSubsumption(binding.usage, UsageLiteral(UAny)),
      ExpectUnrestrictedTypeParameterBinding(binding),
    )
    checkTParamsAreUnrestricted(rest)(using Γ :+ binding)

@throws(classOf[IrError])
private def checkParameterTyDeclarations
  (tParamTys: Telescope, levelBound: Option[VTerm] = None)
  (using Γ: Context)
  (using Σ: Signature)
  (using TypingContext)
  : Telescope = tParamTys match
  case Nil => Nil
  case binding :: rest =>
    val (ty, _) = checkIsType(binding.ty, levelBound)
    val (usage, _) = checkType(binding.usage, UsageType(None))
    Binding(ty, usage)(binding.name) :: checkParameterTyDeclarations(rest)(using Γ :+ binding)

@throws(classOf[IrError])
private def checkLevel
  (level: VTerm)
  (using Γ: Context)
  (using Signature)
  (using TypingContext)
  : (VTerm, Usages) =
  checkType(level, LevelType(LevelOrder.upperBound))

// Precondition: tm is already type-checked and is normalized
@throws(classOf[IrError])
def inferLevel(ty: VTerm)(using Γ: Context)(using Σ: Signature)(using ctx: TypingContext): VTerm =
  ctx.trace[VTerm](
    "inferLevel",
    Block(ChopDown, Aligned, yellow(ty.sourceInfo), pprint(ty)),
    level => Block(ChopDown, Aligned, yellow(level.sourceInfo), green(pprint(level))),
  ):
    ctx.withMetaResolved(ty):
      case u: ResolvedMetaVariable =>
        val levelBound =
          Collapse(ctx.addUnsolved(F(LevelType(LevelOrder.upperBound))))
        val typeBound =
          Collapse(ctx.addUnsolved(F(Type(Top(levelBound)))))
        val effects =
          Collapse(ctx.addUnsolved(F(EffectsType())))
        val usage =
          Collapse(ctx.addUnsolved(F(UsageType())))
        ctx.checkSolved(
          checkIsConvertible(u.ty, F(Type(typeBound), effects, usage), None),
          NotTypeError(ty),
        )
        inferLevel(typeBound.normalized)
      case Type(upperBound) => LevelSuc(inferLevel(upperBound))
      case Top(level, _)    => level
      case r: Var =>
        val levelBound =
          Collapse(ctx.addUnsolved(F(LevelType(LevelOrder.upperBound))))
        val typeBound =
          Collapse(ctx.addUnsolved(F(Type(Top(levelBound)))))
        ctx.checkSolved(
          checkIsConvertible(Γ.resolve(r).ty, Type(typeBound), None),
          NotTypeError(ty),
        )
        inferLevel(typeBound.normalized)
      case t: Collapse =>
        val (_, ty, _) = inferType(t)
        val levelBound =
          Collapse(ctx.addUnsolved(F(LevelType(LevelOrder.upperBound))))
        val typeBound =
          Collapse(ctx.addUnsolved(F(Type(Top(levelBound)))))
        ctx.checkSolved(
          checkIsConvertible(ty, Type(typeBound), None),
          NotTypeError(ty),
        )
        inferLevel(typeBound.normalized)
      case U(cty) => inferLevel(cty)
      case DataType(qn, args) =>
        val data = Σ.getData(qn)
        data.level.substLowers(args.take(data.context.size)*)
      case _: UsageType | _: EqDecidabilityType | _: EffectsType => LevelLiteral(0)
      case LevelType(strictUpperBound)                           => LevelLiteral(strictUpperBound)
      case _ => throw IllegalArgumentException(s"should have been checked to be a type: $ty")

// Precondition: tm is already type-checked and is normalized
@throws(classOf[IrError])
private def inferLevel
  (telescope: Telescope)
  (using Γ: Context)
  (using Σ: Signature)
  (using ctx: TypingContext)
  : VTerm =
  telescope match
    case Nil             => LevelLiteral(0)
    case binding :: rest =>
      // strengthen is always safe because the only case that rest-level would reference 0 is when
      // arg is of type Level. But in that case the overall level would be ω.
      LevelMax(binding.ty.weakened, inferLevel(rest)(using Γ :+ binding)).normalized.strengthened

@throws(classOf[IrError])
def inferType
  (tm: VTerm)
  (using Γ: Context)
  (using Σ: Signature)
  (using ctx: TypingContext)
  : (VTerm, VTerm, Usages) = debugInferType(tm):
  tm match
    case Type(uncheckedUpperBound) =>
      val (upperBound, upperBoundUsages) = checkIsType(uncheckedUpperBound)
      val newTm = Type(upperBound.normalized)(using tm.sourceInfo)
      (newTm, Type(newTm), upperBoundUsages)
    case Top(uncheckedLevel, uncheckedEqD) =>
      val (level, ulUsage) = checkLevel(uncheckedLevel)
      val (eqD, eqDUsage) = checkType(uncheckedEqD, EqDecidabilityType())
      val newTm = Top(level, eqD.normalized)(using tm.sourceInfo)
      (newTm, Type(newTm), ulUsage + eqDUsage)
    case r: Var => (r, Γ.resolve(r).ty, Usages.single(r))
    case Collapse(uncheckedCTm) =>
      val (cTm, cTy, usage) = inferType(uncheckedCTm)
      val vTy = cTy match
        case F(vTy, _, u) if isTotal(cTm, Some(cTy)) =>
          ctx.checkSolved(checkUsageSubsumption(u, u1), CollapsingU0Term(cTm))
          vTy
        case F(_, _, _) => throw CollapsingEffectfulTerm(cTm)
        case _          => throw NotCollapsable(cTm)
      (Collapse(cTm), vTy, usage)
    case U(uncheckedCty) =>
      val (cty, ctyTy, usage) = inferType(uncheckedCty)
      val newTm = U(cty)(using tm.sourceInfo)
      val newTy = ctyTy match
        case CType(_, _) if isTotal(cty, Some(ctyTy)) => Type(newTm)
        // TODO[P0]: think about if this is desirable
        // Automatically promote SomeVType to F(SomeVType)
        case F(Type(_), _, _) if isTotal(cty, Some(ctyTy)) => Type(newTm)
        case CType(_, _) | F(Type(_), _, _)                => throw EffectfulCTermAsType(cty)
        case _                                             => throw NotTypeError(tm)
      (newTm, newTy, usage)
    case Thunk(c) =>
      val (newC, cty, usage) = inferType(c)
      (Thunk(newC), U(cty), usage)
    case DataType(qn, uncheckedArgs) =>
      Σ.getDataOption(qn) match
        case None => throw MissingDeclaration(qn)
        case Some(data) =>
          val (args, usage) =
            checkTypes(uncheckedArgs, (data.context.map(_._1) ++ data.tIndexTys).toList)
          val newTm = DataType(qn, args.map(_.normalized))(using tm.sourceInfo)
          (newTm, Type(newTm), usage)
    case _: Con          => throw IllegalArgumentException("cannot infer type")
    case u: UsageLiteral => (u, UsageType(Some(u)), Usages.zero)
    case UsageProd(uncheckedOperands) =>
      val (operands, usages) = transposeCheckTypeResults(
        uncheckedOperands.map(o => checkType(o, UsageType(None))),
      )
      val newTm = UsageProd(operands.toSet)(using tm.sourceInfo).normalized
      (newTm, UsageType(Some(newTm)), usages)
    case UsageSum(uncheckedOperands) =>
      val (operands, usages) = transposeCheckTypeResults(
        uncheckedOperands.multiToSeq.map(o => checkType(o, UsageType(None))),
      )
      val newTm = UsageSum(operands.toMultiset)(using tm.sourceInfo).normalized
      (newTm, UsageType(Some(newTm)), usages)
    case UsageJoin(uncheckedOperands) =>
      val (operands, usages) = transposeCheckTypeResults(
        uncheckedOperands.map(o => checkType(o, UsageType(None))),
      )
      val newTm = UsageJoin(operands.toSet)(using tm.sourceInfo).normalized
      (newTm, UsageType(Some(newTm)), usages)
    case u: UsageType =>
      u.upperBound.map(upperBound => checkType(upperBound, UsageType(None))) match
        case Some(upperBound, usages) => (u, Type(UsageType(Some(upperBound))), usages)
        case _                        => (u, Type(u), Usages.zero)
    case eqD: EqDecidabilityType          => (eqD, Type(eqD), Usages.zero)
    case eqD: EqDecidabilityLiteral       => (eqD, EqDecidabilityType(), Usages.zero)
    case handlerTypeType: HandlerTypeType => (handlerTypeType, Type(handlerTypeType), Usages.zero)
    case handlerType: HandlerTypeLiteral  => (handlerType, HandlerTypeType(), Usages.zero)
    case EffectsType(continuationUsage, handlerType) =>
      val (checkedContinuationUsage, u1) = checkType(continuationUsage, UsageType())
      val (checkedHandlerType, u2) = checkType(handlerType, HandlerTypeType())
      val e = EffectsType(checkedContinuationUsage, checkedHandlerType)
      (e, Type(e), u1 + u2)
    case Effects(uncheckedLiteral, checkedOperands) =>
      val (literal, literalUsages) = transposeCheckTypeResults(
        uncheckedLiteral.map { (qn, args) =>
          Σ.getEffectOption(qn) match
            case None => throw MissingDeclaration(qn)
            case Some(effect) =>
              val (checkedArgs, usages) = checkTypes(args, effect.context.toList)
              ((qn, checkedArgs), usages)
        },
      )
      val (operands, operandsUsages) = transposeCheckTypeResults(
        checkedOperands.map { (ref, retainSimple) =>
          val (v, usages) = checkType(ref, EffectsType())
          ((v, retainSimple), usages)
        }.toList,
      )
      val newTm: Effects = Effects(literal.toSet, operands.to(SeqMap))(using tm.sourceInfo)
      val usage = getEffectsContinuationUsage(newTm)
      (
        newTm,
        EffectsType(usage),
        literalUsages + operandsUsages,
      )
    case LevelType(strictUpperBound) =>
      (LevelType(strictUpperBound), Type(LevelType(strictUpperBound)), Usages.zero)
    case Level(literal, maxOperands) =>
      val operandsResults = maxOperands.toSeq.map((v, offset) => (inferType(v), offset))
      val newMaxOperands = operandsResults
        .map { case ((t, _, _), offset) =>
          t -> offset
        }
        .to(SeqMap)
      val upperbound = operandsResults
        .map {
          case ((_, LevelType(upperbound), _), offset) => upperbound.sucAsStrictUpperbound(offset)
          case ((_, t, _), _) =>
            ctx.checkSolved(
              checkIsConvertible(t, LevelType(LevelOrder.ω), None),
              NotLevelType(t),
            )
            LevelOrder.ω
        }
        .foldLeft(literal.suc())(LevelOrder.orderMax)
      val usages = operandsResults.map(_._1._3).foldLeft(Usages.zero)(_ + _)
      (Level(literal, newMaxOperands), LevelType(upperbound), usages)
    case Auto() => throw IllegalArgumentException("cannot infer type")

@throws(classOf[IrError])
def checkType
  (tm: VTerm, ty: VTerm)
  (using Γ: Context)
  (using Σ: Signature)
  (using ctx: TypingContext)
  : (VTerm, Usages) = debugCheckType(tm, ty):
  tm match
    case Collapse(c) =>
      val (tm, usages) = checkType(c, F(ty))
      (Collapse(tm), usages)
    case Thunk(c) =>
      ty match
        case U(cty) =>
          val (tm, usages) = checkType(c, cty)
          (Thunk(tm), usages)
        case _ => throw ExpectUType(ty)
    case c @ Con(name, uncheckedArgs) =>
      ty match
        case dataType @ DataType(qn, tArgs) =>
          Σ.getConstructorOption(qn, name) match
            case None => throw MissingConstructor(name, qn)
            case Some(con) =>
              val data = Σ.getData(qn)
              val tParamArgs = tArgs.take(data.context.size)
              val tIndexArgs = tArgs.drop(data.context.size)
              val (args, usages) =
                checkTypes(uncheckedArgs, con.paramTys.substLowers(tParamArgs*))
              ctx.checkSolved(
                checkAreConvertible(
                  con.tArgs.map(_.substLowers(tParamArgs ++ args*)),
                  tIndexArgs,
                  data.tIndexTys.substLowers(tParamArgs*),
                ),
                UnmatchedDataIndex(c, dataType),
              )
              (DataType(qn, args), usages)
        case _ => throw ExpectDataType(ty)
    case Auto() =>
      (
        Collapse(ctx.addUnsolved(F(ty))),
        // TODO[P0]: this is wrong. Usage checking will have to be delayed as a separate pass
        Usages.zero,
      )
    case _ =>
      val (newTm, inferred, usages) = inferType(tm)
      val constraints = checkIsSubtype(inferred, ty)
      ctx.checkSolved(constraints, NotVSubtype(inferred, ty))
      (newTm, usages)

// Precondition: tm is already type-checked
@throws(classOf[IrError])
def inferLevel(ty: CTerm)(using Γ: Context)(using Σ: Signature)(using ctx: TypingContext): VTerm =
  ctx.trace[VTerm](
    "inferLevel",
    Block(ChopDown, Aligned, yellow(ty.sourceInfo), pprint(ty)),
    level => Block(ChopDown, Aligned, yellow(level.sourceInfo), green(pprint(level))),
  ):
    Reducible.reduce(ty) match
      case CType(upperBound, _) => LevelSuc(inferLevel(upperBound))
      case CTop(level, _)       => level
      case F(vTy, _, _)         => inferLevel(vTy)
      case FunctionType(binding, bodyTy, _) =>
        val argLevel = inferLevel(binding.ty)
        val bodyLevel = inferLevel(bodyTy)(using Γ :+ binding)
        // strengthen is always safe because the only case that bodyLevel would reference 0 is when
        // arg is of type Level. But in that case the overall level would be ω.
        LevelMax(argLevel.weakened, bodyLevel).normalized(using Γ :+ binding).strengthened
      case RecordType(qn, args, _) => Σ.getRecord(qn).level.substLowers(args*)
      case Force(ctm) =>
        val (_, cty, _) = inferType(ctm)
        inferLevel(cty)
      case tm =>
        ctx.resolveMetaVariableType(tm) match
          case Some(ty) =>
            ty match
              // TODO[P1]: consider refactor this to use some helper function for such common patterns where we create a
              // stub term when expecting the meta variable to match certain structure.
              case CType(upperBound, _) => inferLevel(upperBound)
              case cty =>
                val level = ctx.addUnsolved(F(LevelType(LevelOrder.ω)))
                val usage = ctx.addUnsolved(F(UsageType()))
                ctx.checkSolved(
                  checkIsConvertible(
                    cty,
                    CType(CTop(Collapse(level)), Collapse(usage)),
                    None,
                  ),
                  NotCTypeError(tm),
                )
                Collapse(level).normalized
          case _ => throw NotCTypeError(tm)

@throws(classOf[IrError])
def inferType
  (tm: CTerm)
  (using Γ: Context)
  (using Σ: Signature)
  (using ctx: TypingContext)
  : (CTerm, CTerm, Usages) =
  debugInferType(tm):
    tm.normalized match
      case Hole =>
        throw IllegalArgumentException(
          "hole should only be present during reduction",
        )
      case cct @ CapturedContinuationTip(ty) => (cct, ty, Usages.zero)
      case CType(uncheckedUpperBound, uncheckedEffects) =>
        val (effects, effUsages) = checkType(uncheckedEffects, EffectsType())
        val (upperBound, upperBoundUsages) = checkIsCType(uncheckedUpperBound)
        val newTm = CType(upperBound.normalized(None), effects.normalized)
        (
          newTm,
          CType(newTm, Total()),
          effUsages + upperBoundUsages,
        )
      case CTop(uncheckedLevel, uncheckedEffects) =>
        val (effects, uUsages) = checkType(uncheckedEffects, EffectsType())
        val (level, ulUsages) = checkLevel(uncheckedLevel)
        val newTm = CTop(level, effects.normalized)(using tm.sourceInfo)
        (newTm, CType(newTm, Total()), uUsages + ulUsages)
      case m: Meta => (m, ctx.resolveMeta(m).contextFreeType, Usages.zero)
      case d @ Def(qn) =>
        Σ.getDefinitionOption(qn) match
          case None => throw MissingDeclaration(qn)
          case Some(definition) =>
            (
              d,
              definition.context.foldRight(definition.ty) { case (binding, bodyTy) =>
                FunctionType(binding, bodyTy, Total())
              },
              Usages.zero,
            )
      case Force(uncheckedV) =>
        val (v, vTy, vUsages) = inferType(uncheckedV)
        val cTy = vTy match
          // TODO: think about whether this is good enough.
          // Annotating all force as maybe-divergent because the computations may be dynamically
          // loaded from handlers and hence there is no way to statically detect cyclic references
          // between computations (functions, etc) unless I make the type system even more
          // complicated to somehow tracking possible call-hierarchy.
          case U(cty) => augmentEffect(MaybeDiv(), cty)
          case _      => throw ExpectUType(vTy)
        (Force(v), cTy, vUsages)
      case F(uncheckedVTy, uncheckedEffects, uncheckedUsage) =>
        val (effects, effUsages) = checkType(uncheckedEffects, EffectsType())
        val (unnormalizedUsage, uUsages) = checkType(uncheckedUsage, UsageType(None))
        val usage = unnormalizedUsage.normalized
        // Prevent returning value of U0 usage, which does not make sense.
        ctx.checkSolved(
          checkUsageSubsumption(usage, UsageLiteral(Usage.U1)),
          NotUsageSubsumption(usage, UsageLiteral(Usage.U1)),
        )
        val levelBound = Collapse(ctx.addUnsolved(F(LevelType(LevelOrder.upperBound))))
        val (unnormalizedVTy, vTyUsages) = checkType(
          uncheckedVTy,
          Type(Collapse(ctx.addUnsolved(F(Type(Top(levelBound)))))),
        )
        val vTy = unnormalizedVTy.normalized
        val newTm = F(vTy, effects, usage)(using tm.sourceInfo)
        (newTm, CType(newTm, Total()), effUsages + uUsages + vTyUsages)
      case Return(uncheckedV, usage) =>
        val (v, vTy, vUsages) = inferType(uncheckedV)
        (Return(v, usage), F(vTy, Total(), usage), vUsages * usage)
      case tm: Let => checkLet(tm, None)
      case FunctionType(binding, uncheckedBodyTy, uncheckedEffects) =>
        val (effects, effUsages) = checkType(uncheckedEffects, EffectsType())
        val (ty, tyTy, tyUsages) = inferType(binding.ty)
        val (bindingUsage, bindingUsageUsages) = checkType(binding.usage, UsageType(None))
        val (newTm, funTyTy, bodyTyUsages) = tyTy match
          case Type(_) =>
            val (bodyTy, bodyTyTy, bodyTyUsages) = inferType(uncheckedBodyTy)(using Γ :+ binding)
            val newTm =
              FunctionType(Binding(ty, bindingUsage)(binding.name), bodyTy, effects.normalized)(
                using tm.sourceInfo,
              )
            bodyTyTy match
              case CType(_, _) if isTotal(bodyTy, Some(bodyTyTy)) =>
                // Strengthen is safe here because if it references the binding, then the
                // binding must be at level ω and hence ULevelMax would return big type.
                // Also, there is no need to check the dropped usage because usages in types
                // is always multiplied by U0.
                (
                  newTm,
                  CType(newTm, Total()),
                  bodyTyUsages.dropRight(1).map(_.strengthened),
                )
              // TODO[P3]: think about whether the following is actually desirable
              // Automatically promote Return(SomeVType) to F(SomeVType) and proceed type
              // inference.
              case F(Type(_), _, _) if isTotal(bodyTy, Some(bodyTyTy)) =>
                (
                  newTm,
                  CType(newTm, Total()),
                  bodyTyUsages.dropRight(1).map(_.strengthened),
                )
              case CType(_, _) | F(Type(_), _, _) => throw EffectfulCTermAsType(bodyTy)
              case _                              => throw NotCTypeError(bodyTy)
          case _ => throw NotTypeError(binding.ty)
        (newTm, funTyTy, effUsages + tyUsages + bodyTyUsages + bindingUsageUsages)
      case Redex(c, elims) =>
        @throws(classOf[IrError])
        def checkElims
          (checkedElims: List[Elimination[VTerm]], cty: CTerm, elims: List[Elimination[VTerm]])
          : (List[Elimination[VTerm]], CTerm, Usages) =
          elims match
            case Nil                                        => (Nil, cty, Usages.zero)
            case (e @ ETerm(uncheckedArg)) :: uncheckedRest =>
              // Note that this `cty` is created by `inferType` so it's already checked.
              cty match
                case FunctionType(binding, bodyTy, effects) =>
                  val (arg, argUsages) = checkType(uncheckedArg, binding.ty)
                  val (rest, cty, restUsages) =
                    checkElims(
                      e :: checkedElims,
                      bodyTy.substLowers(arg).normalized(None),
                      uncheckedRest,
                    )
                  val continuationUsage = getEffectsContinuationUsage(effects)
                  (
                    ETerm(arg) :: rest,
                    augmentEffect(effects, cty),
                    argUsages + restUsages * continuationUsage,
                  )
                case _ => throw ExpectFunction(redex(c, checkedElims.reverse))
            case (e @ EProj(name)) :: uncheckedRest =>
              cty match
                case RecordType(qn, args, effects) =>
                  Σ.getFieldOption(qn, name) match
                    case None    => throw MissingField(name, qn)
                    case Some(f) =>
                      // `self` of record is only used in type checking. Hence usages of variables
                      // in the record are not counted.
                      val self = redex(c, checkedElims)
                      val (rest, checkedCty, restUsages) = checkElims(
                        e :: checkedElims,
                        f.ty.substLowers(args :+ Thunk(self)*).normalized(None),
                        uncheckedRest,
                      )
                      val continuationUsage = getEffectsContinuationUsage(effects)
                      (
                        EProj(name) :: rest,
                        augmentEffect(effects, checkedCty),
                        restUsages * continuationUsage,
                      )
                case _ => throw ExpectRecord(redex(c, checkedElims.reverse))
        val (checkedC, cty, usages) = inferType(c)
        val (_, resultCty, argUsages) = checkElims(Nil, cty, elims)
        (redex(checkedC, elims), resultCty, usages + argUsages)
      case RecordType(qn, uncheckedArgs, uncheckedEffects) =>
        Σ.getRecordOption(qn) match
          case None => throw MissingDeclaration(qn)
          case Some(record) =>
            val (effects, effUsages) = checkType(uncheckedEffects, EffectsType())
            val (args, argsUsages) = checkTypes(uncheckedArgs, record.context.map(_._1).toList)
            (RecordType(qn, args, effects), CType(tm, Total()), effUsages + argsUsages)
      case OperationCall((qn, uncheckedTArgs), name, uncheckedArgs) =>
        Σ.getEffectOption(qn) match
          case None => throw MissingDeclaration(qn)
          case Some(effect) =>
            Σ.getOperationOption(qn, name) match
              case None => throw MissingDefinition(qn)
              case Some(op) =>
                val (checkedTArgs, effUsages) = checkTypes(uncheckedTArgs, effect.context.toList)
                val tArgs = checkedTArgs.map(_.normalized)
                val (args, argsUsages) =
                  checkTypes(uncheckedArgs, op.paramTys.substLowers(tArgs*))
                val newEff = (qn, tArgs)
                val newTm = OperationCall(newEff, name, args)(using tm.sourceInfo)
                val ty = op.resultTy.substLowers(tArgs ++ args*).normalized
                (
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
      case Continuation(uncheckedHandler, continuationUsage) =>
        @tailrec
        def findTip(c: CTerm): CapturedContinuationTip = c match
          case c: CapturedContinuationTip => c
          case l: Let                     => findTip(l)
          case h: Handler                 => findTip(h.input)
          case r: Redex                   => findTip(r.t)
          case _                          => throw IllegalStateException("impossible term")
        val CapturedContinuationTip(F(resultTy, _, resultUsage)) = findTip(uncheckedHandler)
        val (checkedHandler, outputTy, handlerUsages) = inferType(uncheckedHandler)
        val handler = checkedHandler.asInstanceOf[Handler]
        val paramLevel = inferLevel(handler.parameterBinding.ty)
        val resultLevel = inferLevel(resultTy)
        val outputLevel = inferLevel(outputTy)
        val continuationLevel = LevelMax(paramLevel, resultLevel, outputLevel).normalized

        (
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

private def getEffVarContinuationUsage(v: Var)(using Γ: Context)(using Signature): VTerm =
  Γ.resolve(v) match
    case Binding(EffectsType(usage, _), _) => usage
    case _ =>
      throw IllegalStateException("typing exception")

@throws(classOf[IrError])
def checkType
  (tm: CTerm, ty: CTerm)
  (using Γ: Context)
  (using Σ: Signature)
  (using ctx: TypingContext)
  : (CTerm, Usages) = debugCheckType(tm, ty):
  tm match
    case Force(v) =>
      val (checkedV, usages) = checkType(v, U(ty))
      (Force(checkedV), usages)
    case Return(v, uncheckedUsage) =>
      ty match
        case F(ty, _, expectedUsage) =>
          // Usage annotation is erased and hence its usages are ignored.
          val (usage, _) = checkType(uncheckedUsage, UsageType())
          val (checkedV, usages) = checkType(v, ty)
          ctx.checkSolved(
            checkUsageSubsumption(usage, expectedUsage),
            NotUsageSubsumption(usage, expectedUsage),
          )
          (Return(checkedV, usage), usages * usage)
        case _ => throw ExpectFType(ty)
    case l: Let =>
      val (v, _, usages) = checkLet(l, Some(ty))
      (v, usages)
    case h: Handler =>
      val (v, _, usages) = checkHandler(h, Some(ty))
      (v, usages)
    case _ =>
      val (checkedTm, tmTy, usages) = inferType(tm)
      val normalizedTy = ty.normalized(None)
      ctx.checkSolved(checkIsSubtype(tmTy, normalizedTy), NotCSubtype(tmTy, normalizedTy))
      (checkedTm, usages)

private object MetaVarVisitor extends Visitor[TypingContext, Set[Int]]():
  override def combine(rs: Set[Int]*)(using ctx: TypingContext)(using Σ: Signature): Set[Int] =
    rs.flatten.to(Set)
  override def visitMeta(m: Meta)(using ctx: TypingContext)(using Σ: Signature): Set[Int] =
    Set(m.index) ++ (ctx.resolveMeta(m) match
      // bounds in unsolved doesn't need to be checked now. They will be checked when they become solved.
      case _: Unsolved             => Set.empty
      case Guarded(_, _, value, _) => visitCTerm(value)
      case Solved(_, _, value)     => visitCTerm(value)
    )

@tailrec
@throws(classOf[IrError])
def inferEqDecidability
  (ty: VTerm)
  (using Γ: Context)
  (using Σ: Signature)
  (using ctx: TypingContext)
  : VTerm =
  ty match
    case _: Type | _: UsageType | _: EqDecidabilityType | _: EffectsType | _: LevelType =>
      EqDecidabilityLiteral(EqDecidable)
    case Top(_, eqDecidability) => eqDecidability
    case _: Var | _: Collapse =>
      val (_, tyTy, _) = inferType(ty)
      tyTy match
        case Type(upperBound) => inferEqDecidability(upperBound)
        case _                => throw ExpectVType(ty)
    case _: U => EqDecidabilityLiteral(EqUnknown)
    case DataType(qn, args) =>
      val data = Σ.getData(qn)
      data.inherentEqDecidability.substLowers(args.take(data.context.size)*)
    case _ => throw ExpectVType(ty)

@throws(classOf[IrError])
private def checkIsEqDecidableTypes
  (ty: VTerm)
  (using Γ: Context)
  (using Σ: Signature)
  (using ctx: TypingContext)
  : Unit =
  val eqD = inferEqDecidability(ty)
  ctx.checkSolved(
    checkIsConvertible(eqD, EqDecidabilityLiteral(EqDecidable), Some(EqDecidabilityType())),
    NotEqDecidableType(ty),
  )

@tailrec
@throws(classOf[IrError])
private def checkAreEqDecidableTypes
  (telescope: Telescope)
  (using Γ: Context)
  (using Σ: Signature)
  (using TypingContext)
  : Unit = telescope match
  case Nil =>
  case binding :: telescope =>
    checkIsEqDecidableTypes(binding.ty)
    checkAreEqDecidableTypes(telescope)(using Γ :+ binding)

/** @param inputUsages
  *   input usage terms should live in Γ ++ telescope
  * @param telescope
  *   signifies which usages to verify
  * @return
  *   unverified usages
  */
@throws(classOf[IrError])
private def verifyUsages
  (inputUsages: Usages, telescope: Telescope)
  (using Γ: Context)
  (using Σ: Signature)
  (using ctx: TypingContext)
  : Usages =
  ctx.trace("verifyUsages"):
    given Γ2: Context = Γ ++ telescope
    val count = telescope.size
    inputUsages.takeRight(count).reverse.zipWithIndex.foreach { (v, i) =>
      // TODO[P1]: refactor usages verification to happen after other checks.
//      ctx.checkSolved(
//        checkUsageSubsumption(v, Γ2.resolve(i).usage),
//        NotUsageSubsumption(v, Γ2.resolve(i).usage),
//      )
    }
    inputUsages.drop(count).map { v =>
      try v.strengthen(count, 0)
      catch
        // It's possible for a term's usage to reference a usage term after it. For example consider
        // functino `f: u: Usage -> [u] Nat -> Nat` and context `{i: Nat, u: Usage}`, then `f u i`
        // has usage `[u, U1]`. In this case, strengthen usage of `i` is approximated by UAny.
        case _: StrengthenException => UsageLiteral(Usage.UAny)
    }

@throws(classOf[IrError])
def checkTypes
  (tms: Seq[VTerm], tys: Telescope)
  (using Γ: Context)
  (using Σ: Signature)
  (using ctx: TypingContext)
  : (List[VTerm], Usages) =
  ctx.trace("checking multiple terms"):
    if tms.length != tys.length then throw TelescopeLengthMismatch(tms, tys)
    else
      transposeCheckTypeResults(
        tms.zip(tys).zipWithIndex.map { case ((tm, binding), index) =>
          checkType(tm, binding.ty.substLowers(tms.take(index)*))
        },
      )

@throws(classOf[IrError])
private def transposeCheckTypeResults[R]
  (resultsAndUsages: Iterable[(R, Usages)])
  (using Context)
  : (List[R], Usages) =
  (resultsAndUsages.map(_._1).toList, resultsAndUsages.map(_._2).fold(Usages.zero)(_ + _))

@throws(classOf[IrError])
private def checkLet
  (tm: Let, bodyTy: Option[CTerm])
  (using Γ: Context)
  (using Σ: Signature)
  (using TypingContext)
  : (CTerm, CTerm, Usages) =
  val (ty, _) = checkIsType(tm.ty)
  // I thought about adding a check on `ty` to see if it's inhabitable. And if it's not, the usages
  // in body can all be trivialized by multiple U0 since they won't execute. But inhabit-ability is
  // not decidable. Even if we only do some conservative checking, it's hard to check polymorphic
  // type `A` for any `A` passed by the caller. An alternative is to designate a bottom type and
  // just check that. But to make this ergonomic we need to tweak the type checker to make this
  // designated type a subtype of everything else. But type inference becomes impossible with `force
  // t` where `t` has type bottom. If we raise a type error for `force t`, this would violate
  // substitution principle of subtypes.
  // On the other hand, if we don't check inhabit-ability, the usages in body would simply be
  // multiplied with UAff instead of U0, which seems to be a reasonable approximation. The primary
  // reason for such a check is just to flag phantom usages of terms, but I think it's not worth all
  // these complexity.
  val (unnormalizedEffects, _) = checkType(tm.eff, EffectsType())
  val effects = unnormalizedEffects.normalized
  val (usage, _) = checkType(tm.usage, UsageType())
  val (t, unnormalizedTUsages) = checkType(tm.t, F(ty, effects, usage))
  val tUsages = unnormalizedTUsages.map(_.normalized)
  val (newTm, checkedBodyTy, usages) =
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
      val uncheckedNewBody = t.normalized(Some(tTy)) match
        case Return(v, _) => tm.body.substLowers(v)
        case c            => tm.body.substLowers(Collapse(c))
      bodyTy match
        case Some(uncheckedBodyTy) =>
          val (bodyTy, _) = checkIsCType(uncheckedBodyTy)
          val (newBody, usages) = checkType(uncheckedNewBody, bodyTy)
          (newBody, bodyTy, usages)
        case None => inferType(uncheckedNewBody)
    // Otherwise, just add the binding to the context and continue type checking.
    else
      val tBinding = Binding(ty, usage)(gn"v")
      val (body, checkedBodyTy, usagesInBody) =
        given Context = Γ :+ tBinding
        bodyTy match
          case None => inferType(tm.body)
          case Some(uncheckedBodyTy) =>
            val (bodyTy, _) = checkIsCType(uncheckedBodyTy)(using Γ)
            val (body, usages) = checkType(tm.body, bodyTy.weakened)
            (body, bodyTy, usages)
      val leakCheckedBodyTy =
        checkVar0Leak(checkedBodyTy, LeakedReferenceToEffectfulComputationResult(t))
      val verifiedUsagesInBody = verifyUsages(usagesInBody, tBinding :: Nil)
      val continuationUsage = getEffectsContinuationUsage(effects)
      (
        Let(t, ty, effects, usage, body)(tm.boundName)(using tm.sourceInfo),
        leakCheckedBodyTy.strengthened,
        verifiedUsagesInBody * continuationUsage,
      )
  (newTm, augmentEffect(effects, checkedBodyTy), usages)

@throws(classOf[IrError])
def checkHandler
  (h: Handler, outputType: Option[CTerm])
  (using Γ: Context)
  (using Σ: Signature)
  (using ctx: TypingContext)
  : (CTerm, CTerm, Usages) =
  val (eff, _) = checkType(h.eff, EffectsType())
  val effs = eff.normalized match
    case Effects(effs, s) if s.isEmpty => effs
    case _                             => throw EffectTermTooComplex(eff)
  val operations = effs.flatMap(e => Σ.getOperations(e._1).map(op => (e._1 / op.name, e._2, op)))
  val expectedOperationNames = operations.map(_._1)
  val actualOperationNames = h.handlers.keySet
  if expectedOperationNames != actualOperationNames then
    throw HandlerOperationsMismatch(h, expectedOperationNames, actualOperationNames)
  val otherEffects = checkType(h.otherEffects, EffectsType())._1.normalized
  val outputEffects = checkType(h.outputEffects, EffectsType())._1.normalized
  val outputUsage = checkType(h.outputUsage, UsageType())._1.normalized
  val (outputTy, _) = checkIsType(h.outputTy)
  outputType match
    case None =>
    case Some(outputType) =>
      ctx.checkSolved(
        checkIsSubtype(F(outputTy, outputEffects, outputUsage), outputType),
        NotCSubtype(F(outputTy, outputEffects, outputUsage), outputType),
      )
  val (parameterTy, _) = checkIsType(h.parameterBinding.ty)
  // parameter binding usage dictates how much resources the handler needs when consuming the parameter
  val (parameterBindingUsage, _) = checkType(h.parameterBinding.usage, UsageType())
  val parameterBinding = Binding(parameterTy, parameterBindingUsage)(h.parameterBinding.name)
  val (parameter, rawParameterUsages) = checkType(h.parameter, parameterTy)
  val parameterUsages = rawParameterUsages * parameterBindingUsage
  val (inputTy, _) = checkIsType(h.inputBinding.ty)
  // Unlike parameter, input is a computation and hence only executed linearly. The input binding usage is simply a
  // requirement on the final return type of the input computation.
  val (inputBindingUsage, _) = checkType(h.inputBinding.usage, UsageType())
  val inputBinding = Binding(inputTy, inputBindingUsage)(h.inputBinding.name)
  val inputEffects = EffectsUnion(eff, otherEffects).normalized
  val (input, inputUsages) = checkType(h.input, F(inputTy, inputEffects, inputBindingUsage))
  val inputEffectsContinuationUsage = getEffectsContinuationUsage(inputEffects)
  val (parameterDisposer, parameterDisposerUsages) = h.parameterDisposer match
    case Some(parameterDisposer) =>
      val (checkedParameterDisposer, parameterDisposerUsages) = checkType(
        parameterDisposer,
        F(DataType(Builtins.UnitQn, Nil), EffectsRetainSimpleLinear(outputEffects).weakened),
      )(using Γ :+ parameterBinding)
      val verifiedParameterDisposerUsages =
        verifyUsages(parameterDisposerUsages, parameterBinding :: Nil)
      (Some(checkedParameterDisposer), verifiedParameterDisposerUsages)
    case None =>
      (inputEffectsContinuationUsage, parameterBindingUsage) match
        case (UsageLiteral(effUsage), UsageLiteral(paramUsage))
          if effUsage <= Usage.URel || paramUsage >= Usage.U0 =>
          (None, Usages.zero)
        case _ => throw ExpectParameterDisposer(h)
  val (parameterReplicator, parameterReplicatorUsages) = h.parameterReplicator match
    case Some(parameterReplicator) =>
      val (checkedParameterReplicator, parameterReplicatorUsages) = checkType(
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
          EffectsRetainSimpleLinear(outputEffects),
        ).weakened,
      )(using Γ :+ parameterBinding)
      val verifiedParameterReplicatorUsages =
        verifyUsages(parameterReplicatorUsages, parameterBinding :: Nil)
      (Some(checkedParameterReplicator), verifiedParameterReplicatorUsages)
    case None =>
      (inputEffectsContinuationUsage, parameterBindingUsage) match
        case (UsageLiteral(effUsage), UsageLiteral(paramUsage))
          if effUsage <= Usage.UAff || paramUsage >= Usage.URel || paramUsage == Usage.U0 =>
          (None, Usages.zero)
        case _ => throw ExpectParameterReplicator(h)
  val (transform, transformUsages) = checkType(
    h.transform,
    F(outputTy, outputEffects, outputUsage).weaken(2, 0),
  )(using Γ :+ parameterBinding :+ inputBinding)

  val handlerAndUsages = operations.map { (qn, effArgs, operation) =>
    val effect = Σ.getEffect(qn.parent)
    val handlerImpl = h.handlers(qn)
    checkHandlerTypeSubsumption(
      HandlerTypeLiteral(handlerImpl.handlerConstraint.handlerType),
      effect.handlerType.substLowers(effArgs*),
    )
    // Note that usage subsumption check is reversed because this is checking how continuation
    // can be used by handler.
    checkUsageSubsumption(
      effect.continuationUsage.substLowers(effArgs*),
      UsageLiteral(handlerImpl.handlerConstraint.continuationUsage),
    )
    // The followings do not need to be weakened for handler parameter because after substituting the effect args,
    // they do not contain any free variables beyond beginning of paramTys.
    val paramTys = operation.paramTys.substLowers(effArgs*)
    val resultTy = operation.resultTy.substLowers(effArgs*)
    val resultUsage = operation.resultUsage.substLowers(effArgs*)
    val (newHandlerImpl, usages) = handlerImpl.handlerConstraint match
      case HandlerConstraint(continuationUsage, HandlerType.Simple) =>
        given implΓ: Context = Γ ++ (parameterBinding +: paramTys)
        val implOffset = implΓ.size - Γ.size
        val uncheckedImplTy = continuationUsage match
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
        val (implTy, _) = checkIsCType(uncheckedImplTy)
        val (body, usages) = checkType(handlerImpl.body, implTy)
        val effects = checkEffectsAreSimple(implTy.asInstanceOf[F].effects)
        // Simple operation can only perform U1 effects so that linear resources in the continuation
        // are managed correctly.
        ctx.checkSolved(
          checkUsageSubsumption(getEffectsContinuationUsage(effects), u1),
          ExpectU1Effect(qn),
        )
        ctx.checkSolved(
          checkEffSubsumption(effects, implOutputEffects),
          NotEffectSubsumption(effects, implOutputEffects),
        )
        (handlerImpl.copy(body = body)(handlerImpl.boundNames), usages)
      case HandlerConstraint(continuationUsage, HandlerType.Complex) =>
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
        val (checkedContinuationType, _) = checkIsCType(continuationType)
        val implΓ: Context =
          continuationΓ :+ Binding(U(checkedContinuationType), UsageLiteral(Usage.U1))(
            gn"continuation",
          )
        val implOffset = implΓ.size - Γ.size
        val (body, usages) = checkType(
          handlerImpl.body,
          F(
            outputTy.weaken(implOffset, 0),
            outputEffects.weaken(implOffset, 0),
            outputUsage.weaken(implOffset, 0),
          ),
        )(using implΓ)
        (handlerImpl.copy(body = body)(handlerImpl.boundNames), usages)
    (qn, newHandlerImpl, usages)
  }
  (
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
      handlerAndUsages.map((qn, impl, _) => (qn, impl)).to(SeqMap),
      input,
      inputBinding,
    )(using h.sourceInfo),
    F(outputTy, outputEffects, outputUsage),
    inputUsages + parameterUsages + parameterDisposerUsages + parameterReplicatorUsages + transformUsages + handlerAndUsages
      .map((_, _, usages) => usages)
      .reduce(_ + _),
  )

// Input effects should be type-checked.
// returned effects should be normalized
@throws(classOf[IrError])
private def getEffectsContinuationUsage
  (effects: VTerm)
  (using Γ: Context)
  (using Σ: Signature)
  (using ctx: TypingContext)
  : VTerm =
  val usage = ctx.withMetaResolved(effects.normalized):
    case Effects(literal, operands) =>
      val literalUsages = literal.map { case (qn, args) =>
        Σ.getEffect(qn).continuationUsage.substLowers(args*)
      }
      val usages = operands.keySet.map(getEffectsContinuationUsage)
      UsageJoin(Set(UsageLiteral(U1)) ++ usages ++ literalUsages)
    case v: Var =>
      Γ.resolve(v).ty match
        case EffectsType(continuationUsage, _) => continuationUsage
        case _                                 => throw IllegalStateException("type error")
    case r: ResolvedMetaVariable =>
      r.ty match
        case F(EffectsType(continuationUsage, _), _, _) => continuationUsage
        case _                                          => throw IllegalStateException("type error")
    case _ => UsageLiteral(UAny)
  usage.normalized

@throws(classOf[IrError])
private def checkEffectsAreSimple
  (rawEffects: VTerm)
  (using Γ: Context)
  (using Σ: Signature)
  (using ctx: TypingContext)
  : VTerm =
  val effects = rawEffects.normalized
  ctx.withMetaResolved(effects):
    case Effects(literal, operands) =>
      literal.foreach { case (qn, _) =>
        checkHandlerTypeSubsumption(Σ.getEffect(qn).handlerType, VTerm.HandlerTypeLiteral(Simple))
      }
      operands.keySet.map(getEffectsContinuationUsage)
    case v: Var =>
      Γ.resolve(v).ty match
        case EffectsType(_, handlerType) =>
          checkHandlerTypeSubsumption(handlerType, VTerm.HandlerTypeLiteral(Simple))
        case _ => throw IllegalStateException("type error")
    case r: ResolvedMetaVariable =>
      r.ty match
        case F(EffectsType(_, handlerType), _, _) =>
          checkHandlerTypeSubsumption(handlerType, VTerm.HandlerTypeLiteral(Simple))
        case _ => throw IllegalStateException("type error")
    case _ =>
  effects

@throws(classOf[IrError])
def checkIsType
  (uncheckedVTy: VTerm, levelBound: Option[VTerm] = None)
  (using Γ: Context)
  (using Signature)
  (using ctx: TypingContext)
  : (VTerm, Usages) =
  ctx.trace(
    "checking is type",
    Block(ChopDown, Aligned, yellow(uncheckedVTy.sourceInfo), pprint(uncheckedVTy)),
  ):
    checkType(
      uncheckedVTy,
      Type(Top(levelBound.getOrElse(LevelLiteral(LevelOrder.upperBound)))),
    )

@throws(classOf[IrError])
def checkIsCType
  (uncheckedCTy: CTerm, levelBound: Option[VTerm] = None)
  (using Γ: Context)
  (using Signature)
  (using ctx: TypingContext)
  : (CTerm, Usages) =
  ctx.trace("checking is C type", Block(yellow(uncheckedCTy.sourceInfo), pprint(uncheckedCTy))):
    checkType(
      uncheckedCTy,
      CType(
        CTop(
          levelBound.getOrElse(LevelLiteral(LevelOrder.upperBound)),
          Collapse(ctx.addUnsolved(F(EffectsType()))),
        ),
      ),
    )

@throws(classOf[IrError])
def reduceUsage(usage: CTerm)(using Context)(using Signature)(using ctx: TypingContext): VTerm =
  ctx.trace("reduce usage", Block(yellow(usage.sourceInfo), pprint(usage))):
    checkType(usage, F(UsageType()))
    val reduced = reduce(usage)
    reduced match
      case Return(u, _) => u
      case _ =>
        throw IllegalStateException(
          "type checking has bugs: reduced value of type `F(UsageType())` must be `Return(u)`.",
        )

@throws(classOf[IrError])
def reduceVType
  (uncheckedVTy: CTerm)
  (using Context)
  (using Signature)
  (using ctx: TypingContext)
  : VTerm =
  ctx.trace("reduce V type", Block(yellow(uncheckedVTy.sourceInfo), pprint(uncheckedVTy))):
    val (vTy, tyTy, _) = inferType(uncheckedVTy)
    tyTy match
      case F(Type(_), _, _) if isTotal(vTy, Some(tyTy)) =>
        reduce(vTy) match
          case Return(vTy, _) => vTy
          case _ =>
            throw IllegalStateException(
              "type checking has bugs: reduced value of type `F ...` must be `Return ...`.",
            )
      case F(_, _, _) => throw EffectfulCTermAsType(vTy)
      case _          => throw ExpectFType(vTy)

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
@throws(classOf[IrError])
private def checkVar0Leak[T <: CTerm | VTerm](ty: T, error: => IrError)(using Σ: Signature): T =
  val freeVars = ty match
    case ty: CTerm => FreeVarsVisitor.visitCTerm(ty)(using 0)
    case ty: VTerm => FreeVarsVisitor.visitVTerm(ty)(using 0)
  if freeVars.exists(_.idx == 0) then throw error
  else
    ty match
      case ty: CTerm => ty.strengthened.asInstanceOf[T]
      case ty: VTerm => ty.strengthened.asInstanceOf[T]

def isMeta(t: VTerm): Boolean = t match
  case Collapse(Redex(Meta(_), _)) => true
  case Collapse(Meta(_))           => true
  case _                           => false

private def extractDistinctArgVars(args: Seq[VTerm]): Option[List[Nat]] =
  val argVars = args.collect { case v: Var => v.idx }
  if argVars.distinct.length == argVars.length then Some(argVars.toList)
  else None

@throws(classOf[IrError])
private inline def debugCheckType[R]
  (tm: CTerm | VTerm, ty: CTerm | VTerm)
  (result: => R)
  (using Context)
  (using Signature)
  (using ctx: TypingContext)
  : R =
  ctx.trace(
    "checkType",
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

private inline def debugInferType[R <: CTerm | VTerm]
  (tm: R)
  (result: => (R, R, Usages))
  (using Context)
  (using Signature)
  (using ctx: TypingContext)
  : (R, R, Usages) =
  ctx.trace[(R, R, Usages)](
    s"inferType",
    Block(ChopDown, Aligned, yellow(tm.sourceInfo), pprint(tm)),
    ty => Block(ChopDown, Aligned, yellow(ty._1.sourceInfo), green(pprint(ty._2))),
  ):
    result
