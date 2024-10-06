package com.github.tgeng.archon.core.ir

import _root_.pprint.Tree
import com.github.tgeng.archon.common.*
import com.github.tgeng.archon.common.IndentPolicy.*
import com.github.tgeng.archon.common.WrapPolicy.*
import com.github.tgeng.archon.core.common.*
import com.github.tgeng.archon.core.ir
import com.github.tgeng.archon.core.ir.CTerm.*
import com.github.tgeng.archon.core.ir.Elimination.*
import com.github.tgeng.archon.core.ir.IrError.*
import com.github.tgeng.archon.core.ir.MetaVariable.*
import com.github.tgeng.archon.core.ir.PrettyPrinter.pprint
import com.github.tgeng.archon.core.ir.ResolvedMetaVariable.*
import com.github.tgeng.archon.core.ir.UnsolvedMetaVariableConstraint.*
import com.github.tgeng.archon.core.ir.Usage.*
import com.github.tgeng.archon.core.ir.VTerm.*

import scala.collection.immutable.Set
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

class TypingContext
  (
    var traceLevel: Int = 0,
    var enableDebugging: Boolean = false,
  ):

  private val metaVars: mutable.ArrayBuffer[MetaVariable] = mutable.ArrayBuffer()
  private var version: Int = 0
  private var solvedVersion: Int = 0
  given TypingContext = this

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
      case UmcEffSubsumption(lowerBound)   => checkEffectSubsumption(lowerBound, Collapse(value))
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
  def solveTerm(context: Context)(using Σ: Signature): Context =
    Context.fromTelescope(solveTerm(context.toList)(using Context.empty))

  @throws(classOf[IrError])
  def solveTerm(telescope: Telescope)(using Γ: Context)(using Σ: Signature): Telescope =
    telescope match
      case Nil => Nil
      case binding :: telescope =>
        val solvedBinding = solveTerm(binding)
        solvedBinding :: solveTerm(telescope)(using Γ :+ solvedBinding)

  @throws(classOf[IrError])
  def solveTerm(binding: Binding[VTerm])(using Context)(using Σ: Signature): Binding[VTerm] =
    Binding(solveTerm(binding.ty), solveTerm(binding.usage))(binding.name)

  @throws(classOf[IrError])
  def solveTerm(term: VTerm)(using Context)(using Σ: Signature): VTerm =
    solveTermImpl(term)(term => solveOnce(MetaVarCollector.visitVTerm, _.normalized)(term, true))

  @throws(classOf[IrError])
  def solveTerm(term: CTerm)(using Context)(using Σ: Signature): CTerm =
    solveTermImpl(term)(term => solveOnce(MetaVarCollector.visitCTerm, _.normalized)(term, true))

  @throws(classOf[IrError])
  inline def solveTermImpl[T](term: T)(solveStep: T => T)(using Context)(using Σ: Signature): T =
    trace[T](
      "solveTerm",
      Block(ChopDown, Aligned, pprint(term)),
      term => Block(ChopDown, Aligned, pprint(term)),
    ):
      var previousTerm = term
      var currentTerm = solveStep(term)
      while previousTerm != currentTerm do
        previousTerm = currentTerm
        currentTerm = solveStep(currentTerm)
      currentTerm

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
      val solveStep = solveOnce(MetaVarCollector.visitConstraints, solveConstraints)
      var currentConstraints = constraints
      while solvedVersion != version do
        solvedVersion = version
        currentConstraints = solveStep(currentConstraints, false)
      if currentConstraints.nonEmpty && aggressivelySolveConstraints then
        currentConstraints = solveStep(currentConstraints, true)
        while solvedVersion != version do
          solvedVersion = version
          currentConstraints = solveStep(currentConstraints, true)
      currentConstraints

  @throws(classOf[IrError])
  private def solveOnce[T]
    (
      metaVarExtractor: T => Set[Nat],
      iterator: T => T,
    )
    (
      t: T,
      proactivelySolveAmbiguousMetaVars: Boolean,
    )
    (using Context)
    (using Signature)
    : T =
    val metaVarIndexes = metaVarExtractor(t)
    solveAllMetaVars(metaVarIndexes, false)
    val newT = iterator(t)
    if proactivelySolveAmbiguousMetaVars then
      val metaVarIndexes = metaVarExtractor(newT)
      solveAllMetaVars(metaVarIndexes, true)
      iterator(newT)
    else newT

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
                case F(EffectsType(_), _, u)                      => Return(total, u)
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
        // Include all meta variables in the constraints of guarded meta-variables so that solving
        // these can potentially turn guarded meta-variables to solved ones.
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
        checkEffectSubsumption(sub, sup)(using context)
      case Constraint.LevelSubsumption(context, sub, sup) =>
        checkLevelSubsumption(sub, sup)(using context)
      case Constraint.UsageSubsumption(context, sub, sup) =>
        checkUsageSubsumption(sub, sup)(using context)

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
