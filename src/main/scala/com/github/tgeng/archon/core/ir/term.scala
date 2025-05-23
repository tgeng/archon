package com.github.tgeng.archon.core.ir

import com.github.tgeng.archon.common.*
import com.github.tgeng.archon.core.common.*
import com.github.tgeng.archon.core.ir.EscapeStatus.{EsLocal, EsUnknown}
import com.github.tgeng.archon.core.ir.SourceInfo.*
import com.github.tgeng.archon.core.ir.Usage.*

import scala.annotation.targetName
import scala.collection.immutable.{MultiSet, SeqMap}

// TODO[P2]: Replace all Set with SeqSet so that type checking become deterministic after
//  https://github.com/scala/scala-library-next/issues/22 is resolved

// Term hierarchy is inspired by Pédrot 2020 [0]. The difference is that our computation types are
// graded with type of effects, which then affects type checking: any computation that has side
// effects would not reduce during type checking.

/** This is to aid escape analysis of effect instance variables.
  */
enum EscapeStatus extends Ordered[EscapeStatus]:
  /** The variable is consumed locally */
  case EsLocal

  /** The variable escaped via the terminal `return` */
  case EsReturned

  /** The variable's usage is complex and untracked statically */
  case EsUnknown

  infix def &(that: EscapeStatus): EscapeStatus = (this, that) match
    case (EsLocal, _) | (_, EsLocal)       => EsLocal
    case (EsReturned, _) | (_, EsReturned) => EsReturned
    case _                                 => EsUnknown

  infix def |(that: EscapeStatus): EscapeStatus = (this, that) match
    case (EsUnknown, _) | (_, EsUnknown)   => EsUnknown
    case (EsReturned, _) | (_, EsReturned) => EsReturned
    case _                                 => EsLocal

  infix def *(that: EscapeStatus): EscapeStatus = (this, that) match
    case (EsUnknown, _) | (_, EsUnknown) => EsUnknown
    case (EsLocal, _)                    => EsLocal
    case (EsReturned, _)                 => EsReturned

  override def compare(that: EscapeStatus): Nat = this.ordinal - that.ordinal

case class Binding[+T](ty: T, usage: T)(val name: Ref[Name], val isImplicitlyAvailable: Boolean):
  def map[S](f: T => S): Binding[S] = Binding(f(ty), f(usage))(name)

object Binding:
  def apply[T](ty: T, usage: T)(name: Ref[Name]): Binding[T] =
    new Binding(ty, usage)(name, false)

  def apply[T](ty: T, usage: T)(name: Ref[Name], isImplicitlyAvailable: Boolean): Binding[T] =
    new Binding(ty, usage)(name, isImplicitlyAvailable)

  def apply(ty: VTerm, usage: Usage = Usage.UAny)(name: Ref[Name]): Binding[VTerm] =
    new Binding(ty, VTerm.UsageLiteral(usage))(name, false)

/** Heap key is simply a unique value that identifies a handler.
  */
class HandlerKey

/** Head is on the left, e.g. Z :: S Z :: []
  */
type Arguments = List[VTerm]

enum HandlerType extends Ordered[HandlerType]:
  /** No continuation is captured, execution simply progresses. The continuation usage can be U0,
    * U1, or UAff.
    */
  case Simple

  /** Continuation may be captured and complex control transfer may occur. The continuation usage
    * can be any value.
    */
  case Complex

  override def compare(that: HandlerType): Int = this.ordinal - that.ordinal
  @targetName("handlerTypeUnion")
  infix def |(that: HandlerType): HandlerType = (this, that) match
    case (Simple, Simple) => Simple
    case _                => Complex

  infix def &(that: HandlerType): HandlerType = (this, that) match
    case (Complex, Complex) => Complex
    case _                  => Simple

/** Semantic:
  *
  *   - Usage: operations can manipulate continuations in ways according to `usage`. Specifically,
  *     - U0: continuation can only be disposed
  *     - U1: continuation can only be resumed. Difference from `None` is that output of
  *       continuation can be inspected and more computation can be done after the continuation is
  *       resumed.
  *     - UAff: continuation can be resumed or disposed
  *     - URel: continuation can be resumed or replicated
  *     - UAny: continuation an be resumed, disposed, or replicated. Note that continuation is
  *       always captured linearly in `U`. It's difficult to sugarize the corecord type `U U1
  *       Continuation` as a function type with various usages and automatically insert dispose and
  *       replicate wherever needed. This is because dispose and replicate can be effectful. The
  *       effect is captured by the `Continuation` corecord type, though such effects can only have
  *       `None` continuation usage so that the operation semantic is simple.
  *
  *   - simplicity:
  *     - `true` means the effect is a simple effect. That is, continuation won't be captured in any
  *       operation handlers. This is only possible if `continuationUsage` is `U0` or `U1`, in which
  *       case
  *       - `U0`: any handlers between the handling handler and the tip of the stack are disposed
  *         before the handling handler starts execution.
  *       - `U1`: the handling handler behaves just like a simple function call, with no
  *         continuation capturing at all. In some literature, this is called "linear". That is, the
  *         computation executes immediately and the results are returned to the caller intact.
  *       - `UAff`: all operations are simple and some are U1, some are U0, or some are UAff (the
  *         operation may throw or return under the hood)
  *   - any other values: this is not
  *   - `false` means the effect may capture continuations and do something with them. For example,
  *     replicate it to invoke multiple times (multi-shot continuation) or delay the execution to a
  *     later time.
  *
  * Also a handler implementation of a simple operation can only perform effects that are simple and
  * linear. This is because otherwise continuation would be captured and violating the assumption
  * that simple effect means no continuation capturing. Practically, this restriction is necessary
  * to implement parameter disposers and parameter replicators, which can only perform linear and
  * simple effects.
  *
  * In addition, a any simple operations (linear or exceptional) cannot throw another exceptions
  * (a.k.a perform simple U0 effects) because that would violate resource usages at the callsite of
  * this simple linear operation. In order to throw, the operation must be complex instead. See
  * docs/trade_offs.md for more details.
  *
  * Simple operations have an advantage at runtime because compiling it doesn't require CPS
  * transformation.
  */
case class HandlerConstraint(continuationUsage: Usage, handlerType: HandlerType)
  extends PartiallyOrdered[HandlerConstraint]:
  infix def |(that: HandlerConstraint): HandlerConstraint =
    HandlerConstraint(continuationUsage | that.continuationUsage, handlerType | that.handlerType)

  infix def &(that: HandlerConstraint): Option[HandlerConstraint] =
    continuationUsage & that.continuationUsage match
      case Some(u) => Some(HandlerConstraint(u, handlerType & that.handlerType))
      case _       => None

  override def tryCompareTo[B >: HandlerConstraint: AsPartiallyOrdered](that: B): Option[Int] =
    that match
      case that: HandlerConstraint =>
        this.handlerType.compare(that.handlerType) match
          case 0 => this.continuationUsage.tryCompareTo(that.continuationUsage)
          case i => Some(i)
      case _ => None

given PartialOrdering[HandlerConstraint] with
  override def tryCompare(x: HandlerConstraint, y: HandlerConstraint): Option[Int] =
    x.tryCompareTo(y)
  override def lteq(x: HandlerConstraint, y: HandlerConstraint): Boolean = x <= y
  override def lt(x: HandlerConstraint, y: HandlerConstraint): Boolean = x < y
  override def gteq(x: HandlerConstraint, y: HandlerConstraint): Boolean = x >= y
  override def gt(x: HandlerConstraint, y: HandlerConstraint): Boolean = x > y
  override def equiv(x: HandlerConstraint, y: HandlerConstraint): Boolean = x == y

object HandlerConstraint:
  import HandlerType.*
  val CuAny: HandlerConstraint = HandlerConstraint(Usage.UAny, Complex)
  val CuRel: HandlerConstraint = HandlerConstraint(Usage.URel, Complex)
  val CuAff: HandlerConstraint = HandlerConstraint(Usage.UAff, Complex)
  val Cu1: HandlerConstraint = HandlerConstraint(Usage.U1, Complex)
  val Cu0: HandlerConstraint = HandlerConstraint(Usage.U1, Complex)
  val CuSimple: HandlerConstraint = HandlerConstraint(Usage.UAff, Simple)
  val CuException: HandlerConstraint = HandlerConstraint(Usage.U0, Simple)
  val CuLinear: HandlerConstraint = HandlerConstraint(Usage.U0, Simple)

enum Elimination[T](val sourceInfo: SourceInfo) extends SourceInfoOwner[Elimination[T]]:
  case ETerm(v: T)(using sourceInfo: SourceInfo) extends Elimination[T](sourceInfo)
  case EProj(n: Name)(using sourceInfo: SourceInfo) extends Elimination[T](sourceInfo)

  override def withSourceInfo(sourceInfo: SourceInfo): Elimination[T] =
    given SourceInfo = sourceInfo
    this match
      case ETerm(v) => ETerm(v)
      case EProj(n) => EProj(n)

  def map[R](f: T => R): Elimination[R] = this match
    case ETerm(v) => ETerm(f(v))
    case EProj(n) => EProj(n)

  def mapEither[L, R](f: T => Either[L, R]): Either[L, Elimination[R]] = this match
    case ETerm(v) => f(v).map(ETerm(_))
    case EProj(n) => Right(EProj(n))

type Eff = (QualifiedName, Arguments)

import com.github.tgeng.archon.core.ir.Builtins.*

sealed trait QualifiedNameOwner(_qualifiedName: QualifiedName):
  def qualifiedName: QualifiedName = _qualifiedName

extension (eff: Eff) def map(f: VTerm => VTerm): Eff = (eff._1, eff._2.map(f))

/** Represents an order number `m * ω + n`.
  */
case class LevelOrder(m: Nat, n: Nat) extends Ordered[LevelOrder]:
  override def compare(that: LevelOrder): Int =
    if this.m < that.m then -1
    else if this.m > that.m then 1
    else this.n.compare(that.n)

  def suc(offset: Nat = 1): LevelOrder = LevelOrder(m, n + offset)

  /** There is no need to succ the level if `n==0` because the upperbound is strict and `0` means
    * any levels must be in a lower universe and any number of succ would still be in the same lower
    * universe.
    */
  def sucAsStrictUpperbound(offset: Nat = 1): LevelOrder =
    if n == 0 then this else suc(offset)

object LevelOrder:
  def orderMax(a: LevelOrder, b: LevelOrder): LevelOrder =
    if a.m > b.m then a else if a.m < b.m then b else LevelOrder(a.m, a.n max b.n)

  val ω: LevelOrder = LevelOrder(1, 0)
  val zero: LevelOrder = LevelOrder(0, 0)
  // 256 is arbitrary but it should be enough for any practical purpose
  val upperBound: LevelOrder = LevelOrder(256, 0)

sealed trait UsageCompound(val distinctOperands: Set[VTerm])

/** @param body
  *   the handler implementation. The type depends on the continuation usage
  *   - simple
  *     - U0: handler param -> op param1 -> op param2 -> ... -> op paramN -> (handler param, handler
  *       output)
  *     - U1: handler param -> op param1 -> op param2 -> ... -> op paramN -> (handler param, op
  *       output)
  *     - UAff: handler param -> op param1 -> op param2 -> ... -> op paramN -> (handler param,
  *       Either[handler output, op output])
  *   - complex
  *     - handler param -> op param1 -> op param2 -> ... -> op paramN -> continuation -> (handler
  *       param, handler output)
  * @param boundNames
  *   the parameter and optional continuation parameter names. Note that handler parameter name is
  *   not among the names here because it's shared across all handler implementations and stored in
  *   the parent `Handler` construct under the `parameterBinding` cofield.
  * @param continuationType
  *   type of the continuation parameter when the handler is complex. This is only available when
  *   the handler is complex.
  */
case class HandlerImpl
  (
    handlerConstraint: HandlerConstraint,
    body: CTerm,
    bodyTy: CTerm,
    continuationType: Option[VTerm],
  )
  (val boundNames: Seq[Ref[Name]]):
  (handlerConstraint.handlerType, continuationType) match
    case (HandlerType.Simple, None) | (HandlerType.Complex, Some(_)) =>
    case _ =>
      throw new IllegalArgumentException("mismatch between handlerConstraint and continuation type")

enum VTerm(val sourceInfo: SourceInfo) extends SourceInfoOwner[VTerm]:
  case Type(upperBound: VTerm)(using sourceInfo: SourceInfo)
    extends VTerm(sourceInfo),
    QualifiedNameOwner(TypeQn)

  // The idea is that by default all usage declarations in bindings and `F` are 1 (linear) and types
  // determines how they can be used: strict linear types (for example thunks or user declared
  // resources like file descriptors) can only be used linearly, while simple data types can be
  // used in an unrestricted manner. That is, the effective usage count is the declared usage in
  // binding multiplied by the natural allowed usages of the type. This also generalizes to the case
  // where the usage declaration from the binding is not 1. This way, users only need to worry about
  // linearity for linear types. Also, 0 usage still effectively erases compile-only terms. In
  // addition, some transparent optimization (like in-place update, proactive free, etc) can be done
  // on unrestricted types that are used linearly.
  case Top(level: VTerm)(using sourceInfo: SourceInfo)
    extends VTerm(sourceInfo),
    QualifiedNameOwner(TopQn)

  case Var(idx: Nat)(using sourceInfo: SourceInfo) extends VTerm(sourceInfo)

  /** Execute a effect free computation and get the returned value. That is, `cTm` must be of type
    * `F(V, Total()` for some value type `V`. This VTerm construct is used to embed effect free
    * computations into values so that the type theory is as expressive as typical dependent type
    * theory.
    */
  case Collapse(cTm: CTerm)(using sourceInfo: SourceInfo) extends VTerm(sourceInfo)

  // When checking usages, vars in cTy should be multiplied by UAny so that type U is Unrestricted
  case U(cTy: CTerm)(using sourceInfo: SourceInfo) extends VTerm(sourceInfo)
  // Note: simply multiply the usage of `U ...` to the usages of everything in `cTy`
  case Thunk(c: CTerm)(using sourceInfo: SourceInfo) extends VTerm(sourceInfo)

  // On sigma types, simulating this with inductive types requires functions for the dependent
  // piece, which can be very unwieldy with the separation of computation from values. However,
  // sigma type make type matching on them impossible because the second part depends on the first
  // part. Also, it should be possible to add some user language sugar to make the inductive type
  // version more palatable. So I'm removing sigma type for now to make the core language simpler.

  case DataType(qn: QualifiedName, args: Arguments = Nil)(using sourceInfo: SourceInfo)
    extends VTerm(sourceInfo),
    QualifiedNameOwner(qn)
  case Con(name: Name, args: Arguments = Nil)(using sourceInfo: SourceInfo)
    extends VTerm(sourceInfo)

  // Note, `upper` here is in the sense of typing subsumption, not the usage lattice. This is, the
  // lower bound in the usage lattice. Hence Option.None is used to represent unbounded case, as the
  // lattice is not bounded below. Note that the semantic of this `upperBound` is different from
  // `continuationUsage`.
  case UsageType(upperBound: Option[VTerm] = None)(using sourceInfo: SourceInfo)
    extends VTerm(sourceInfo)
  case UsageLiteral(usage: Usage)(using sourceInfo: SourceInfo) extends VTerm(sourceInfo)
  case UsageProd(operands: Set[VTerm])(using sourceInfo: SourceInfo)
    extends VTerm(sourceInfo),
    UsageCompound(operands)
  case UsageSum(operands: MultiSet[VTerm])(using sourceInfo: SourceInfo)
    extends VTerm(sourceInfo),
    UsageCompound(operands.toSet)
  case UsageJoin(operands: Set[VTerm])(using sourceInfo: SourceInfo)
    extends VTerm(sourceInfo),
    UsageCompound(operands)

  /** @param continuationUsage
    *   see ContinuationUsage for explanation. The reason that we need this part to be a term
    *   instead of a literal usage is because this part needs to participate in usage tracking of
    *   following computations (aka continuation). Having a first-class value here makes definitions
    *   parametric in continuation usage.
    */
  case EffectsType
    (continuationUsage: VTerm = VTerm.UsageLiteral(Usage.UAny))
    (using sourceInfo: SourceInfo)
    extends VTerm(sourceInfo),
    QualifiedNameOwner(
      EffectsQn,
    )

  case Effects
    (
      handlerKeys: Set[VTerm],
      unionOperands: SeqMap[
        VTerm,
        /* whether to filter out complex or non-linear effects. True means only retain simple linear effects */ Boolean,
      ],
    )
    (using sourceInfo: SourceInfo) extends VTerm(sourceInfo)

  /** @param strictUpperBound
    *   the upper bound of the level. It's called strict because only levels that are strictly less
    *   than this level are inhabitants.
    */
  case LevelType(strictUpperBound: LevelOrder = LevelOrder.ω)(using sourceInfo: SourceInfo)
    extends VTerm(sourceInfo),
    QualifiedNameOwner(LevelQn)

  case Level
    (literal: LevelOrder, maxOperands: SeqMap[VTerm, /* level offset */ Nat])
    (using sourceInfo: SourceInfo) extends VTerm(sourceInfo)

  // TODO[P2]: It's possible to introduce TranEff or even DepEff like in idris
  //  https://docs.idris-lang.org/en/latest/effects/state.html#the-type-eff. To do that, basically
  //  here we need to track both the input eff args and output eff args (I don't think we can do
  //  transition across effect qn since the handler is already bound and we do fine-grained effect
  //  instance level tracking.) Then
  //  * at call-site,
  //    - before each computation check, we need to make sure the current eff args are convertible
  //      with the input eff args
  //    - after each computation check, we need to update the current context to have
  //      the output eff args
  //  * in handler operation implementation, we need to make sure the declared effect args indeed
  //    match the implementation. Practically this means
  //    - start checking the body using the input eff args.
  //    - checking the handler param and operation output type matches the declared output eff args.
  //  A practical need of this capability is to track type changes across mutable states, like
  //  pushing to a vector should update the length tracked in type. Using a sigma type indexed by
  //  length is too coarse as the length information is lost through effect updates. This seems to
  //  defeat the ultimate goal of combining dependent type with effects.
  case EffectInstanceType
    (eff: Eff, handlerConstraint: HandlerConstraint)
    (using sourceInfo: SourceInfo) extends VTerm(sourceInfo)

  case EffectInstance
    (eff: Eff, handlerConstraint: HandlerConstraint, handlerKey: HandlerKey = HandlerKey())
    extends VTerm(SourceInfo.SiEmpty)

  /** Automatically derived term, aka, `_` in Agda-like languages. During type checking, this is
    * replaced with `Collapse(Application...(Meta(...)))` and solved through meta-variable
    * unification.
    */
  case Auto()(using sourceInfo: SourceInfo) extends VTerm(sourceInfo)

  // Note: during development, I once had devoted constructs for heap handler, alloc, set, and get
  // operations. But they are entirely redundant because one can just use a linear piece of data as
  // the storage and do the same with the general handler. In addition, the heap key concept is
  // arbitrary and it can actually be substituted with a simple nat instead. The previous heap
  // handler basically does two things under the hood: heap allocation and using it. Since the old
  // implementation actually allocates stuff on the heap, the allocation part is non-deterministic.
  // So one either has to make the type checker to do some hard work to prevent the heap variable
  // from being leaked or just add a non-deterministic effect to all heap handler creations. By
  // simulating heap handler with general handler, the heap allocation (aka, heap key generation)
  // can be a separate step. It can even be deterministically created so that a total computation
  // can rely on mutable states under the hood.

  this match
    case UsageJoin(operands) if operands.isEmpty =>
      throw IllegalArgumentException(
        "Empty operands not allowed for join because join does not have an identity.",
      )
    case _ =>

  override def withSourceInfo(sourceInfo: SourceInfo): VTerm =
    given SourceInfo = sourceInfo

    this match
      case Type(upperBound)                => Type(upperBound)
      case Top(l)                          => Top(l)
      case Var(index)                      => Var(index)
      case Collapse(cTm)                   => Collapse(cTm)
      case U(cTy)                          => U(cTy)
      case Thunk(c)                        => Thunk(c)
      case DataType(qn, args)              => DataType(qn, args)
      case Con(name, args)                 => Con(name, args)
      case UsageType(u)                    => UsageType(u)
      case UsageLiteral(u)                 => UsageLiteral(u)
      case UsageProd(operands)             => UsageProd(operands)
      case UsageSum(operands)              => UsageSum(operands)
      case UsageJoin(operands)             => UsageJoin(operands)
      case EffectsType(continuationUsage)  => EffectsType(continuationUsage)
      case Effects(literal, unionOperands) => Effects(literal, unionOperands)
      case LevelType(strictUpperBound)     => LevelType(strictUpperBound)
      case Level(literal, maxOperands)     => Level(literal, maxOperands)
      case Auto()                          => Auto()
      case EffectInstanceType(effect, handlerConstraint) =>
        EffectInstanceType(effect, handlerConstraint)
      case EffectInstance(effect, handlerConstraint, handlerKey) =>
        EffectInstance(effect, handlerConstraint, handlerKey)

  def visitWith[C, R]
    (visitor: Visitor[C, R])
    (using ctx: C)
    (using Σ: Signature)
    (using TypingContext)
    : R =
    visitor.visitVTerm(this)

  def transformWith[C]
    (transformer: Transformer[C])
    (using ctx: C)
    (using Σ: Signature)
    (using TypingContext)
    : VTerm =
    transformer.transformVTerm(this)

object VTerm:

  def UsageProd(operands: VTerm*)(using SourceInfo): VTerm =
    val (usages, terms) = separateUsageLiteralsFromRest(operands)
    (usages.foldLeft(U1)(_ * _), terms) match
      case (u, Nil)    => UsageLiteral(u)
      case (U1, terms) => UsageProd(terms.toSet)
      case (U0, _)     => UsageLiteral(U0)
      case (u, terms)  => UsageProd((UsageLiteral(u) :: terms).toSet)

  def UsageSum(operands: VTerm*)(using SourceInfo): VTerm =
    val (usages, terms) = separateUsageLiteralsFromRest(operands)
    (usages.foldLeft(U0)(_ + _), terms) match
      case (u, Nil)    => UsageLiteral(u)
      case (U0, terms) => UsageSum(MultiSet.from(terms))
      case (URel, _)   => UsageLiteral(URel)
      case (u, terms)  => UsageSum(MultiSet.from(UsageLiteral(u) :: terms))

  def UsageJoin(operands: VTerm*)(using SourceInfo): VTerm =
    if operands.isEmpty then throw IllegalStateException("UsageJoin cannot be empty")
    val (usages, terms) = separateUsageLiteralsFromRest(operands)
    if usages.isEmpty then return UsageJoin(terms.toSet)
    (usages.reduce(_ | _), terms) match
      case (u, Nil)  => UsageLiteral(u)
      case (UAny, _) => UsageLiteral(UAny)
      // Note that something joining itself is the same as the thing itself, so there is never any need to hold
      // duplicates
      case (u, terms) => UsageJoin((UsageLiteral(u) :: terms).toSet)

  private def separateUsageLiteralsFromRest(operands: Seq[VTerm]): (List[Usage], List[VTerm]) =
    operands.foldLeft[(List[Usage], List[VTerm])]((Nil, Nil)):
      case ((usages, terms), UsageLiteral(u)) => (u :: usages, terms)
      case ((usages, terms), term)            => (usages, term :: terms)

  def LevelLiteral(n: Nat)(using sourceInfo: SourceInfo): Level =
    Level(LevelOrder(0, n), SeqMap())
  val l0 = LevelLiteral(0)
  val lω = LevelLiteral(1, 0)

  def LevelLiteral(m: Nat, n: Nat)(using sourceInfo: SourceInfo): Level =
    Level(LevelOrder(m, n), SeqMap())

  def LevelLiteral(l: LevelOrder)(using sourceInfo: SourceInfo): Level =
    Level(l, SeqMap())

  def LevelUpperBound(): Level = Level(LevelOrder.upperBound, SeqMap())

  def LevelSuc(t: VTerm): Level = Level(LevelOrder.zero, SeqMap(t -> 1))

  def LevelMax(ts: VTerm*): Level = Level(LevelOrder.zero, SeqMap(ts.map(_ -> 0)*))

  def Total()(using sourceInfo: SourceInfo): Effects = EffectsLiteral(Set.empty)
  val total: Effects = EffectsLiteral(Set.empty)(using SourceInfo.SiEmpty)
  val u0: VTerm = VTerm.UsageLiteral(Usage.U0)
  val u1: VTerm = VTerm.UsageLiteral(Usage.U1)
  val uAff: VTerm = VTerm.UsageLiteral(Usage.UAff)
  val uRel: VTerm = VTerm.UsageLiteral(Usage.URel)
  val uAny: VTerm = VTerm.UsageLiteral(Usage.UAny)
  val div: EffectInstance =
    EffectInstance((Builtins.DivQn, Nil), HandlerConstraint(Usage.U0, HandlerType.Simple))
  val ndet: EffectInstance =
    EffectInstance((Builtins.NdetQn, Nil), HandlerConstraint(Usage.U1, HandlerType.Simple))
  val globalKeys: Set[EffectInstance] = Set(div, ndet)

  /** Marker of a computation that surely diverges. Computation with this effect will not be
    * executed by the type checker.
    */
  def Div()(using sourceInfo: SourceInfo): Effects = EffectsLiteral(
    Set(div),
  )

  def EffectsLiteral(effectInstances: Set[VTerm])(using sourceInfo: SourceInfo): Effects =
    Effects(effectInstances, SeqMap.empty)

  def EffectsUnion(effects: VTerm*): Effects =
    Effects(Set.empty, SeqMap(effects.map(_ -> false)*))

  def EffectsRetainSimpleLinear(effects: VTerm): Effects =
    Effects(Set.empty, SeqMap(effects -> true))

  /** @param firstIndex
    *   inclusive
    * @param lastIndex
    *   inclusive
    */
  def vars(firstIndex: Nat, lastIndex: Nat = 0): List[Var] = firstIndex
    .to(lastIndex, -1)
    .map(new Var(_)(using SiEmpty))
    .toList

sealed trait IType:
  def effects: VTerm

enum CTerm(val sourceInfo: SourceInfo) extends SourceInfoOwner[CTerm]:
  /** Used in stack machine to represent the computations above the computation term containing
    * this. For example, `f a b` converted to the stack machine becomes
    *   - f
    *   - Application(Hole, a)
    *   - Application(Hole, b)
    */
  case Hole extends CTerm(SiEmpty)

  /** Internal only, created by reduction. This is used to signify the tip of a captured
    * continuation term.
    */
  case CapturedContinuationTip(ty: F) extends CTerm(SiEmpty)

  /** archon.builtin.CType */
  case CType
    (
      upperBound: CTerm,
      effects: VTerm = VTerm.Total()(using SiEmpty),
    )
    (using sourceInfo: SourceInfo) extends CTerm(sourceInfo), IType

  case CTop
    (level: VTerm, effects: VTerm = VTerm.Total()(using SiEmpty))
    (using sourceInfo: SourceInfo) extends CTerm(sourceInfo), IType

  /** Represents either a metavariable or a guarded constant in [2]. This is always created during
    * type checking and user-term won't include this. Rather, user terms should contain `Auto` where
    * needed.
    */
  case Meta(index: Nat)(using sourceInfo: SourceInfo) extends CTerm(sourceInfo)
  case Def(qn: QualifiedName)(using sourceInfo: SourceInfo) extends CTerm(sourceInfo)

  case Force(v: VTerm)(using sourceInfo: SourceInfo) extends CTerm(sourceInfo)

  /** archon.builtin.F */
  case F
    (
      vTy: VTerm,
      effects: VTerm = VTerm.Total()(using SiEmpty),
      usage: VTerm = VTerm.Auto(),
    )
    (using sourceInfo: SourceInfo) extends CTerm(sourceInfo), IType
  case Return(v: VTerm, usage: VTerm = VTerm.Auto()(using SiEmpty))(using sourceInfo: SourceInfo)
    extends CTerm(sourceInfo)
  // Note that we do not have DLet like [0]. Instead we use inductive type and thunk to simulate
  // the existential computation type Σx:A.C̲ in eMLTT [1]. From practical purpose it seems OK,
  // especially after graded modality is added to support linear usage of computations when needed.
  case Let
    (t: CTerm, tBinding: Binding[VTerm], eff: VTerm, body: CTerm /* binding += 1 */ )
    (using sourceInfo: SourceInfo) extends CTerm(sourceInfo)

  // TODO[P4]: (probably not good idea) consider adding CLet that carries out a computation and
  //  capture the resulted computation as a thunk
  //  For example,
  //    clet plus_1 = plus 1
  //    force plus_1 1
  //  The point of this construct is to be able to perform side effects in middle of a function type
  //  For example, consider `foo : Int -> <print> Int -> Int`. This is a function that performs
  //  `print` side effect when given the first argument. It's total when given the second argument.
  //  Without `CLet`, it's impossible to capture the function after applying the first argument as
  //  a total function `Int -> Int` because `thunk foo 1` would delay all side effects and the
  //  resulted function would have type `<print> Int -> Int`.
  //  However, such a construct is not without problems:
  //  1. it encourages people to avoid using `thunk` to capture computations that they would like to
  //     return. Since computations are always linear, this means clet has little flexibility in
  //     terms of resource counting. For example, `plus_1` can only be linear.

  case Redex(t: CTerm, elims: List[Elimination[VTerm]])(using sourceInfo: SourceInfo)
    extends CTerm(sourceInfo)

  /** archon.builtin.Function */
  case FunctionType
    (
      binding: Binding[VTerm],
      bodyTy: CTerm, /* binding offset = 1 */
      /** effects that needed for getting the function of this type. The effects caused by function
        * application is tracked by the `bodyTy`.
        */
      effects: VTerm = VTerm.Total()(using SiEmpty),
      escapeStatus: EscapeStatus = EsUnknown,
    )
    (using sourceInfo: SourceInfo) extends CTerm(sourceInfo), IType

  case CorecordType
    (
      qn: QualifiedName,
      args: Arguments = Nil,
      effects: VTerm = VTerm.Total()(using SiEmpty),
    )
    (using sourceInfo: SourceInfo) extends CTerm(sourceInfo), IType, QualifiedNameOwner(qn)

  case OperationCall
    (effInstance: VTerm, name: Name, args: Arguments = Nil)
    (using sourceInfo: SourceInfo) extends CTerm(sourceInfo)

  /** Internal only. This is only created by reduction.
    *
    * @param continuationTerm
    *   a term with a hole at the top. This is equivalent to the captured stack between the matching
    *   handler (inclusive) and the computation right after the corresopnding handler operation (the
    *   tip of the stack, which must be a term of type `ContinuationHole`.)
    */
  case Continuation(continuationTerm: Handler, continuationUsage: Usage) extends CTerm(SiEmpty)

  /** @param eff
    *   The effect this handler is supposed to handle.
    * @param otherEffects
    *   the effect of the input term without effects being handled by this handler
    * @param handlerEffects
    *   effects used in parameter disposer, parameter replicator, transformer, and (simple)
    *   operation handler implementations. Hence, this is also the effect of the `dispose`, and the
    *   `replicate` (after filtering out complex operations) calls on continuations captured inside
    *   handlers implementations. `resume` calls would perform union of `handlerEffects` and
    *   `otherEffects`. Hence, complex handlers would perform such union effects as well (since it
    *   likely would invoke `resume`).
    * @param outputUsage
    *   the usage of the output of the handler. This is also the usage of the resume call on
    *   continuations captured inside handler implementations. This is also the usage of the final
    *   returned value in each operation handler implementation.
    * @param outputTy
    *   the type of the output of the handler. This is also the type of the resume call on
    *   continuations captured inside handler implementations. This is also the type of the final
    *   returned value in each operation handler.
    * @param parameterDisposer
    *   This is invoked by Continuation.dispose on continuations created by parent handlers or this
    *   handler. In other words, it's to clean up the parameter when computation under this handler
    *   decides to abort (by calling some aborting operation). Therefore, it's not needed if the
    *   inputEffects have continuation usage URel or U1 (which means the handler will never need to
    *   be aborted) or if the parameter usage is U0, UAff, or UAny (which means the parameter does
    *   not need to be explicitly cleaned up).
    * @param parameterReplicator
    *   This is invoked by Continuation.replicate on continuations created by parent handlers or
    *   this handler. In other words, it's to replicate the parameter when computation under this
    *   handler features non-deterministic behavior (by calling some non-deterministic operation).
    *   Therefore, it's not needed if the inputEffects have continuation usage UAff or U1 (which
    *   means the handler is never non-deterministic) or if the parameter usage is U0, URel or UAny
    *   (which means the parameter does not need to be explicitly replicated).
    * @param transform
    *   The transformer that transforms a var at DeBruijn index 0 of type `inputBinding.ty` to
    *   `outputType`. for cases where `outputType` equals `F(someEffects, inputBinding.ty)`, a
    *   sensible default value is simply `return (var 0)`
    * @param handlers
    *   All handler implementations declared by the effect. Each handler is essentially a function
    *   body that takes some parameters and return a value, depending on the continuation usage of
    *   the operation. See [[HandlerImpl]] for details.
    * @param handlerKey
    *   The so-called "instance variable" in [3]. It's empty initially and populated during
    *   reduction. Handler matching is done through this variable.
    */

  case Handler
    (
      eff: Eff,
      otherEffects: VTerm,
      handlerEffects: VTerm,
      outputUsage: VTerm,
      outputTy: VTerm,
      parameter: VTerm,
      parameterBinding: Binding[VTerm],
      parameterDisposer: Option[CTerm], // binding offset: + 1 (for parameter)
      parameterReplicator: Option[CTerm], // binding offset: + 1 (for parameter)
      transform: CTerm, // binding offset: + 1 (for parameter) + 1 (for input value)
      handlers: SeqMap[ /* name identifying an effect operation */ QualifiedName, HandlerImpl],
      input: CTerm, // binding offset: + 1 (for effect instance variable)
      inputBinding: Binding[
        VTerm,
      ], // binding offset: +0 (effect instance is not bound because it's not available in handler implementations
      // TODO[P1]: figure out how to compile this to a pointer to the handler directly so that at
      //  runtime there won't be any label matching. Invoking simple effects should be as simple as
      //  dereferencing a pointer.
      handlerKey: Option[HandlerKey] = None,
    )
  // TODO[P2]: track user specified effect instance binding name
    (using sourceInfo: SourceInfo) extends CTerm(sourceInfo)

  override def withSourceInfo(sourceInfo: SourceInfo): CTerm =
    given SourceInfo = sourceInfo

    this match
      case Hole                       => Hole
      case t: CapturedContinuationTip => t.copy()
      case t: CType                   => t.copy()
      case t: CTop                    => t.copy()
      case t: Meta                    => t.copy()
      case t: Def                     => t.copy()
      case t: Force                   => t.copy()
      case t: F                       => t.copy()
      case t: Return                  => t.copy()
      case t: Let                     => t.copy()
      case t: Redex                   => t.copy()
      case t: FunctionType            => t.copy()
      case t: CorecordType            => t.copy()
      case t: OperationCall           => t.copy()
      case c: Continuation            => c
      case h: Handler                 => h.copy()

  // TODO[P3]: support array operations on heap
  // TODO[P3]: consider adding builtin set and maps with decidable equality because we do not
  //  support quotient type and set semantic is very common in software engineering.

  def visitWith[C, R]
    (visitor: Visitor[C, R])
    (using ctx: C)
    (using Σ: Signature)
    (using TypingContext)
    : R =
    visitor.visitCTerm(this)

  def transformWith[C]
    (transformer: Transformer[C])
    (using ctx: C)
    (using Σ: Signature)
    (using TypingContext)
    : CTerm =
    transformer.transformCTerm(this)

object CTerm:
  def CTop
    (t: VTerm, effects: VTerm = VTerm.Total()(using SiEmpty))
    (using sourceInfo: SourceInfo)
    : CTop =
    CTop(t, effects)

  @targetName("redexFromElims")
  def redex(c: CTerm, elims: Iterable[Elimination[VTerm]])(using SourceInfo): CTerm =
    if elims.isEmpty then c else Redex(c, elims.toList)

  @targetName("redexFromElimsStar")
  def redex(c: CTerm, elims: Elimination[VTerm]*)(using SourceInfo): CTerm = redex(c, elims)

  @targetName("redexFromTerms")
  def redex(c: CTerm, args: Seq[VTerm])(using SourceInfo): CTerm =
    redex(c, args.map(Elimination.ETerm(_)))

  @targetName("redexFromTermsStar")
  def redex(c: CTerm, args: VTerm*)(using SourceInfo): CTerm = redex(c, args)

  @targetName("redexFromProjection")
  def projection(c: CTerm, cofieldName: Name)(using SourceInfo): CTerm =
    redex(c, Elimination.EProj(cofieldName))

  def Application(fun: CTerm, arg: VTerm)(using SourceInfo): CTerm =
    fun match
      case Redex(c, elims) => Redex(c, elims :+ Elimination.ETerm(arg))
      case t               => Redex(t, List(Elimination.ETerm(arg)))

  def Projection(rec: CTerm, name: Name)(using SourceInfo): CTerm =
    rec match
      case Redex(c, elims) => Redex(c, elims :+ Elimination.EProj(name))
      case t               => Redex(t, List(Elimination.EProj(name)))

  extension (binding: Binding[VTerm])
    infix def ->:(body: CTerm): FunctionType = FunctionType(binding, body)

/* References:
 [0]  Pierre-Marie Pédrot and Nicolas Tabareau. 2019. The fire triangle: how to mix substitution,
      dependent elimination, and effects. Proc. ACM Program. Lang. 4, POPL, Article 58 (January
      2020), 28 pages. DOI:https://doi.org/10.1145/3371126
 [1]  Danel Ahman. 2017. Handling fibred algebraic effects. Proc. ACM Program. Lang. 2, POPL,
      Article 7 (January 2018), 29 pages. DOI:https://doi.org/10.1145/3158095
 [2]  Norell, Ulf. “Towards a practical programming language based on dependent type theory.” (2007).
 [3]  Dariusz Biernacki, Maciej Piróg, Piotr Polesiuk, and Filip Sieczkowski. 2019. Binders by day,
      labels by night: effect instances via lexically scoped handlers. Proc. ACM Program. Lang. 4,
      POPL, Article 48 (January 2020), 29 pages. https://doi.org/10.1145/3371116
 */
