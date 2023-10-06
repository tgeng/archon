package com.github.tgeng.archon.core.ir

import collection.mutable
import com.github.tgeng.archon.common.*
import com.github.tgeng.archon.core.common.*
import QualifiedName.*
import SourceInfo.*
import EqDecidability.*
import Usage.*
import scala.annotation.targetName

// Term hierarchy is inspired by Pédrot 2020 [0]. The difference is that our computation types are
// graded with type of effects, which then affects type checking: any computation that has side
// effects would not reduce during type checking.

case class Binding[+T](ty: T, usage: T)(val name: Ref[Name]):
  def map[S](f: T => S): Binding[S] = Binding(f(ty), f(usage))(name)

object Binding:
  def apply[T](ty: T, usage: T)(name: Ref[Name]): Binding[T] =
    new Binding(ty, usage)(name)

  def apply(ty: VTerm, usage: Usage = Usage.U1)(name: Ref[Name]): Binding[VTerm] =
    new Binding(ty, VTerm.UsageLiteral(usage))(name)

/** Head is on the left, e.g. Z :: S Z :: []
  */
type Arguments = List[VTerm]

enum ControlMode extends Ordered[ControlMode]:
  /** No continuation is captured, execution simply progresses.
    */
  case Simple

  /** Continuation may be captured and complex control transfer may occur.
    */
  case Complex

  override def compare(that: ControlMode): Int = this.ordinal - that.ordinal
  infix def |(that: ControlMode): ControlMode = (this, that) match
    case (Simple, Simple) => Simple
    case _                => Complex

  infix def &(that: ControlMode): ControlMode = (this, that) match
    case (Complex, Complex) => Complex
    case _                  => Simple

/** Semantic:
  *
  *   - Usage: operations can manipulate continuations in ways according to `usage`. Specifically,
  *     - U0: continuation can only be disposed
  *     - U1: continuation can only be resumed. Difference from `None` is that output of continuation can be inspected
  *       and more computation can be done after the continuation is resumed.
  *     - UAff: continuation can be resumed or disposed
  *     - URel: continuation can be resumed or replicated
  *     - UAny: continuation an be resumed, disposed, or replicated. Note that continuation is always captured linearly
  *       in `U`. It's difficult to sugarize the record type `U U1 Continuation` as a function type with various usages
  *       and automatically insert dispose and replicate wherever needed. This is because dispose and replicate can be
  *       effectful. The effect is captured by the `Continuation` record type, though such effects can only have `None`
  *       continuation usage so that the operation semantic is simple.
  *
  *   - simplicity:
  *     - `true` means the effect is a simple effect. That is, continuation won't be captured in any operation handlers.
  *       This is only possible if `continuationUsage` is `U0` or `U1`, in which case
  *       - `U0`: any handlers between the handling handler and the tip of the stack are disposed before the handling
  *         handler starts execution.
  *       - `U1`: the handling handler behaves just like a simple function call, with no continuation capturing at all.
  *         In some literature, this is called "linear". That is, the computation executes immediately and the results
  *         are returned to the caller intact.
  *       - `UAff`: all operations are simple and some are U1, some are U0, or some are UAff (the operation may throw
  * or return under the hood)
  *   - any other values: this is not
  *   - `false` means the effect may capture continuations and do something with them. For example, replicate it to
  *     invoke multiple times (multi-shot continuation) or delay the execution to a later time.
  *
  * Also a handler implementation of a simple operation can only perform effects that are also simple. This is because
  * otherwise continuation would be captured and violating the assumption that simple effect means no continuation
  * capturing. Practically, this restriction is necessary to implement parameter disposers and parameter replicators,
  * which can only perform simple effects.
  *
  * In addition, a simple linear operation cannot throw exceptions (a.k.a perform simple U0 effects) because that would
  * violate resource usages at the callsite of this simple linear operation. In order to throw, the operation must be
  * marked as "simple UAff" instead.
  */
case class ContinuationUsage(usage: Usage, controlMode: ControlMode) extends PartiallyOrdered[ContinuationUsage]:
  infix def |(that: ContinuationUsage): ContinuationUsage =
    ContinuationUsage(usage | that.usage, controlMode | that.controlMode)

  infix def &(that: ContinuationUsage): Option[ContinuationUsage] =
    usage & that.usage match
      case Some(u) => Some(ContinuationUsage(u, controlMode & that.controlMode))
      case _       => None

  override def tryCompareTo[B >: ContinuationUsage: AsPartiallyOrdered](that: B): Option[Int] =
    that match
      case that: ContinuationUsage =>
        this.controlMode.compare(that.controlMode) match
          case 0 => this.usage.tryCompareTo(that.usage)
          case i => Some(i)
      case _ => None

given PartialOrdering[ContinuationUsage] with
  override def tryCompare(x: ContinuationUsage, y: ContinuationUsage): Option[Int] = x.tryCompareTo(y)
  override def lteq(x: ContinuationUsage, y: ContinuationUsage): Boolean = x <= y
  override def lt(x: ContinuationUsage, y: ContinuationUsage): Boolean = x < y
  override def gteq(x: ContinuationUsage, y: ContinuationUsage): Boolean = x >= y
  override def gt(x: ContinuationUsage, y: ContinuationUsage): Boolean = x > y
  override def equiv(x: ContinuationUsage, y: ContinuationUsage): Boolean = x == y

object ContinuationUsage:
  import ControlMode.*
  val CuAny = ContinuationUsage(Usage.UAny, Complex)
  val CuRel = ContinuationUsage(Usage.URel, Complex)
  val CuAff = ContinuationUsage(Usage.UAff, Complex)
  val Cu1 = ContinuationUsage(Usage.U1, Complex)
  val Cu0 = ContinuationUsage(Usage.U1, Complex)
  val CuSimple = ContinuationUsage(Usage.UAff, Simple)
  val CuException = ContinuationUsage(Usage.U0, Simple)
  val CuLinear = ContinuationUsage(Usage.U0, Simple)

import ContinuationUsage.*

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

import Builtins.*

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

object LevelOrder:
  def orderMax(a: LevelOrder, b: LevelOrder): LevelOrder =
    if a.m > b.m then a else if a.m < b.m then b else LevelOrder(a.m, a.n max b.n)

  val ω = LevelOrder(1, 0)
  val zero = LevelOrder(0, 0)
  // 256 is arbitrary but it should be enough for any practical purpose
  val upperBound = LevelOrder(256, 0)

extension (o: LevelOrder) infix def suc(n: Nat): LevelOrder = LevelOrder(o.m, o.n + n)

sealed trait UsageCompound(val distinctOperands: Set[VTerm])

enum VTerm(val sourceInfo: SourceInfo) extends SourceInfoOwner[VTerm]:
  case Type(upperBound: VTerm)(using sourceInfo: SourceInfo) extends VTerm(sourceInfo), QualifiedNameOwner(TypeQn)

  // The idea is that by default all usage declarations in bindings and `F` are 1 (linear) and types
  // determines how they can be used: strict linear types (for example thunks or user declared
  // resources like file descriptors) can only be used linearly, while simple data types can be
  // used in an unrestricted manner. That is, the effective usage count is the declared usage in
  // binding multiplied by the natural allowed usages of the type. This also generalizes to the case
  // where the usage declaration from the binding is not 1. This way, users only need to worry about
  // linearity for linear types. Also, 0 usage still effectively erases compile-only terms. In
  // addition, some transparent optimization (like in-place update, proactive free, etc) can be done
  // on unrestricted types that are used linearly.
  case Top
    (
      level: VTerm,
      eqDecidability: VTerm = EqDecidabilityLiteral(EqDecidable),
    )
    (using sourceInfo: SourceInfo) extends VTerm(sourceInfo), QualifiedNameOwner(TopQn)

  case Var(idx: Nat)(using sourceInfo: SourceInfo) extends VTerm(sourceInfo)

  /** Execute a effect free computation and get the returned value. That is, `cTm` must be of type `F(V, Total()` for
    * some value type `V`. This VTerm construct is used to embed effect free computations into values so that the type
    * theory is as expressive as typical dependent type theory.
    */
  case Collapse(cTm: CTerm)(using sourceInfo: SourceInfo) extends VTerm(sourceInfo)

  // When checking usages, vars in cTy should be multiplied by UAny so that type U is Unrestricted
  case U(cTy: CTerm)(using sourceInfo: SourceInfo) extends VTerm(sourceInfo)
  // Note: simply multiply the usage of `U ...` to the usages of everything in `cTy`
  case Thunk(c: CTerm)(using sourceInfo: SourceInfo) extends VTerm(sourceInfo)

  // On sigma types, simulating this with inductive types requires functions for the dependent piece, which can be very
  // unwieldy with the separation of computation from values. However, sigma type make type matching on them impossible
  // because the second part depends on the first part. Also, it should be possible to add some user language sugar to
  // make the inductive type version more palatable. So I'm removing sigma type for now to make the core language
  // simpler.

  case DataType(qn: QualifiedName, args: Arguments = Nil)(using sourceInfo: SourceInfo)
    extends VTerm(sourceInfo),
    QualifiedNameOwner(qn)
  case Con(name: Name, args: Arguments = Nil)(using sourceInfo: SourceInfo) extends VTerm(sourceInfo)

  // Note, `upper` here is in the sense of typing subsumption, not the usage lattice. This is the
  // lower bound in the usage lattice. Hence Option.None is used to represent unbounded case, as the
  // lattice is not bounded below. Note that the semantic of this `upperBound` is different from
  // `continuationUsage`.
  case UsageType(upperBound: Option[VTerm] = None)(using sourceInfo: SourceInfo) extends VTerm(sourceInfo)
  case UsageLiteral(usage: Usage)(using sourceInfo: SourceInfo) extends VTerm(sourceInfo)
  case UsageProd(operands: Set[VTerm])(using sourceInfo: SourceInfo) extends VTerm(sourceInfo), UsageCompound(operands)
  case UsageSum(operands: Multiset[VTerm])(using sourceInfo: SourceInfo)
    extends VTerm(sourceInfo),
    UsageCompound(operands.keySet)
  case UsageJoin(operands: Set[VTerm])(using sourceInfo: SourceInfo) extends VTerm(sourceInfo), UsageCompound(operands)
  case EqDecidabilityType()(using sourceInfo: SourceInfo) extends VTerm(sourceInfo)
  // It's possible to introduce `EqDecidabilityJoin` that signifies the decidability of some compound data consisting of
  // multiple pieces of data, each of which has some parameterized decidability. However, such a construct does not seem
  // to increase expressiveness because eqDecidability can only take two values and user can always just declare a
  // single eqDecidability parameter and use this single parameter to constrain other parameters.
  case EqDecidabilityLiteral(eqDecidability: EqDecidability)(using sourceInfo: SourceInfo) extends VTerm(sourceInfo)

  /** @param continuationUsage
    *   see ContinuationUsage for explanation. The reason that we need this part to be a term instead of a literal usage
    *   is because this part needs to participate in usage tracking of following computations (aka continuation). Having
    *   a first-class value here makes definitions parametric in continuation usage.
    * @param controlMode
    *   see ContinuationUsage for explanation
    * @param sourceInfo
    */
  case EffectsType
    (continuationUsage: VTerm = VTerm.UsageLiteral(Usage.UAny), controlMode: ControlMode = ControlMode.Complex)
    (using sourceInfo: SourceInfo)
    extends VTerm(sourceInfo),
    QualifiedNameOwner(
      EffectsQn,
    )

  /** Note: during development I once had a usage filter for each operand. The primary purpose was to filter out complex
    * effects so that the fact that disposing and replicating a continuation can only invoke simple effects can be
    * captured in the type system, in order to allow one to call dispose and replicate inside another parameter disposer
    * or replicator (aka, wrapping continuation inside a handler in order to manage the linear continuation resource).
    * However, this introduces extra complexity into the type checker and it does not seem to be very useful because one
    * typically do not need to manage continuations like that: there are no operations on continuation that does
    * something on it and return a "copy" of the linear resource for future consumptions.
    */
  case Effects(literal: Set[Eff], unionOperands: Set[VTerm])(using sourceInfo: SourceInfo) extends VTerm(sourceInfo)

  case LevelType(upperBound: VTerm = Level(LevelOrder.ω, Map()))(using sourceInfo: SourceInfo)
    extends VTerm(sourceInfo),
    QualifiedNameOwner(LevelQn)

  case Level(literal: LevelOrder, maxOperands: Map[VTerm, /* level offset */ Nat])(using sourceInfo: SourceInfo)
    extends VTerm(sourceInfo)

  /** Automatically derived term, aka, `_` in Agda-like languages. During type checking, this is replaced with
    * `Collapse(Application...(Meta(...)))` and solved through meta-variable unification.
    */
  case Auto()(using sourceInfo: SourceInfo) extends VTerm(sourceInfo)

  // Note: during development, I once had devoted constructs for heap handler, alloc, set, and get operations. But they
  // are entirely redundant because one can just use a linear piece of data as the storage and do the same with the
  // general handler. In addition, the heap key concept is arbitrary and it can actually be substitued with a simple
  // nat instead. The previous heap handler basically does two things under the hood: heap allocation and using it.
  // Since the old implementation actually allocates stuff on the heap, the allocation part is non-deterministic. So
  // one either has to make the type checker to do some hard work to prevent the heap variable from being leaked or
  // just add a non-deterministc effect to all heap handler creations. By simulating heap hander with general handler,
  // the heap allocation (aka, heap key generation) can be a separate step. It can even be deterministically created so
  // that a total computation can rely on mutable states under the hood.

  this match
    case UsageJoin(operands) if operands.isEmpty =>
      throw IllegalArgumentException(
        "Empty operands not allowed for join because join does not have an identity.",
      )
    case _ =>

  override def withSourceInfo(sourceInfo: SourceInfo): VTerm =
    given SourceInfo = sourceInfo

    this match
      case Type(upperBound)                            => Type(upperBound)
      case Top(l, eqD)                                 => Top(l, eqD)
      case Var(index)                                  => Var(index)
      case Collapse(cTm)                               => Collapse(cTm)
      case U(cTy)                                      => U(cTy)
      case Thunk(c)                                    => Thunk(c)
      case DataType(qn, args)                          => DataType(qn, args)
      case Con(name, args)                             => Con(name, args)
      case UsageType(u)                                => UsageType(u)
      case UsageLiteral(u)                             => UsageLiteral(u)
      case UsageProd(operands)                         => UsageProd(operands)
      case UsageSum(operands)                          => UsageSum(operands)
      case UsageJoin(operands)                         => UsageJoin(operands)
      case EqDecidabilityType()                        => EqDecidabilityType()
      case EqDecidabilityLiteral(eqD)                  => EqDecidabilityLiteral(eqD)
      case EffectsType(continuationUsage, controlMode) => EffectsType(continuationUsage, controlMode)
      case Effects(literal, unionOperands)             => Effects(literal, unionOperands)
      case LevelType(upperBound)                       => LevelType(upperBound)
      case Level(literal, maxOperands)                 => Level(literal, maxOperands)
      case Auto()                                      => Auto()

  def visitWith[C, R](visitor: Visitor[C, R])(using ctx: C)(using Σ: Signature): R =
    visitor.visitVTerm(this)

  def transformWith[C](transformer: Transformer[C])(using ctx: C)(using Σ: Signature): VTerm =
    transformer.transformVTerm(this)

object VTerm:

  def Top(t: VTerm, eqDecidability: VTerm = EqDecidabilityLiteral(EqDecidable))(using SourceInfo) =
    new Top(t, eqDecidability)

  def UsageProd(operands: VTerm*)(using SourceInfo): VTerm =
    val (usages, terms) = collectUsage(operands)
    (usages.foldLeft(U1)(_ * _), terms) match
      case (u, Nil)    => UsageLiteral(u)
      case (U1, terms) => UsageProd(terms.toSet)
      case (U0, _)     => UsageLiteral(U0)
      case (u, terms)  => UsageProd((UsageLiteral(u) :: terms).toSet)

  def UsageSum(operands: VTerm*)(using SourceInfo): VTerm =
    val (usages, terms) = collectUsage(operands)
    (usages.foldLeft(U0)(_ + _), terms) match
      case (u, Nil)    => UsageLiteral(u)
      case (U0, terms) => UsageSum(terms.toMultiset)
      case (URel, _)   => UsageLiteral(URel)
      case (u, terms)  => UsageSum((UsageLiteral(u) :: terms).toMultiset)

  def UsageJoin(operands: VTerm*)(using SourceInfo): VTerm =
    if operands.isEmpty then throw IllegalStateException("UsageJoin cannot be empty")
    val (usages, terms) = collectUsage(operands)
    (usages.reduce(_ | _), terms) match
      case (u, Nil)  => UsageLiteral(u)
      case (UAny, _) => UsageLiteral(UAny)
      // Note that something joining itself is the same as the thing itself, so there is never any need to hold
      // duplicates
      case (u, terms) => UsageJoin((UsageLiteral(u) :: terms).toSet)

  private def collectUsage(operands: Seq[VTerm]): (List[Usage], List[VTerm]) =
    operands.foldLeft[(List[Usage], List[VTerm])]((Nil, Nil)) {
      case ((usages, terms), UsageLiteral(u)) => (u :: usages, terms)
      case ((usages, terms), term)            => (usages, terms)
    }

  def LevelLiteral(n: Nat)(using sourceInfo: SourceInfo): Level =
    Level(LevelOrder(0, n), Map())

  def LevelLiteral(m: Nat, n: Nat)(using sourceInfo: SourceInfo): Level =
    Level(LevelOrder(m, n), Map())

  def LevelUpperBound(): Level = Level(LevelOrder.upperBound, Map())

  def LevelSuc(t: VTerm): Level = Level(LevelOrder.zero, Map(t -> 1))

  def LevelMax(ts: VTerm*): Level = Level(LevelOrder.zero, Map(ts.map(_ -> 0): _*))

  def Total()(using sourceInfo: SourceInfo): Effects = EffectsLiteral(Set.empty)
  val u0 = VTerm.UsageLiteral(Usage.U0)
  val u1 = VTerm.UsageLiteral(Usage.U1)
  val uAff = VTerm.UsageLiteral(Usage.UAff)
  val uRel = VTerm.UsageLiteral(Usage.URel)
  val uAny = VTerm.UsageLiteral(Usage.UAny)

  /** Marker of a computation that surely diverges. Computation with this effect will not be executed by the type
    * checker.
    */
  def Div()(using sourceInfo: SourceInfo): Effects = EffectsLiteral(
    Set((Builtins.DivQn, Nil), (Builtins.MaybeDivQn, Nil)),
  )

  /** Marker of a computation that may or may not diverge. Computation with this effect will be further checked by
    * statically at callsite (with additional information available) to ensure it's total before executed by the type
    * checker.
    */
  def MaybeDiv()(using sourceInfo: SourceInfo): Effects = EffectsLiteral(
    Set((Builtins.MaybeDivQn, Nil)),
  )

  def EffectsLiteral(effects: Set[Eff])(using sourceInfo: SourceInfo): Effects =
    Effects(effects, Set.empty)

  def EffectsUnion(effects1: VTerm, effects2: VTerm): Effects =
    Effects(Set.empty, Set(effects1, effects2))

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
  /** Used in stack machine to represent the computations above the computation term containing this. For example, `f a
    * b` converted to the stack machine becomes
    *   - f
    *   - Application(Hole, a)
    *   - Application(Hole, b)
    */
  case Hole extends CTerm(SiEmpty)

  /** Internal only, created by reduction. This is used to signify the tip of a captured continuation term.
    */
  case CapturedContinuationTip(ty: F) extends CTerm(SiEmpty)

  /** archon.builtin.CType */
  case CType
    (
      upperBound: CTerm,
      effects: VTerm = VTerm.Total()(using SiEmpty),
    )
    (using sourceInfo: SourceInfo) extends CTerm(sourceInfo), IType

  case CTop(level: VTerm, effects: VTerm = VTerm.Total()(using SiEmpty))(using sourceInfo: SourceInfo)
    extends CTerm(sourceInfo),
    IType

  /** Represents either a metavariable or a guarded constant in [2]. This is always created during type checking and
    * user-term won't include this. Rather, user terms should contain `Auto` where needed.
    */
  case Meta(index: Nat)(using sourceInfo: SourceInfo) extends CTerm(sourceInfo)
  case Def(qn: QualifiedName)(using sourceInfo: SourceInfo) extends CTerm(sourceInfo)

  case Force(v: VTerm)(using sourceInfo: SourceInfo) extends CTerm(sourceInfo)

  /** archon.builtin.F */
  case F
    (
      vTy: VTerm,
      effects: VTerm = VTerm.Total()(using SiEmpty),
      usage: VTerm = VTerm.UsageLiteral(Usage.U1),
    )
    (using sourceInfo: SourceInfo) extends CTerm(sourceInfo), IType
  case Return(v: VTerm, usage: VTerm)(using sourceInfo: SourceInfo) extends CTerm(sourceInfo)
  // Note that we do not have DLet like [0]. Instead we use inductive type and thunk to simulate
  // the existential computation type Σx:A.C̲ in eMLTT [1]. From practical purpose it seems OK,
  // especially after graded modality is added to support linear usage of computations when needed.
  case Let
    (t: CTerm, ty: VTerm, eff: VTerm, usage: VTerm, ctx: CTerm /* binding += 1 */ )
    (val boundName: Ref[Name])
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

  case Redex(t: CTerm, elims: List[Elimination[VTerm]])(using sourceInfo: SourceInfo) extends CTerm(sourceInfo)

  /** archon.builtin.Function */
  case FunctionType
    (
      binding: Binding[VTerm],
      bodyTy: CTerm, /* binding offset = 1 */
      /** effects that needed for getting the function of this type. The effects caused by function application is
        * tracked by the `bodyTy`.
        */
      effects: VTerm = VTerm.Total()(using SiEmpty),
    )
    (using sourceInfo: SourceInfo) extends CTerm(sourceInfo), IType

  case RecordType
    (
      qn: QualifiedName,
      args: Arguments = Nil,
      effects: VTerm = VTerm.Total()(using SiEmpty),
    )
    (using sourceInfo: SourceInfo) extends CTerm(sourceInfo), IType, QualifiedNameOwner(qn)

  case OperationCall(eff: Eff, name: Name, args: Arguments = Nil)(using sourceInfo: SourceInfo)
    extends CTerm(sourceInfo)

  /** Internal only. This is only created by reduction.
    *
    * @param continuationTerm
    *   a term with a hole at the top. This is equivalent to the captured stack between the matching handler (inclusive)
    *   and the computation right after the corresopnding handler operation (the tip of the stack, which must be a term
    *   of type `ContinuationHole`.)
    */
  case Continuation(continuationTerm: Handler, continuationUsage: Usage) extends CTerm(SiEmpty)

  /** @param eff
    *   Handle general term here instead of a single effect. During type checking it will fail if this term is not
    *   convertible to a effect literal. The ability to handle multiple effects is useful when one needs to use a linear
    *   resource (as parameter to the handler) with multiple effects.
    * @param otherEffects
    *   the effect of the input term without effects being handled by this handler
    * @param outputEffects
    *   otherEffects + effects used in parameter disposer, parameter replicaor, transformer, and operation handler
    *   implementations. This is the effect of each operation handler implementation. This is also the effect of the
    *   resume, dispose, and replicate (strictly speaking the latter two would never perform any complex effects but
    *   capturing this in the type system would require adding another filtering operation on effects based on control
    *   mode and that seems to have little benefits as far as I can see) calls on continuations captured inside handlers
    *   implementations. This is also the effect in the type of the curret handler being defined.
    * @param outputUsage
    *   the usage of the output of the handler. This is also the usage of the resume call on continuations captured
    *   inside handler implementations. This is also the usage of the final returned value in each operation handler
    *   implementation.
    * @param outputTy
    *   the type of the output of the handler. This is also the type of the resume call on continuations captured inside
    *   handler implementations. This is also the type of the final returned value in each operation handler.
    * @param parameter
    * @param parameterBinding
    * @param parameterDisposer
    *   This is invoked by Continuation.dispose on continuations created by parent handlers or this handler. In other
    *   words, it's to clean up the parameter when computation under this handler decides to abort (by calling some
    *   aborting operation). Therefore, it's not needed if the inputEffects have continuation usage URel or U1 (which
    *   means the handler will never need to be aborted) or if the parameter usage is U0, UAff, or UAny (which means the
    *   parameter does not need to be explicitly cleaned up).
    * @param parameterReplicator
    *   This is invoked by Continuation.replicate on continuations created by parent handlers or this handler. In other
    *   words, it's to replicate the parameter when computation under this handler features non-deterministic behavior
    *   (by calling some non-deterministic operation). Therefore, it's not needed if the inputEffects have continuation
    *   usage UAff or U1 (which means the handler is never non-deterministic) or if the parameter usage is U0, URel or
    *   UAny (which means the parameter does not need to be explicitly replicated).
    * @param transform
    *   The transformer that transforms a var at DeBruijn index 0 of type `inputBinding.ty` to `outputType`. for cases
    *   where `outputType` equals `F(someEffects, inputBinding.ty)`, a sensible default value is simply `return (var 0)`
    * @param handlers
    *   All handler implementations declared by the effect. Each handler is essentially a function body that takes some
    *   parameters and return a value, depending on the continuation usage of the operation.
    *   - simple and linear
    *     - handler parameter
    *     - all parameters declared in the operation
    *     - return pair of handler parameter and the output type declared in the operation
    *   - simple and exceptional
    *     - all parameters declared in the operation
    *     - return output type matching the handler output
    *   - complex
    *     - handler parameter
    *     - all parameters declared in the operation
    *     - a continuation taking in a `declared operation output type -> outputType` and outputs `outputType`
    *     - return output type matching the handler output
    * @param input
    * @param inputBinding
    * @param handlersBoundNames
    * @param sourceInfo
    */
  case Handler
    (
      eff: VTerm,
      otherEffects: VTerm,
      outputEffects: VTerm,
      outputUsage: VTerm,
      outputTy: VTerm,
      parameter: VTerm,
      parameterBinding: Binding[VTerm],
      parameterDisposer: Option[CTerm], // binding offset + 1 (for parameter)
      parameterReplicator: Option[CTerm], // binding offset + 1 (for parameter)
      transform: CTerm, // binding offset + 1 (for parameter) + 1 (for value)
      handlers: Map[
        QualifiedName,
        /* binding offset = 1 (for parameter) + paramTys + 1 (for continuation if control mode is complex) */ CTerm,
      ],
      input: CTerm,
      inputBinding: Binding[VTerm],
    )
    (
      val handlersBoundNames: Map[
        QualifiedName,
        (Seq[Ref[Name]], /* resume name */ Option[Ref[Name]]),
      ],
    )
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
      case t: Let                     => t.copy()(t.boundName)
      case t: Redex                   => t.copy()
      case t: FunctionType            => t.copy()
      case t: RecordType              => t.copy()
      case t: OperationCall           => t.copy()
      case c: Continuation            => c
      case h: Handler                 => h.copy()(h.handlersBoundNames)

  // TODO[P3]: support array operations on heap
  // TODO[P3]: consider adding builtin set and maps with decidable equality because we do not
  //  support quotient type and set semantic is very common in software engineering.

  def visitWith[C, R](visitor: Visitor[C, R])(using ctx: C)(using Σ: Signature): R =
    visitor.visitCTerm(this)

  def transformWith[C](transformer: Transformer[C])(using ctx: C)(using Σ: Signature): CTerm =
    transformer.transformCTerm(this)

object CTerm:
  def CTop(t: VTerm, effects: VTerm = VTerm.Total()(using SiEmpty))(using sourceInfo: SourceInfo) =
    new CTop(t, effects)

  @targetName("redexFromElims")
  def redex(c: CTerm, elims: Seq[Elimination[VTerm]])(using SourceInfo): Redex =
    Redex(c, elims.toList)

  @targetName("redexFromElimsStar")
  def redex(c: CTerm, elims: Elimination[VTerm]*)(using SourceInfo): Redex = redex(c, elims)

  @targetName("redexFromTerms")
  def redex(c: CTerm, args: Seq[VTerm])(using SourceInfo): Redex =
    Redex(c, args.map(Elimination.ETerm(_)).toList)

  @targetName("redexFromTermsStar")
  def redex(c: CTerm, args: VTerm*)(using SourceInfo): Redex = redex(c, args)

  def Application(fun: CTerm, arg: VTerm)(using SourceInfo): Redex =
    fun match
      case Redex(c, elims) => Redex(c, elims :+ Elimination.ETerm(arg))
      case t               => Redex(t, List(Elimination.ETerm(arg)))

  def Projection(rec: CTerm, name: Name)(using SourceInfo): Redex =
    rec match
      case Redex(c, elims) => Redex(c, elims :+ Elimination.EProj(name))
      case t               => Redex(t, List(Elimination.EProj(name)))

  extension (binding: Binding[VTerm])
    infix def ->:(body: CTerm): FunctionType =
      new FunctionType(binding, body)

/* References:
 [0]  Pierre-Marie Pédrot and Nicolas Tabareau. 2019. The fire triangle: how to mix substitution,
      dependent elimination, and effects. Proc. ACM Program. Lang. 4, POPL, Article 58 (January
      2020), 28 pages. DOI:https://doi.org/10.1145/3371126
 [1]  Danel Ahman. 2017. Handling fibred algebraic effects. Proc. ACM Program. Lang. 2, POPL,
      Article 7 (January 2018), 29 pages. DOI:https://doi.org/10.1145/3158095
 [2]  Norell, Ulf. “Towards a practical programming language based on dependent type theory.” (2007).
 */
