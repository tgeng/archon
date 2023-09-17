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

class HeapKey:
  private val id = HeapKey.nextId

  override def toString: String = "heap" + id

object HeapKey:
  private var globalIdCounter = 0

  private def nextId: Int =
    val r = globalIdCounter
    globalIdCounter += 1
    r

val GlobalHeapKey = new HeapKey:
  override def toString = "<globalHeapKey>"

type Eff = (QualifiedName, Arguments)

import Builtins.*

sealed trait QualifiedNameOwner(_qualifiedName: QualifiedName):
  def qualifiedName: QualifiedName = _qualifiedName

extension (eff: Eff) def map(f: VTerm => VTerm): Eff = (eff._1, eff._2.map(f))

/** Represents an order number `m * ω + n`.
  */
case class LevelOrder(m: Nat, n: Nat) extends Comparable[LevelOrder]:
  override def compareTo(that: LevelOrder): Int =
    if this.m < that.m then -1
    else if this.m > that.m then 1
    else this.n.compareTo(that.n)

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

  // When checking usages, vars in cTy should be multiplied by UUnres so that type U is Unrestricted
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
    *   see `Effect` for the semantic of this. Some(Usage.UUnres) is the most general value and allows any effects.
    */
  case EffectsType(continuationUsage: Option[Usage] = Some(Usage.UUnres))(using sourceInfo: SourceInfo)
    extends VTerm(sourceInfo),
    QualifiedNameOwner(
      EffectsQn,
    )
  case Effects(literal: Set[Eff], unionOperands: Set[VTerm])(using sourceInfo: SourceInfo) extends VTerm(sourceInfo)

  case LevelType(upperBound: VTerm = Level(LevelOrder.ω, Map()))(using sourceInfo: SourceInfo)
    extends VTerm(sourceInfo),
    QualifiedNameOwner(LevelQn)

  case Level(literal: LevelOrder, maxOperands: Map[VTerm, /* level offset */ Nat])(using sourceInfo: SourceInfo)
    extends VTerm(sourceInfo)

  /** archon.builtin.Heap */
  case HeapType()(using sourceInfo: SourceInfo) extends VTerm(sourceInfo), QualifiedNameOwner(HeapQn)

  /** Internal only, created by [[CTerm.HeapHandler]]
    */
  case Heap(key: HeapKey)(using sourceInfo: SourceInfo) extends VTerm(sourceInfo)

  /** archon.builtin.Cell */
  case CellType(heap: VTerm, ty: VTerm)(using sourceInfo: SourceInfo) extends VTerm(sourceInfo)

  /** Internal only, created by [[CTerm.AllocOp]]
    */
  case Cell(heapKey: HeapKey, index: Nat)(using sourceInfo: SourceInfo) extends VTerm(sourceInfo)

  /** Automatically derived term, aka, `_` in Agda-like languages. During type checking, this is replaced with
    * `Collapse(Application...(Meta(...)))` and solved through meta-variable unification.
    */
  case Auto()(using sourceInfo: SourceInfo) extends VTerm(sourceInfo)

  this match
    case UsageJoin(operands) if operands.isEmpty =>
      throw IllegalArgumentException(
        "empty operands not allowed for join because join does not have an identity",
      )
    case _ =>

  override def withSourceInfo(sourceInfo: SourceInfo): VTerm =
    given SourceInfo = sourceInfo

    this match
      case Type(upperBound)                => Type(upperBound)
      case Top(l, eqD)                     => Top(l, eqD)
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
      case EqDecidabilityType()            => EqDecidabilityType()
      case EqDecidabilityLiteral(eqD)      => EqDecidabilityLiteral(eqD)
      case EffectsType(continuationUsage)  => EffectsType(continuationUsage)
      case Effects(literal, unionOperands) => Effects(literal, unionOperands)
      case LevelType(upperBound)           => LevelType(upperBound)
      case Level(literal, maxOperands)     => Level(literal, maxOperands)
      case HeapType()                      => HeapType()
      case Heap(key)                       => Heap(key)
      case CellType(heap, ty)              => CellType(heap, ty)
      case Cell(heapKey, index)            => Cell(heapKey, index)
      case Auto()                          => Auto()

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
      case (u, Nil)    => UsageLiteral(u)
      case (UUnres, _) => UsageLiteral(UUnres)
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

  /** Marker of a computation that surely diverges. Computation with this effect will not be executed by the type
    * checker.
    */
  def Div()(using sourceInfo: SourceInfo): Effects = EffectsLiteral(
    Set((Builtins.DivQn, Nil), (Builtins.MaybeDivQn, Nil)),
  )

  /** Marker of a computation that may or may not diverge. Computation with this effect will be executed by the type
    * checker with timeout.
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
  case Return(v: VTerm)(using sourceInfo: SourceInfo) extends CTerm(sourceInfo)
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
    * @param handler
    *   the handler that delimits this continuation
    * @param capturedStack
    *   stack containing the delimited continuation from the tip (right below operation call) to the computation right
    *   above corresponding handler. Note that the first term is at the bottom of the stack and the last term is the tip
    *   of the stack.
    */
  case Continuation(handler: Handler, capturedStack: Seq[CTerm | Elimination[VTerm]]) extends CTerm(SiEmpty)

  /** Internaly only. This is only created by reduction.
    *
    * During reduction, this value is specially handled: any non-handlers are skipped and parameterReplicator in
    * handlers are executed one by one to collect the replicated parameters. These replicated parameters are then
    * collected into the two stacks, until reaching the handler at `handlerIndex` (the handler that contains the
    * operation implementation which invokes the continuation replication).
    * @param handlerIndex:
    *   index of this handler in the reduction machine stack. In other words, size of the stack before this handler is
    *   pushed onto the stack.
    * @param stack1:
    *   the replicated stack
    * @param stack1:
    *   the other replicated stack
    */
  case ContinuationReplicationState
    (
      handlerIndex: Nat,
      stack1: Seq[CTerm | Elimination[VTerm]],
      stack2: Seq[CTerm | Elimination[VTerm]],
    ) extends CTerm(SiEmpty)

  /** Internaly only. This is only created by reduction.
    *
    * A helper that marks the end of execution of a `parameterReplicator`.
    * @param paramPairs
    *   computation that returns a pair of parameters. This should simply be application of `parameterReplicator` in
    *   handlers.
    * @param handler
    *   the handler that should be replicated and contain the replicated params
    * @param state
    *   the target ContinuationReplicationState to which the replicated parameters is appended
    */
  case ContinuationReplicationStateAppender(paramPairs: CTerm, handler: Handler, state: ContinuationReplicationState)
    extends CTerm(SiEmpty)

  case Handler
    (
      /** Handle general term here instead of a single effect. During type checking it will fail if this term is not
        * convertible to a effect literal. The ability to handle multiple effects is useful when one needs to use a
        * linear resource (as parameter to the handler) with multiple effects.
        */
      eff: VTerm,
      parameter: VTerm,
      parameterBinding: Binding[VTerm],
      // Effects of this term can not be re-entrant for simplicity
      parameterDisposer: CTerm, // binding offset + 1 (for parameter)
      // Replicator is optional: if it's present, outputEffects can be re-entrant; otherwise, output
      // effects can only be linear or disposable
      // Also, effects of this term can not be re-entrant for simplicity
      parameterReplicator: Option[CTerm], // binding offset + 1 (for parameter)
      outputEffects: VTerm,
      outputUsage: VTerm,

      /** This is the output value type. The computation type of this handler is `F(outputType, outputEffects,
        * outputUsage)`.
        */
      outputType: VTerm,

      /** The transformer that transforms a var at DeBruijn index 0 of type `inputBinding.ty` to `outputType`. for cases
        * where `outputType` equals `F(someEffects, inputBinding.ty)`, a sensible default value is simply `return (var
        * 0)`
        */

      transform: CTerm, // binding offset + 1 (for parameter) + 1 (for value)

      /** All handler implementations declared by the effect. Each handler is essentially a function body that takes the
        * following arguments
        *   - all declared parameters
        *   - a continuation parameter of type `declared operation output type -> outputType` and outputs `outputType`
        */
      handlers: Map[
        QualifiedName,
        /* binding offset = 1 (for parameter) + paramTys + 1 (for resume if needed) */ CTerm,
      ],
      input: CTerm,
    )
    (
      val transformBoundName: Ref[Name],
      val handlersBoundNames: Map[
        QualifiedName,
        (Seq[Ref[Name]], /* resume name */ Option[Ref[Name]]),
      ],
    )
    (using sourceInfo: SourceInfo) extends CTerm(sourceInfo)

  case AllocOp(heap: VTerm, ty: VTerm, value: VTerm)(using sourceInfo: SourceInfo) extends CTerm(sourceInfo)
  case SetOp(cell: VTerm, value: VTerm)(using sourceInfo: SourceInfo) extends CTerm(sourceInfo)
  case GetOp(cell: VTerm)(using sourceInfo: SourceInfo) extends CTerm(sourceInfo)
  case HeapHandler
    (
      /** Newly created heap handler should always set this to `None`. This key is instantiated during reduction to a
        * fresh value.
        */
      key: Option[HeapKey],
      heapContent: IndexedSeq[VTerm],

      /** Note that the logic here should not expose the heap variable (i.e. `var 0`) through existential types like (t:
        * Type, x: t) where `t` can be `HeapType`. A syntax-based check is used to ensure this never happens. For cases
        * where such flexibility is needed, one should use `GlobalHeapKey` instead.
        */
      /* binding offset + 1 */ input: CTerm,
    )
    (val boundName: Ref[Name])
    (using sourceInfo: SourceInfo) extends CTerm(sourceInfo)

  override def withSourceInfo(sourceInfo: SourceInfo): CTerm =
    given SourceInfo = sourceInfo

    this match
      case Hole                            => Hole
      case CType(upperBound, effects)      => CType(upperBound, effects)
      case CTop(l, effects)                => CTop(l, effects)
      case Meta(index)                     => Meta(index)
      case Def(qn)                         => Def(qn)
      case Force(v)                        => Force(v)
      case F(vTy, effects, u)              => F(vTy, effects, u)
      case Return(v)                       => Return(v)
      case l @ Let(t, ty, eff, usage, ctx) => Let(t, ty, eff, usage, ctx)(l.boundName)
      case Redex(t, elims)                 => Redex(t, elims)
      case FunctionType(binding, bodyTy, effects) =>
        FunctionType(binding, bodyTy, effects)
      case RecordType(qn, args, effects)  => RecordType(qn, args, effects)
      case OperationCall(eff, name, args) => OperationCall(eff, name, args)
      case c: (Continuation | ContinuationReplicationState | ContinuationReplicationStateAppender) =>
        c
      case h @ Handler(
          eff,
          paramterBinding,
          parameter,
          parameterDisposer,
          parameterReplicator,
          outputEffects,
          outputUsage,
          outputType,
          transform,
          handlers,
          input,
        ) =>
        Handler(
          eff,
          paramterBinding,
          parameter,
          parameterDisposer,
          parameterReplicator,
          outputEffects,
          outputUsage,
          outputType,
          transform,
          handlers,
          input,
        )(
          h.transformBoundName,
          h.handlersBoundNames,
        )
      case AllocOp(heap, ty, value) => AllocOp(heap, ty, value)
      case SetOp(cell, value)       => SetOp(cell, value)
      case GetOp(cell)              => GetOp(cell)
      case h @ HeapHandler(key, heapContent, input) =>
        HeapHandler(
          key,
          heapContent,
          input,
        )(h.boundName)

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
