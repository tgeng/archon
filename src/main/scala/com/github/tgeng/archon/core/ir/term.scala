package com.github.tgeng.archon.core.ir

import collection.mutable
import com.github.tgeng.archon.common.*
import com.github.tgeng.archon.core.common.*
import QualifiedName.*
import SourceInfo.*
import EqDecidability.*
import Usage.*
import com.github.tgeng.archon.core.ir.VTerm.EqDecidabilityLiteral

// Term hierarchy is inspired by Pédrot 2020 [0]. The difference is that our computation types are
// graded with type of effects, which then affects type checking: any computation that has side
// effects would not reduce during type checking.

case class Binding[+T](ty: T, usage: T)(val name: Ref[Name]):
  def map[S](f: T => S): Binding[S] = Binding(f(ty), f(usage))(name)

object Binding:
  def apply[T](ty: T, usage: T)(name: Ref[Name]): Binding[T] =
    new Binding(ty, usage)(name)

  def apply(ty: VTerm, usage: Usage)(name: Ref[Name]): Binding[VTerm] =
    new Binding(ty, VTerm.UsageLiteral(usage))(name)

/** Head is on the left, e.g. Z :: S Z :: []
  */
type Arguments = List[VTerm]

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

extension(eff: Eff) def map(f: VTerm => VTerm): Eff = (eff._1, eff._2.map(f))

enum ULevel(val sourceInfo: SourceInfo) extends SourceInfoOwner[ULevel]:
  case USimpleLevel(level: VTerm) extends ULevel(level.sourceInfo)
  case UωLevel(layer: Nat)(using sourceInfo: SourceInfo) extends ULevel(sourceInfo)

  override def withSourceInfo(sourceInfo: SourceInfo): ULevel =
    given SourceInfo = sourceInfo

    this match
      case USimpleLevel(level) => USimpleLevel(level)
      case UωLevel(layer)      => UωLevel(layer)

object ULevel:
  extension(u: ULevel)
    def map(f: VTerm => VTerm): ULevel = u match
      case USimpleLevel(level) => USimpleLevel(f(level))
      case _: ULevel.UωLevel   => u

  def ULevelSuc(u: ULevel): ULevel =
    given SourceInfo = SiLevelSuc(u.sourceInfo)

    u match
      case USimpleLevel(l) => USimpleLevel(VTerm.LevelSuc(l))
      case UωLevel(layer)  => UωLevel(layer + 1)

  def ULevelMax(u1: ULevel, u2: ULevel): ULevel =
    given SourceInfo = SiLevelMax(u1.sourceInfo, u2.sourceInfo)

    (u1, u2) match
      case (USimpleLevel(l1), USimpleLevel(l2)) =>
        USimpleLevel(VTerm.LevelMax(l1, l2))
      case (UωLevel(layer1), UωLevel(layer2)) =>
        UωLevel(math.max(layer1, layer2))
      case (_, u: UωLevel) => u
      case (u, _)          => u

enum CellStatus extends Comparable[CellStatus]:
  case Initialized, Uninitialized

  override def compareTo(that: CellStatus): Int =
    if this == that then 0
    else if this == CellStatus.Initialized then -1
    else 1

enum UsageOperator:
  case USum, UProd, UJoin

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
  case Top
    (
      ul: ULevel,
      usage: VTerm = UsageLiteral(Usage.U1),
      eqDecidability: VTerm = EqDecidabilityLiteral(EqUnres)
    )
    (using sourceInfo: SourceInfo) extends VTerm(sourceInfo), QualifiedNameOwner(TopQn)

  case Var(idx: Nat)(using sourceInfo: SourceInfo) extends VTerm(sourceInfo)

  /** Execute a effect free computation and get the returned value. That is, `cTm` must be of type
    * `F(V, Total)` for some value type `V`. This VTerm construct is used to embed effect free
    * computations into values so that the type theory is as expressive as typical dependent type
    * theory.
    */
  case Collapse(cTm: CTerm)(using sourceInfo: SourceInfo) extends VTerm(sourceInfo)

  // When checking usages, vars in cTy should be multiplied by UUnres so that type U is Unrestricted
  case U(cTy: CTerm)(using sourceInfo: SourceInfo) extends VTerm(sourceInfo)
  // Note: simply multiply the usage of `U ...` to the usages of everything in `cTy`
  case Thunk(c: CTerm)(using sourceInfo: SourceInfo) extends VTerm(sourceInfo)

  case DataType
    (qn: QualifiedName, args: Arguments = Nil)
    (using
      sourceInfo: SourceInfo
    ) extends VTerm(sourceInfo), QualifiedNameOwner(qn)
  case Con(name: Name, args: Arguments = Nil)(using sourceInfo: SourceInfo)
    extends VTerm(sourceInfo)

  case EqualityType
    (
      ty: VTerm,
      left: VTerm,
      right: VTerm
    )
    (using sourceInfo: SourceInfo) extends VTerm(sourceInfo) // , QualifiedNameOwner(EqualityQn)
  case Refl()(using sourceInfo: SourceInfo) extends VTerm(sourceInfo)

  // Note, `upper` here is in the sense of typing subsumption, not the usage lattice. This is the
  // lower bound in the usage lattice. Hence Option.None is used to represent unbounded case, as the
  // lattice is not bounded below.
  case UsageType(upperBound: Option[Usage])(using sourceInfo: SourceInfo)
    extends VTerm(sourceInfo)
  case UsageLiteral(usage: Usage)(using sourceInfo: SourceInfo) extends VTerm(sourceInfo)
  case UsageCompound
    (operator: UsageOperator, operands: Multiset[VTerm])
    (using
      sourceInfo: SourceInfo
    ) extends VTerm(sourceInfo)

  case EqDecidabilityType()(using sourceInfo: SourceInfo) extends VTerm(sourceInfo)
  case EqDecidabilityLiteral(eqDecidability: EqDecidability)(using sourceInfo: SourceInfo)
    extends VTerm(
      sourceInfo
    )

  case EffectsType(continuationUsage: VTerm = UsageLiteral(UUnres))(using sourceInfo: SourceInfo)
    extends VTerm(sourceInfo),
    QualifiedNameOwner(
      EffectsQn
    )
  case Effects(literal: Set[Eff], unionOperands: Set[VTerm])(using sourceInfo: SourceInfo)
    extends VTerm(sourceInfo)

  case LevelType()(using sourceInfo: SourceInfo)
    extends VTerm(sourceInfo),
    QualifiedNameOwner(
      LevelQn
    )
  case Level
    (literal: Nat, maxOperands: Map[VTerm, /* level offset */ Nat])
    (using sourceInfo: SourceInfo) extends VTerm(sourceInfo)

  /** archon.builtin.Heap */
  case HeapType()(using sourceInfo: SourceInfo)
    extends VTerm(sourceInfo),
    QualifiedNameOwner(HeapQn)

  /** Internal only, created by [[CTerm.HeapHandler]]
    */
  case Heap(key: HeapKey)(using sourceInfo: SourceInfo) extends VTerm(sourceInfo)

  /** archon.builtin.Cell */
  case CellType(heap: VTerm, ty: VTerm, status: CellStatus)(using sourceInfo: SourceInfo)
    extends VTerm(sourceInfo) // , QualifiedNameOwner(CellQn)

  /** Internal only, created by [[CTerm.AllocOp]]
    */
  case Cell(heapKey: HeapKey, index: Nat)(using sourceInfo: SourceInfo) extends VTerm(sourceInfo)

  this match
    case UsageCompound(UsageOperator.UJoin, operands) if operands.isEmpty =>
      throw IllegalArgumentException(
        "empty operands not allowed for join because join does not have an identity"
      )
    case _ =>

  override def withSourceInfo(sourceInfo: SourceInfo): VTerm =
    given SourceInfo = sourceInfo

    this match
      case Type(upperBound)                => Type(upperBound)
      case Top(ul, u, eqD)                 => Top(ul, u, eqD)
      case Var(index)                      => Var(index)
      case Collapse(cTm)                   => Collapse(cTm)
      case U(cTy)                          => U(cTy)
      case Thunk(c)                        => Thunk(c)
      case DataType(qn, args)              => DataType(qn, args)
      case Con(name, args)                 => Con(name, args)
      case EqualityType(ty, left, right)   => EqualityType(ty, left, right)
      case Refl()                          => Refl()
      case UsageType(u)                    => UsageType(u)
      case UsageLiteral(u)                 => UsageLiteral(u)
      case UsageCompound(op, operands)     => UsageCompound(op, operands)
      case EqDecidabilityType()            => EqDecidabilityType()
      case EqDecidabilityLiteral(eqD)      => EqDecidabilityLiteral(eqD)
      case EffectsType(continuationUsage)  => EffectsType(continuationUsage)
      case Effects(literal, unionOperands) => Effects(literal, unionOperands)
      case LevelType()                     => LevelType()
      case Level(literal, maxOperands)     => Level(literal, maxOperands)
      case HeapType()                      => HeapType()
      case Heap(key)                       => Heap(key)
      case CellType(heap, ty, status)      => CellType(heap, ty, status)
      case Cell(heapKey, index)            => Cell(heapKey, index)

  def visitWith[C, R](visitor: Visitor[C, R])(using ctx: C)(using Σ: Signature): R =
    visitor.visitVTerm(this)

  def transformWith[C](transformer: Transformer[C])(using ctx: C)(using Σ: Signature): VTerm =
    transformer.transformVTerm(this)

object VTerm:
  def UsageSum(operands: VTerm*)(using SourceInfo) =
    UsageCompound(UsageOperator.USum, operands.toMultiset)
  def UsageProd(operands: VTerm*)(using SourceInfo) =
    UsageCompound(UsageOperator.UProd, operands.toMultiset)
  def UsageJoin(operands: VTerm*)(using SourceInfo) =
    UsageCompound(UsageOperator.UJoin, operands.toMultiset)

  def LevelLiteral(n: Nat)(using sourceInfo: SourceInfo): Level =
    Level(n, Map())

  def LevelSuc(t: VTerm): Level = t match
    case Level(literal, maxOperands) =>
      Level(
        literal + 1,
        maxOperands.map { (r, o) => (r, o + 1) }
      )(using SiLevelSuc(t.sourceInfo))
    case r: Var => Level(1, Map((r, 1)))(using SiLevelSuc(t.sourceInfo))
    case _      => throw IllegalArgumentException("type error")

  def LevelMax(t1: VTerm, t2: VTerm): Level = t1 match
    case Level(literal1, maxOperands1) =>
      t2 match
        case Level(literal2, maxOperands2) =>
          Level(
            math.max(literal1, literal2),
            Map.from(
              (maxOperands1.toSeq ++ maxOperands2.toSeq)
                .groupBy(_._1)
                .map { (k, vs) => (k, vs.map(_._2).max) }
            )
          )(using SiLevelMax(t1.sourceInfo, t2.sourceInfo))
        case r: Var =>
          Level(literal1, maxOperands1.updated(r, 0))(using
            SiLevelMax(t1.sourceInfo, t2.sourceInfo)
          )
        case _ => throw IllegalArgumentException("type error")
    case r1: Var =>
      t2 match
        case Level(literal2, maxOperands2) =>
          Level(literal2, maxOperands2.updated(r1, 0))(using
            SiLevelMax(t1.sourceInfo, t2.sourceInfo)
          )
        case r2: Var =>
          Level(0, Map((r1, 0), (r2, 0)))(
            using
            SiLevelMax(
              t1.sourceInfo,
              t2.sourceInfo
            )
          )
        case _ => throw IllegalArgumentException("type error")
    case _ => throw IllegalArgumentException("type error")

  def Total(using sourceInfo: SourceInfo): Effects = EffectsLiteral(Set.empty)

  def EffectsLiteral(effects: Set[Eff])(using sourceInfo: SourceInfo): Effects =
    Effects(
      effects,
      Set.empty
    )

  def EffectsUnion(effects1: VTerm, effects2: VTerm): Effects =
    given SourceInfo = SiEffectUnion(effects1.sourceInfo, effects2.sourceInfo)

    effects1 match
      case Effects(literal1, unionOperands1) =>
        effects2 match
          case Effects(literal2, unionOperands2) =>
            Effects(
              literal1 ++ literal2,
              unionOperands1 ++ unionOperands2
            )
          case r: Var => Effects(literal1, unionOperands1 + r)
          case _      => throw IllegalArgumentException("type error")
      case r1: Var =>
        effects2 match
          case Effects(literal2, unionOperands2) =>
            Effects(
              literal2,
              unionOperands2 + r1
            )
          case r2: Var => Effects(Set(), Set(r1, r2))
          case _       => throw IllegalArgumentException("type error")
      case _ => throw IllegalArgumentException("type error")

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

  /** archon.builtin.CType */
  case CType
    (
      upperBound: CTerm,
      effects: VTerm = VTerm.Total(using SiEmpty)
    )
    (using sourceInfo: SourceInfo) extends CTerm(sourceInfo), IType

  case CTop(ul: ULevel, effects: VTerm = VTerm.Total(using SiEmpty))(using sourceInfo: SourceInfo)
    extends CTerm(sourceInfo),
    IType

  case Def(qn: QualifiedName)(using sourceInfo: SourceInfo) extends CTerm(sourceInfo)

  case Force(v: VTerm)(using sourceInfo: SourceInfo) extends CTerm(sourceInfo)

  /** archon.builtin.F */
  case F
    (
      vTy: VTerm,
      effects: VTerm = VTerm.Total(using SiEmpty),
      usage: VTerm = VTerm.UsageLiteral(Usage.U1)
    )
    (using sourceInfo: SourceInfo) extends CTerm(sourceInfo), IType
  case Return(v: VTerm, usage: VTerm = VTerm.UsageLiteral(Usage.U1))(using sourceInfo: SourceInfo)
    extends CTerm(sourceInfo)
  // Note that we do not have DLet like [0]. Instead we use inductive type and thunk to simulate
  // the existential computation type Σx:A.C̲ in eMLTT [1]. From practical purpose it seems OK,
  // especially after graded modality is added to support linear usage of computations when needed.
  case Let
    (t: CTerm, /* binding offset = 1 */ ctx: CTerm)
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

  /** archon.builtin.Function */
  case FunctionType
    (
      binding: Binding[VTerm],
      bodyTy: CTerm, /* binding offset = 1 */
      /** effects that needed for getting the function of this type. The effects caused by
        * function application is tracked by the `bodyTy`.
        */
      effects: VTerm = VTerm.Total(using SiEmpty)
    )
    (using sourceInfo: SourceInfo) extends CTerm(sourceInfo), IType

  case Application(fun: CTerm, arg: VTerm)(using sourceInfo: SourceInfo) extends CTerm(sourceInfo)

  case RecordType
    (
      qn: QualifiedName,
      args: Arguments = Nil,
      effects: VTerm = VTerm.Total(using SiEmpty)
    )
    (using sourceInfo: SourceInfo) extends CTerm(sourceInfo), IType, QualifiedNameOwner(qn)

  case Projection(rec: CTerm, name: Name)(using sourceInfo: SourceInfo) extends CTerm(sourceInfo)

  case OperatorCall(eff: Eff, name: Name, args: Arguments = Nil)(using sourceInfo: SourceInfo)
    extends CTerm(sourceInfo)

  /** Internal only. This is only created by reduction.
    *
    * A continuation behaves like a (linear) function, it has type `U inputBinding -> outputType`,
    * where `inputBinding` is the type of the hole at the tip of the continuation seq and
    * `outputType` is the type of the bottom continuation stack.
    *
    * @param continuation
    *   stack containing the delimited continuation from the tip (right below operator call) to
    *   the corresponding handler, inclusively. Note that the first term is at the bottom of the
    *   stack and the last term is the tip of the stack.
    */
  case Continuation(capturedStack: Seq[CTerm]) extends CTerm(SiEmpty)

  case Handler
    (
      eff: Eff,
      outputEffects: VTerm,
      outputUsage: VTerm,

      /** This is the output value type. The computation type of this handler is `F(outputType,
        * outputEffects, outputUsage)`.
        */
      outputType: VTerm,

      /** The transformer that transforms a var at DeBruijn index 0 of type `inputBinding.ty` to
        * `outputType`. for cases where `outputType` equals `F(someEffects, inputBinding.ty)`, a
        * sensible default value is simply `return (var 0)`
        */
      /* binding offset + 1 */ transform: CTerm,

      /** All handler implementations declared by the effect. Each handler is essentially a
        * function body that takes the following arguments
        *   - all declared parameters
        *   - a continuation parameter of type `declared operator output type -> outputType` and
        *     outputs `outputType`
        */
      handlers: Map[
        Name, /* binding offset = paramTys + 1 (for resume) */ CTerm
      ],
      input: CTerm
    )
    (
      val transformBoundName: Ref[Name],
      val handlersBoundNames: Map[
        Name,
        (Seq[Ref[Name]], /* resume name */ Ref[Name])
      ]
    )
    (using sourceInfo: SourceInfo) extends CTerm(sourceInfo)

  case AllocOp(heap: VTerm, ty: VTerm)(using sourceInfo: SourceInfo) extends CTerm(sourceInfo)
  case SetOp(cell: VTerm, value: VTerm)(using sourceInfo: SourceInfo) extends CTerm(sourceInfo)
  case GetOp(cell: VTerm)(using sourceInfo: SourceInfo) extends CTerm(sourceInfo)
  case HeapHandler
    (
      outputEffects: VTerm,

      /** Newly created heap handler should always set this to `None`. This key is instantiated
        * during reduction to a fresh value.
        */
      key: Option[HeapKey],
      heapContent: IndexedSeq[Option[VTerm]],

      /** Note that the logic here should not expose the heap variable (i.e. `var 0`) through
        * existential types like (t: Type, x: t) where `t` can be `HeapType`. A syntax-based check
        * is used to ensure this never happens. For cases where such flexibility is needed, one
        * should use `GlobalHeapKey` instead.
        */
      /* binding offset + 1 */ input: CTerm
    )
    (val boundName: Ref[Name])
    (using sourceInfo: SourceInfo) extends CTerm(sourceInfo)

  override def withSourceInfo(sourceInfo: SourceInfo): CTerm =
    given SourceInfo = sourceInfo

    this match
      case Hole                       => Hole
      case CType(upperBound, effects) => CType(upperBound, effects)
      case CTop(ul, effects)          => CTop(ul, effects)
      case Def(qn)                    => Def(qn)
      case Force(v)                   => Force(v)
      case F(vTy, effects, u)         => F(vTy, effects, u)
      case Return(v, u)               => Return(v, u)
      case l @ Let(t, ctx)            => Let(t, ctx)(l.boundName)
      case FunctionType(binding, bodyTy, effects) =>
        FunctionType(binding, bodyTy, effects)
      case Application(fun, args)        => Application(fun, args)
      case RecordType(qn, args, effects) => RecordType(qn, args, effects)
      case Projection(rec, name)         => Projection(rec, name)
      case OperatorCall(eff, name, args) => OperatorCall(eff, name, args)
      case c: Continuation               => c
      case h @ Handler(
          eff,
          outputEffects,
          outputUsage,
          outputType,
          transform,
          handlers,
          input
        ) =>
        Handler(
          eff,
          outputEffects,
          outputUsage,
          outputType,
          transform,
          handlers,
          input
        )(
          h.transformBoundName,
          h.handlersBoundNames
        )
      case AllocOp(heap, ty)  => AllocOp(heap, ty)
      case SetOp(cell, value) => SetOp(cell, value)
      case GetOp(cell)        => GetOp(cell)
      case h @ HeapHandler(outputEffects, key, heapContent, input) =>
        HeapHandler(
          outputEffects,
          key,
          heapContent,
          input
        )(h.boundName)

  // TODO[P3]: support array operations on heap
  // TODO[P3]: consider adding builtin set and maps with decidable equality because we do not
  //  support quotient type and set semantic is very common in software engineering.

  def visitWith[C, R](visitor: Visitor[C, R])(using ctx: C)(using Σ: Signature): R =
    visitor.visitCTerm(this)

  def transformWith[C](transformer: Transformer[C])(using ctx: C)(using Σ: Signature): CTerm =
    transformer.transformCTerm(this)

/* References:
 [0]  Pierre-Marie Pédrot and Nicolas Tabareau. 2019. The fire triangle: how to mix substitution,
      dependent elimination, and effects. Proc. ACM Program. Lang. 4, POPL, Article 58 (January
      2020), 28 pages. DOI:https://doi.org/10.1145/3371126
 [1]  Danel Ahman. 2017. Handling fibred algebraic effects. Proc. ACM Program. Lang. 2, POPL,
      Article 7 (January 2018), 29 pages. DOI:https://doi.org/10.1145/3158095
 */
