package com.github.tgeng.archon.core.ir

import scala.collection.immutable.{ListMap, ListSet}
import com.github.tgeng.archon.common.*
import com.github.tgeng.archon.core.common.*
import QualifiedName.*

// Term hierarchy is inspired by Pédrot 2020 [0]. The difference is that our computation types are
// graded with type of effects, which then affects type checking: any computation that has side
// effects would not reduce during type checking.

case class Binding[+T](ty: T)(name: Name):
  def map[S](f: T => S): Binding[S] = Binding(f(ty))(name)

/**
 * Head is on the left, e.g. Z :: S Z :: []
 */
type Arguments = List[VTerm]

class HeapKey

val GlobalHeapKey = new HeapKey

type Eff = (QualifiedName, Arguments)

import Builtins._

sealed trait QualifiedNameOwner(_qualifiedName: QualifiedName):
  def qualifiedName: QualifiedName = _qualifiedName

extension (eff: Eff)
  def map[S](f: VTerm => VTerm): Eff = (eff._1, eff._2.map(f))

enum ULevel:
  case USimpleLevel(level: VTerm)
  case UωLevel(layer: Nat)

object ULevel:
  extension (u: ULevel)
    def map(f: VTerm => VTerm): ULevel = u match
      case USimpleLevel(level) => USimpleLevel(f(level))
      case _: ULevel.UωLevel => u

  def ULevelSuc(u: ULevel): ULevel = u match
    case USimpleLevel(l) => USimpleLevel(VTerm.LevelSuc(l))
    case UωLevel(layer) => UωLevel(layer + 1)

  def ULevelMax(u1: ULevel, u2: ULevel): ULevel = (u1, u2) match
    case (USimpleLevel(l1), USimpleLevel(l2)) => USimpleLevel(VTerm.LevelMax(l1, l2))
    case (UωLevel(layer1), UωLevel(layer2)) => UωLevel(math.max(layer1, layer2))
    case (_, u: UωLevel) => u
    case (u, _) => u

enum CellStatus extends Comparable[CellStatus] :
  case Initialized, Uninitialized

  override def compareTo(that: CellStatus): Int =
    if this == that then 0
    else if this == CellStatus.Initialized then -1
    else 1

enum VTerm:
  case Type(ul: ULevel, upperBound: VTerm) extends VTerm, QualifiedNameOwner(TypeQn)
  case Top(ul: ULevel) extends VTerm, QualifiedNameOwner(TopQn)

  /**
   * Top type of pure value types.
   */
  case Pure(ul: ULevel) extends VTerm, QualifiedNameOwner(PureQn)

  case Var(index: Nat)

  /**
   * Execute a effect free computation and get the returned value. That is, `cTm` must be of type
   * `F(V, Total)` for some value type `V`. This VTerm construct is used to embed effect free
   * computations into values so that the type theory is as expressive as typical dependent type
   * theory.
   */
  case Collapse(cTm: CTerm)

  case U(cty: CTerm)
  case Thunk(c: CTerm)

  case DataType(qn: QualifiedName, args: Arguments = Nil) extends VTerm, QualifiedNameOwner(qn)
  case Con(name: Name, args: Arguments = Nil)

  case EqualityType(
    ty: VTerm,
    left: VTerm,
    right: VTerm
  ) extends VTerm //, QualifiedNameOwner(EqualityQn)
  case Refl

  case EffectsType extends VTerm, QualifiedNameOwner(EffectsQn)
  case Effects(literal: ListSet[Eff], unionOperands: ListSet[VTerm.Var])

  case LevelType extends VTerm, QualifiedNameOwner(LevelQn)
  case Level(literal: Nat, maxOperands: ListMap[VTerm.Var, /* level offset */ Nat])

  /** archon.builtin.Heap */
  case HeapType extends VTerm, QualifiedNameOwner(HeapQn)

  /**
   * Internal only, created by [[CTerm.HeapHandler]]
   */
  case Heap(key: HeapKey)

  /** archon.builtin.Cell */
  case CellType(
    heap: VTerm,
    ty: VTerm,
    status: CellStatus
  ) extends VTerm //, QualifiedNameOwner(CellQn)

  /**
   * Internal only, created by [[CTerm.AllocOp]]
   */
  case Cell(heapKey: HeapKey, index: Nat)

object VTerm:
  def LevelLiteral(n: Nat): Level = Level(n, ListMap())

  def LevelSuc(t: VTerm): Level = t match
    case Level(literal, maxOperands) => Level(
      literal + 1,
      maxOperands.map { (r, o) => (r, o + 1) }
    )
    case r: Var => Level(1, ListMap((r, 1)))
    case _ => throw IllegalArgumentException("type error")

  def LevelMax(t1: VTerm, t2: VTerm): Level = t1 match
    case Level(literal1, maxOperands1) => t2 match
      case Level(literal2, maxOperands2) => Level(
        math.max(literal1, literal2),
        ListMap.from(
          (maxOperands1.toSeq ++ maxOperands2.toSeq)
            .groupBy(_._1)
            .map { (k, vs) => (k, vs.map(_._2).max) }
        )
      )
      case r: Var => Level(literal1, maxOperands1.updated(r, 0))
      case _ => throw IllegalArgumentException("type error")
    case r1: Var => t2 match
      case Level(literal2, maxOperands2) => Level(literal2, maxOperands2.updated(r1, 0))
      case r2: Var => Level(0, ListMap((r1, 0), (r2, 0)))
      case _ => throw IllegalArgumentException("type error")
    case _ => throw IllegalArgumentException("type error")

  def Total = EffectsLiteral(ListSet.empty)

  def EffectsLiteral(effects: ListSet[Eff]): Effects = Effects(effects, ListSet.empty)

  def EffectsUnion(effects1: VTerm, effects2: VTerm): Effects = effects1 match
    case Effects(literal1, unionOperands1) => effects2 match
      case Effects(literal2, unionOperands2) => Effects(
        literal1 ++ literal2,
        unionOperands1 ++ unionOperands2
      )
      case r: Var => Effects(literal1, unionOperands1 + r)
      case _ => throw IllegalArgumentException("type error")
    case r1: Var => effects2 match
      case Effects(literal2, unionOperands2) => Effects(literal2, unionOperands2 + r1)
      case r2: Var => Effects(ListSet(), ListSet(r1, r2))
      case _ => throw IllegalArgumentException("type error")
    case _ => throw IllegalArgumentException("type error")

  def vars(firstIndex: Nat, lastIndex: Nat = 0) : List[VTerm] = firstIndex.to(lastIndex, -1).map(Var(_)).toList


sealed trait IType:
  def effects: VTerm

enum CTerm:
  /**
   * Used in stack machine to represent the computations above the computation term containing
   * this. For example, `f a b` converted to the stack machine becomes
   *  - f
   *  - Application(Hole, a)
   *  - Application(Hole, b)
   */
  case Hole

  /** archon.builtin.CType */
  case CType(ul: ULevel, upperBound: CTerm, effects: VTerm = VTerm.Total) extends CTerm, IType
  case CTop(ul: ULevel, effects: VTerm = VTerm.Total) extends CTerm, IType

  case Def(qn: QualifiedName)

  case Force(v: VTerm)

  /** archon.builtin.F */
  case F(vTy: VTerm, effects: VTerm = VTerm.Total) extends CTerm, IType
  case Return(v: VTerm)
  // Note that we do not have DLet like [0]. Instead we use inductive type and thunking to simulate
  // the existential computation type Σx:A.C̲ in eMLTT [1]. From practical purpose it seems OK,
  // especially after graded modality is added to support linear usage of computations when needed.
  case Let(t: CTerm, /* binding offset = 1 */ ctx: CTerm)(val boundName: Name = gn"_")

  /** archon.builtin.Function */
  case FunctionType(
    binding: Binding[VTerm], // effects that needed for getting the function of this type. The effects caused
    // by function application is tracked by the `bodyTy`.
    bodyTy: CTerm, /* binding offset = 1 */
    effects: VTerm = VTerm.Total
  ) extends CTerm, IType
  case Application(fun: CTerm, arg: VTerm)

  case RecordType(
    qn: QualifiedName,
    args: Arguments = Nil,
    effects: VTerm = VTerm.Total
  ) extends CTerm, IType
  case Projection(rec: CTerm, name: Name)

  case OperatorCall(eff: Eff, name: Name, args: Arguments = Nil)

  /**
   * Internal only. This is only created by reduction.
   *
   * A continuation behaves like a (linear) function, it has type `U inputBinding -> outputType`, where
   * `inputBinding` is the type of the hole at the tip of the continuation seq and `outputType` is the
   * type of the bottom continuation stack.
   *
   * @param continuation stack containing the delimited continuation from the tip (right below
   *                     operator call) to the corresponding handler, inclusively. Note that the
   *                     first term is at the bottom of the stack and the last term is the tip of
   *                     the stack.
   */
  case Continuation(capturedStack: Seq[CTerm])

  case Handler(
    eff: Eff,

    otherEffects: VTerm,

    /**
     * This is the output value type. The computation type of this handler is `F(outputType, otherEffects)`.
     */
    outputType: VTerm,

    /**
     * The transformer that transforms a var at DeBruijn index 0 of type `inputBinding.ty` to `outputType`.
     * for cases where `outputType` equals `F(someEffects, inputBinding.ty)`, a sensible default value
     * is simply `return (var 0)`
     */
    /* binding + 1 */ transform: CTerm,

    /**
     * All handler implementations declared by the effect. Each handler is essentially a function
     * body that takes the following arguments
     *  - all declared parameters
     *  - a continuation parameter of type `declared operator output type -> outputType` and outputs `outputType`
     */
    handlers: Map[Name, /* binding offset = paramTys + 1 (for resume) */ CTerm],
    input: CTerm,
  )

  case AllocOp(heap: VTerm, ty: VTerm)
  case SetOp(cell: VTerm, value: VTerm)
  case GetOp(cell: VTerm)
  case HeapHandler(
    otherEffects: VTerm,

    /**
     * Newly created heap handler should always set this to `None`. This key is instantiated during reduction to a fresh
     * value.
     */
    key: Option[HeapKey],
    heapContent: IndexedSeq[Option[VTerm]],

    /**
     * Note that the logic here should not expose the heap variable (i.e. `var 0`) through
     * existential types like (t: Type, x: t) where
     * `t` can be `HeapType`. A syntax-based check is used to ensure this never happens. For cases where such
     * flexibility is needed, one should use `GlobalHeapKey` instead.
     */
    /* binding + 1 */ input: CTerm,
  )

// TODO: support array operations on heap
// TODO: consider adding builtin set (aka map pure keys) with decidable equality because we do not
//  support quotient type and set semantic is very common in software engineering.

def getFreeVars(tele: Telescope)
  (using bar: Nat)
  (using Σ: Signature): ( /* positive */ Set[Nat], /* negative */ Set[Nat]) = tele match
  case Nil => (Set(), Set())
  case binding :: rest => getFreeVars(binding.ty) | getFreeVars(rest)(using bar + 1) - 1

def getFreeVars(tm: VTerm)
  (using bar: Nat)
  (using Σ: Signature): ( /* positive */ Set[Nat], /* negative */ Set[Nat]) =
  import VTerm.*
  tm match
    case Type(ul, upperBound) => getFreeVars(ul) | getFreeVars(upperBound)
    case Top(ul) => getFreeVars(ul)
    case Pure(ul) => getFreeVars(ul)
    case Var(index) => (if index < bar then Set() else Set(index), Set())
    case Collapse(cTm) => getFreeVars(cTm)
    case U(cty) => getFreeVars(cty)
    case Thunk(c) => getFreeVars(c)
    case DataType(qn, args) =>
      val data = Σ.getData(qn)
      data.tParamTys.zip(args).map { case ((_, variance), arg) => variance match
        case Variance.COVARIANT => getFreeVars(arg)
        case Variance.CONTRAVARIANT => swap(getFreeVars(arg))
        case Variance.INVARIANT => mix(getFreeVars(arg))
      }.reduceOption(_ | _).getOrElse((Set.empty, Set.empty))
    case Con(_, args) => getFreeVars(args)
    case EqualityType(ty, left, right) => getFreeVars(ty) | getFreeVars(left) | getFreeVars(right)
    case Effects(literal, unionOperands) =>
      getFreeVars(literal.flatMap { (_, args) => args }) |
        getFreeVars(unionOperands)
    case Level(_, maxOperands) =>
      maxOperands
        .map { (v, _) => getFreeVars(v) }
        .reduceOption(_ | _)
        .getOrElse((Set.empty, Set.empty))
    case CellType(heap, ty, status) => getFreeVars(heap) | mix(getFreeVars(ty))
    case Refl | EffectsType | LevelType | HeapType | _: Heap | _: Cell => (Set(), Set())

def getFreeVars(tm: CTerm)
  (using bar: Nat)
  (using Σ: Signature)
: ( /* positive */ Set[Nat], /* negative */ Set[Nat]) =
  import CTerm.*
  tm match
    case Hole => (Set(), Set())
    case CType(ul, upperBound, eff) =>
      getFreeVars(eff) | getFreeVars(ul) | getFreeVars(upperBound)
    case CTop(ul, eff) => getFreeVars(eff) | getFreeVars(ul)
    case Force(v) => getFreeVars(v)
    case F(vTy, eff) => getFreeVars(eff) | getFreeVars(vTy)
    case Return(v) => getFreeVars(v)
    case Let(t, ctx) => getFreeVars(t) |
      getFreeVars(ctx)(using bar + 1) - 1
    case FunctionType(binding, bodyTy, effects) =>
      getFreeVars(effects) |
        swap(getFreeVars(binding.ty)) |
        getFreeVars(bodyTy)(using bar + 1) - 1
    case Application(fun, arg) => getFreeVars(fun) | getFreeVars(arg)
    case RecordType(qn, args, effects) =>
      val record = Σ.getRecord(qn)
      getFreeVars(effects) |
        record.tParamTys.zip(args).map { case ((_, variance), arg) => variance match
          case Variance.COVARIANT => getFreeVars(arg)
          case Variance.CONTRAVARIANT => swap(getFreeVars(arg))
          case Variance.INVARIANT => mix(getFreeVars(arg))
        }.reduceOption(_ | _)
          .getOrElse((Set.empty, Set.empty))
    case Projection(rec, _) => getFreeVars(rec)
    case OperatorCall(eff, _, args) => getFreeVars(eff) | getFreeVars(args)
    case Handler(eff@(qn, _), otherEffects, outputType, transform, handlers, input) =>
      getFreeVars(eff) |
        getFreeVars(otherEffects) |
        getFreeVars(outputType) |
        getFreeVars(transform)(using bar + 1) - 1 |
        handlers.map { (name, t) =>
          val offset = Σ.getOperator(qn, name).paramTys.size + 1
          getFreeVars(t)(using bar + offset) - offset
        }.reduceOption(_ | _)
          .getOrElse((Set.empty, Set.empty)) |
        getFreeVars(input)
    case AllocOp(heap, ty) => getFreeVars(heap) | getFreeVars(ty)
    case SetOp(cell, value) => getFreeVars(cell) | getFreeVars(value)
    case GetOp(cell) => getFreeVars(cell)
    case HeapHandler(otherEffects, _, _, input) =>
      getFreeVars(otherEffects) |
        getFreeVars(input)(using bar + 1) - 1
    case _: Def | _: Continuation => (Set(), Set())

def getFreeVars(ul: ULevel)
  (using bar: Nat)
  (using Σ: Signature)
: ( /* positive */ Set[Nat], /* negative */ Set[Nat]) =
  import ULevel.*
  ul match
    case USimpleLevel(l) => getFreeVars(l)
    case UωLevel(_) => (Set(), Set())

def getFreeVars(eff: Eff)
  (using bar: Nat)
  (using Σ: Signature)
: ( /* positive */ Set[Nat], /* negative */ Set[Nat]) = eff._2.map(getFreeVars).reduceOption(_ | _)
  .getOrElse((Set.empty, Set.empty))

def getFreeVars(args: Iterable[VTerm])
  (using bar: Nat)
  (using Σ: Signature)
: ( /* positive */ Set[Nat], /* negative */ Set[Nat]) = args.map(getFreeVars)
  .reduceOption(_ | _)
  .getOrElse((Set.empty, Set.empty))

extension (freeVars1: (Set[Nat], Set[Nat]))
  def |(freeVars2: (Set[Nat], Set[Nat])): (Set[Nat], Set[Nat]) =
    (freeVars1._1 | freeVars2._1, freeVars1._2 | freeVars2._2)

  def -(offset: Nat): (Set[Nat], Set[Nat]) = (freeVars1._1.map(_ - offset), freeVars1._2.map(_ - offset))

def mix(freeVars: (Set[Nat], Set[Nat])) =
  val r = freeVars._1 | freeVars._2
  (r, r)

/* References:
 [0]  Pierre-Marie Pédrot and Nicolas Tabareau. 2019. The fire triangle: how to mix substitution,
      dependent elimination, and effects. Proc. ACM Program. Lang. 4, POPL, Article 58 (January
      2020), 28 pages. DOI:https://doi.org/10.1145/3371126
 [1]  Danel Ahman. 2017. Handling fibred algebraic effects. Proc. ACM Program. Lang. 2, POPL,
      Article 7 (January 2018), 29 pages. DOI:https://doi.org/10.1145/3158095
*/