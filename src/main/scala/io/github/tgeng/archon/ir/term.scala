package io.github.tgeng.archon.ir

import scala.collection.immutable.{ListMap, ListSet}
import io.github.tgeng.archon.common.*
import QualifiedName.*

// Term hierarchy is inspired by Pédrot 2020 [0]. The difference is that our computation types are
// graded with type of effects, which then affects type checking: any computation that has side
// effects would not reduce during type checking.

case class Binding[T](ty: T)(name: Name):
  def map[S](f: T => S): Binding[S] = Binding(f(ty))(name)

/**
 * Head is on the left, e.g. Z :: S Z :: []
 */
type Arguments = List[VTerm]

/**
 * Non negative int. Note that this is only a visual hint and nothing actually checks this.
 */
type Nat = Int

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
  extension(u: ULevel)
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

enum CellStatus extends Comparable[CellStatus]:
  case Initialized, Uninitialized

  override def compareTo(that: CellStatus): Int =
    if this == that then 0
    else if this == CellStatus.Initialized then -1
    else 1

enum VTerm:
  case VUniverse(ul: ULevel, upperBound: VTerm) extends VTerm, QualifiedNameOwner(VUniverseQn)
  case VTop(ul: ULevel) extends VTerm, QualifiedNameOwner(VTopQn)

  /**
   * Top type of pure value types.
   */
  case Pure(ul: ULevel) extends VTerm, QualifiedNameOwner(PureQn)

  case Var(index: Nat)

  /** archon.builtin.U */
  case U(cty: CTerm)
  case Thunk(c: CTerm)

  case DataType(qn: QualifiedName, args: Arguments = Nil) extends VTerm, QualifiedNameOwner(qn)
  case Con(name: Name, args: Arguments = Nil)

  case EqualityType(
    level: VTerm,
    ty: VTerm,
    left: VTerm,
    right: VTerm
  ) extends VTerm, QualifiedNameOwner(EqualityQn)
  case Refl

  case EffectsType extends VTerm, QualifiedNameOwner(EffectsQn)
  case Effects(literal: ListSet[Eff], unionOperands: ListSet[VTerm.Var])

  case LevelType extends VTerm, QualifiedNameOwner(LevelQn)
  case Level(literal: Nat, maxOperands: ListMap[VTerm.Var, /* offset */ Nat])

  /** archon.builtin.Heap */
  case HeapType extends VTerm, QualifiedNameOwner(HeapQn)

  /**
   * Internal only, created by [[CTerm.HeapHandler]]
   */
  case Heap(key: HeapKey)

  /** archon.builtin.Cell */
  case CellType(heap: VTerm, ty: VTerm, status: CellStatus) extends VTerm, QualifiedNameOwner(CellQn)

  /**
   * Internal only, created by [[CTerm.Alloc]]
   */
  case Cell(heapKey: HeapKey, index: Nat)

object VTerm:
  def LevelLiteral(n: Nat): Level = new Level(n, ListMap())

  def LevelSuc(t: VTerm): Level = t match
    case Level(literal, maxOperands) => new Level(
      literal + 1,
      maxOperands.map { (r, o) => (r, o + 1) }
    )
    case r: Var => new Level(1, ListMap((r, 1)))
    case _ => throw IllegalArgumentException("type error")

  def LevelMax(t1: VTerm, t2: VTerm): Level = t1 match
    case Level(literal1, maxOperands1) => t2 match
      case Level(literal2, maxOperands2) => new Level(
        math.max(literal1, literal2),
        ListMap.from(
          (maxOperands1.toSeq ++ maxOperands2.toSeq)
            .groupBy(_._1)
            .map { (k, vs) => (k, vs.map(_._2).max) }
        )
      )
      case r: Var => new Level(literal1, maxOperands1.updated(r, 0))
      case _ => throw IllegalArgumentException("type error")
    case r1: Var => t2 match
      case Level(literal2, maxOperands2) => new Level(literal2, maxOperands2.updated(r1, 0))
      case r2: Var => new Level(0, ListMap((r1, 0), (r2, 0)))
      case _ => throw IllegalArgumentException("type error")
    case _ => throw IllegalArgumentException("type error")

  def Total = EffectsLiteral(ListSet.empty)
  def EffectsLiteral(effects: ListSet[Eff]): Effects = Effects(effects, ListSet.empty)
  def EffectsUnion(effects1: VTerm, effects2: VTerm): Effects = effects1 match
    case Effects(literal1, unionOperands1) => effects2 match
      case Effects(literal2, unionOperands2) => new Effects(literal1 ++ literal2, unionOperands1 ++ unionOperands2)
      case r: Var => new Effects(literal1, unionOperands1 + r)
      case _ => throw IllegalArgumentException("type error")
    case r1: Var => effects2 match
      case Effects(literal2, unionOperands2) => new Effects(literal2, unionOperands2 + r1)
      case r2: Var => new Effects(ListSet(), ListSet(r1, r2))
      case _ => throw IllegalArgumentException("type error")
    case _ => throw IllegalArgumentException("type error")


sealed trait CType:
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

  /** archon.builtin.CUniverse */
  case CUniverse(effects: VTerm, ul: ULevel, upperBound: CTerm) extends CTerm, CType
  case CTop(effects: VTerm, ul: ULevel) extends CTerm, CType

  case Def(qn: QualifiedName)

  case Force(v: VTerm)

  /** archon.builtin.F */
  case F(effects: VTerm, vTy: VTerm) extends CTerm, CType
  case Return(v: VTerm)
  // Note that we do not have DLet like [0]. Instead we use inductive type and thunking to simulate
  // the existential computation type Σx:A.C̲ in eMLTT [1]. From practical purpose it seems OK,
  // especially after graded modality is added to support linear usage of computations when needed.
  case Let(t: CTerm, effects: VTerm, binding: Binding[VTerm], /* binding + 1 */ ctx: CTerm)

  /** archon.builtin.Function */
  case FunctionType(
    effects: VTerm, // effects that needed for getting the function of this type. The effects caused
                    // by function application is tracked by the `bodyTy`.
    binding: Binding[VTerm],
    /* binding + 1 */ bodyTy: CTerm
  ) extends CTerm, CType
  case Application(fun: CTerm, arg: VTerm)

  case RecordType(effects: VTerm, qn: QualifiedName, args: Arguments = Nil) extends CTerm, CType
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

    /**
     * A handler is a computation transformer. The input value type is then `U inputBinding`. Note that the effects of
     * input should be `eff ⊎ effect of outputType`.
     */
    inputBinding: Binding[VTerm],
    otherEffects: VTerm,

    /**
     * This is the output value type. The computation type of this handler is `F(otherEffects, outputType)`.
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
    handlers: Map[Name, (Nat, /* binding + n + 1 (for resume) */ CTerm)],
    input: CTerm,
  )

  case Alloc(heap: VTerm, ty: VTerm)
  case Set(cell: VTerm, value: VTerm)
  case Get(cell: VTerm)
  case HeapHandler(
    /**
     * Similar to `inputBinidng` of [[Handler]]. But note that the type of `input` is
     * `F(heap(var 0) ⊎ otherEffects, inputBinding.ty)` where referenced terms are weakened to
     * accommodate the heap variable created by this heap handler. Note that this type must not. The
     * output type of this handler should be `F(otherEffects, inputBinding.ty)`.
     */
    inputBinding: Binding[VTerm],
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

/* References:
 [0]  Pierre-Marie Pédrot and Nicolas Tabareau. 2019. The fire triangle: how to mix substitution,
      dependent elimination, and effects. Proc. ACM Program. Lang. 4, POPL, Article 58 (January
      2020), 28 pages. DOI:https://doi.org/10.1145/3371126
 [1]  Danel Ahman. 2017. Handling fibred algebraic effects. Proc. ACM Program. Lang. 2, POPL,
      Article 7 (January 2018), 29 pages. DOI:https://doi.org/10.1145/3158095
*/