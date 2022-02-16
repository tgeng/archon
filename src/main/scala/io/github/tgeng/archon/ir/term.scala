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

type Effect = (QualifiedName, Arguments)

sealed trait QualifiedNameOwner(_qualifiedName: QualifiedName):
  def qualifiedName: QualifiedName = _qualifiedName

extension (eff: Effect)
  def map[S](f: VTerm => VTerm): Effect = (eff._1, eff._2.map(f))

enum VTerm:
  case VUniverse(level: VTerm) extends VTerm, QualifiedNameOwner(Builtin / "VUniverse")

  case LocalRef(idx: Nat)

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
  ) extends VTerm, QualifiedNameOwner(Builtin / "Equality")
  case Refl

  case EffectsType extends VTerm, QualifiedNameOwner(Builtin / "Effects")
  case EffectsLiteral(effects: ListSet[Effect])
  case EffectsUnion(effects1: VTerm, effects2: VTerm)

  case LevelType extends VTerm, QualifiedNameOwner(Builtin / "Level")
  case LevelLiteral(value: Nat)
  case CompoundLevel(offset: Nat, operands: ListSet[VTerm])

  /** archon.builtin.Heap */
  case HeapType extends VTerm, QualifiedNameOwner(Builtin / "Heap")

  /** Any need for leaky heap usage goes here. */
  case GlobalHeap

  /**
   * Internal only, created by [[CTerm.HeapHandler]]
   */
  case Heap(key: HeapKey)

  /** archon.builtin.Cell */
  case CellType(heap: VTerm, ty: VTerm)

  /**
   * Internal only, created by [[CTerm.Alloc]]
   */
  case Cell(heapKey: HeapKey, index: Nat)

sealed trait CType:
  def effects: VTerm

enum CTerm:
  /** Used in stack representation of computation. */
  case Hole

  /** archon.builtin.CUniverse */
  case CUniverse(effects: VTerm, level: VTerm) extends CTerm, CType

  case GlobalRef(qn: QualifiedName)

  case Force(v: VTerm)

  /** archon.builtin.F */
  case F(effects: VTerm, vTerm: VTerm) extends CTerm, CType
  case Return(v: VTerm)
  case Let(t: CTerm, ctx: CTerm)
  case DLet(t: CTerm, ctx: CTerm)

  /** archon.builtin.Function */
  case FunctionType(
    effects: VTerm,
    /* binding + 1 */ binding: Binding[VTerm],
    bodyTy: CTerm
  ) extends CTerm, CType
  case Application(fun: CTerm, arg: VTerm)

  case RecordType(effects: VTerm, qn: QualifiedName, args: Arguments = Nil) extends CTerm, CType
  case Projection(rec: CTerm, name: Name)

  case OperatorCall(eff: Effect, name: Name, args: Arguments = Nil)

  /**
   * A continuation behaves like a function, it has type `U inputType -> outputType`, where
   * `inputType` is the type of the hole at the tip of the continuation seq and `outputType` is the
   * type of the bottom continuation stack.
   *
   * @param continuation stack containing the delimited continuation from the tip (right below
   *                     operator call) to the corresponding handler, inclusively. Note that the
   *                     first term is at the bottom of the stack and the last term is the tip of
   *                     the stack.
   */
  case Continuation(capturedStack: Seq[CTerm])

  case Handler(
    eff: Effect,

    /**
     * A handler is a computation transformer. The input value type is then `U inputType`. Note that the effects of
     * input should be `eff ⊎ effect of outputType`.
     */
    inputType: CTerm,

    /**
     * This is the output type..
     */
    outputType: CTerm,

    /**
     * The transformer that transforms a ref at DeBruijn index 0 of type `U inputType` to `outputType`.
     * for cases where `inputType` equals `outputType`, a sensible default value
     * is simply `force (ref 0)`
     */
    /* binding + 1 */ transform: CTerm,

    /**
     * All handler implementations declared by the effect. Each handler is essentially a function body that takes the
     * following arguments
     *  - all declared parameters
     *  - a continuation parameter of type `parameterType -> declared operator output type -> outputType`
     *    and outputs `outputType`
     */
    handlers: Map[Name, (Nat, /* binding + n + 1 (for resume) */ CTerm)],
    input: CTerm,
  )

  case Alloc(heap: VTerm, ty: VTerm)
  case Set(cell: VTerm, value: VTerm)
  case Get(cell: VTerm)
  case HeapHandler(
    /**
     * A handler is a computation transformer. this is input type that has `ref 0` bound to a heap
     * argument, which will be bound by this handler to the new heap created by this handler. The input type
     * should have effect `{heap (ref 0)} ⊎ effect of outputType`.
     */
    /* binding + 1 */ inputType: CTerm,

    /**
     * This is the output type. The effects of the output type should be exactly `otherEffects`.
     * Note that we do not allow heap to be leaked through `outputType` by existential types like (t: Type, x: t) where
     * `t` can be `HeapType`. A syntax-based check is used to ensure this never happens. For cases where such
     * flexibility is needed, one should use `GlobalHeap` instead.
     */
    outputType: CTerm,

    /**
     * Newly created heap handler should always set this to `None`. This key is instantiated during reduction to a fresh
     * value.
     */
    key: Option[HeapKey],
    heapContent: IndexedSeq[Option[VTerm]],
    /* binding + 1 */ input: CTerm,
  )

// TODO: support array operations on heap

/* References:
 [0]  Pierre-Marie Pédrot and Nicolas Tabareau. 2019. The fire triangle: how to mix substitution,
      dependent elimination, and effects. Proc. ACM Program. Lang. 4, POPL, Article 58 (January
      2020), 28 pages. DOI:https://doi.org/10.1145/3371126
*/