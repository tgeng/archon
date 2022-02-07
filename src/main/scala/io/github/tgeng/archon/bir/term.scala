package io.github.tgeng.archon.bir

import scala.collection.immutable.ListSet
import io.github.tgeng.archon.common.*

// Term hierarchy is inspired by Pédrot 2020 [0]. The difference is that our computation types are
// graded with type of effects, which then affects type checking: any computation that has side
// effects would not reduce during type checking.

case class Binding[T](ty: T)(name: String)

/**
 * Head is on the left, e.g. x: Nat :: y: Vector String x :: []
 */
type Telescope = List[Binding[VTerm]]

/**
 * Head is on the left, e.g. Z :: S Z :: []
 */
type Arguments = List[VTerm]

/**
 * Non negative int. Note that this is only a visual hint and nothing actually checks this.
 */
type Nat = Int

type HeapKey = Any
type CellKey = Any

type Effect = (QualifiedName, Arguments)

enum VTerm:
  /** archon.builtin.VUniverse */
  case VUniverse(level: VTerm)

  case LocalRef(idx: Nat)

  /** archon.builtin.U */
  case U(cty: CTerm)
  case Thunk(c: CTerm)

  case DataType(qn: QualifiedName, args: Arguments)
  case Con(name: String, args: Arguments)

  /** archon.builtin.Equality */
  case EqualityType(level: VTerm, ty: VTerm, left: VTerm, right: VTerm)
  case Refl

  /** archon.builtin.Effects */
  case EffectsType
  case EffectsLiteral(effects: ListSet[Effect])
  case EffectsUnion(effects1: VTerm, effects2: VTerm)

  /** archon.builtin.Level */
  case LevelType
  case LevelLiteral(value: Nat)
  case CompoundLevel(offset: Nat, operands: ListSet[VTerm])

  /** archon.builtin.Heap */
  case HeapType

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
  case Cell(key: CellKey)

trait CType:
  def effects: VTerm

enum CTerm:
  /** used for interpreting terms as an abstract stack machine */
  case Hole

  /** archon.builtin.CUniverse */
  case CUniverse(level: VTerm, effects: VTerm) extends CTerm, CType

  case GlobalRef(qn: QualifiedName)

  case Force(v: VTerm)

  /** archon.builtin.F */
  case F(vTerm: VTerm, effects: VTerm) extends CTerm, CType
  case Return(v: VTerm)
  case Let(t: CTerm, ctx: CTerm)
  case DLet(t: CTerm, ctx: CTerm)

  /** archon.builtin.Function */
  case FunctionType(binding: Binding[VTerm], bodyTy: CTerm, effects: VTerm) extends CTerm, CType
  case Lambda(body: CTerm)
  case Application(fun: CTerm, arg: VTerm)

  case RecordType(qn: QualifiedName, args: Arguments, effects: VTerm) extends CTerm, CType
  case Record(fields: List[CTerm])
  case Projection(rec: CTerm, name: String)

  case TypeCase(arg: VTerm, cases: Map[QualifiedName, CTerm])
  case DataCase(arg: VTerm, cases: Map[String, CTerm])
  case EqualityCase(arg: VTerm, body: CTerm)

  case Operator(eff: Effect, name: String)

  /**
   * Marker that signifies the computation that generates the effect containing the current
   * operator. This construct is only used when typing operators. For example an operator of type
   * `Nat -> OperatorEffectMarker (Nat -> F Nat)` means the effect owning this operator should
   * be triggered after applying the first argument, while
   * `Nat -> (Nat -> OperatorEffectMarker (F Nat))` means it's applied after both args are applied.
   */
  case OperatorEffectMarker(outputType: CTerm)
  case Handler(
    body: CTerm,
    eff: Effect,

    /**
     * Inner parameter of the handler, also passed in resume function
     */
    parameterType: VTerm,

    /**
     * A handler is a computation transformer. this is input computation type
     */
    inputType: CTerm,

    /**
     * This is the output type. The resulted handler has type
     * `parameterType -> U inputType -> outputType`
     */
    outputType: CTerm,

    /**
     * The transformer that transforms a ref at DeBrujin index 0 of type `U inputType` to `outputType`.
     * for cases where `inputType` equals `outputType`, a sensible default value
     * is simply `force (ref 0)`
     */
    transform: CTerm,

    /**
     * All handler implementations declared by the effect. Each handler takes all declared
     * parameters plus a last continuation parameter of type
     * `parameterType -> declared operator output type -> outputType`
     */
    handlers: Map[String, CTerm]
  )

  case Set(cell: VTerm, value: VTerm)
  case Get(cell: VTerm)
  case Alloc(heap: VTerm, ty: VTerm)
  case HeapHandler(
    key: HeapKey,
    body: CTerm,

    /**
     * A handler is a computation transformer. this is input computation type that accepts a heap
     * argument, which will be bound by this handler to the new heap created by this handler.
     */
    inputType: CTerm,

    /**
     * This is the output type. The resulted handler has type
     * `(h : HeapType) -> U (inputType h) -> outputType`. Note that we do not allow heap to be
     * leaked through `outputType` by existential types like (t: Type, x: t) where `t` can be
     * `HeapType`. A syntax-based check is used to ensure this never happens. For cases where such
     * flexibility is needed, one should use `GlobalHeap` instead.
     */
    outputType: CTerm,
  )

// TODO: support array operations on heap

/* References:
 [0]  Pierre-Marie Pédrot and Nicolas Tabareau. 2019. The fire triangle: how to mix substitution,
      dependent elimination, and effects. Proc. ACM Program. Lang. 4, POPL, Article 58 (January
      2020), 28 pages. DOI:https://doi.org/10.1145/3371126
*/