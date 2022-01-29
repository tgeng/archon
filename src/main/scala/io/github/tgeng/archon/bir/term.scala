package io.github.tgeng.archon.bir

import scala.collection.immutable.ListSet
import io.github.tgeng.archon.common.*

// Term hierarchy is inspired by Pédrot 2020 [0]. The difference is that our computation types are
// graded with type of effects, which then affects type checking: any computation that has side
// effects would not reduce during type checking.

/**
 * Non negative int. Note that this is only a visual hint and nothing actually checks this.
 */
type Nat = Int

/**
 * Eliminators of positive types are omitted because they are defined through pattern matching
 */
enum VTerm:
  case VUniverse(level: VTerm)

  case LocalVariable(idx: Nat)
  case GlobalVariable(qn: QualifiedName)

  case U(cty: CTerm)
  case Thunk(c: CTerm)

  case DataTypeCon(qn: QualifiedName, params: List[VTerm])
  case EqualityTypeCon(level: VTerm, ty: VTerm, left: VTerm, right: VTerm)
  case ValueCon(name: String, args: List[VTerm])

  case EffectsType
  case EffectsLiteral(effects: ListSet[(QualifiedName, List[VTerm])])
  case EffectsUnion(effects1: VTerm, effects2: VTerm)

  case LevelType
  case LevelLiteral(value: Nat)
  case CompoundLevel(offset: Nat, operands: ListSet[VTerm])

  case HeapType

  case CellType(heap: VTerm, ty: VTerm)
  case Cell(id: Any)

trait CType:
  def effects: VTerm

/**
 *  Introduction of negative types are omitted because they are defined through copattern matching
 */
enum CTerm:
  /**
   * used for interpreting terms as an abstract stack machine
   */
  case Hole

  case CUniverse(level: VTerm, effects: VTerm) extends CTerm, CType

  case F(vTerm: VTerm, effects: VTerm) extends CTerm, CType
  case Return(v: VTerm)
  case Force(v: VTerm)

  case Let(t: CTerm, ctx: CTerm)
  case DLet(t: CTerm, ctx: CTerm)

  case FunctionTypeCon(argTy: VTerm, bodyTy: CTerm, effects: VTerm) extends CTerm, CType
  case Application(fun: CTerm, arg: VTerm)

  case RecordTypeCon(qn: QualifiedName, params: List[VTerm], effects: VTerm) extends CTerm, CType
  case Projection(rec: CTerm, name: String)

  case Operator(eff: VTerm, name: String)

  /**
   * Marker that signifies the computation that generates the effect containing the current
   * operator. This construct is only used when typing operators. For example an operator of type
   * `Nat -> OperatorEffectMarker (Nat -> F Nat)` means the effect owning this operator should
   * be triggered after applying the first argument, while
   * `Nat -> (Nat -> OperatorEffectMarker (F Nat))` means it's applied after both args are applied.
   */
  case OperatorEffectMarker(outputType: CTerm)
  case Handler(
    eff: VTerm,

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
     * The transformer that transforms variable of `U inputType` to `outputType`.
     * for cases where `inputType` equals `outputType`, a sensible default value
     * is simply `force (var 0)`
     */
    transform: CTerm,

    /**
     * All handler implementations declared by the effect. Each handler takes all declared
     * parameters plus a last continuation parameter of type
     * `parameterType -> declared operator output type -> outputType`
     */
    handlers: List[CTerm])

  case Set(cell: VTerm, value: VTerm)
  case Get(cell: VTerm)
  case Alloc(heap: VTerm, ty: VTerm)
  case HeapHandler(
    /**
     * A handler is a computation transformer. this is input computation type that accepts a heap
     * argument, which will be bound by this handler to the new heap created by this handler.
     */
    inputType: CTerm,

    /**
     * This is the output type. The resulted handler has type
     * `(h : HeapType) -> U (inputType h) -> outputType`. Note that we allow heap to be leaked
     * through `outputType` by existential types like (t: Type, x: t) where `t` can be `HeapType`.
     * This is OK because there is nothing can be done with such heap variables: set, get, or alloc
     * with such heap variables would create an unhandleable heap effect and hence fail type
     * checking.
     */
    outputType: CTerm,
  )

  // TODO: support array operations on heap

/* References:
 [0]  Pierre-Marie Pédrot and Nicolas Tabareau. 2019. The fire triangle: how to mix substitution,
      dependent elimination, and effects. Proc. ACM Program. Lang. 4, POPL, Article 58 (January
      2020), 28 pages. DOI:https://doi.org/10.1145/3371126
*/