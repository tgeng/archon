package io.github.tgeng.archon.bir

import io.github.tgeng.archon.common.QualifiedName

import scala.annotation.tailrec
import scala.collection.mutable

trait Reducible[T]:
  def reduce(t: T, useCaseTree: Boolean = false)(using signature: Signature): Either[Error, T]

private final class StackMachine(val stack: mutable.Stack[CTerm],
                   val heap: mutable.Map[HeapKey, mutable.Map[CellKey, VTerm]],
                   val signature: Signature,
                   val useCaseTree: Boolean):
  import CTerm.*
  import VTerm.*
  import Error.ReductionStuck

  /**
   * @param pc "program counter"
   * @param reduceDown if true, logic should not try to decompose the [[pc]] and push it's components on to the stack.
   *                   This is useful so that the run logic does not spin into infinite loop if the given term has type
   *                   errors. (Ideally, input should be type-checked so this should never happen, unless there are bugs
   *                   in type checking code.)
   * @return
   */
  @tailrec
  def run(pc: CTerm, reduceDown: Boolean = false): Either[Error, CTerm] =
    pc match
      case Hole => throw IllegalArgumentException("invalid CTerm construction: Hole should only appear as a sub CTerm")
      // terminal cases
      case _: CUniverse | _: F | _: Return | _: FunctionType | _: Lambda | _: RecordType | _: Record =>
        if stack.isEmpty then
          Right(pc)
        else
          run(substHole(stack.pop(), pc), true)
      case GlobalRef(qn) => ???
      case Force(v) => v match
        case Thunk(c) => run(c)
        case _: LocalRef => Left(ReductionStuck(reconstructTermFromStack(pc)))
        case _ => throw IllegalArgumentException("type error")
      case Let(t, ctx) =>
        t match
          case Return(v) => run(ctx.substHead(v))
          case _ if reduceDown => throw IllegalArgumentException("type error")
          case _ =>
            stack.push(Let(Hole, ctx))
            run(t)
      case DLet(t, ctx) =>
        t match
          case Return(v) => run(ctx.substHead(v))
          case _ if reduceDown => throw IllegalArgumentException("type error")
          case _ =>
            stack.push(Let(Hole, ctx))
            run(t)
      case Application(fun, arg) =>
        fun match
          case Lambda(body) => run(body.substHead(arg))
          case _ if reduceDown => throw IllegalArgumentException("type error")
          case _ =>
            stack.push(Application(Hole, arg))
            run(fun)
      case Projection(rec, name) => ???
      case TypeCase(arg, cases, default) => ???
      case DataCase(arg, cases) => ???
      case EqualityCase(arg, body) =>
        arg match
          case Refl => run(body)
          case _: LocalRef => Left(ReductionStuck(reconstructTermFromStack(pc)))
          case _ => throw IllegalArgumentException("type error")
      case OperatorEffectMarker(outputType) => run(outputType)
      case Handler(eff, parameterType, inputType, outputType, transform, handlers, parameter, input) => ???
      case OperatorCall(eff, name, args) => ???
      case Set(cell, value) => ???
      case Get(cell) => ???
      case Alloc(heap, ty) => ???
      case HeapHandler(inputType, outputType, key, input) => ???

  private def substHole(ctx: CTerm, c: CTerm): CTerm = ctx match
    case Let(t, ctx) if t == Hole => Let(c, ctx)
    case DLet(t, ctx) if t == Hole => DLet(c, ctx)
    case Application(fun, arg) if fun == Hole => Application(c, arg)
    case Projection(rec, name) if rec == Hole => Projection(c, name)
    case Handler(eff, parameterType, inputType, outputType, transform, handlers, parameter, input) if input == Hole =>
      Handler(eff, parameterType, inputType, outputType, transform, handlers, parameter, c)
    case HeapHandler(inputType, outputType, key, input) if input == Hole => HeapHandler(inputType, outputType, key, c)
    case _ => throw IllegalArgumentException("unexpected context")
  private def reconstructTermFromStack(pc: CTerm): CTerm = ???

given Reducible[CTerm] with
  /**
   * It's assumed that `t` is effect-free.
   */
  override def reduce(t: CTerm, useCaseTree: Boolean)(using signature: Signature): Either[Error, CTerm] = StackMachine(
    mutable.Stack(),
    mutable.Map(),
    signature,
    useCaseTree
  ).run(t)
