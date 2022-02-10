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
      case Hole => throw IllegalStateException()
      // terminal cases
      case _: CUniverse | _: F | _: Return | _: FunctionType | _: Lambda | _: Continuation | _: RecordType | _: Record =>
        if stack.isEmpty then
          Right(pc)
        else
          run(substHole(stack.pop(), pc), true)
      case GlobalRef(qn) =>
        if useCaseTree then
          run(signature.getDef(qn).caseTree)
        else ??? // TODO: implement strict first clause match semantic by inspecting tip of the stack
      case Force(v) => v match
        case Thunk(c) => run(c)
        case _: LocalRef => Left(ReductionStuck(reconstructTermFromStack(pc)))
        case _ => throw IllegalArgumentException("type error")
      case Let(t, ctx) =>
        t match
          case Return(v) => run(ctx.substHead(v))
          case _ if reduceDown => throw IllegalArgumentException("type error")
          case _ =>
            stack.push(pc)
            run(t)
      case DLet(t, ctx) =>
        t match
          case Return(v) => run(ctx.substHead(v))
          case _ if reduceDown => throw IllegalArgumentException("type error")
          case _ =>
            stack.push(pc)
            run(t)
      case Application(fun, arg) =>
        fun match
          case Lambda(body) => run(body.substHead(arg))
          case Continuation(inputType, outputType, stack) => ??? // TODO: explode the stack here
          case _ if reduceDown => throw IllegalArgumentException("type error")
          case _ =>
            stack.push(pc)
            run(fun)
      case Projection(rec, name) =>
        rec match
          case Record(fields) if fields.contains(name) => run(fields(name))
          case _ if reduceDown => throw IllegalArgumentException("type error")
          case _ =>
            stack.push(pc)
            run(rec)
      case TypeCase(arg, cases, default) => arg match
        case _: LocalRef => Left(ReductionStuck(reconstructTermFromStack(pc)))
        case q: QualifiedNameOwner if cases.contains(q.qualifiedName) =>
          val (count, body) = cases(q.qualifiedName)
          q match
            case VUniverse(level) =>
              assert(count == 1)
              run(body.substHead(arg, level))
            case DataType(qn, args) =>
              assert(count == args.length)
              run(body.substHead(arg +: args : _*))
            case EqualityType(level, ty, left, right) =>
              assert(count == 4)
              run(body.substHead(arg, level, ty, left, right))
            case EffectsType | LevelType | HeapType =>
              assert(count == 1)
              run(body.substHead(arg))
        case _ => run(default.substHead(arg))
      case DataCase(arg, cases) => arg match
        case _: LocalRef => Left(ReductionStuck(reconstructTermFromStack(pc)))
        case Con(name, args) if cases.contains(name) =>
          val (count, body) = cases(name)
          assert(count == args.length)
          run(body.substHead(arg +: args : _*))
        case _ => throw IllegalArgumentException("type error")
      case EqualityCase(arg, body) =>
        arg match
          case Refl => run(body.substHead(Refl))
          case _: LocalRef => Left(ReductionStuck(reconstructTermFromStack(pc)))
          case _ => throw IllegalArgumentException("type error")
      case OperatorCall(eff, name, args) => ??? // TODO: construct a continuation here inside two lambdas, which bind
                                                //  1. the handler parameter
                                                //  2. the operation result
      case OperatorEffectMarker(outputType) => run(outputType)
      case Handler(eff, otherEffects, parameterType, inputType, outputType, transform, handlers, parameter, input) =>
        input match
          case Return(v) => run(transform.substHead(v))
          case _ if reduceDown => throw IllegalArgumentException("type error")
          case _ =>
            stack.push(pc)
            run(input)
      case Set(cell, value) => ???
      case Get(cell) => ???
      case Alloc(heap, ty) => ???
      case HeapHandler(otherEffects, inputType, outputType, key, input) => ???

  private def substHole(ctx: CTerm, c: CTerm): CTerm = ctx match
    case Let(t, ctx) => Let(c, ctx)
    case DLet(t, ctx) => DLet(c, ctx)
    case Application(fun, arg) => Application(c, arg)
    case Projection(rec, name) => Projection(c, name)
    case Handler(eff, otherEffects, parameterType, inputType, outputType, transform, handlers, parameter, input) =>
      Handler(eff, otherEffects, parameterType, inputType, outputType, transform, handlers, parameter, c)
    case HeapHandler(otherEffects, inputType, outputType, key, input) => HeapHandler(otherEffects, inputType, outputType, key, c)
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
