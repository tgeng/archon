package io.github.tgeng.archon.bir

import io.github.tgeng.archon.common.*

import scala.annotation.tailrec
import scala.collection.mutable

trait Reducible[T]:
  /**
   * @param useCaseTree reduction during type checking should not use case tree because it can get
   *                    stuck more often than evaluating by clauses in presence of local variables.
   *                    Note that we are taking a different strategy than in Agda: when evaluating
   *                    pattern match, we let mismatch dominate stuckness because we always eval by
   *                    clauses during type checking. We may even support overlapping patterns at
   *                    some point later. Eval by case tree, on the other hand, is only used to
   *                    evaluate a complete program, similar to running a compiled program.
   */
  def reduce(t: T, useCaseTree: Boolean = false)(using signature: Signature): Either[Error, T]

extension [T](a: mutable.ArrayBuffer[T])
  def pop(): T = a.remove(a.length - 1)
  def push(t: T) = a.addOne(t)
  def pushAll(ts: Iterable[T]) = a.addAll(ts)

private final class StackMachine(
  val stack: mutable.ArrayBuffer[CTerm],
  val signature: Signature,
  val useCaseTree: Boolean
):

  private val heapKeyIndex = mutable.WeakHashMap[HeapKey, mutable.Stack[Nat]]()
  refreshHeapKeyIndex()

  import CTerm.*
  import VTerm.*
  import Error.ReductionStuck

  private def updateHeapKeyIndex(heapKey: HeapKey, index: Nat) = heapKeyIndex.getOrElseUpdate(heapKey, mutable.Stack()).push(index)
  private def refreshHeapKeyIndex(startIndex: Nat = 0) : Unit =
    for case (HeapHandler(_, _, Some(heapKey), _, _), index) <- stack.view.zipWithIndex.drop(startIndex) do
      updateHeapKeyIndex(heapKey, index)

  /**
   * @param pc         "program counter"
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
      case _: CUniverse | _: F | _: Return | _: FunctionType | _: Lambda | _: RecordType | _: Record =>
        if stack.isEmpty then
          Right(pc)
        else
          run(substHole(stack.pop(), pc), true)
      case GlobalRef(qn) =>
        if useCaseTree then
          run(signature.getDef(qn).caseTree)
        else ??? // TODO: implement first clause match semantic by inspecting tip of the stack
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
              run(body.substHead(arg +: args: _*))
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
          run(body.substHead(arg +: args: _*))
        case _ => throw IllegalArgumentException("type error")
      case EqualityCase(arg, body) =>
        arg match
          case Refl => run(body.substHead(Refl))
          case _: LocalRef => Left(ReductionStuck(reconstructTermFromStack(pc)))
          case _ => throw IllegalArgumentException("type error")
      case OperatorCall(eff, name, args) =>
        val cterms = mutable.ArrayBuffer[CTerm]()
        var nextComputation: CTerm | Null = null
        while (nextComputation == null) {
          val c = stack.pop()
          c match
            case Handler(
            hEff,
            inputType,
            outputType,
            transform,
            handlers,
            input
            ) if eff == hEff =>
              val (count, handlerBody) = handlers(name)
              val continuation = Handler(
                hEff.map(_.weakened),
                inputType.weakened,
                outputType.weakened,
                transform.weakened,
                handlers.view.mapValues { case (n, c) => (n, c.weakened) }.toMap,
                Hole
              ) +: cterms.reverseIterator.map(_.weakened).toSeq

              val resume = Thunk(
                Lambda( // operation result
                  ContinuationCall(
                    continuation,
                    LocalRef(0) // reference the operation result
                  ),
                )
              )
              nextComputation = handlerBody.substHead(args :+ resume: _*)
            case _ if stack.isEmpty => throw IllegalArgumentException("type error")
            // remove unnecessary computations with Hole so substitution and raise on the stack becomes more efficient
            case HeapHandler(_, _, Some(heapKey), _, _) =>
              heapKeyIndex(heapKey).pop()
              cterms.addOne(substHole(c, Hole))
            case _ =>
              cterms.addOne(substHole(c, Hole))
        }
        run(nextComputation.!!)
      case ContinuationCall(continuation, result) =>
        val currentStackHeight = stack.length
        stack.pushAll(continuation)
        refreshHeapKeyIndex(currentStackHeight)
        run(Force(result))
      case Handler(eff, inputType, outputType, transform, handlers, input) =>
        if reduceDown then
          run(transform.substHead(Thunk(input)))
        else
          stack.push(pc)
          run(input)
      case Alloc(heap, ty) =>
        heap match
          case _ : LocalRef => Left(ReductionStuck(reconstructTermFromStack(pc)))
          case Heap(heapKey) =>
            val heapHandlerIndex = heapKeyIndex(heapKey).top
            stack(heapHandlerIndex) match
              case HeapHandler(inputType, outputType, key, heapContent, input) =>
                val cell = new Cell(heapKey, heapContent.size)
                stack(heapHandlerIndex) = HeapHandler(inputType, outputType, key, heapContent :+ None, input)
                run(substHole(stack.pop(), Return(cell)))
              case _ => throw IllegalStateException("corrupted heap key index")
          case _ => throw IllegalArgumentException("type error")
      case Set(cell, value) =>
        cell match
          case _ : LocalRef => Left(ReductionStuck(reconstructTermFromStack(pc)))
          case Cell(heapKey, index) =>
            val heapHandlerIndex = heapKeyIndex(heapKey).top
            stack(heapHandlerIndex) match
              case HeapHandler(inputType, outputType, key, heapContent, input) =>
                stack(heapHandlerIndex) = HeapHandler(inputType, outputType, key, heapContent.updated(index, Some(value)), input)
                run(substHole(stack.pop(), Return(Builtins.Unit)))
              case _ => throw IllegalStateException("corrupted heap key index")
          case _ => throw IllegalArgumentException("type error")
      case Get(cell) =>
        cell match
          case _ : LocalRef => Left(ReductionStuck(reconstructTermFromStack(pc)))
          case Cell(heapKey, index) =>
            val heapHandlerIndex = heapKeyIndex(heapKey).top
            stack(heapHandlerIndex) match
              case HeapHandler(_, _, _, heapContent, _) =>
                heapContent(index) match
                  case None => Left(Error.UninitializedCell(reconstructTermFromStack(pc)))
                  case Some(value) => run(substHole(stack.pop(), Return(value)))
              case _ => throw IllegalStateException("corrupted heap key index")
          case _ => throw IllegalArgumentException("type error")
      case HeapHandler(inputType, outputType, currentKey, heapContent, input) =>
        if reduceDown then
          assert(currentKey.nonEmpty)
          heapKeyIndex(currentKey.get).pop()
          run(input)
        else
          assert(currentKey.isEmpty) // this heap handler should be fresh if evaluating upwards
          val key = new HeapKey
          updateHeapKeyIndex(key, stack.length)
          stack.push(HeapHandler(inputType, outputType, Some(key), heapContent, input))
          run(input.substHead(Heap(key)))

  private def substHole(ctx: CTerm, c: CTerm): CTerm = ctx match
    case Let(t, ctx) => Let(c, ctx)
    case DLet(t, ctx) => DLet(c, ctx)
    case Application(fun, arg) => Application(c, arg)
    case Projection(rec, name) => Projection(c, name)
    case Handler(eff, inputType, outputType, transform, handlers, input) =>
      Handler(eff, inputType, outputType, transform, handlers, c)
    case HeapHandler(inputType, outputType, key, heap, input) => HeapHandler(inputType, outputType, key, heap, c)
    case _ => throw IllegalArgumentException("unexpected context")

  private def reconstructTermFromStack(pc: CTerm): CTerm =
    var current = pc
    while (stack.nonEmpty) {
      current = substHole(stack.pop(), current)
    }
    current

given Reducible[CTerm] with

  /**
   * It's assumed that `t` is effect-free.
   */
  override def reduce(t: CTerm, useCaseTree: Boolean)(using signature: Signature): Either[Error, CTerm] = StackMachine(
    mutable.ArrayBuffer(),
    signature,
    useCaseTree
  ).run(t)
