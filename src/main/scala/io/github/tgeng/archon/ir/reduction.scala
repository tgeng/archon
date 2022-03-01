package io.github.tgeng.archon.ir

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
  def reduce(t: T, useCaseTree: Boolean = false)
    (using ctx: Context)
    (using signature: Signature): Either[Error, T]

extension[T] (a: mutable.ArrayBuffer[T])
  def pop(): T = a.remove(a.length - 1)
  def push(t: T) = a.addOne(t)
  def pushAll(ts: Iterable[T]) = a.addAll(ts)


private val builtinHandlers = Seq(
  CTerm.HeapHandler(
    CTerm.Hole, // placeholder value, not important
    CTerm.Hole, // placeholder value, not important
    Some(GlobalHeapKey),
    IndexedSeq(),
    CTerm.Hole
  )
)

private final class StackMachine(
  val stack: mutable.ArrayBuffer[CTerm],
  val signature: Signature,
  val useCaseTree: Boolean
):

  stack.prependAll(builtinHandlers)

  private val heapKeyIndex = mutable.WeakHashMap[HeapKey, mutable.Stack[Nat]]()
  refreshHeapKeyIndex()

  import CTerm.*
  import VTerm.*
  import Pattern.*
  import Error.ReductionStuck

  private def updateHeapKeyIndex(heapKey: HeapKey, index: Nat) = heapKeyIndex.getOrElseUpdate(
    heapKey,
    mutable.Stack()
  ).push(index)

  private def refreshHeapKeyIndex(startIndex: Nat = 0): Unit =
    for case (HeapHandler(_, _, Some(heapKey), _, _), index) <- stack.view.zipWithIndex.drop(
      startIndex
    ) do
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
  def run(pc: CTerm, reduceDown: Boolean = false)(using ctx: Context): Either[Error, CTerm] =
    pc match
      case Hole => throw IllegalStateException()
      // terminal cases
      case _: CUniverse | _: F | _: Return | _: FunctionType | _: RecordType =>
        if stack.size == builtinHandlers.length then
          Right(pc)
        else
          run(substHole(stack.pop(), pc), true)
      case Def(qn) =>
        val definition = signature.getDef(qn)
        if useCaseTree then
          val caseTree = definition.caseTree
          //      case TypeCase(arg, cases, default) => arg match
          //        case _: Var => Left(ReductionStuck(reconstructTermFromStack(pc)))
          //        case q: QualifiedNameOwner if cases.contains(q.qualifiedName) =>
          //          val (count, body) = cases(q.qualifiedName)
          //          q match
          //            case VUniverse(level) =>
          //              assert(count == 1)
          //              run(body.substLowers(arg, level))
          //            case DataType(qn, args) =>
          //              assert(count == args.length)
          //              run(body.substLowers(arg +: args: _*))
          //            case EqualityType(level, ty, left, right) =>
          //              assert(count == 4)
          //              run(body.substLowers(arg, level, ty, left, right))
          //            case EffectsType | LevelType | HeapType =>
          //              assert(count == 1)
          //              run(body.substLowers(arg))
          //        case _ => run(default.substLowers(arg))
          //      case DataCase(arg, cases) => arg match
          //        case _: Var => Left(ReductionStuck(reconstructTermFromStack(pc)))
          //        case Con(name, args) if cases.contains(name) =>
          //          val (count, body) = cases(name)
          //          assert(count == args.length)
          //          run(body.substLowers(arg +: args: _*))
          //        case _ => throw IllegalArgumentException("type error")
          //      case EqualityCase(arg, body) =>
          //        arg match
          //          case Refl => run(body.substLowers(Refl))
          //          case _: Var => Left(ReductionStuck(reconstructTermFromStack(pc)))
          //          case _ => throw IllegalArgumentException("type error")
          ??? // TODO: implement reduction with case tree
        else
          definition.clauses.first {
            case CheckedClause(bindings, lhs, rhs, ty) =>
              val mapping = mutable.Map[Nat, VTerm]()
              matchPattern(
                lhs.zip(
                  stack.reverseIterator.map {
                    case Application(_, arg) => Elimination.Value(arg)
                    case Projection(_, name) => Elimination.Proj(name)
                    case _ => throw IllegalArgumentException("type error")
                  }
                ), mapping, MatchingStatus.Matched
              ) match
                case MatchingStatus.Matched =>
                  stack.dropRightInPlace(lhs.length)
                  Some(Right(rhs.subst(mapping.get)))
                case MatchingStatus.Stuck => Some(Left(ReductionStuck(reconstructTermFromStack(pc))))
                case MatchingStatus.Mismatch => None
          } match
            case Some(Right(t)) => run(t)
            case Some(error) => error
            case None => throw IllegalArgumentException(s"leaky pattern in $qn")
      case Force(v) => v match
        case Thunk(c) => run(c)
        case _: Var => Left(ReductionStuck(reconstructTermFromStack(pc)))
        case _ => throw IllegalArgumentException("type error")
      case Let(t, ctx) =>
        t match
          case Return(v) => run(ctx.substLowers(v))
          case _ if reduceDown => throw IllegalArgumentException("type error")
          case _ =>
            stack.push(pc)
            run(t)
      case DLet(t, ctx) =>
        t match
          case Return(v) => run(ctx.substLowers(v))
          case _ if reduceDown => throw IllegalArgumentException("type error")
          case _ =>
            stack.push(pc)
            run(t)
      case Application(fun, arg) =>
        fun match
          case _ if reduceDown => throw IllegalArgumentException("type error")
          case _ =>
            stack.push(pc)
            run(fun)
      case Projection(rec, name) =>
        rec match
          case _ if reduceDown => throw IllegalArgumentException("type error")
          case _ =>
            stack.push(pc)
            run(rec)
      case OperatorCall(eff, name, args) =>
        val cterms = mutable.ArrayBuffer[CTerm]()
        var nextHole: CTerm | Null = null
        while (nextHole == null) {
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
              val capturedStack = Handler(
                hEff,
                inputType,
                outputType,
                transform,
                handlers,
                Hole
              ) +: cterms.reverseIterator.toSeq

              val resume = Thunk(Continuation(capturedStack))
              nextHole = handlerBody.substLowers(args :+ resume: _*)
            case _ if stack.isEmpty => throw IllegalArgumentException("type error")
            // remove unnecessary computations with Hole so substitution and raise on the stack becomes more efficient
            case HeapHandler(_, _, Some(heapKey), _, _) =>
              heapKeyIndex(heapKey).pop()
              cterms.addOne(substHole(c, Hole))
            case _ =>
              cterms.addOne(substHole(c, Hole))
        }
        run(nextHole.!!)
      case Continuation(capturedStack) =>
        stack.pop() match
          case Application(_, arg) =>
            val currentStackHeight = stack.length
            stack.pushAll(capturedStack)
            refreshHeapKeyIndex(currentStackHeight)
            run(Force(arg))
          case _ => throw IllegalArgumentException("type error")
      case Handler(eff, inputType, outputType, transform, handlers, input) =>
        if reduceDown then
          run(transform.substLowers(Thunk(input)))
        else
          stack.push(pc)
          run(input)
      case Alloc(heap, ty) =>
        heap match
          case _: Var => Left(ReductionStuck(reconstructTermFromStack(pc)))
          case Heap(heapKey) =>
            val heapHandlerIndex = heapKeyIndex(heapKey).top
            stack(heapHandlerIndex) match
              case HeapHandler(inputType, outputType, key, heapContent, input) =>
                val cell = new Cell(heapKey, heapContent.size, ty)
                stack(heapHandlerIndex) = HeapHandler(
                  inputType,
                  outputType,
                  key,
                  heapContent :+ None,
                  input
                )
                run(substHole(stack.pop(), Return(cell)))
              case _ => throw IllegalStateException("corrupted heap key index")
          case _ => throw IllegalArgumentException("type error")
      case Set(cell, value) =>
        cell match
          case _: Var => Left(ReductionStuck(reconstructTermFromStack(pc)))
          case Cell(heapKey, index, _) =>
            val heapHandlerIndex = heapKeyIndex(heapKey).top
            stack(heapHandlerIndex) match
              case HeapHandler(inputType, outputType, key, heapContent, input) =>
                stack(heapHandlerIndex) = HeapHandler(
                  inputType,
                  outputType,
                  key,
                  heapContent.updated(index, Some(value)),
                  input
                )
                run(substHole(stack.pop(), Return(Builtins.Unit)))
              case _ => throw IllegalStateException("corrupted heap key index")
          case _ => throw IllegalArgumentException("type error")
      case Get(cell) =>
        cell match
          case _: Var => Left(ReductionStuck(reconstructTermFromStack(pc)))
          case Cell(heapKey, index, _) =>
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
          run(input.substLowers(Heap(key)))

  private enum Elimination:
    case Value(v: VTerm)
    case Proj(n: Name)

  private enum MatchingStatus:
    case Matched, Stuck, Mismatch

  @tailrec
  private def matchPattern(
    elims: List[(Pattern, Elimination)],
    mapping: mutable.Map[Nat, VTerm],
    matchingStatus: MatchingStatus
  ): MatchingStatus =
    import Elimination.*
    import Builtins.*
    elims match
      case Nil => matchingStatus
      case elim :: rest =>
        var status: MatchingStatus = matchingStatus
        var elims = rest
        elim match
          case (PRef(idx), Value(v)) => mapping(idx) = v
          case (PRefl, Value(Refl)) |
               (PValueType(EffectsQn, Nil), Value(EffectsType)) |
               (PValueType(LevelQn, Nil), Value(LevelType)) |
               (PValueType(HeapQn, Nil), Value(HeapType)) |
               (PForced(_), Value(_)) =>
          case (PValueType(VUniverseQn, p :: Nil), Value(VUniverse(l))) =>
            elims = (p, Value(l)) :: elims
          case (PValueType(CellQn, heapP :: tyP :: Nil), Value(CellType(heap, ty))) =>
            elims = (heapP, Value(heap)) :: (tyP, Value(ty)) :: elims
          case (PValueType(EqualityQn, levelP :: tyP :: leftP :: rightP :: Nil), Value(
          EqualityType(
          level,
          ty,
          left,
          right
          )
          )) =>
            elims = (levelP, Value(level)) ::
              (tyP, Value(ty)) ::
              (leftP, Value(left)) ::
              (rightP, Value(right)) ::
              elims
          case (PValueType(pQn, pArgs), Value(DataType(qn, args))) if pQn == qn =>
            elims = pArgs.zip(args.map(Value(_))) ++ elims
          case (PForcedValueType(_, pArgs), Value(DataType(qn2, args))) =>
            elims = pArgs.zip(args.map(Value(_))) ++ elims
          case (PConstructor(pName, pArgs), Value(Con(name, args))) if pName == name =>
            elims = pArgs.zip(args.map(Value(_))) ++ elims
          case (PForcedValueType(pName, pArgs), Value(Con(name, args))) =>
            elims = pArgs.zip(args.map(Value(_))) ++ elims
          case (PProjection(n1), Proj(n2)) if n1 == n2 =>
          case (PProjection(_), Value(_)) |
               (_, Proj(_)) |
               (PAbsurd, _) => throw IllegalArgumentException("type error")
          case (_, Value(Var(_))) => status = MatchingStatus.Stuck
          // Note that we make mismatch dominating stuck because we do not eval by case tree during
          // type checking.
          case _ => return MatchingStatus.Mismatch
        matchPattern(elims, mapping, status)

  private def substHole(ctx: CTerm, c: CTerm): CTerm = ctx match
    case Let(t, ctx) => Let(c, ctx)
    case DLet(t, ctx) => DLet(c, ctx)
    case Application(fun, arg) => Application(c, arg)
    case Projection(rec, name) => Projection(c, name)
    case Handler(eff, inputType, outputType, transform, handlers, input) =>
      Handler(eff, inputType, outputType, transform, handlers, c)
    case HeapHandler(inputType, outputType, key, heap, input) => HeapHandler(
      inputType,
      outputType,
      key,
      heap,
      c
    )
    case _ => throw IllegalArgumentException("unexpected context")

  private def reconstructTermFromStack(pc: CTerm): CTerm =
    var current = pc
    while (stack.size >= builtinHandlers.length) {
      current = substHole(stack.pop(), current)
    }
    current

given Reducible[CTerm] with

  /**
   * It's assumed that `t` is effect-free.
   */
  override def reduce(t: CTerm, useCaseTree: Boolean)
    (using ctx: Context)
    (using signature: Signature): Either[Error, CTerm] = StackMachine(
    mutable.ArrayBuffer(),
    signature,
    useCaseTree
  ).run(t)
