package io.github.tgeng.archon.ir

import io.github.tgeng.archon.common.*

import scala.annotation.tailrec
import scala.collection.immutable.ListSet
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
    VTerm.Total, // placeholder value, not important
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
  import CoPattern.*

  private def updateHeapKeyIndex(heapKey: HeapKey, index: Nat) = heapKeyIndex.getOrElseUpdate(
    heapKey,
    mutable.Stack()
  ).push(index)

  private def refreshHeapKeyIndex(startIndex: Nat = 0): Unit =
    for case (HeapHandler(_, Some(heapKey), _, _), index) <- stack.view.zipWithIndex.drop(
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
  def run(pc: CTerm, reduceDown: Boolean = false)(using ctx: Context)(using Σ: Signature): Either[Error, CTerm] =
    pc match
      case Hole => throw IllegalStateException()
      // terminal cases
      case _: CType | _: F | _: Return | _: FunctionType | _: RecordType | _: CTop =>
        if stack.size == builtinHandlers.length then
          Right(pc)
        else
          run(substHole(stack.pop(), pc), true)
      case Def(qn) =>
        if useCaseTree then
          //      case TypeCase(arg, cases, default) => arg match
          //        case _: Var => Left(ReductionStuck(reconstructTermFromStack(pc)))
          //        case q: QualifiedNameOwner if cases.contains(q.qualifiedName) =>
          //          val (count, body) = cases(q.qualifiedName)
          //          q match
          //            case VType(level) =>
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
          Σ.getClauses(qn).first {
            case CheckedClause(bindings, lhs, rhs, ty) =>
              val mapping = mutable.Map[Nat, VTerm]()
              matchPattern(
                lhs.zip(
                  stack.reverseIterator.map {
                    case Application(_, arg) => Elimination.ETerm(arg)
                    case Projection(_, name) => Elimination.EProj(name)
                    case _ => throw IllegalArgumentException("type error")
                  }
                ), mapping, MatchingStatus.Matched
              ) match
                case MatchingStatus.Matched =>
                  stack.dropRightInPlace(lhs.length)
                  Some(Right(rhs.subst(mapping.get)))
                case MatchingStatus.Stuck => Some(Right(reconstructTermFromStack(pc)))
                case MatchingStatus.Mismatch => None
          } match
            case Some(Right(t)) => run(t)
            case None => throw IllegalArgumentException(s"leaky pattern in $qn")
      case Force(v) => v match
        case Thunk(c) => run(c)
        case _: Var => Right(reconstructTermFromStack(pc))
        case _ => throw IllegalArgumentException("type error")
      case Let(t, ctx) =>
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
            otherEffects,
            outputType,
            transform,
            handlers,
            input
            ) if eff == hEff =>
              val (count, handlerBody) = handlers(name)
              val capturedStack = Handler(
                hEff,
                otherEffects,
                outputType,
                transform,
                handlers,
                Hole
              ) +: cterms.reverseIterator.toSeq

              val resume = Thunk(Continuation(capturedStack))
              nextHole = handlerBody.substLowers(args :+ resume: _*)
            case _ if stack.isEmpty => throw IllegalArgumentException("type error")
            // remove unnecessary computations with Hole so substitution and raise on the stack becomes more efficient
            case HeapHandler(_, Some(heapKey), _, _) =>
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
      case Handler(eff, otherEffects, outputType, transform, handlers, input) =>
        if reduceDown then
          run(transform.substLowers(Thunk(input)))
        else
          stack.push(pc)
          run(input)
      case AllocOp(heap, ty) =>
        heap match
          case _: Var => Right(reconstructTermFromStack(pc))
          case Heap(heapKey) =>
            val heapHandlerIndex = heapKeyIndex(heapKey).top
            stack(heapHandlerIndex) match
              case HeapHandler(otherEffects, key, heapContent, input) =>
                val cell = new Cell(heapKey, heapContent.size)
                stack(heapHandlerIndex) = HeapHandler(
                  otherEffects,
                  key,
                  heapContent :+ None,
                  input
                )
                run(substHole(stack.pop(), Return(cell)))
              case _ => throw IllegalStateException("corrupted heap key index")
          case _ => throw IllegalArgumentException("type error")
      case SetOp(cell, value) =>
        cell match
          case _: Var => Right(reconstructTermFromStack(pc))
          case Cell(heapKey, index) =>
            val heapHandlerIndex = heapKeyIndex(heapKey).top
            stack(heapHandlerIndex) match
              case HeapHandler(otherEffects, key, heapContent, input) =>
                stack(heapHandlerIndex) = HeapHandler(
                  otherEffects,
                  key,
                  heapContent.updated(index, Some(value)),
                  input
                )
                run(substHole(stack.pop(), Return(new Cell(heapKey, index))))
              case _ => throw IllegalStateException("corrupted heap key index")
          case _ => throw IllegalArgumentException("type error")
      case GetOp(cell) =>
        cell match
          case _: Var => Right(reconstructTermFromStack(pc))
          case Cell(heapKey, index) =>
            val heapHandlerIndex = heapKeyIndex(heapKey).top
            stack(heapHandlerIndex) match
              case HeapHandler(_, _, heapContent, _) =>
                heapContent(index) match
                  case None => Left(Error.UninitializedCell(reconstructTermFromStack(pc)))
                  case Some(value) => run(substHole(stack.pop(), Return(value)))
              case _ => throw IllegalStateException("corrupted heap key index")
          case _ => throw IllegalArgumentException("type error")
      case HeapHandler(otherEffects, currentKey, heapContent, input) =>
        if reduceDown then
          assert(currentKey.nonEmpty)
          heapKeyIndex(currentKey.get).pop()
          run(input)
        else
          assert(currentKey.isEmpty) // this heap handler should be fresh if evaluating upwards
          val key = new HeapKey
          updateHeapKeyIndex(key, stack.length)
          stack.push(HeapHandler(otherEffects, Some(key), heapContent, input))
          run(input.substLowers(Heap(key)))

  private enum MatchingStatus:
    case Matched, Stuck, Mismatch

  @tailrec
  private def matchPattern(
    elims: List[(CoPattern, Elimination)],
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
          case (CPattern(PVar(idx)), ETerm(v)) => mapping(idx) = v
          case (CPattern(PRefl), ETerm(Refl)) |
               (CPattern(PDataType(EffectsQn, Nil)), ETerm(EffectsType)) |
               (CPattern(PDataType(LevelQn, Nil)), ETerm(LevelType)) |
               (CPattern(PDataType(HeapQn, Nil)), ETerm(HeapType)) |
               (CPattern(PForced(_)), ETerm(_)) =>
          case (CPattern(PDataType(VTypeQn, p :: Nil)), ETerm(VType(l, upperBound))) =>
            l match
              case ULevel.USimpleLevel(l) => elims = (CPattern(p), ETerm(l)) :: elims
              case ULevel.UωLevel(_) => throw IllegalArgumentException("type error")
          case (CPattern(PDataType(CellQn, heapP :: tyP :: Nil)), ETerm(CellType(heap, ty, status))) =>
            elims = (CPattern(heapP), ETerm(heap)) :: (CPattern(tyP), ETerm(ty)) :: elims
          case (CPattern(PDataType(EqualityQn, levelP :: tyP :: leftP :: rightP :: Nil)),
          ETerm(EqualityType(ty, left, right))) =>
            elims = (CPattern(tyP), ETerm(ty)) ::
              (CPattern(leftP), ETerm(left)) ::
              (CPattern(rightP), ETerm(right)) ::
              elims
          case (CPattern(PDataType(pQn, pArgs)), ETerm(DataType(qn, args))) if pQn == qn =>
            elims = pArgs.map(CPattern.apply).zip(args.map(ETerm(_))) ++ elims
          case (CPattern(PForcedDataType(_, pArgs)), ETerm(DataType(qn2, args))) =>
            elims = pArgs.map(CPattern.apply).zip(args.map(ETerm(_))) ++ elims
          case (CPattern(PConstructor(pName, pArgs)), ETerm(Con(name, args))) if pName == name =>
            elims = pArgs.map(CPattern.apply).zip(args.map(ETerm(_))) ++ elims
          case (CPattern(PForcedDataType(pName, pArgs)), ETerm(Con(name, args))) =>
            elims = pArgs.map(CPattern.apply).zip(args.map(ETerm(_))) ++ elims
          case (CProjection(n1), EProj(n2)) if n1 == n2 =>
          case (CProjection(_), ETerm(_)) |
               (_, EProj(_)) |
               (CPattern(PAbsurd), _) => throw IllegalArgumentException("type error")
          case (_, ETerm(Var(_))) => status = MatchingStatus.Stuck
          // Note that we make mismatch dominating stuck because we do not eval by case tree during
          // type checking.
          case _ => return MatchingStatus.Mismatch
        matchPattern(elims, mapping, status)

  private def substHole(ctx: CTerm, c: CTerm): CTerm = ctx match
    case Let(t, ctx) => Let(c, ctx)
    case Application(fun, arg) => Application(c, arg)
    case Projection(rec, name) => Projection(c, name)
    case Handler(eff, otherEffects, outputType, transform, handlers, input) =>
      Handler(eff, otherEffects, outputType, transform, handlers, c)
    case HeapHandler(otherEffects, key, heap, input) => HeapHandler(otherEffects, key, heap, c)
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

object Reducible:
  def reduce(t: CTerm, useCaseTree: Boolean = false)
    (using ctx: Context)
    (using signature: Signature) = summon[Reducible[CTerm]].reduce(t, useCaseTree)