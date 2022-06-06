package com.github.tgeng.archon.core.ir

import com.github.tgeng.archon.common.*

import scala.annotation.tailrec
import scala.collection.immutable.ListSet
import scala.collection.mutable
import CTerm.*
import VTerm.*
import Pattern.*
import CoPattern.*
import com.github.tgeng.archon.core.ir.IrError.MissingDeclaration

trait Reducible[T]:
  def reduce(t: T)
    (using ctx: Context)
    (using signature: Signature)
    (using TypingContext)
  : Either[IrError, T]

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
):

  stack.prependAll(builtinHandlers)

  private val heapKeyIndex = mutable.WeakHashMap[HeapKey, mutable.Stack[Nat]]()
  refreshHeapKeyIndex()

  private def updateHeapKeyIndex(heapKey: HeapKey, index: Nat) =
    heapKeyIndex.getOrElseUpdate(heapKey, mutable.Stack()).push(index)

  private def refreshHeapKeyIndex(startIndex: Nat = 0): Unit =
    for
      case (HeapHandler(_, Some(heapKey), _, _), index) <- stack.view.zipWithIndex.drop(startIndex)
    do
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
  def run(pc: CTerm, reduceDown: Boolean = false)
    (using ctx: Context)
    (using Σ: Signature)
    (using TypingContext)
  : Either[IrError, CTerm] =
    pc match
      case Hole => throw IllegalStateException()
      // terminal cases
      case _: CType | _: F | _: Return | _: FunctionType | _: RecordType | _: CTop =>
        if stack.size == builtinHandlers.length then
          Right(pc)
        else
          run(substHole(stack.pop(), pc), true)
      case Def(qn) =>
        Σ.getClausesOption(qn) match
          // This is allowed because it could be that the body is not defined yet.
          case None => Right(reconstructTermFromStack(pc))
          case Some(clauses) => clauses.first {
            case Clause(bindings, lhs, rhs, ty) =>
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
      case Force(v) => v.normalized match
        case Left(e) => Left(e)
        case Right(Thunk(c)) => run(c)
        case Right(_: Var | _: Collapse) => Right(reconstructTermFromStack(pc))
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
          case _ => arg.normalized match
            case Left(e) => Left(e)
            case Right(v) =>
              stack.push(Application(Hole, v))
              run(fun)
      case Projection(rec, name) =>
        rec match
          case _ if reduceDown => throw IllegalArgumentException("type error")
          case _ =>
            stack.push(pc)
            run(rec)
      case OperatorCall((effQn, effArgs), name, args) =>
        Σ.getEffectOption(effQn) match
          case None => Left(MissingDeclaration(effQn))
          case Some(eff) =>
            effArgs.normalized match
              case Left(e) => Left(e)
              case Right(effArgs) =>
                args.normalized match
                  case Left(e) => Left(e)
                  case Right(args) =>
                    def areEffArgsConvertible(
                      ts1: List[VTerm],
                      ts2: List[VTerm],
                      tys: Telescope
                    ): Boolean =
                      (ts1, ts2, tys) match
                        case (Nil, Nil, Nil) => true
                        case (t1 :: ts1, t2 :: ts2, ty :: tys) =>
                          checkSubsumption(
                            t1,
                            t2,
                            Some(ty.ty)
                          )(using CheckSubsumptionMode.CONVERSION) match
                            case Right(_) => areEffArgsConvertible(ts1, ts2, tys.substLowers(t1))
                            case _ => false
                        case _ => throw IllegalArgumentException()

                    val cterms = mutable.ArrayBuffer[CTerm]()
                    var nextHole: CTerm | Null = null
                    while (nextHole == null) {
                      val c = stack.pop()
                      c match
                        case Handler(
                        hEff@(hEffQn, hEffArgs),
                        otherEffects,
                        outputType,
                        transform,
                        handlers,
                        input
                        ) if {
                          val tys = eff.tParamTys
                          effQn == hEffQn &&
                            effArgs.size == hEffArgs.size &&
                            effArgs.size == tys.size &&
                            areEffArgsConvertible(effArgs, hEffArgs, tys)
                        } =>
                          val handlerBody = handlers(name)
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
      case Handler((effQn, effArgs), otherEffects, outputType, transform, handlers, input) =>
        if reduceDown then
          run(transform.substLowers(Thunk(input)))
        else
          effArgs.normalized match
            case Left(e) => Left(e)
            case Right(effArgs) =>
              stack.push(
                Handler(
                  (effQn, effArgs),
                  otherEffects,
                  outputType,
                  transform,
                  handlers,
                  Hole
                )
              )
              run(input)
      case AllocOp(heap, ty) =>
        heap.normalized match
          case Left(e) => Left(e)
          case Right(_: Var | _: Collapse) => Right(reconstructTermFromStack(pc))
          case Right(Heap(heapKey)) =>
            val heapHandlerIndex = heapKeyIndex(heapKey).top
            stack(heapHandlerIndex) match
              case HeapHandler(otherEffects, key, heapContent, input) =>
                val cell = Cell(heapKey, heapContent.size)
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
        cell.normalized match
          case Left(e) => Left(e)
          case Right(_: Var | _: Collapse) => Right(reconstructTermFromStack(pc))
          case Right(Cell(heapKey, index)) =>
            value.normalized match
              case Left(e) => Left(e)
              case Right(value) =>
                val heapHandlerIndex = heapKeyIndex(heapKey).top
                stack(heapHandlerIndex) match
                  case HeapHandler(otherEffects, key, heapContent, input) =>
                    stack(heapHandlerIndex) = HeapHandler(
                      otherEffects,
                      key,
                      heapContent.updated(index, Some(value)),
                      input
                    )
                    run(substHole(stack.pop(), Return(Cell(heapKey, index))))
                  case _ => throw IllegalStateException("corrupted heap key index")
          case _ => throw IllegalArgumentException("type error")
      case GetOp(cell) =>
        cell.normalized match
          case Left(e) => Left(e)
          case Right(_: Var | _: Collapse) => Right(reconstructTermFromStack(pc))
          case Right(Cell(heapKey, index)) =>
            val heapHandlerIndex = heapKeyIndex(heapKey).top
            stack(heapHandlerIndex) match
              case HeapHandler(_, _, heapContent, _) =>
                heapContent(index) match
                  case None => Left(IrError.UninitializedCell(reconstructTermFromStack(pc)))
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
    elims: List[(CoPattern, Elimination[VTerm])],
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
          case (CPattern(PDataType(TypeQn, p :: Nil)), ETerm(Type(l, upperBound))) =>
            l match
              case ULevel.USimpleLevel(l) => elims = (CPattern(p), ETerm(l)) :: elims
              case ULevel.UωLevel(_) => throw IllegalArgumentException("type error")
          // TODO: matching cell type is probably not a good idea because it's unknown at what
          //  level `tyP` should be. In order to allow this, we need to make each `Cell`
          //  self-contained, just like all declared `Data`. The downside is then the need to carry
          //  a level everywhere with the cell. On the other hand, whether to allow this does not
          //  affect the expressive power because one can simulate such by declaring a wrapper
          //  data class. This same trick can be used for equality type, function type, and record
          //  type.
          // case (CPattern(PDataType(CellQn, heapP :: tyP :: Nil)), ETerm(CellType(heap, ty, status))) =>
          //   elims = (CPattern(heapP), ETerm(heap)) :: (CPattern(tyP), ETerm(ty)) :: elims

          // TODO: similarly, we don't allow matching equality type either for the same reason.
          // case (CPattern(PDataType(EqualityQn, levelP :: tyP :: leftP :: rightP :: Nil)),
          // ETerm(EqualityType(ty, left, right))) =>
          //   elims = (CPattern(tyP), ETerm(ty)) ::
          //     (CPattern(leftP), ETerm(left)) ::
          //     (CPattern(rightP), ETerm(right)) ::
          //     elims
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
    case l@Let(t, ctx) => Let(c, ctx)(l.boundName)
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

extension (v: VTerm)
  def normalized(using ctx: Context)(using Σ: Signature)(using TypingContext)
  : Either[IrError, VTerm] = v match
    case Collapse(cTm) =>
      for reduced <- Reducible.reduce(cTm)
          r <- reduced match
            case Return(v) => Right(v)
            case _ => Left(IrError.NormalizationError(cTm))
      yield r
    case _ => Right(v)

extension (vs: List[VTerm])
  def normalized(using ctx: Context)
    (using Σ: Signature)
    (using TypingContext): Either[IrError, List[VTerm]] =
    transpose(vs.map(_.normalized))

given Reducible[CTerm] with

  /**
   * It's assumed that `t` is effect-free.
   */
  override def reduce(t: CTerm)
    (using ctx: Context)
    (using signature: Signature)
    (using TypingContext)
  : Either[IrError, CTerm] = StackMachine(
    mutable.ArrayBuffer(),
    signature
  ).run(t)

object Reducible:
  def reduce(t: CTerm)
    (using Context)
    (using Signature)
    (using ctx: TypingContext)
  : Either[IrError, CTerm] = ctx.trace(
    s"reducing $t",
    r => r.toString,
    e => e.toString,
    summon[Reducible[CTerm]].reduce(t),
  )
