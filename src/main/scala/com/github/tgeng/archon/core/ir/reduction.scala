package com.github.tgeng.archon.core.ir

import com.github.tgeng.archon.common.*
import com.github.tgeng.archon.common.DelimitPolicy.*
import com.github.tgeng.archon.common.IndentPolicy.*
import com.github.tgeng.archon.common.WrapPolicy.*
import com.github.tgeng.archon.common.eitherFilter.*
import com.github.tgeng.archon.core.common.*
import com.github.tgeng.archon.core.ir.CTerm.*
import com.github.tgeng.archon.core.ir.CoPattern.*
import com.github.tgeng.archon.core.ir.Elimination.*
import com.github.tgeng.archon.core.ir.IrError.*
import com.github.tgeng.archon.core.ir.MetaVariable.*
import com.github.tgeng.archon.core.ir.Pattern.*
import com.github.tgeng.archon.core.ir.PrettyPrinter.pprint
import com.github.tgeng.archon.core.ir.Usage.*
import com.github.tgeng.archon.core.ir.VTerm.*

import scala.annotation.tailrec
import scala.collection.immutable.SeqMap
import scala.collection.mutable

trait Reducible[T]:
  @throws(classOf[IrError])
  def reduce(t: T)(using ctx: Context)(using signature: Signature)(using TypingContext): T

extension [T](a: mutable.ArrayBuffer[T])
  def pop(): T = a.remove(a.length - 1)
  def push(t: T): a.type = a.addOne(t)
  def pushAll(ts: Iterable[T]): a.type = a.addAll(ts)

private case class ReplicationState
  (
    currentHandlerEntry: Handler,
    baseStackSize: Nat,
    continuationTerm1: CTerm,
    continuationTerm2: CTerm,
    continuationUsage: Usage,
  )

private case class FinishSimpleOperation
  (handlerIndex: Nat, operationContinuationUsage: Usage, restoredHandlerEntry: Option[HandlerEntry])

private case class HandlerEntry(index: Nat, handler: Handler, previous: Option[HandlerEntry])

private final class StackMachine
  (
    val stack: mutable.ArrayBuffer[
      CTerm | Elimination[VTerm] | ReplicationState | FinishSimpleOperation | HandlerEntry,
    ],
  ):

  /** Pre-constructed term before replicating continuation. This is used to avoid the need to
    * represent partially replicated continuation in the stack.
    */
  private var preConstructedTerm: Option[CTerm] = None
  private var currentHandlerEntry: Option[HandlerEntry] = None
  @tailrec
  private def getMatchingHandler
    (effAndArgs: Eff, start: Option[HandlerEntry] = currentHandlerEntry)
    : HandlerEntry =
    val current = start.getOrElse(throw IllegalStateException("type error: no more handlers"))
    if current.handler.eff == effAndArgs then current
    else getMatchingHandler(effAndArgs, current.previous)

  /** @param pc
    *   "program counter"
    * @param reduceDown
    *   if true, logic should not try to decompose the [[pc]] and push it's components on to the
    *   stack. This is useful so that the run logic does not spin into infinite loop if the given
    *   term has type errors. (Ideally, input should be type-checked so this should never happen,
    *   unless there are bugs in type checking code.)
    * @return
    */
  @tailrec
  @throws(classOf[IrError])
  def run
    (pc: CTerm, reduceDown: Boolean = false)
    (using Context)
    (using Σ: Signature)
    (using ctx: TypingContext)
    : CTerm =
    pc match
      case Hole | CapturedContinuationTip(_) => throw IllegalStateException()
      // Take a shortcut when returning a collapsable computation
      case Return(Collapse(c), _) => run(c)
      // terminal cases
      case _: CType | _: F | _: Return | _: FunctionType | _: RecordType | _: CTop =>
        if stack.isEmpty then pc
        else
          stack.pop() match
            case c: CTerm => run(substHole(c, pc), true)
            case h @ HandlerEntry(_, handler, _) =>
              assert(h == this.currentHandlerEntry)
              run(handler, reduceDown = true)
            case ReplicationState(
                handler,
                baseStackSize,
                continuationTerm1,
                continuationTerm2,
                continuationUsage,
              ) =>
              pc match
                case Return(Con(name, param1 :: param2 :: Nil), _) if name == n"MkPair" =>
                  replicate(
                    baseStackSize,
                    handler.copy(parameter = param1, input = continuationTerm1),
                    handler.copy(parameter = param2, input = continuationTerm2),
                    continuationUsage,
                  )
                case _ => throw IllegalStateException("type error")
            case FinishSimpleOperation(
                handlerIndex,
                operationContinuationUsage,
                previousHandlerEntry,
              ) =>
              pc match
                case Return(Con(name, param :: result :: Nil), _) if name == n"MkPair" =>
                  val handler = stack(handlerIndex).asInstanceOf[Handler]
                  stack(handlerIndex) = handler.copy(parameter = param)
                  def getU0Term(result: VTerm): CTerm =
                    val capturedStack = stack.slice(handlerIndex, stack.size).toIndexedSeq
                    stack.dropRightInPlace(stack.size - handlerIndex)
                    // Construct a term that contains all invocations of parameter disposers in captured handlers. Then
                    // this result is passed to a let term which discards the unit result from the handlers and then
                    // invoke the corresponding operation handler implementation.
                    Let(
                      capturedStack.foldRight[CTerm](Return(Con(n"MkUnit", Nil), uAny)):
                        case (HandlerEntry(_, handler, _), term) =>
                          processStackEntryForDisposerCall(term)(handler)
                        case (_, term) => term
                      ,
                      DataType(Builtins.UnitQn, Nil),
                      handler.outputEffects,
                      UsageLiteral(UAny),
                      // The usage here may not be correct. Technically it should be the usage of the result captured in
                      // the type of the Pair. But we don't have that information here. Fortunately this information is
                      // not needed anyway because reduction would substitute the result later.
                      Return(result.weakened, uAny),
                    )(
                      gn"disposeResult",
                    )
                  def getU1Term(result: VTerm): CTerm =
                    // The usage here may not be correct. Technically it should be the usage of the result captured in
                    // the type of the Pair. But we don't have that information here. Fortunately this information is
                    // not needed anyway because reduction would substitute the result later.
                    Return(result, uAny)

                  val term = operationContinuationUsage match
                    case U0 => getU0Term(result)
                    case U1 => getU1Term(result)
                    case UAff =>
                      result match
                        case Con(name, result :: Nil) if name == n"Left"  => getU0Term(result)
                        case Con(name, result :: Nil) if name == n"Right" => getU1Term(result)
                        case _ => throw IllegalStateException("type error")
                    case _ => throw IllegalStateException("type error")
                  currentHandlerEntry = previousHandlerEntry
                  run(term)
                case _ => throw IllegalStateException("type error")
            case _: Elimination[?] =>
              throw IllegalStateException(
                "type error: none of the terms above can take an argument or projection",
              )
      case m: Meta =>
        val t = ctx.resolveMeta(m) match
          case Solved(context, _, value) =>
            val args = stack
              .takeRight(context.size)
              .map:
                case ETerm(arg) => arg.normalized
                case _          => throw IllegalStateException("bad meta variable application")
            stack.dropRightInPlace(context.size)
            Some(value.substLowers(args.toSeq*))
          case _ => None // stuck for unresolved meta variables
        t match
          case Some(t) => run(t)
          case None    => reconstructTermFromStack(pc)
      case Def(qn) =>
        Σ.getClausesOption(qn) match
          // This is allowed because it could be that the body is not defined yet.
          case None => reconstructTermFromStack(pc)
          case Some(clauses) =>
            clauses.first { case Clause(_, lhs, rhs, _) =>
              val mapping = mutable.SeqMap[Nat, VTerm]()
              matchCoPattern(
                lhs.zip(
                  stack.reverseIterator.map {
                    case e: Elimination[_] => e
                    case t =>
                      throw IllegalArgumentException(
                        s"type error: expect application or projection, but got $t",
                      )
                  },
                ),
                mapping,
              ) match
                case MatchingStatus.Matched =>
                  val defContext = Σ.getDefinition(qn).context
                  stack.dropRightInPlace(lhs.length)
                  val partiallySubstituted = rhs.subst(mapping.get)

                  val defArgs = stack
                    .takeRight(defContext.size)
                    .map:
                      case ETerm(arg) => arg
                      case _          => throw IllegalStateException("type error")
                    .toSeq
                  stack.dropRightInPlace(defContext.size)
                  Some((partiallySubstituted.substLowers(defArgs*), /* stuck */ false))
                case MatchingStatus.Stuck =>
                  Some((reconstructTermFromStack(pc), /* stuck */ true))
                case MatchingStatus.Mismatch => None
            } match
              case Some((t, false)) => run(t)
              case Some((t, true))  => t
              // This is possible when checking the clauses of a definition in some mutually recursive
              // definitions
              case None => reconstructTermFromStack(pc)
      case Force(v) =>
        v.normalized match
          case Thunk(c)             => run(c)
          case _: Var | _: Collapse => reconstructTermFromStack(pc)
          case _                    => throw IllegalArgumentException("type error")
      case Let(t, _, _, _, ctx) =>
        t match
          case Return(v, _)    => run(ctx.substLowers(v))
          case _ if reduceDown => throw IllegalArgumentException("type error")
          case _ =>
            stack.push(pc)
            run(t)
      case Redex(t, elims) =>
        elims match
          case _ if reduceDown => throw IllegalArgumentException("type error")
          case Nil             => run(t)
          case _ =>
            val normalizedElims = elims.reverse.map[Elimination[VTerm]]:
              case ETerm(t) => ETerm.apply(t.normalized)
              case EProj(n) => EProj(n)
            stack.pushAll(normalizedElims)
            run(t)
      case OperationCall(effAndArgs @ (effQn, rawEffArgs), name, rawArgs) =>
        Σ.getEffectOption(effQn) match
          case None => throw MissingDeclaration(effQn)
          case Some(eff) =>
            val effArgs = rawEffArgs.normalized
            val args = rawArgs.normalized
            val matchingHandler = getMatchingHandler(effAndArgs)
            val matchingHandlerIdx = matchingHandler.index
            val handler = matchingHandler.handler
            val handlerImpl = handler.handlers(effQn / name)
            val operation = Σ.getOperation(effQn, name)
            val restoredHandlerEntry = this.currentHandlerEntry
            this.currentHandlerEntry = matchingHandler.previous
            run(handlerImpl.handlerConstraint match
              case HandlerConstraint(usage, HandlerType.Simple) =>
                preConstructedTerm = Some(reconstructTermFromStack(pc))
                stack.push(FinishSimpleOperation(matchingHandlerIdx, usage, restoredHandlerEntry))
                handlerImpl.body.substLowers(handler.parameter :: args*)
              case HandlerConstraint(continuationUsage, HandlerType.Complex) =>
                val allOperationArgs = effArgs ++ args
                val tip = CapturedContinuationTip(
                  F(
                    operation.resultTy.substLowers(allOperationArgs*),
                    Total(),
                    operation.resultUsage.substLowers(allOperationArgs*),
                  ),
                )
                val continuationTerm = stack
                  .slice(matchingHandlerIdx, stack.size)
                  .foldRight(tip):
                    case (entry: Elimination[VTerm], term) => redex(term, entry)
                    case (entry: Let, term)                => entry.copy(t = term)(entry.boundName)
                    case (HandlerEntry(_, entry, _), term) => entry.copy(input = term)
                    case _ => throw IllegalStateException("type error")
                stack.dropRightInPlace(stack.size - matchingHandlerIdx)
                val continuation =
                  Thunk(Continuation(continuationTerm.asInstanceOf[Handler], continuationUsage))
                handlerImpl.body.substLowers(handler.parameter +: args :+ continuation*),
            )
      case Continuation(continuationTerm, continuationUsage) =>
        stack.pop() match
          case EProj(name) if name == n"resume" =>
            val ETerm(param) = stack.pop(): @unchecked
            val ETerm(arg) = stack.pop(): @unchecked
            run(
              replaceTip(
                continuationTerm.copy(parameter = param),
                arg,
              ),
            )
          case EProj(name) if name == n"dispose" =>
            val ETerm(param) = stack.pop(): @unchecked
            val (handlerStack, handlerEntry) =
              expandTermToStack(continuationTerm.copy(parameter = param))(
                processStackEntryForDisposerCall(Hole),
              )()
            stack.pushAll(handlerStack)
            this.currentHandlerEntry = handlerEntry
            run(Return(Con(n"MkUnit", Nil), uAny))
          case proj @ EProj(name) if name == n"replicate" =>
            preConstructedTerm = Some(reconstructTermFromStack(redex(pc, proj)))
            val ETerm(param) = stack.pop(): @unchecked
            val baseStackHeight = stack.size
            val (stackToDuplicate, handlerEntry) =
              expandTermToStack(continuationTerm.copy(parameter = param))(h => h.copy(input = Hole),
              ):
                case t: Redex => t.copy(t = Hole)
                case t: Let   => t.copy(t = Hole)(t.boundName)
                case t        => t
            stack.pushAll(stackToDuplicate)
            this.currentHandlerEntry = handlerEntry
            val tip = stack.pop().asInstanceOf[CapturedContinuationTip]
            replicate(baseStackHeight, tip, tip, continuationUsage)
          case _ => throw IllegalArgumentException("type error")
      case h: Handler =>
        val eff = h.eff.normalized
        if reduceDown then
          h.input match
            case Return(v, _) =>
              this.currentHandlerEntry = this.currentHandlerEntry.get.previous
              run(h.transform.substLowers(h.parameter, v))
            case _ => throw IllegalArgumentException("type error")
        else
          stack.push(
            HandlerEntry(
              stack.size,
              h.copy(eff = eff, input = Hole),
              this.currentHandlerEntry,
            ),
          )
          run(h.input)

  /** @param baseStackSize
    *   size of the base stack, excludng the part that needs to be replicated
    */
  @tailrec
  @throws(classOf[IrError])
  private def replicate
    (
      baseStackSize: Nat,
      continuationTerm1: CTerm,
      continuationTerm2: CTerm,
      continuationUsage: Usage,
    )
    (using Context)
    (using Σ: Signature)
    (using TypingContext)
    : CTerm =
    if stack.size == baseStackSize then
      run(
        Return(
          Con(
            n"MkPair",
            List(
              // This is safe because the continuationTerm1 and continuationTerm2 are both from the term as the index
              // value of baseStackSize, which is the bottom handler in the original captured continuation.
              Thunk(Continuation(continuationTerm1.asInstanceOf[Handler], continuationUsage)),
              Thunk(Continuation(continuationTerm2.asInstanceOf[Handler], continuationUsage)),
            ),
          ),
          u1,
        ),
      )
    else
      stack.pop() match
        case t: Let =>
          replicate(
            baseStackSize,
            t.copy(t = continuationTerm1)(t.boundName),
            t.copy(t = continuationTerm2)(t.boundName),
            continuationUsage,
          )
        case t: Redex =>
          replicate(
            baseStackSize,
            t.copy(t = continuationTerm1),
            t.copy(t = continuationTerm2),
            continuationUsage,
          )
        case HandlerEntry(_, h, previousEntry) =>
          this.currentHandlerEntry = previousEntry
          h.parameterReplicator match
            case Some(parameterReplicator) =>
              stack.push(
                ReplicationState(
                  h,
                  baseStackSize,
                  continuationTerm1,
                  continuationTerm2,
                  continuationUsage,
                ),
              )
              run(parameterReplicator.substLowers(h.parameter))
            case None =>
              replicate(
                baseStackSize,
                h.copy(input = continuationTerm1),
                h.copy(input = continuationTerm2),
                continuationUsage,
              )
        case _ => throw IllegalStateException("type error")

  private def substHole(ctx: CTerm, c: CTerm): CTerm =
    given SourceInfo = ctx.sourceInfo

    ctx match
      case t: Let     => t.copy(t = c)(t.boundName)
      case t: Handler => t.copy(input = c)
      case t: Redex   => t.copy(t = c)
      case _          => throw IllegalArgumentException("unexpected context")

  private def reconstructTermFromStack(pc: CTerm): CTerm =
    var current = pc
    val elims = mutable.ArrayBuffer[Elimination[VTerm]]()
    while stack.nonEmpty do
      stack.pop() match
        case e: Elimination[_] => elims.append(e)
        case c: CTerm =>
          current = substHole(c, current)
          if elims.nonEmpty then
            current = Redex(current, elims.toList)(using c.sourceInfo)
            elims.clear()
        case HandlerEntry(_, handler, _) =>
          current = substHole(handler, current)
          if elims.nonEmpty then
            current = Redex(current, elims.toList)(using handler.sourceInfo)
            elims.clear()
        case _: ReplicationState | _: FinishSimpleOperation =>
          preConstructedTerm match
            case Some(t) => return t
            case _       => throw IllegalStateException("type error")
    if elims.nonEmpty then
      Redex(current, elims.toList)
    else
      current

  @tailrec
  private def expandTermToStack
    (
      term: CTerm,
      currentIndex: Nat = stack.size,
      currentHandlerEntry: Option[HandlerEntry] = None,
      acc: Iterable[CTerm | HandlerEntry] = Iterable(),
    )
    (handlerTransform: Handler => Handler)
    (transform: (CTerm => CTerm) | Unit = ())
    : (Iterable[CTerm | HandlerEntry], Option[HandlerEntry]) =
    term match
      case term: (Redex | Let) =>
        val subTerm = term match
          case t: Redex => t.t
          case t: Let   => t.t
        transform match
          case () =>
            expandTermToStack(subTerm, currentIndex, currentHandlerEntry, acc)(handlerTransform)(
              transform,
            )
          case f: (CTerm => CTerm) =>
            expandTermToStack(
              subTerm,
              currentIndex + 1,
              currentHandlerEntry,
              acc ++ Iterable(f(term)),
            )(
              handlerTransform,
            )(f)
      case term: Handler =>
        val handlerEntry = HandlerEntry(
          currentIndex,
          handlerTransform(term),
          currentHandlerEntry,
        )
        expandTermToStack(
          term.input,
          currentIndex + 1,
          Some(handlerEntry),
          acc ++ Iterable(handlerEntry),
        )(
          handlerTransform,
        )(transform)
      case _ => (acc ++ Iterable(term), currentHandlerEntry)

extension (c: CTerm)
  @throws(classOf[IrError])
  def normalized(using Γ: Context)(using Signature)(using TypingContext): CTerm =
    // inline meta variable, consolidate immediately nested redex
    val transformer = new Transformer[TypingContext]():
      override def transformMeta(m: Meta)(using ctx: TypingContext)(using Σ: Signature): CTerm =
        ctx.resolveMeta(m) match
          case Solved(_, _, t) => transformCTerm(t)
          case _               => m
      override def transformRedex(r: Redex)(using ctx: TypingContext)(using Σ: Signature): CTerm =
        redex(
          transformCTerm(r.t),
          r.elims.map(transformElim),
        )(using r.sourceInfo)

      override def transformCollapse
        (c: Collapse)
        (using ctx: TypingContext)
        (using Σ: Signature)
        : VTerm = transformCTerm(
        c.cTm,
      ) match
        case Return(v, _) => transformVTerm(v)
        case _            => c

    transformer.transformCTerm(c) match
      case Redex(t, elims) => redex(t, elims.map(_.map(_.normalized)))
      case t               => t

  @throws(classOf[IrError])
  def normalized(ty: Option[CTerm])(using Context)(using Signature)(using TypingContext): CTerm =
    if isTotal(c, ty) then Reducible.reduce(c)
    else c.normalized

extension (v: VTerm)
  @throws(classOf[IrError])
  def normalized(using Γ: Context)(using Σ: Signature)(using ctx: TypingContext): VTerm = v match
    case Collapse(cTm) =>
      val reduced = Reducible.reduce(cTm)
      reduced match
        case Return(v, _) => v
        case stuckC       => Collapse(stuckC)(using v.sourceInfo)
    case u: UsageCompound =>
      @throws(classOf[IrError])
      def dfs(tm: VTerm): ULub[VTerm] = ctx.withMetaResolved(tm):
        case UsageLiteral(u)                  => uLubFromLiteral(u)
        case UsageSum(operands)               => uLubSum(operands.multiToSeq.map(dfs))
        case UsageProd(operands)              => uLubProd(operands.map(dfs))
        case UsageJoin(operands)              => uLubJoin(operands.map(dfs))
        case c: Collapse                      => dfs(c.normalized)
        case _: ResolvedMetaVariable | _: Var => uLubFromT(tm)
        case _ =>
          throw IllegalStateException(s"expect to be of Usage type: $tm")

      def lubToTerm(lub: ULub[VTerm]): VTerm = UsageJoin(lub.map(sumToTerm).toSeq*)

      def sumToTerm(sum: USum[VTerm]): VTerm = UsageSum(sum.map(prodToTerm)*)

      def prodToTerm(prod: UProd[VTerm]): VTerm = UsageProd(prod.map(varOrUsageToTerm).toSeq*)

      def varOrUsageToTerm(t: VTerm | Usage): VTerm = t match
        case v: VTerm => v
        case u: Usage => UsageLiteral(u)

      lubToTerm(dfs(u))
    case e: Effects =>
      @throws(classOf[IrError])
      def dfs(tm: VTerm, retainSimpleLinearOnly: Boolean): (Set[Eff], SeqMap[VTerm, Boolean]) =
        ctx.withMetaResolved(tm):
          case Effects(literal, operands) =>
            val literalsAndOperands: Seq[(Set[Eff], SeqMap[VTerm, Boolean])] =
              operands.map((k, v) => dfs(k.normalized, retainSimpleLinearOnly || v)).toSeq
            (
              (literalsAndOperands.flatMap { case (l, _) => l } ++ literal)
                .filter((qn, args) =>
                  if retainSimpleLinearOnly then {
                    val effect = Σ.getEffect(qn)
                    effect.continuationUsage
                      .substLowers(args*)
                      .normalized == UsageLiteral(U1) && effect.handlerType
                      .substLowers(args*)
                      .normalized == HandlerTypeLiteral(HandlerType.Simple)
                  } else true,
                )
                .toSet,
              groupMapReduce(
                literalsAndOperands
                  .flatMap { case (_, o) => o },
              )(_._1)(_._2)(_ && _),
            )
          case _: Collapse => (Set.empty, SeqMap(tm -> false))
          case v: Var =>
            Γ.resolve(v).ty match
              case EffectsType(UsageLiteral(U1), HandlerTypeLiteral(HandlerType.Simple)) =>
                (Set.empty, SeqMap(tm -> true))
              case _ => (Set.empty, SeqMap(tm -> false))
          case r: ResolvedMetaVariable =>
            r.ty match
              case F(EffectsType(UsageLiteral(U1), HandlerTypeLiteral(HandlerType.Simple)), _, _) =>
                (Set.empty, SeqMap(tm -> true))
              case _ => (Set.empty, SeqMap(tm -> false))
          case _ =>
            throw IllegalStateException(s"expect to be of Effects type: $tm")

      val (eff, operands) = dfs(e, false)
      if eff.isEmpty && operands.size == 1 && !operands.head._2 then operands.head._1
      else Effects(eff, operands)
    case l: Level =>
      @throws(classOf[IrError])
      def dfs(tm: VTerm): (LevelOrder, SeqMap[VTerm, Nat]) = ctx.withMetaResolved(tm):
        case Level(literal, operands) =>
          val literalsAndOperands: Seq[(LevelOrder, SeqMap[VTerm, Nat])] =
            operands.map { (tm, offset) =>
              val (l, m) = dfs(tm.normalized)
              (l.suc(offset), m.map((tm, l) => (tm, l + offset)))
            }.toList
          (
            (literalsAndOperands.map(_._1) ++ Seq(literal)).max,
            groupMap(literalsAndOperands.flatMap[(VTerm, Nat)](_._2))(_._1)(_._2)
              .map { (tm, offsets) => (tm, offsets.max) },
          )
        case _: ResolvedMetaVariable | _: Var | _: Collapse => (LevelOrder.zero, SeqMap((tm, 0)))
        case _ => throw IllegalStateException(s"expect to be of Level type: $tm")

      val (literal, m) = dfs(l)
      if literal == LevelOrder.zero && m.size == 1 && m.head._2 == 0
      then m.head._1
      else Level(literal, m)
    case _ => v

extension (vs: List[VTerm])
  @throws(classOf[IrError])
  def normalized(using ctx: Context)(using Signature)(using TypingContext): List[VTerm] =
    vs.map(_.normalized)

given Reducible[CTerm] with

  /** It's assumed that `t` is effect-free.
    */
  @throws(classOf[IrError])
  override def reduce
    (t: CTerm)
    (using ctx: Context)
    (using signature: Signature)
    (using TypingContext)
    : CTerm =
    StackMachine(mutable.ArrayBuffer()).run(t).withSourceInfo(t.sourceInfo)

object Reducible:
  @throws(classOf[IrError])
  def reduce(t: CTerm)(using Context)(using Signature)(using ctx: TypingContext): CTerm =
    ctx.trace[CTerm](
      s"reducing",
      Block(ChopDown, Aligned, yellow(t.sourceInfo), pprint(t)),
      tm => Block(ChopDown, Aligned, yellow(tm.sourceInfo), green(pprint(tm))),
    )(summon[Reducible[CTerm]].reduce(t))

enum MatchingStatus:
  case Matched, Stuck, Mismatch

@tailrec
def matchPattern
  (
    constraints: List[(Pattern, VTerm)],
    mapping: mutable.SeqMap[Nat, VTerm],
    matchingStatus: MatchingStatus = MatchingStatus.Matched,
  )
  : MatchingStatus =
  import Builtins.*
  constraints match
    case Nil => matchingStatus
    case elim :: rest =>
      var status: MatchingStatus = matchingStatus
      var constraints = rest
      elim match
        case (PVar(idx), v) => mapping(idx) = v
        // TODO[P4]: matching type doesn't seem to be useful.
        // TODO[P4]: matching cell type is probably not a good idea because it's unknown at what
        //  level `tyP` should be. In order to allow this, we need to make each `Cell`
        //  self-contained, just like all declared `Data`. The downside is then the need to carry
        //  a level everywhere with the cell. On the other hand, whether to allow this does not
        //  affect the expressive power because one can simulate such by declaring a wrapper
        //  data class. This same trick can be used for equality type, function type, and record
        //  type.
        // case (PDataType(CellQn, heapP :: tyP :: Nil), CellType(heap, ty, status)) =>
        //   constraints = (heapP, heap) :: (tyP, ty) :: constraints

        // TODO[P4]: similarly, we don't allow matching equality type either for the same reason.
        // case (PDataType(EqualityQn, levelP :: tyP :: leftP :: rightP :: Nil),
        // EqualityType(ty, left, right)) =>
        //   constraints = (tyP, ty) ::
        //     (leftP, left) ::
        //     (rightP, right) ::
        //     constraints

        // TODO[P4]: matching usage does not seem very useful. But it can be added if needed.
        case (PDataType(pQn, pArgs), DataType(qn, args)) if pQn == qn =>
          constraints = pArgs.zip(args) ++ constraints
        case (PForcedDataType(_, pArgs), DataType(_, args)) =>
          constraints = pArgs.zip(args) ++ constraints
        case (PConstructor(pName, pArgs), Con(name, args)) if pName == name =>
          constraints = pArgs.zip(args) ++ constraints
        case (
            PForcedDataType(_, pArgs),
            Con(_, args),
          ) =>
          constraints = pArgs.zip(args) ++ constraints
        case (PAbsurd(), _) =>
          throw IllegalArgumentException("type error")
        case (_, Var(_)) | (_, Auto()) => status = MatchingStatus.Stuck
        // Note that we make mismatch dominating stuck because we do not eval by case tree during
        // type checking.
        case _ => return MatchingStatus.Mismatch
      matchPattern(constraints, mapping, status)

@tailrec
def matchCoPattern
  (
    elims: List[(CoPattern, Elimination[VTerm])],
    mapping: mutable.SeqMap[Nat, VTerm],
    matchingStatus: MatchingStatus = MatchingStatus.Matched,
  )
  : MatchingStatus =
  import Builtins.*
  import Elimination.*
  elims match
    case Nil => matchingStatus
    case elim :: rest =>
      elim match
        case (CPattern(p), ETerm(w)) => matchPattern(List((p, w)), mapping, matchingStatus)
        case (CProjection(n1), EProj(n2)) if n1 == n2 =>
        case (CProjection(_), ETerm(_)) | (_, EProj(_)) =>
          throw IllegalArgumentException("type error")
        case _ => return MatchingStatus.Mismatch
      matchCoPattern(rest, mapping, matchingStatus)

private def replaceTip(continuationTerm: CTerm, newTip: VTerm)(using Σ: Signature): CTerm =
  CapturedContinuationTipReplacer.transformCTerm(continuationTerm)(using newTip)

private object CapturedContinuationTipReplacer extends Transformer[VTerm]:
  override def transformCapturedContinuationTip
    (cct: CapturedContinuationTip)
    (using newTip: VTerm)
    (using Σ: Signature)
    : CTerm = Return(newTip, cct.ty.usage)

private def processStackEntryForDisposerCall
  (input: CTerm)
  (handler: Handler)
  (using Signature)
  : Handler =
  // retain all handlers for two reasons
  // 1. if it contains a parameter disposer, the disposer needs to be invoked
  // 2. the handler may provide effects needed by upper disposers
  handler.copy(
    input = input,
    outputUsage = UsageLiteral(Usage.UAny),
    outputTy = DataType(Builtins.UnitQn, Nil),
    // weakened because transform also takes a output value. But for disposer calls this
    // value is always unit and ignored by the parameterDisposer.
    transform = handler.parameterDisposer match
      case Some(parameterDisposer) => parameterDisposer.weakened
      case None                    => Return(Con(n"MkUnit", Nil), uAny),
  )

private def joinContinuationUsages[K]
  (m1: IterableOnce[(K, HandlerConstraint)], m2: IterableOnce[(K, HandlerConstraint)])
  : SeqMap[K, HandlerConstraint] =
  groupMapReduce(m1.iterator.to(Seq) ++ m2)(_._1)(_._2)(_ | _)
