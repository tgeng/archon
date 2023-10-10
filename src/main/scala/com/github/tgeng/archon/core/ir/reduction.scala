package com.github.tgeng.archon.core.ir

import com.github.tgeng.archon.common.eitherFilter.*
import com.github.tgeng.archon.common.*
import com.github.tgeng.archon.core.common.*

import scala.annotation.tailrec
import scala.collection.mutable
import CTerm.*
import VTerm.*
import Pattern.*
import CoPattern.*
import PrettyPrinter.pprint
import WrapPolicy.*
import IndentPolicy.*
import DelimitPolicy.*
import Usage.*
import IrError.*
import MetaVariable.*
import Elimination.*

trait Reducible[T]:
  def reduce(t: T)(using ctx: Context)(using signature: Signature)(using TypingContext): Either[IrError, T]

extension [T](a: mutable.ArrayBuffer[T])
  def pop(): T = a.remove(a.length - 1)
  def push(t: T) = a.addOne(t)
  def pushAll(ts: Iterable[T]) = a.addAll(ts)

private case class ReplicationState
  (
    currentHandler: Handler,
    baseStackSize: Nat,
    continuationTerm1: CTerm,
    continuationTerm2: CTerm,
    continuationUsage: Usage,
  )

private case class FinishSimpleOperation(handlerIndex: Nat, operationContinuationUsage: Usage)

private final class StackMachine
  (val stack: mutable.ArrayBuffer[CTerm | Elimination[VTerm] | ReplicationState | FinishSimpleOperation]):

  /** Pre-constructed term before replicating continuation. This is used to avoid the need to represent partially
    * replicated continuation in the stack.
    */
  private var preConstructedTerm: Option[CTerm] = None
  private val handlerIndex = mutable.WeakHashMap[Eff, mutable.Stack[Nat]]()
  regenerateHandlerIndex()

  private def updateHandlerIndex(eff: VTerm, index: Nat) = eff match
    case Effects(effs, s) if s.isEmpty =>
      for eff <- effs do handlerIndex.getOrElseUpdate(eff, mutable.Stack()).push(index)
    case _ => throw IllegalStateException(s"bad effects $eff")

  private def regenerateHandlerIndex(startIndex: Nat = 0): Unit =
    trimHandlerIndex(startIndex)
    stack.view.zipWithIndex.drop(startIndex).foreach {
      case (handler: Handler, index) => updateHandlerIndex(handler.eff, index)
      case _                         =>
    }
  private def trimHandlerIndex(size: Nat = stack.size): Unit =
    handlerIndex.foreach { (_, idxStack) =>
      while idxStack.nonEmpty && idxStack.top >= size do idxStack.pop()
    }

  /** @param pc
    *   "program counter"
    * @param reduceDown
    *   if true, logic should not try to decompose the [[pc]] and push it's components on to the stack. This is useful
    *   so that the run logic does not spin into infinite loop if the given term has type errors. (Ideally, input should
    *   be type-checked so this should never happen, unless there are bugs in type checking code.)
    * @return
    */
  @tailrec
  def run
    (pc: CTerm, reduceDown: Boolean = false)
    (using Context)
    (using Σ: Signature)
    (using ctx: TypingContext)
    : Either[IrError, CTerm] =
    pc match
      case Hole | CapturedContinuationTip(_) => throw IllegalStateException()
      // Take a shortcut when returning a collapsable computation
      case Return(Collapse(c), _) => run(c)
      // terminal cases
      case _: CType | _: F | _: Return | _: FunctionType | _: RecordType | _: CTop =>
        if stack.isEmpty then Right(pc)
        else
          stack.pop() match
            case c: CTerm => run(substHole(c, pc), true)
            case ReplicationState(handler, baseStackSize, continuationTerm1, continuationTerm2, continuationUsage) =>
              pc match
                case Return(Con(name, param1 :: param2 :: Nil), _) if name == n"MkPair" =>
                  replicate(
                    baseStackSize,
                    handler.copy(parameter = param1, input = continuationTerm1)(
                      handler.handlersBoundNames,
                    ),
                    handler.copy(parameter = param1, input = continuationTerm2)(
                      handler.handlersBoundNames,
                    ),
                    continuationUsage,
                  )
                case _ => throw IllegalStateException("type error")
            case FinishSimpleOperation(handlerIndex, operationContinuationUsage) =>
              regenerateHandlerIndex(handlerIndex)
              pc match
                case Return(Con(name, param :: result :: Nil), _) if name == n"MkPair" =>
                  val handler = stack(handlerIndex).asInstanceOf[Handler]
                  stack(handlerIndex) = handler.copy(parameter = param)(
                    handler.handlersBoundNames,
                  )
                  def getU0Term(result: VTerm): CTerm =
                    val capturedStack = stack.slice(handlerIndex, stack.size).toIndexedSeq
                    stack.dropRightInPlace(stack.size - handlerIndex)
                    trimHandlerIndex()
                    // Construct a term that contains all invocations of parameter disposers in captured handlers. Then
                    // this result is passed to a let term which discards the unit result from the handlers and then
                    // invoke the corresponding operation handler implementation.
                    Let(
                      capturedStack.foldRight[CTerm](Return(Con(n"MkUnit", Nil), uAny)):
                        case (entry: CTerm, term) =>
                          processStackEntryForDisposerCall(term)(entry) match
                            case Some(t) => t
                            case _       => term
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
                        case _                                            => throw IllegalStateException("type error")
                    case _ => throw IllegalStateException("type error")

                  run(term)
                case _ => throw IllegalStateException("type error")
            case _ =>
              throw IllegalStateException(
                "type error: none of the terms above can take an argument or projection",
              )
      case m: Meta =>
        val t = ctx.resolveMeta(m) match
          case Solved(context, ty, value) =>
            for
              args <- transpose(stack.takeRight(context.size).map {
                case ETerm(arg) => arg.normalized
                case _          => throw IllegalStateException("bad meta variable application")
              })
              _ = stack.dropRightInPlace(context.size)
            yield Some(value.substLowers(args.toSeq: _*)) // stuck for unresolved meta variables
          case _ => Right(None)
        t match
          case Right(Some(t)) => run(t)
          case Right(None)    => Right(reconstructTermFromStack(pc))
          case Left(e)        => Left(e)
      case Def(qn) =>
        Σ.getClausesOption(qn) match
          // This is allowed because it could be that the body is not defined yet.
          case None => Right(reconstructTermFromStack(pc))
          case Some(clauses) =>
            clauses.first { case Clause(bindings, lhs, rhs, ty) =>
              val mapping = mutable.Map[Nat, VTerm]()
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
                  stack.dropRightInPlace(lhs.length)
                  Some(Right((rhs.subst(mapping.get), /* stuck */ false)))
                case MatchingStatus.Stuck =>
                  Some(Right((reconstructTermFromStack(pc), /* stuck */ true)))
                case MatchingStatus.Mismatch => None
            } match
              case Some(Right((t, false))) => run(t)
              case Some(Right((t, true)))  => Right(t)
              // This is possible when checking the clauses of a definition in some mutually recursive
              // definitions
              case None => Right(reconstructTermFromStack(pc))
      case Force(v) =>
        v.normalized match
          case Left(e)         => Left(e)
          case Right(Thunk(c)) => run(c)
          case Right(_: Var | _: Collapse) =>
            Right(reconstructTermFromStack(pc))
          case _ => throw IllegalArgumentException("type error")
      case Let(t, _, _, _, ctx) =>
        t match
          case Return(v, usage) => run(ctx.substLowers(v))
          case _ if reduceDown  => throw IllegalArgumentException("type error")
          case _ =>
            stack.push(pc)
            run(t)
      case Redex(t, elims) =>
        elims match
          case _ if reduceDown => throw IllegalArgumentException("type error")
          case Nil             => run(t)
          case _ =>
            val normalizedElims = transpose(elims.reverse.map[Either[IrError, Elimination[VTerm]]] {
              case ETerm(t) => t.normalized.map(ETerm.apply)
              case EProj(n) => Right(EProj(n))
            })
            normalizedElims match
              case Right(elims) =>
                stack.pushAll(elims)
                run(t)
              case Left(e) => Left(e)
      case OperationCall((effQn, effArgs), name, args) =>
        Σ.getEffectOption(effQn) match
          case None => Left(MissingDeclaration(effQn))
          case Some(eff) =>
            (for
              effArgs <- effArgs.normalized
              args <- args.normalized
              r <-
                val handlerIdx = handlerIndex((effQn, effArgs)).top
                val handler = stack(handlerIdx).asInstanceOf[Handler]
                val opHandler = handler.handlers(effQn / name)
                val operation = Σ.getOperation(effQn, name)
                operation.continuationUsage match
                  case ContinuationUsage(usage, ControlMode.Simple) =>
                    preConstructedTerm = Some(reconstructTermFromStack(pc))
                    // TODO[P1]: redo the index with a HMAT instead so trimming is not needed.
                    // Remove all index into handlers between the matching handler and the current tip so that the
                    // corresponding operation handler implementation can run as if there are no inbetween handlers.
                    trimHandlerIndex(handlerIdx)
                    stack.push(FinishSimpleOperation(handlerIdx, usage))
                    Right(opHandler.substLowers(handler.parameter :: args: _*))
                  case ContinuationUsage(continuationUsage, ControlMode.Complex) =>
                    val allOperationArgs = effArgs ++ args
                    val tip = CapturedContinuationTip(
                      F(
                        operation.resultTy.substLowers(allOperationArgs: _*),
                        Total(),
                        operation.resultUsage.substLowers(allOperationArgs: _*),
                      ),
                    )
                    val continuationTerm = stack
                      .slice(handlerIdx, stack.size)
                      .foldRight(tip):
                        case (entry: Elimination[VTerm], term) => redex(term, entry)
                        case (entry: Let, term)                => entry.copy(t = term)(entry.boundName)
                        case (entry: Handler, term) =>
                          entry.copy(input = term)(entry.handlersBoundNames)
                        case _ => throw IllegalStateException("type error")
                    stack.dropRightInPlace(stack.size - handlerIdx)
                    trimHandlerIndex()
                    val continuation = Thunk(Continuation(continuationTerm.asInstanceOf[Handler], continuationUsage))
                    Right(opHandler.substLowers(handler.parameter +: args :+ continuation: _*))
            yield r) match
              case Right(pc) => run(pc)
              case Left(e)   => Left(e)
      case Continuation(continuationTerm, continuationUsage) =>
        def getContinuationTermWithNewParameter(param: VTerm) = continuationTerm.copy(parameter = param)(
          continuationTerm.handlersBoundNames,
        )
        stack.pop() match
          case EProj(name) if name == n"resume" =>
            val ETerm(param) = stack.pop(): @unchecked
            val ETerm(arg) = stack.pop(): @unchecked
            run(
              replaceTip(
                getContinuationTermWithNewParameter(param),
                arg,
              ),
            )
          case EProj(name) if name == n"dispose" =>
            val ETerm(param) = stack.pop(): @unchecked
            val handlerStack =
              expandTermToStack(getContinuationTermWithNewParameter(param))(processStackEntryForDisposerCall(Hole))
            val stackHeight = stack.size
            stack.pushAll(handlerStack)
            regenerateHandlerIndex(stackHeight)
            run(Return(Con(n"MkUnit", Nil), uAny))
          case proj @ EProj(name) if name == n"replicate" =>
            preConstructedTerm = Some(reconstructTermFromStack(redex(pc, proj)))
            val ETerm(param) = stack.pop(): @unchecked
            val baseStackHeight = stack.size
            val stackToDuplicate = expandTermToStack(getContinuationTermWithNewParameter(param)):
              case t: Redex   => Some(t.copy(t = Hole))
              case t: Let     => Some(t.copy(t = Hole)(t.boundName))
              case h: Handler => Some(h.copy(input = Hole)(h.handlersBoundNames))
              case t          => Some(t)
            stack.pushAll(stackToDuplicate)
            val tip = stack.pop().asInstanceOf[CapturedContinuationTip]
            replicate(baseStackHeight, tip, tip, continuationUsage)
          case _ => throw IllegalArgumentException("type error")
      case h: Handler =>
        h.eff.normalized match
          case Left(e) => Left(e)
          case Right(eff) =>
            if reduceDown then
              updateHandlerIndex(eff, stack.length)
              h.input match
                case Return(v, usage) => run(h.transform.substLowers(h.parameter, v))
                case _                => throw IllegalArgumentException("type error")
            else
              stack.push(h.copy(eff = eff, input = Hole)(h.handlersBoundNames))
              updateHandlerIndex(eff, stack.length)
              run(h.input)

  /** @param baseStackSize
    *   size of the base stack, excludng the part that needs to be replicated
    * @param continuationTerm1
    * @param continuationTerm2
    * @return
    */
  @tailrec
  private def replicate
    (baseStackSize: Nat, continuationTerm1: CTerm, continuationTerm2: CTerm, continuationUsage: Usage)
    (using Context)
    (using Σ: Signature)
    (using ctx: TypingContext)
    : Either[IrError, CTerm] =
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
        case h: Handler =>
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
                h.copy(input = continuationTerm1)(h.handlersBoundNames),
                h.copy(input = continuationTerm2)(h.handlersBoundNames),
                continuationUsage,
              )
        case _ => throw IllegalStateException("type error")

  private def substHole(ctx: CTerm, c: CTerm): CTerm =
    given SourceInfo = ctx.sourceInfo

    ctx match
      case t: Let     => t.copy(t = c)(t.boundName)
      case t: Handler => t.copy(input = c)(t.handlersBoundNames)
      case t: Redex   => t.copy(t = c)
      case _          => throw IllegalArgumentException("unexpected context")

  private def reconstructTermFromStack(pc: CTerm): CTerm =
    var current = pc
    val elims = mutable.ArrayBuffer[Elimination[VTerm]]()
    while (stack.nonEmpty) {
      stack.pop() match
        case e: Elimination[_] => elims.append(e)
        case c: CTerm =>
          current = substHole(c, current)
          if elims.nonEmpty then
            current = Redex(current, elims.toList)(using c.sourceInfo)
            elims.clear()
        case _: ReplicationState | _: FinishSimpleOperation =>
          preConstructedTerm match
            case Some(t) => return t
            case _       => throw IllegalStateException("type error")
    }
    current

extension (c: CTerm)
  def normalized(using Γ: Context)(using Σ: Signature)(using TypingContext): Either[IrError, CTerm] =
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

      override def transformCollapse(c: Collapse)(using ctx: TypingContext)(using Σ: Signature): VTerm = transformCTerm(
        c.cTm,
      ) match
        case Return(v, _) => transformVTerm(v)
        case _            => c

    transformer.transformCTerm(c) match
      case Redex(t, elims) =>
        for elims <- transpose(elims.map(_.mapEither(_.normalized)))
        yield redex(t, elims)
      case t => Right(t)

  def normalized(ty: Option[CTerm])(using Γ: Context)(using Σ: Signature)(using TypingContext): Either[IrError, CTerm] =
    if isTotal(c, ty) then Reducible.reduce(c)
    else c.normalized

extension (v: VTerm)
  def normalized(using Γ: Context)(using Σ: Signature)(using TypingContext): Either[IrError, VTerm] = v match
    case Collapse(cTm) =>
      for
        reduced <- Reducible.reduce(cTm)
        r <- reduced match
          case Return(v, _) => Right(v)
          case stuckC       => Right(Collapse(stuckC)(using v.sourceInfo))
      yield r
    case u: UsageCompound =>
      def dfs(tm: VTerm): Either[IrError, ULub[Var]] = tm match
        case UsageLiteral(u)     => Right(uLubFromLiteral(u))
        case UsageSum(operands)  => transpose(operands.multiToSeq.map(dfs)).map(uLubProd)
        case UsageProd(operands) => transpose(operands.map(dfs)).map(uLubProd)
        case UsageJoin(operands) => transpose(operands.map(dfs)).map(uLubJoin)
        case c: Collapse         => c.normalized.flatMap(dfs)
        case v: Var              => Right(uLubFromT(v))
        case _ =>
          throw IllegalStateException(s"expect to be of Usage type: $tm")

      def lubToTerm(lub: ULub[Var]): VTerm = UsageJoin(lub.map(sumToTerm).toSeq: _*)

      def sumToTerm(sum: USum[Var]): VTerm = UsageSum(sum.map(prodToTerm).toSeq: _*)

      def prodToTerm(prod: UProd[Var]): VTerm = UsageProd(prod.map(varOrUsageToTerm).toSeq: _*)

      def varOrUsageToTerm(t: Var | Usage): VTerm = t match
        case v: Var   => v
        case u: Usage => UsageLiteral(u)

      dfs(u).map(lubToTerm)
    case e: Effects =>
      def dfs(tm: VTerm): Either[IrError, (Set[Eff], Set[VTerm])] = tm match
        case Effects(literal, operands) =>
          for literalsAndOperands: Set[(Set[Eff], Set[VTerm])] <- transpose(
              operands.map(_.normalized.flatMap(dfs)),
            )
          yield (
            literalsAndOperands.flatMap { case (l, _) => l } ++ literal,
            literalsAndOperands.flatMap { case (_, o) => o },
          )
        case _: Var | _: Collapse => Right((Set.empty, Set(tm)))
        case _ =>
          throw IllegalStateException(s"expect to be of Effects type: $tm")

      dfs(e).map { case (eff, operands) =>
        if eff.isEmpty && operands.size == 1 then operands.head
        else Effects(eff, operands)
      }
    case l: Level =>
      def dfs(tm: VTerm): Either[IrError, (LevelOrder, Map[VTerm, Nat])] = tm match
        case Level(literal, operands) =>
          for literalsAndOperands: Seq[(LevelOrder, Map[VTerm, Nat])] <- transpose(
              operands.map { (tm, offset) =>
                for
                  tm <- tm.normalized
                  (l, m) <- dfs(tm)
                yield (l.suc(offset), m.map((tm, l) => (tm, l + offset)))
              }.toList,
            )
          yield (
            (literalsAndOperands.map(_._1) ++ Seq(literal)).max,
            literalsAndOperands
              .flatMap[(VTerm, Nat)](_._2)
              .groupMap(_._1)(_._2)
              .map { (tm, offsets) => (tm, offsets.max) },
          )
        case _: Var | _: Collapse => Right(LevelOrder.zero, Map((tm, 0)))
        case _                    => throw IllegalStateException(s"expect to be of Level type: $tm")

      dfs(l).map { case (l, m) =>
        if l == LevelOrder.zero && m.size == 1 && m.head._2 == 0
        then m.head._1
        else Level(l, m)
      }
    case _ => Right(v)

extension (vs: List[VTerm])
  def normalized(using ctx: Context)(using Σ: Signature)(using TypingContext): Either[IrError, List[VTerm]] =
    transpose(vs.map(_.normalized))

given Reducible[CTerm] with

  /** It's assumed that `t` is effect-free.
    */
  override def reduce
    (t: CTerm)
    (using ctx: Context)
    (using signature: Signature)
    (using TypingContext)
    : Either[IrError, CTerm] = StackMachine(mutable.ArrayBuffer())
    .run(t)
    .map(_.withSourceInfo(t.sourceInfo))

object Reducible:
  def reduce(t: CTerm)(using Context)(using Signature)(using ctx: TypingContext): Either[IrError, CTerm] =
    ctx.trace[IrError, CTerm](
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
    mapping: mutable.Map[Nat, VTerm],
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
        case (PForcedDataType(_, pArgs), DataType(qn2, args)) =>
          constraints = pArgs.zip(args) ++ constraints
        case (PConstructor(pName, pArgs), Con(name, args)) if pName == name =>
          constraints = pArgs.zip(args) ++ constraints
        case (
            PForcedDataType(pName, pArgs),
            Con(name, args),
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
    mapping: mutable.Map[Nat, VTerm],
    matchingStatus: MatchingStatus = MatchingStatus.Matched,
  )
  : MatchingStatus =
  import Elimination.*
  import Builtins.*
  elims match
    case Nil => matchingStatus
    case elim :: rest =>
      var status: MatchingStatus = matchingStatus
      var elims = rest
      elim match
        case (CPattern(p), ETerm(w))                  => matchPattern(List((p, w)), mapping, matchingStatus)
        case (CProjection(n1), EProj(n2)) if n1 == n2 =>
        case (CProjection(_), ETerm(_)) | (_, EProj(_)) =>
          throw IllegalArgumentException("type error")
        case _ => return MatchingStatus.Mismatch
      matchCoPattern(elims, mapping, status)

private def replaceTip(continuationTerm: CTerm, newTip: VTerm)(using Σ: Signature): CTerm =
  CapturedContinuationTipReplacer.transformCTerm(continuationTerm)(using newTip)

private object CapturedContinuationTipReplacer extends Transformer[VTerm]:
  override def transformCapturedContinuationTip
    (cct: CapturedContinuationTip)
    (using newTip: VTerm)
    (using Σ: Signature)
    : CTerm = Return(newTip, cct.ty.usage)

private def expandTermToStack(term: CTerm)(transform: CTerm => Option[CTerm]): Iterable[CTerm] = term match
  case term: Redex   => transform(term) ++ expandTermToStack(term.t)(transform)
  case term: Let     => transform(term) ++ expandTermToStack(term.t)(transform)
  case term: Handler => transform(term) ++ expandTermToStack(term.input)(transform)
  case _             => Iterable(term)

private def processStackEntryForDisposerCall(input: CTerm)(entry: CTerm)(using Signature): Option[CTerm] = entry match
  // retain all handlers for two reasons
  // 1. if it contains a parameter disposer, the disposer needs to be invoked
  // 2. the handler may provide effects needed by upper disposers
  case h: Handler =>
    Some(
      h.copy(
        input = input,
        outputUsage = UsageLiteral(Usage.UAny),
        outputTy = DataType(Builtins.UnitQn, Nil),
        // weakened because transform also takes a output value. But for disposer calls this
        // value is always unit and ignored by the parameterDisposer.
        transform = h.parameterDisposer match
          case Some(parameterDisposer) => parameterDisposer.weakened
          case None                    => Return(Con(n"MkUnit", Nil), uAny),
      )(
        h.handlersBoundNames,
      ),
    )
  case _ => None

private def joinContinuationUsages[K]
  (m1: IterableOnce[(K, ContinuationUsage)], m2: IterableOnce[(K, ContinuationUsage)])
  : Map[K, ContinuationUsage] =
  (m1.iterator.to(Seq) ++ m2).groupMapReduce(_._1)(_._2)(_ | _)
