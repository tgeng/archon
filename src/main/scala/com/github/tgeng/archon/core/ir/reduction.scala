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

private final class StackMachine(val stack: mutable.ArrayBuffer[CTerm | Elimination[VTerm]]):

  // Note: for now this does not seem to be useful because this stack machine is only used for type
  // checking, in which case there are no builtin handlers at all because during type checking all
  // computations carried by this machine should be total.

  // stack.prependAll(builtinHandlers)
  // private val builtinHandlers = Seq(
  //   CTerm.HeapHandler(
  //     VTerm.Total(), // placeholder value, not important
  //     Some(GlobalHeapKey),
  //     IndexedSeq(),
  //     CTerm.Hole
  //   )
  // )

  private val handlerIndex = mutable.WeakHashMap[Eff, mutable.Stack[Nat]]()
  regenerateHandlerIndex()

  private def updateHandlerIndex(eff: VTerm, index: Nat) = eff match
    case Effects(effs, s) if s.isEmpty =>
      for eff <- effs do handlerIndex.getOrElseUpdate(eff, mutable.Stack()).push(index)
    case _ => throw IllegalStateException(s"bad effects $eff")

  private def regenerateHandlerIndex(startIndex: Nat = 0): Unit =
    stack.view.zipWithIndex.drop(startIndex).foreach {
      case (handler: Handler, index) => updateHandlerIndex(handler.eff, index)
      case _                         =>
    }
  private def trimHandlerIndex(): Unit =
    handlerIndex.foreach { (_, idxStack) =>
      while idxStack.nonEmpty && idxStack.top >= stack.size do idxStack.pop()
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
      case Return(Collapse(c)) => run(c, reduceDown)
      // terminal cases
      case _: CType | _: F | _: Return | _: FunctionType | _: RecordType | _: CTop =>
        if stack.isEmpty then Right(pc)
        else
          stack.pop() match
            case c: CTerm => run(substHole(c, pc), true)
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
          case Return(v)       => run(ctx.substLowers(v))
          case _ if reduceDown => throw IllegalArgumentException("type error")
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
        def areEffArgsConvertible(ts1: List[VTerm], ts2: List[VTerm], tys: Telescope): Boolean =
          (ts1, ts2, tys) match
            case (Nil, Nil, Nil) => true
            case (t1 :: ts1, t2 :: ts2, ty :: tys) =>
              (for
                t1 <- t1.normalized
                t2 <- t2.normalized
              // Here we don't use checkSubsumption because that has side effect on the typing context (instantiating
              // meta variables). Also, during type checking, the conversion check on effect args is also done by simply
              // normalizing the terms and comparing their equality.
              // In addition, the language has the `decidable-equality` concept, which corresponds to simple equality
              // checks (hence efficient to implement at runtime).
              yield t1 == t2) match
                case Right(true) => areEffArgsConvertible(ts1, ts2, tys.substLowers(t1))
                case _           => false
            case _ => throw IllegalArgumentException()

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
                Σ.getOperation(effQn, name).continuationUsage match
                  case ContinuationUsage(U1, ControlMode.Simple) => Right(opHandler.substLowers(args :+ handler.parameter: _*))
                  case ContinuationUsage(U0, ControlMode.Simple) =>
                    val capturedStack = stack.slice(handlerIdx + 1, stack.size).toSeq
                    stack.dropRightInPlace(stack.size - handlerIdx)
                    trimHandlerIndex()
                    // TODO[P0]: invoke disposer in capturedStack. Note, the handling handler doesn't need to be
                    // processed because the parameter is passed to the corresponding operation handler below.
                    Right(opHandler.substLowers(args :+ handler.parameter: _*))
                  case ContinuationUsage(_, ControlMode.Complex) =>
                    val capturedStack = stack.slice(handlerIdx + 1, stack.size).toSeq
                    stack.dropRightInPlace(stack.size - handlerIdx)
                    trimHandlerIndex()
                    // TODO[P0]: add type information here
                    val continuation = Thunk(Continuation(???))
                    Right(opHandler.substLowers(args :+ handler.parameter :+ continuation: _*))
                  case _ => throw IllegalStateException("bad continuation type for operations")
            yield r) match
              case Right(pc) => run(pc)
              case Left(e)   => Left(e)
      case Continuation(continuationTerm) =>
        stack.pop() match
          case EProj(name) if name == n"resume" => ???
            // val ETerm(param) = stack.pop(): @unchecked
            // val ETerm(arg) = stack.pop(): @unchecked
            // val currentStackHeight = stack.length
            // stack.push(
            //   handler.copy(parameter = param)(
            //     handler.transformBoundName,
            //     handler.handlersBoundNames,
            //   ),
            // )
            // stack.pushAll(capturedStack)
            // regenerateHandlerIndex(currentStackHeight)
            // run(Return(arg))
          case EProj(name) if name == n"dispose" => ???
          // val ETerm(param) = stack.pop(): @unchecked
          // stack.push(
          //   handler.copy(
          //     parameter = param,
          //     transform = handler.parameterDisposer.map(_.weakened),
          //   )(
          //     handler.transformBoundName,
          //     handler.handlersBoundNames,
          //   ),
          // )
          // capturedStack.foreach {
          //   case handler: Handler =>
          //     stack.push(
          //       handler.copy(
          //         // weakened because transform also takes a output value. But for disposer calls this
          //         // value is always unit and ignored by the parameterDisposer.
          //         transform = handler.parameterDisposer.weakened,
          //       )(
          //         handler.transformBoundName,
          //         handler.handlersBoundNames,
          //       ),
          //     )
          //   case _ => // ignore non-handler cases since they do not contain any disposing logic.
          // }
          // run(Return(Con(n"MkUnit", Nil)))
          case EProj(name) if name == n"replicate" => ???
            // val ETerm(param) = stack.pop(): @unchecked
            // val currentStackSize = stack.size
            // stack.push(
            //   handler.copy(parameter = param)(
            //     handler.transformBoundName,
            //     handler.handlersBoundNames,
            //   ),
            // )
            // stack.pushAll(capturedStack)
            // run(ContinuationReplicationState(currentStackSize, Nil, Nil), true)
          case _ => throw IllegalArgumentException("type error")
      // case cr @ ContinuationReplicationState(handlerIndex, stack1, stack2) =>
      //   assert(
      //     reduceDown,
      //     "all calls to run with ContinuationReplicationState should pass reduceDown=True",
      //   )
      //   stack.pop() match
      //     case handler: Handler =>
      //       handler.parameterReplicator match
      //         case None =>
      //           throw IllegalArgumentException(
      //             "type error: handler missing parameterReplicator is not compatible with re-entrant effects.",
      //           )
      //         case Some(parameterReplicator) =>
      //           run(
      //             ContinuationReplicationStateAppender(
      //               parameterReplicator.substLowers(handler.parameter),
      //               handler,
      //               cr,
      //             ),
      //           )
      //     case t =>
      //       run(ContinuationReplicationState(handlerIndex, t +: stack1, t +: stack2), true)
      // case ContinuationReplicationStateAppender(
      //     paramPairs,
      //     handler,
      //     cr @ ContinuationReplicationState(handlerIndex, stack1, stack2),
      //   ) =>
      //   if reduceDown then
      //     paramPairs match
      //       case Return(Con(name, param1 :: param2 :: Nil)) if name == n"MkPair" =>
      //         val handler1 = handler
      //           .copy(parameter = param1)(
      //             handler.transformBoundName,
      //             handler.handlersBoundNames,
      //           )
      //         val handler2 = handler
      //           .copy(parameter = param2)(
      //             handler.transformBoundName,
      //             handler.handlersBoundNames,
      //           )
      //         if stack.size == handlerIndex then
      //           run(
      //             Return(
      //               Con(
      //                 n"MkPair",
      //                 List(
      //                   Thunk(Continuation(handler1, stack1, ???)),
      //                   Thunk(Continuation(handler2, stack2, ???)),
      //                 ),
      //               ),
      //             ),
      //           )
      //         else if stack.size < handlerIndex then
      //           throw IllegalStateException(
      //             "stack is corruptted: somehow execution has passed root handler of replication",
      //           )
      //         else
      //           run(
      //             ContinuationReplicationState(
      //               handlerIndex,
      //               handler1 +: stack1,
      //               handler2 +: stack2,
      //             ),
      //             true,
      //           )
      //       case _ =>
      //         throw IllegalArgumentException(
      //           "type error: parameterReplicator should have returned a pair of parameters",
      //         )
      //   else
      //     stack.push(ContinuationReplicationStateAppender(Hole, handler, cr))
      //     run(paramPairs)
      case h @ Handler(
          eff,
          parameter,
          parameterBinding,
          parameterDisposer,
          parameterReplicator,
          transform,
          handlers,
          input,
        ) =>
        eff.normalized match
          case Left(e) => Left(e)
          case Right(eff) =>
            if reduceDown then
              updateHandlerIndex(eff, stack.length)
              input match
                case Return(v) => run(transform.substLowers(parameter, v))
                case _         => throw IllegalArgumentException("type error")
            else
              updateHandlerIndex(eff, stack.length)
              stack.push(
                Handler(
                  eff,
                  parameter,
                  parameterBinding,
                  parameterDisposer,
                  parameterReplicator,
                  transform,
                  handlers,
                  Hole,
                )(h.transformBoundName, h.handlersBoundNames),
              )
              run(input)

  private def substHole(ctx: CTerm, c: CTerm): CTerm =
    given SourceInfo = ctx.sourceInfo

    ctx match
      case l @ Let(t, ty, effects, usage, ctx) => Let(c, ty, effects, usage, ctx)(l.boundName)
      case h @ Handler(
          eff,
          parameterBinding,
          parameter,
          parameterDisposer,
          parameterReplicator,
          transform,
          handlers,
          input,
        ) =>
        Handler(
          eff,
          parameterBinding,
          parameter,
          parameterDisposer,
          parameterReplicator,
          transform,
          handlers,
          c,
        )(
          h.transformBoundName,
          h.handlersBoundNames,
        )
      case _                                 => throw IllegalArgumentException("unexpected context")

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
        case Return(v) => transformVTerm(v)
        case _         => c

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
          case Return(v) => Right(v)
          case stuckC    => Right(Collapse(stuckC)(using v.sourceInfo))
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

private def joinContinuationUsages[K]
  (m1: IterableOnce[(K, ContinuationUsage)], m2: IterableOnce[(K, ContinuationUsage)])
  : Map[K, ContinuationUsage] =
  (m1.iterator.to(Seq) ++ m2).groupMapReduce(_._1)(_._2)(_ | _)
