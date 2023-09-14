package com.github.tgeng.archon.parser.mixfix

import com.github.tgeng.archon.common.*
import com.github.tgeng.archon.core.common.*
import com.github.tgeng.archon.parser.combinators.{*, given}
import scala.collection.mutable

// This implementation follows from this paper https://www.cse.chalmers.se/~nad/publications/danielsson-norell-mixfix.pdf
enum Associativity:
  case Left, Right, Non

enum Fixity:
  case Prefix
  case Infix(val associativity: Associativity)
  case Postfix

  /** Note that an operator of this fixity should have at least one hole inside, for example `[_]`.
    * In other words, atoms like `myVariable` should not be represented as an operator but simply an
    * [[MixfixAst.Identifier]] instead.
    */
  case Closed

import com.github.tgeng.archon.parser.mixfix.Fixity.*

case class Operator(namespace: QualifiedName, fixity: Fixity, nameParts: Seq[Seq[String]]):
  def operatorName: String =
    val rawName = nameParts.map(_.mkString).mkString("_")
    fixity match
      case Closed   => rawName
      case Prefix   => rawName + "_"
      case Postfix  => "_" + rawName
      case Infix(_) => "_" + rawName + "_"

  override def toString: String = namespace.toString + "." + operatorName

object Operator:
  def apply(qualifiedName: QualifiedName, fixity: Fixity, nameParts: Seq[Seq[String]]): Operator =
    if nameParts.isEmpty then throw IllegalArgumentException("nameParts should not be empty")
    if fixity == Closed && nameParts.size == 1 then
      throw IllegalArgumentException(
        "for closed operator the nameParts must contain at least 2 elements",
      )
    nameParts.foreach(namePart => assert(namePart.nonEmpty))
    new Operator(qualifiedName, fixity, nameParts)

/** Operators in neighbor nodes binds tighter than operators in this node. Note that there must not
  * be cycles. Implementation should be immutable.
  */
trait PrecedenceNode:
  def operators: Map[Fixity, Seq[Operator]]

  def neighbors: Seq[PrecedenceNode]

/** A DAG.
  */
type PrecedenceGraph = Seq[PrecedenceNode]

trait NamePart[N]:
  def asString(n: N): String

enum MixfixAst[N, L]:
  case OperatorCall(operator: Operator, args: List[MixfixAst[N, L]], nameParts: List[List[N]])
  case ApplyCall(args: List[MixfixAst[N, L]])
  case Identifier(name: N)
  case Literal(literal: L)

  override def toString: String = this match
    case OperatorCall(op, args, nameParts) =>
      val namePartsString = nameParts.map(_.mkString)
      op.fixity match
        case Closed =>
          (interleave(namePartsString, args) :+ namePartsString.last).mkString(
            "[",
            " ",
            "]",
          )
        case Prefix => interleave(namePartsString, args).mkString("[", " ", "]")
        case Postfix =>
          interleave(args, namePartsString).mkString("[", " ", "]")
        case Infix(_) =>
          (interleave(args, namePartsString) :+ args.last).mkString(
            "[",
            " ",
            "]",
          )
    case ApplyCall(args)  => args.mkString("[@ ", " ", "]")
    case Identifier(name) => "`" + name.toString + "`"
    case Literal(literal) => literal.toString

  private def interleave[T](s1: Seq[T], s2: Seq[T]): Seq[T] =
    s1.zip(s2).flatMap(_.toList)

import com.github.tgeng.archon.parser.mixfix.MixfixAst.*

def createMixfixParser[N, M[+_]: Alternative: Monad: Applicative: Functor, L]
  (g: PrecedenceGraph, literalParser: ParserT[N, L, M])
  (using Functor[ParserT[N, *, M]])
  (using Applicative[ParserT[N, *, M]])
  (using Monad[ParserT[N, *, M]])
  (using Alternative[ParserT[N, *, M]])
  (using Alternative[ParseResult[M, *]])
  (using nn: NamePart[N])
  (using cache: ParserCache[N, M])
  : ParserT[N, MixfixAst[N, L], M] =
// Filter out operators that does not appear in the input.
  for
    nameParts <- P.info((input, _) => input.map(n => nn.asString(n)).toSet)
    r <- createMixfixParserImpl(trimGraph(g, nameParts), literalParser)
  yield r

def trimGraph(g: PrecedenceGraph, nameParts: Set[String]): PrecedenceGraph =
  // key is old node, value is new node
  val nodeMap = mutable.Map[PrecedenceNode, PrecedenceNode]()
  val newPrecedenceMap = mutable.Map[PrecedenceNode, Seq[PrecedenceNode]]()

  def isOperatorRelevant(op: Operator) = op.nameParts.flatten.exists(nameParts)

  def isNodeRelevant(node: PrecedenceNode) =
    node.operators.values.flatten.exists(isOperatorRelevant)

  for oldNode <- g.filter(isNodeRelevant) do
    nodeMap(oldNode) = new PrecedenceNode:
      override val operators: Map[Fixity, Seq[Operator]] =
        oldNode.operators.map((fixity, operators) =>
          (
            fixity,
            operators.filter(
              isOperatorRelevant,
            ),
          ),
        )

      override def neighbors: Seq[PrecedenceNode] = newPrecedenceMap(this)

      override def toString: String = operators.head.toString + "->" + operators

  for (oldNode, newNode) <- nodeMap do
    newPrecedenceMap(newNode) = oldNode.neighbors.filter(isNodeRelevant).map(nodeMap)
  g.flatMap(nodeMap.lift).toSeq

def createMixfixParserImpl[N, M[
  +_,
]: Alternative: Monad: Applicative: Functor, L]
  (g: PrecedenceGraph, literalParser: ParserT[N, L, M])
  (using Functor[ParserT[N, *, M]])
  (using Applicative[ParserT[N, *, M]])
  (using Monad[ParserT[N, *, M]])
  (using Alternative[ParserT[N, *, M]])
  (using Alternative[ParseResult[M, *]])
  (using nn: NamePart[N])
  (using cache: ParserCache[N, M])
  : ParserT[N, MixfixAst[N, L], M] =
  val illegalIdentifierNames = g
    .flatMap(node => node.operators.values.flatMap(ops => ops.flatMap(op => op.nameParts.flatten)))
    .toSet

  def getNodeTargetName(node: PrecedenceNode) = node.operators.values
    .flatMap(
      _.map(_.nameParts.map(_.mkString).mkString("_")),
    )
    .mkString("{", ", ", "}")

  def union[T](parsers: Iterable[ParserT[N, T, M]]): ParserT[N, T, M] =
    parsers.reduceOption(_ | _).getOrElse(P.fail("<tighter ops>"))

  def unionBiased[T](parsers: Iterable[ParserT[N, T, M]]): ParserT[N, T, M] =
    parsers.reduceOption(_ || _).getOrElse(P.fail("<tighter ops>"))

  def expr: ParserT[N, MixfixAst[N, L], M] = P(
    P.cached(g, unionBiased(g.map(pHat)) | closedPlus),
  )

  extension (node: PrecedenceNode)
    def pHat: ParserT[N, MixfixAst[N, L], M] =
      P(
        P.cached(
          node,
          for
            ops <- P
              .lift((node.pUp, node.op(Infix(Associativity.Non)), node.pUp))
              .map((preArg, t, postArg) => OperatorCall(t(0), preArg +: t(1) :+ postArg, t(2))) |
              // somehow type inferencing is not working here and requires explicit type arguments
              P.foldRight1[
                (Operator, List[MixfixAst[N, L]], List[List[N]]),
                MixfixAst[N, L],
              ](
                pRight,
                P.pure((t, postArg) => OperatorCall(t(0), t(1) :+ postArg, t(2))),
                pUp,
              ) |
              P.foldLeft1[MixfixAst[
                N,
                L,
              ], (Operator, List[MixfixAst[N, L]], List[List[N]])](
                pUp,
                P.pure((preArg, t) => OperatorCall(t(0), preArg +: t(1), t(2))),
                pLeft,
              )
            args <- closed.**
          yield if args.isEmpty then ops else ApplyCall(ops +: args),
        ),
        getNodeTargetName(node),
        lazily = true,
      )

    def pRight: ParserT[N, (Operator, List[MixfixAst[N, L]], List[List[N]]), M] =
      P.cached(
        (node, "right"),
        node.op(Prefix) |
          P.lift((node.pUp, node.op(Infix(Associativity.Right))))
            .map((preArg, t) => (t(0), preArg +: t(1), t(2))),
      )

    def pLeft: ParserT[N, (Operator, List[MixfixAst[N, L]], List[List[N]]), M] =
      P.cached(
        (node, "left"),
        node.op(Postfix) |
          P.lift((node.op(Infix(Associativity.Left)), node.pUp))
            .map((t, postArg) => (t(0), t(1) :+ postArg, t(2))),
      )

    def pUp: ParserT[N, MixfixAst[N, L], M] =
      P.cached(
        (node, "up"),
        unionBiased(node.neighbors.map(_.pHat)) | closedPlus,
      )

    def op(fix: Fixity): ParserT[N, (Operator, List[MixfixAst[N, L]], List[List[N]]), M] =
      P.cached(
        (node, fix),
        union(
          node.operators
            .getOrElse(fix, Seq())
            .map(operator =>
              between(expr, operator.nameParts)
                .map((args, nameParts) => (operator, args, nameParts)),
            ),
        ),
      )

  def closedPlus: ParserT[N, MixfixAst[N, L], M] =
    closed.++.map(args =>
      if args.size == 1
      then args.head
      else ApplyCall(args),
    )

  def closed: ParserT[N, MixfixAst[N, L], M] =
    P.cached(
      (g, "closed"),
      union(
        g.map(node =>
          // prefer literal over closed operator and identifiers
          P.satisfySingle(
            "<quoted identifier>",
            n =>
              val s = nn.asString(n)
              s
                .startsWith("`") && s.endsWith("`"),
          ).map(Identifier.apply) ||
            literalParser.map(Literal.apply) ||
            P(
              node
                .op(Closed)
                .map((op, args, nameParts) => OperatorCall(op, args, nameParts)),
              getNodeTargetName(node),
            ),
        ),
      ) ||
        P.satisfySingle(
          s"<none of $illegalIdentifierNames>",
          n => !illegalIdentifierNames.contains(nn.asString(n)),
        ).map(Identifier.apply),
    )

  def between[T]
    (p: => ParserT[N, T, M], nameParts: Seq[Seq[String]])
    : ParserT[N, (List[T], List[List[N]]), M] =
    nameParts match
      case Nil => throw IllegalArgumentException()
      case firstName :: names =>
        for
          firstNamePart <- namePart(firstName)
          argsAndRestNameParts <- P.lift(
            names.map(name => P.lift((p, namePart(name)))),
          )
        yield (
          argsAndRestNameParts.map(_(0)),
          firstNamePart :: argsAndRestNameParts.map(_(1)),
        )

  def namePart(s: Seq[String]) = P.lift(
    s.map(s =>
      P.satisfySingle(
        s"'$s'",
        n => nn.asString(n) == s,
      ),
    ).toList,
  )

  expr << P.eos
