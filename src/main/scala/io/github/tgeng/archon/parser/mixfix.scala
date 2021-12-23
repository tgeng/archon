package io.github.tgeng.archon.parser

import io.github.tgeng.archon.common.*
import io.github.tgeng.archon.parser.combinators.{*, given}

// This implementation follows from this paper https://www.cse.chalmers.se/~nad/publications/danielsson-norell-mixfix.pdf
enum Associativity:
  case Left, Right, Non

enum Fixity:
  case Prefix
  case Infix(val associativity: Associativity)
  case Postfix

  /**
   * Note that an operator of this fixity should have at least one hole inside, for example `[_]`.
   * In other words, atoms like `myVariable` should not be represented as an operator but simply an
   * [[MixfixAst.Identifier]] instead.
   */
  case Closed

import io.github.tgeng.archon.parser.Fixity.*

case class Operator(namespace: QualifiedName, fixity: Fixity, nameParts: List[String])
object Operator:
  def apply(qualifiedName: QualifiedName, fixity: Fixity, nameParts: List[String]): Operator =
    if nameParts.isEmpty then throw IllegalArgumentException("nameParts should not be empty")
    if fixity == Closed && nameParts.size == 1 then throw IllegalArgumentException("for closed operator the nameParts must contain at least 2 elements")
    new Operator(qualifiedName, fixity, nameParts)

/**
 * Operators in neighbor nodes binds tighter than operators in this node. Note that there must
 * not be cycles.
 */
class PrecedenceNode(val operators: Map[Fixity, Set[Operator]], val neighbors: Set[PrecedenceNode])

/**
 * A DAG.
 */
type PrecedenceGraph = Set[PrecedenceNode]

trait NamePart[N]:
  def asString(n: N): String

enum MixfixAst[N]:
  case OperatorCall(operator: Operator, args: List[MixfixAst[N]], nameParts: List[N])
  case ApplyCall(args: List[MixfixAst[N]])
  case Identifier(name: N)

import io.github.tgeng.archon.parser.MixfixAst.*

def createMixfixParser[N, M[+_]](g: PrecedenceGraph)(using pm: MonadPlus[ParserM[N, M]])(using mm: MonadPlus[M])(using nn: NamePart[N]): ParserT[N, MixfixAst[N], M] =
  def expr: ParserT[N, MixfixAst[N], M] = g.map(pHat).reduce(_ | _) | closedPlus

  extension (node: PrecedenceNode)
    def pHat: ParserT[N, MixfixAst[N], M] = P(
      (node.pUp, node.op(Infix(Associativity.Non)), node.pUp).map((preArg, t, postArg) => OperatorCall(t(0), preArg +: t(1) :+ postArg, t(2))) |
        P.foldRight1(pRight, P.pure((t, postArg) => OperatorCall(t(0), t(1) :+ postArg, t(2))), pUp) |
        // somehow type inferencing is not working here and requires explicit type arguments
        P.foldLeft1[MixfixAst[N], (Operator, List[MixfixAst[N]], List[N])](pUp, P.pure((preArg, t) => OperatorCall(t(0), preArg +: t(1), t(2))), pLeft)
    )

    def pRight: ParserT[N, (Operator, List[MixfixAst[N]], List[N]), M] = P(node.op(Prefix) | (node.pUp, node.op(Infix(Associativity.Right))).map((preArg, t) => (t(0), preArg +: t(1), t(2))))

    def pLeft: ParserT[N, (Operator, List[MixfixAst[N]], List[N]), M] = P(node.op(Postfix) | (node.op(Infix(Associativity.Right)), node.pUp).map((t, postArg) => (t(0), t(1) :+ postArg, t(2))))

    def pUp: ParserT[N, MixfixAst[N], M] = P(node.neighbors.map(_.pHat).reduce(_ | _) | closedPlus)

    def op(fix: Fixity): ParserT[N, (Operator, List[MixfixAst[N]], List[N]), M] = P(
      node.operators(fix)
        .map(operator => between(expr, operator.nameParts).map((args, nameParts) => (operator, args, nameParts)))
        .reduce(_ | _)
    )

  def closedPlus: ParserT[N, MixfixAst[N], M] = P(closed.+ map ApplyCall.apply)

  def closed: ParserT[N, MixfixAst[N], M] = P(
    g.map(node => node.op(Closed).map((op, args, nameParts) => OperatorCall(op, args, nameParts))).reduce(_ | _) |
    P.any.map(Identifier.apply)
  )

  def between[T](p: => ParserT[N, T, M], nameParts: List[String]): ParserT[N, (List[T], List[N]), M] =
    nameParts match
      case Nil => throw IllegalArgumentException()
      case firstName :: names =>
        for
          firstNamePart <- namePart(firstName)
          argsAndRestNameParts <- P.lift(nameParts.map(name => P.lift((p, namePart(name)))))
        yield
          (argsAndRestNameParts.map(_ (0)), firstNamePart :: argsAndRestNameParts.map(_ (1)))

  def namePart(s: String) = P.satisfySingle(s"'$s'", n => nn.asString(n) == s)

  expr
