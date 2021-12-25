package io.github.tgeng.archon.parser.mixfix

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

import io.github.tgeng.archon.parser.mixfix.Fixity.*

case class Operator(namespace: QualifiedName, fixity: Fixity, nameParts: List[String]):
  def operatorName : String =
    val rawName = nameParts.mkString("_")
    fixity match
      case Closed => rawName
      case Prefix => rawName + "_"
      case Postfix => "_" + rawName
      case Infix(_) => "_" + rawName + "_"

  override def toString: String = namespace.toString + "." + operatorName
object Operator:
  def apply(qualifiedName: QualifiedName, fixity: Fixity, nameParts: List[String]): Operator =
    if nameParts.isEmpty then throw IllegalArgumentException("nameParts should not be empty")
    if fixity == Closed && nameParts.size == 1 then throw IllegalArgumentException("for closed operator the nameParts must contain at least 2 elements")
    new Operator(qualifiedName, fixity, nameParts)

/**
 * Operators in neighbor nodes binds tighter than operators in this node. Note that there must
 * not be cycles. Implementation should be immutable.
 */
trait PrecedenceNode:
  def operators: Map[Fixity, Set[Operator]]
  def neighbors: Set[PrecedenceNode]

/**
 * A DAG.
 */
type PrecedenceGraph = Seq[PrecedenceNode]

trait NamePart[N]:
  def asString(n: N): String

enum MixfixAst[N, L]:
  case OperatorCall(operator: Operator, args: List[MixfixAst[N, L]], nameParts: List[N])
  case ApplyCall(args: List[MixfixAst[N, L]])
  case Identifier(name: N)
  case Literal(literal: L)

  override def toString: String = this match
    case OperatorCall(op, args, nameParts) => op.fixity match
      case Closed => (interleave(nameParts, args) :+ nameParts.last).mkString("[", " ", "]")
      case Prefix => interleave(nameParts, args).mkString("[", " ", "]")
      case Postfix => interleave(args, nameParts).mkString("[", " ", "]")
      case Infix(_) => (interleave(args, nameParts) :+ args.last).mkString("[", " ", "]")
    case ApplyCall(args) => args.mkString("[@ ", " ", "]")
    case Identifier(name) => "`" + name.toString + "`"
    case Literal(literal) => literal.toString

  private def interleave[T](s1: Seq[T], s2: Seq[T]) : Seq[T] = s1.zip(s2).flatMap(_.toList)

import io.github.tgeng.archon.parser.mixfix.MixfixAst.*

// TODO: filter operators by name part. This can be done by creating another info parser for
//  querying available name parts in the input and then create the second parser based on this info.
def createMixfixParser[N, M[+_], L](g: PrecedenceGraph, literalParser: ParserT[N, L, M])(using pm: MonadPlus[ParserM[N, M]])(using mm: MonadPlus[M])(using env: MonadPlus[ParseResultM[M]])(using nn: NamePart[N]): ParserT[N, MixfixAst[N, L], M] =
  def union[T](parsers: Iterable[ParserT[N, T, M]]) : ParserT[N, T, M] = parsers.reduceOption(_ | _).getOrElse(P.fail("<tighter ops>"))
  def expr: ParserT[N, MixfixAst[N, L], M] = union(g.map(pHat)) | closedPlus

  extension (node: PrecedenceNode)
    def pHat: ParserT[N, MixfixAst[N, L], M] = P(
      (node.pUp, node.op(Infix(Associativity.Non)), node.pUp).map((preArg, t, postArg) => OperatorCall(t(0), preArg +: t(1) :+ postArg, t(2))) |
        // somehow type inferencing is not working here and requires explicit type arguments
        P.foldRight1[(Operator, List[MixfixAst[N, L]], List[N]), MixfixAst[N, L]](pRight, P.pure((t, postArg) => OperatorCall(t(0), t(1) :+ postArg, t(2))), pUp) |
        P.foldLeft1[MixfixAst[N, L], (Operator, List[MixfixAst[N, L]], List[N])](pUp, P.pure((preArg, t) => OperatorCall(t(0), preArg +: t(1), t(2))), pLeft)
    )

    def pRight: ParserT[N, (Operator, List[MixfixAst[N, L]], List[N]), M] = P(node.op(Prefix) |
      (node.pUp, node.op(Infix(Associativity.Right))).map((preArg, t) => (t(0), preArg +: t(1), t(2))))

    def pLeft: ParserT[N, (Operator, List[MixfixAst[N, L]], List[N]), M] = P(node.op(Postfix) |
      (node.op(Infix(Associativity.Left)), node.pUp).map((t, postArg) => (t(0), t(1) :+ postArg, t(2))))

    def pUp: ParserT[N, MixfixAst[N, L], M] = P(union(node.neighbors.map(_.pHat)) | closedPlus)

    def op(fix: Fixity): ParserT[N, (Operator, List[MixfixAst[N, L]], List[N]), M] = P(
      union(node.operators.getOrElse(fix, Set())
        .map(operator => between(expr, operator.nameParts).map((args, nameParts) => (operator, args, nameParts))))
    )

  def closedPlus: ParserT[N, MixfixAst[N, L], M] = P(closed.+.map(args => if args.size == 1 then args(0) else ApplyCall(args)))

  def closed: ParserT[N, MixfixAst[N, L], M] = P(
    // prefer literal over closed operator and literal
    literalParser.map(Literal.apply) ||
    union(g.map(node => node.op(Closed).map((op, args, nameParts) => OperatorCall(op, args, nameParts)))) ||
    P.any.map(Identifier.apply)
  )

  def between[T](p: => ParserT[N, T, M], nameParts: List[String]): ParserT[N, (List[T], List[N]), M] =
    nameParts match
      case Nil => throw IllegalArgumentException()
      case firstName :: names =>
        for
          firstNamePart <- namePart(firstName)
          argsAndRestNameParts <- P.lift(names.map(name => P.lift((p, namePart(name)))))
        yield
          (argsAndRestNameParts.map(_ (0)), firstNamePart :: argsAndRestNameParts.map(_ (1)))

  def namePart(s: String) = P.satisfySingle(s"'$s'", n => nn.asString(n) == s)

  expr << P.eos
