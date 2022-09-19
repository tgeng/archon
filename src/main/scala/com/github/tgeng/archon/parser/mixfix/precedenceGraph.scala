package com.github.tgeng.archon.parser.mixfix

import com.github.tgeng.archon.common.*
import com.github.tgeng.archon.parser.mixfix.PrecedenceGraphBuilder.*
import com.github.tgeng.archon.parser.mixfix.PrecedenceGraphBuilder.ErrorKind.*
import com.github.tgeng.archon.parser.mixfix.PrecedenceGraphBuilder.Precedence.*
import com.github.tgeng.archon.parser.mixfix.PrecedenceGraphBuilder.PrecedenceKind.*

import scala.collection.mutable

class PrecedenceGraphBuilder
  (
    private val representatives: mutable.Map[Operator, Operator] =
      mutable.Map(),

    /** Maps from a representative operator to the representative of the tighter
      * node.
      */
    private val precedenceMap: mutable.Map[Operator, mutable.ArrayBuffer[
      Operator
    ]] = mutable.Map()
  ):

  def add
    (operator: Operator, precedences: Seq[Precedence])
    : Either[PrecedenceGraphError, Unit] =
    def error(kind: ErrorKind) = Left(PrecedenceGraphError(operator, kind))

    if representatives.contains(operator) then return error(AlreadyExist)
    val sameAsOperators = precedences.flatMap(p =>
      p.kind match
        case SameAs => Seq(representatives(p.operator))
        case _      => Seq()
    )
    val representative = sameAsOperators.size match
      case 0 => operator
      case 1 => representatives(sameAsOperators.head)
      case _ => return error(ConflictingAdd(sameAsOperators))

    val tighterThanOperators = precedences.flatMap(p =>
      p.kind match
        case TighterThan => Seq(representatives(p.operator))
        case _           => Seq()
    )
    val looserThanOperators = precedences.flatMap(p =>
      p.kind match
        case LooserThan => Seq(representatives(p.operator))
        case _          => Seq()
    )

    val loop = precedenceMap.keys.detectLoop(op =>
      val neighbors = precedenceMap.getOrElse(op, Set()).to(mutable.Set)
      if op == representative then neighbors.addAll(looserThanOperators)
      if tighterThanOperators.contains(op) then neighbors.add(representative)
      neighbors
    )
    loop match
      case Some(loop) => return error(LoopDetected(loop))
      case _          => ()

    representatives(operator) = representative
    tighterThanOperators.foreach(o =>
      precedenceMap
        .getOrElseUpdate(o, mutable.ArrayBuffer())
        .append(representative)
    )
    looserThanOperators.foreach(o =>
      precedenceMap
        .getOrElseUpdate(representative, mutable.ArrayBuffer())
        .append(o)
    )
    Right(())

  def build(filter: Operator => Boolean = _ => true): PrecedenceGraph =
    import math.Ordering.Implicits.seqOrdering
    val nodes: Map[Operator, Iterable[Operator]] =
      this.representatives.groupMap(_(1))(_(0))
    val maxIncomingPathLengths = nodes.keys.getMaxIncomingPathLength(
      this.precedenceMap.withDefaultValue(mutable.ArrayBuffer())
    )
    // Remove unnecessary edges in the graph
    this.precedenceMap.foreach((op, ops) =>
      ops.subtractAll(
        ops.filter(o =>
          maxIncomingPathLengths(o) != maxIncomingPathLengths(op) + 1
        )
      )
    )
    val precedenceMap = this.precedenceMap.view.mapValues(_.toSeq).toMap
    val nodePrecedenceMap =
      mutable.Map[PrecedenceNode, Seq[PrecedenceNode]]().withDefaultValue(Seq())
    val operatorToNodeMap = nodes.map((representative, operators) =>
      val operatorsMap =
        operators.filter(filter).toSeq.sortBy(_.nameParts).groupBy(_.fixity)
      (
        representative,
        new PrecedenceNode:
          override def operators: Map[Fixity, Seq[Operator]] = operatorsMap

          override def neighbors: Seq[PrecedenceNode] =
            nodePrecedenceMap(this).bfs(nodePrecedenceMap).iterator.toSeq

          override def toString: String =
            representative.toString + "->" + precedenceMap.getOrElse(
              representative,
              Nil
            )
      )
    )
    precedenceMap.foreach((k, v) =>
      nodePrecedenceMap(operatorToNodeMap(k)) = v.map(operatorToNodeMap)
    )
    // TODO: topologically sort this so that lower nodes are visited first. This makes it faster to
    // yield the correct AST with the mixfix parser.
    nodes.keys.toSeq.sortBy(maxIncomingPathLengths).map(operatorToNodeMap)

  override def clone(): PrecedenceGraphBuilder =
    new PrecedenceGraphBuilder(representatives.clone(), precedenceMap.clone())

object PrecedenceGraphBuilder:
  case class PrecedenceGraphError(operator: Operator, kind: ErrorKind)

  enum ErrorKind:
    case AlreadyExist
    case ConflictingAdd(distinctOperators: Seq[Operator])
    case LoopDetected(loop: Seq[Operator])

  case class Precedence(operator: Operator, kind: PrecedenceKind)

  enum PrecedenceKind:
    case TighterThan, LooserThan, SameAs

case class PrecedenceRule
  (
    fixity: Fixity,
    operatorNames: Seq[String],
    precedences: List[(PrecedenceKind, String)]
  )

object PrecedenceRule:

  import com.github.tgeng.archon.common.given
  import com.github.tgeng.archon.parser.combinators.{*, given}
  import Fixity.*

  val precedenceRuleParser: StrParser[PrecedenceRule] = P {
    val operatorName: StrParser[String] = "\\p{Graph}+".r
      .map(_.matched)
      .withFilter(s => !s.contains("__"), "<no consecutive _>")
    val operatorNames: StrParser[List[String]] = P.indentedBlockFromHere(
      (operatorName sepBy1 P.whitespacesWithIndent) <%%< P.eob
    )
    val precedence: StrParser[List[(PrecedenceKind, String)]] =
      P.indentedBlock {
        "looser than " >%%> operatorNames.map(_.map((LooserThan, _))) ||
        "tighter than " >%%> operatorNames.map(_.map((TighterThan, _))) ||
        "same as " >%%> operatorNames.map(_.map((SameAs, _)))
      }
    import Fixity.*
    import Associativity.*
    val fixity: StrParser[Fixity] =
      ("closed " as Closed) || ("infixl " as Infix(
        Left
      )) || ("infixr " as Infix(Right)) ||
        ("infix " as Infix(
          Non
        )) || ("prefix " as Prefix) || ("postfix " as Postfix)
    P.indentedBlock {
      P.lift(
        (
          fixity << P.whitespacesWithIndent,
          operatorNames,
          (P.indent >> P.space.++ >> precedence.++.map(_.flatten)) ??
        )
      )
        // Somehow type inference fails here and thinks the above yields `StrParser[Nothing, ...]`
        // instead of `StrParser[Char, ...]`
        .asInstanceOf[StrParser[
          (Fixity, List[String], Option[List[(PrecedenceKind, String)]])
        ]]
        .map(t => PrecedenceRule(t(0), t(1), t(2).getOrElse(Nil)))
    }
  }

  def normalizeOperatorName(name: String, fixity: Fixity): String =
    val noUnderscore = name.stripPrefix("_").stripSuffix("_")
    fixity match
      case Closed   => noUnderscore
      case Infix(_) => s"_${noUnderscore}_"
      case Prefix   => s"_${noUnderscore}"
      case Postfix  => s"_${noUnderscore}"
