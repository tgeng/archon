package io.github.tgeng.archon.parser

import io.github.tgeng.archon.common.*

import scala.collection.mutable

case class Precedence(operator: Operator, kind: PrecedenceKind)

enum PrecedenceKind:
  case TighterThan, LooserThan, SameAs

class PrecedenceGraphBuilder
(
  private val representatives: mutable.Map[Operator, Operator] = mutable.Map(),

  /**
   * Maps from a representative operator to the representative of the tighter node.
   */
  private val precedenceMap: mutable.Map[Operator, mutable.Set[Operator]] = mutable.Map()
):

  import Precedence.*
  import PrecedenceGraphBuilder.*
  import PrecedenceGraphBuilder.ErrorKind.*
  import PrecedenceKind.*

  def add(operator: Operator, precedences: Seq[Precedence]): Either[Error, Unit] =
    def error(kind: ErrorKind) = Left(new Error(operator, kind))

    if representatives.contains(operator) then return error(AlreadyExist)
    val sameAsOperators = precedences.flatMap(p => p.kind match
      case SameAs => Set(representatives(p.operator))
      case _ => Set()
    )
    val representative = sameAsOperators.size match
      case 0 => operator
      case 1 => representatives(sameAsOperators.head)
      case _ => return error(ConflictingAdd(sameAsOperators.toSet))

    val tighterThanOperators = precedences.flatMap(p => p.kind match
      case TighterThan => Set(representatives(p.operator))
      case _ => Set()
    ).toSet
    val looserThanOperators = precedences.flatMap(p => p.kind match
      case LooserThan => Set(representatives(p.operator))
      case _ => Set()
    ).toSet

    val loop = detectLoop(precedenceMap.keys, op =>
      val neighbors = precedenceMap(op).to(mutable.Set)
      if op == representative then neighbors.addAll(looserThanOperators)
      if tighterThanOperators.contains(op) then neighbors.add(representative)
      neighbors
    )
    loop match
      case Some(loop) => return error(LoopDetected(loop))
      case _ => ()

    representatives(operator) = representative
    tighterThanOperators.foreach(o => precedenceMap.getOrElseUpdate(o, mutable.Set()).add(representative))
    looserThanOperators.foreach(o => precedenceMap.getOrElseUpdate(representative, mutable.Set()).add(o))
    Right(())

  def build(filter: Operator => Boolean = _ => true): PrecedenceGraph =
    val nodes: Map[Operator, Iterable[Operator]] = this.representatives.groupMap(_ (1))(_ (0))
    val precedenceMap = this.precedenceMap.view.mapValues(_.toSet).toMap
    val nodePrecedenceMap = mutable.Map[PrecedenceNode, Set[PrecedenceNode]]()
    val operatorToNodeMap = nodes.map((representative, operators) =>
      val operatorsMap = operators.toSet.filter(filter).groupBy(_.fixity)
      (representative, new PrecedenceNode {
        override def operators: Map[Fixity, Set[Operator]] = operatorsMap

        override def neighbors: Set[PrecedenceNode] = nodePrecedenceMap(this).bfs(nodePrecedenceMap).iterator.toSet
      })
    )
    precedenceMap.foreach((k, v) =>
      nodePrecedenceMap(operatorToNodeMap(k)) = v.map(operatorToNodeMap)
    )
    nodePrecedenceMap.keys.toSet

  override def clone(): PrecedenceGraphBuilder = new PrecedenceGraphBuilder(representatives.clone(), precedenceMap.clone())

object PrecedenceGraphBuilder {
  class Error(operator: Operator, kind: ErrorKind)

  enum ErrorKind:
    case AlreadyExist
    case ConflictingAdd(distinctOperators: Set[Operator])
    case LoopDetected(loop: Seq[Operator])
}
