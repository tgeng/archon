package io.github.tgeng.archon.parser.mixfix

import io.github.tgeng.archon.common.*
import io.github.tgeng.archon.parser.mixfix.PrecedenceGraphBuilder.*
import io.github.tgeng.archon.parser.mixfix.PrecedenceGraphBuilder.ErrorKind.*
import io.github.tgeng.archon.parser.mixfix.PrecedenceGraphBuilder.Precedence.*
import io.github.tgeng.archon.parser.mixfix.PrecedenceGraphBuilder.PrecedenceKind.*

import scala.collection.mutable

class PrecedenceGraphBuilder
(
  private val representatives: mutable.Map[Operator, Operator] = mutable.Map(),

  /**
   * Maps from a representative operator to the representative of the tighter node.
   */
  private val precedenceMap: mutable.Map[Operator, mutable.Set[Operator]] = mutable.Map()
):

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
      val neighbors = precedenceMap.get(op).getOrElse(Set()).to(mutable.Set)
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
    val nodePrecedenceMap = mutable.Map[PrecedenceNode, Set[PrecedenceNode]]().withDefaultValue(Set())
    val operatorToNodeMap = nodes.map((representative, operators) =>
      val operatorsMap = operators.toSet.filter(filter).groupBy(_.fixity)
      (representative, new PrecedenceNode {
        override def operators: Map[Fixity, Set[Operator]] = operatorsMap

        override def neighbors: Set[PrecedenceNode] = nodePrecedenceMap(this).bfs(nodePrecedenceMap).iterator.toSet

        override def toString: String = representative.toString
      })
    )
    precedenceMap.foreach((k, v) =>
      nodePrecedenceMap(operatorToNodeMap(k)) = v.map(operatorToNodeMap)
    )
    // TODO: topologically sort this so that lower nodes are visited first. This makes it faster to
    // yield the correct AST with the mixfix parser.
    representatives.values.map(operatorToNodeMap).toSeq

  override def clone(): PrecedenceGraphBuilder = new PrecedenceGraphBuilder(representatives.clone(), precedenceMap.clone())

object PrecedenceGraphBuilder:
  case class Error(operator: Operator, kind: ErrorKind)

  enum ErrorKind:
    case AlreadyExist
    case ConflictingAdd(distinctOperators: Set[Operator])
    case LoopDetected(loop: Seq[Operator])

  case class Precedence(operator: Operator, kind: PrecedenceKind)

  enum PrecedenceKind:
    case TighterThan, LooserThan, SameAs

case class PrecedenceRule(fixity: Fixity, operatorNames: Seq[String], precedences: List[(PrecedenceKind, String)])

object PrecedenceRule:

  import io.github.tgeng.archon.common.given
  import io.github.tgeng.archon.parser.combinators.single.given
  import io.github.tgeng.archon.parser.combinators.{*, given}
  import Fixity.*

  val precedenceRuleParser: StrParser[PrecedenceRule] = P {
    val operatorName = "\\p{Graph}+".r.map(_.matched).withFilter(s => !s.contains("__"), "<no consecutive _>")
    val operatorNames = P.indentedBlockFromHere((operatorName sepBy1 P.whitespacesWithIndent) <%%< P.eob)
    val precedences = P.indentedBlock {
      "looser than " >%%> operatorNames.map(_.map((LooserThan, _))) |
        "tighter than " >%%> operatorNames.map(_.map((TighterThan, _))) |
        "same as " >%%> operatorNames.map(_.map((SameAs, _)))
    }
    import Fixity.*
    import Associativity.*
    val fixity = ("closed " as Closed) | ("infixl " as Infix(Left)) | ("infixr " as Infix(Right)) |
      ("infix " as Infix(Non)) | ("prefix " as Prefix) | ("postfix " as Postfix)
    P.indentedBlock {
      (fixity << P.whitespacesWithIndent, operatorNames, (P.indent >> P.space.+ >> precedences)?)
        .map(t => PrecedenceRule(t(0), t(1), t(2).getOrElse(Nil)))
    }
  }

  def normalizeOperatorName(name: String, fixity: Fixity) : String =
    val noUnderscore = name.stripPrefix("_").stripSuffix("_")
    fixity match
      case Closed => noUnderscore
      case Infix(_) => s"_${noUnderscore}_"
      case Prefix => s"_${noUnderscore}"
      case Postfix => s"_${noUnderscore}"

