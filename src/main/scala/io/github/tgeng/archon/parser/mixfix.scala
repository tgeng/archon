package io.github.tgeng.archon.parser

enum Associativity:
  case Left, Right, Non

enum Fixity:
  case Prefix
  case Infix[A <: Associativity](val associativity: A)
  case Postfix
  case Closed

case class Operator[F <: Fixity](fixity: F, nameParts: List[String])

trait PrecedenceNode():
  def getOperators(fixity: Fixity): Set[Operator[fixity.type]]

/**
 * @param nodes values nodes have higher precedence (binds tighter) than keys
 */
case class PrecedenceGraph(nodes: Map[PrecedenceNode, Set[PrecedenceNode]])




