package io.github.tgeng.archon.common

import org.scalatest.freespec.AnyFreeSpec

class RecursiveDerivationSpec extends AnyFreeSpec:
  enum Tree derives Recursive:
    case Leaf(i: Int)
    case Node(left: Tree, right: Tree)
  import Tree.*

  enum Tree2 derives Recursive:
    case Leaf2(i: Int)
    case Node2(left: Tree2, right: Tree)
  import Tree2.*

  "recursive tree" in {
    assert(
      Recursive.transform(Node(Leaf(1), Node(Leaf(2), Leaf(3))), {
        case Leaf(i) =>
          if i % 2 == 1 then
            Some(Leaf(i * 2))
          else
            None
        case _ => None
      }) == Node(Leaf(2), Node(Leaf(2), Leaf(6)))
    )
  }

  "recursive tree2" in {
    assert(
      Recursive.transform(Node2(Leaf2(1), Node(Leaf(2), Leaf(3))), {
        case Leaf2(i) =>
          if i % 2 == 1 then
            Some(Leaf2(i * 2))
          else
            None
        case _ => None
      }) == Node2(Leaf2(2), Node(Leaf(2), Leaf(3)))
    )
  }
