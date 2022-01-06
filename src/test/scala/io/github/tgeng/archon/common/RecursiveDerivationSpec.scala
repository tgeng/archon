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

  enum WideTree derives Recursive:
    case WNode(children: List[WideTree])
    case WTupleNode(t: (Int, WideTree))
    case WLeaf(i: Int)
  import WideTree.*

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

  "wide tree" in {
      assert(Recursive.transform(
        WNode(List(WLeaf(1), WNode(List(WLeaf(2), WLeaf(3))), WTupleNode((1, WLeaf(5))))),
        {
          case WLeaf(i) =>
            if i % 2 == 1 then
              Some(WLeaf(i * 2))
            else
              None
          case _ => None
        }) == WNode(List(WLeaf(2), WNode(List(WLeaf(2), WLeaf(6))), WTupleNode((1, WLeaf(10)))))
    )
  }

//  enum ParameterizedTree[T] derives Recursive:
//    case PNode(left: ParameterizedTree[T], right: ParameterizedTree[T])
//    case PLeaf(t: T)
//  import ParameterizedTree.*
//
//  "parameterized tree" in {
//    val input : ParameterizedTree[Int] = PNode(PLeaf(1), PNode(PLeaf(2), PLeaf(3)))
//    val output : ParameterizedTree[Int] = PNode(PLeaf(2), PNode(PLeaf(2), PLeaf(6)))
//    assert(
//      Recursive.transform(input, {
//        case PLeaf(i) =>
//          if i % 2 == 1 then
//            Some(PLeaf(i * 2))
//          else
//            None
//        case _ => None
//      }) == output
//    )
//  }
