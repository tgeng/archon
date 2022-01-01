package io.github.tgeng.archon.common

import org.scalatest.freespec.AnyFreeSpec

class FunctorDerivationSpec extends AnyFreeSpec:
  enum Tree[T] derives Functor:
    case Branch(left: Tree[T], right: Tree[T])
    case Leaf(elem: T)
  import Tree.*

  "tree" in {
    assert(
      Functor.map(Branch(Leaf(1), Branch(Leaf(2), Leaf(3))), _ + 1) ==
      Branch(Leaf(2), Branch(Leaf(3), Leaf(4)))
    )
  }

  case class Blob[T](s: String, t: T, listT: List[T], setT: Set[T], optionT: Option[T], eitherT: Either[String, T], i: Int, listInt: List[Int])

  "blob" in {
    assert(
      Functor.map(Blob("1", 2, List(3, 4), Set(5, 6), Some(7), Right(8), 9, List(10, 11)), - _) ==
        Blob("1", -2, List(-3, -4), Set(-5, -6), Some(-7), Right(-8), 9, List(10, 11))
    )
  }

