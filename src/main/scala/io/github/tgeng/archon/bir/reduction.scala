package io.github.tgeng.archon.bir

import io.github.tgeng.archon.common.QualifiedName

import scala.collection.mutable

class StackMachine(val stack: mutable.Stack[CTerm],
                   val heap: mutable.Map[HeapKey, mutable.Map[CellKey, VTerm]],
                   val signature: Signature,
                   val useCaseTree: Boolean):

  def run(): CTerm =
    while(stack.nonEmpty) {
    }
    ???


extension (c: CTerm)
  def reduce(useCaseTree: Boolean = false)(using signature: Signature) = StackMachine(
    mutable.Stack(c),
    mutable.Map(),
    signature,
    useCaseTree
  ).run()