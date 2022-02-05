package io.github.tgeng.archon.bir

import io.github.tgeng.archon.common.QualifiedName

import scala.collection.mutable

class StackMachine(val stack: mutable.ArrayBuffer[CTerm],
                   val handlerIndex: mutable.Map[QualifiedName, Int],
                   val heap: mutable.Map[HeapKey, mutable.Map[CellKey, VTerm]],
                   val signature: Signature,
                   val useCaseTree: Boolean):

  def reduce(): CTerm = ???

extension (c: CTerm)
  def reduce(useCaseTree: Boolean = false)(using signature: Signature) = StackMachine(
    mutable.ArrayBuffer(c),
    mutable.Map(),
    mutable.Map(),
    signature,
    useCaseTree
  ).reduce()