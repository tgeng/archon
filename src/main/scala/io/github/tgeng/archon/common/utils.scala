package io.github.tgeng.archon.common

extension[T] (t: T | Null)
  def !! : T =
    assert(t != null)
    t

def indexToLineColumn(input: IndexedSeq[Char], index: Int): (Int, Int) =
  var line = 0
  var column = 0
  for (i <- 0 until scala.math.min(index, input.size)) {
    column += 1
    if (input(i) == '\n') line += 1
    if (input(i) == '\n' || input(i) == '\r') column = 0
  }
  (line, column)
