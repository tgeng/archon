package io.github.tgeng.archon.common

import java.io.{BufferedWriter, File, FileWriter}

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

extension[T <: AutoCloseable] (t: T)
  def use[S](block:T => S) : S =
    try
      block(t)
    finally
      t.close()

extension (f: File)
  infix def / (subPath: String) = new File(f, subPath)
  def write(text: String) = new BufferedWriter(FileWriter(f)).use { writer => writer.write(text) }
