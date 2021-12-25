package io.github.tgeng.archon.common

import java.io.{BufferedWriter, File, FileWriter}
import java.nio.charset.StandardCharsets
import java.nio.file.Files
import scala.collection.mutable

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
  def read() = String.join("\n", Files.readAllLines(f.toPath, StandardCharsets.UTF_8)).!!
  def write(text: String) = new BufferedWriter(FileWriter(f)).use { writer => writer.write(text) }

extension[E] (nodes: IterableOnce[E])
  def bfs(getNeighbors: E => IterableOnce[E], seen: mutable.Set[E] = mutable.Set[E]()) : IterableOnce[E] =
      val queue = mutable.Queue(nodes.iterator.toSeq : _*)
      seen.addAll(queue)
      new Iterator[E]:
        def hasNext: Boolean = queue.nonEmpty
        def next(): E =
          val e = queue.dequeue()
          queue.enqueueAll(getNeighbors(e).iterator.filter(e => seen.add(e)))
          e

  def detectLoop(getNeighbors: E => IterableOnce[E]): Option[Seq[E]] =
    val stack = mutable.Stack[(E, Int)](nodes.iterator.map(n => (n, 0)).toSeq : _*)
    val parents = mutable.LinkedHashSet[E]()
    val safeNodes = mutable.Set[E]()
    while stack.nonEmpty do
      val (t, index) = stack.pop()
      while index != parents.size do
        safeNodes.add(parents.last)
        parents.remove(parents.last)
      if parents.contains(t) then
        return Some(parents.dropWhile(_ != t).toSeq)
      parents.add(t)
      getNeighbors(t).iterator.filterNot(safeNodes).foreach(t => stack.push((t, index + 1)))
    None

extension (s: String)
  def removeSuffix(suffix: String) = if s.endsWith(suffix) then s.dropRight(suffix.length) else s
  def split2(regex: String) = s.split(regex).asInstanceOf[Array[String]]

extension[T] (inline t: T)
  inline def debug : T =
    println(stringify(t) + " = " + t)
    t
