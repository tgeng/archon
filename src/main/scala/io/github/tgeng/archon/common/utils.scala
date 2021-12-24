package io.github.tgeng.archon.common

import java.io.{BufferedWriter, File, FileWriter}
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
  def write(text: String) = new BufferedWriter(FileWriter(f)).use { writer => writer.write(text) }

extension[E] (it: IterableOnce[E])
  def bfs(gen: E => IterableOnce[E], seen: mutable.Set[E] = mutable.Set[E]()) : IterableOnce[E] =
      val queue = mutable.Queue(it.iterator.toSeq : _*)
      seen.addAll(queue)
      new Iterator[E]:
        def hasNext: Boolean = queue.nonEmpty
        def next(): E =
          val e = queue.dequeue()
          queue.enqueueAll(gen(e).iterator.filter(e => seen.add(e)))
          e

def detectLoop[T](nodes: IterableOnce[T], getNeighbors: T => IterableOnce[T]): Option[Seq[T]] =
  val stack = mutable.Stack[(T, Int)](nodes.iterator.map(n => (n, 0)).toSeq : _*)
  val parents = mutable.LinkedHashSet[T]()
  while stack.nonEmpty do
    val (t, index) = stack.pop()
    if parents.contains(t) then
      return Some(parents.dropWhile(_ != t).toSeq)
    while index != parents.size do
      parents.remove(parents.last)
    parents.add(t)
    getNeighbors(t).iterator.foreach(t => stack.push((t, index + 1)))
  None

extension (s: String)
  def removeSuffix(suffix: String) = if s.endsWith(suffix) then s.dropRight(suffix.length) else s

inline def debug(inline a: Any) =
  println(stringify(a) + " = " + a)