package io.github.tgeng.archon.common

import java.io.{BufferedWriter, File, FileWriter}
import java.nio.charset.StandardCharsets
import java.nio.file.Files
import scala.collection.mutable
import scala.math.max

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

extension[E] (startingNodes: IterableOnce[E])
  def bfs(getNeighbors: E => IterableOnce[E], seen: mutable.Set[E] = mutable.Set[E]()) : IterableOnce[E] =
      val queue = mutable.Queue(startingNodes.iterator.toSeq : _*)
      seen.addAll(queue)
      new Iterator[E]:
        def hasNext: Boolean = queue.nonEmpty
        def next(): E =
          val e = queue.dequeue()
          queue.enqueueAll(getNeighbors(e).iterator.filter(e => seen.add(e)))
          e

/** [[nodes]] may or may not contain every single nodes in the graph. */
extension[E] (nodes: IterableOnce[E])
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

extension[E] (allNodes: IterableOnce[E])
  def getMaxIncomingPathLength(getNeighbors: E => IterableOnce[E]): Map[E, Int] =
    val inDegree = mutable.Map[E, Int]().withDefaultValue(0)
    for node <- allNodes do
      for neighbor <- getNeighbors(node) do
        inDegree(neighbor) += 1
      if !inDegree.contains(node) then inDegree(node) = 0
    val maxIncomingPathLengths = mutable.Map[E, Int]().withDefaultValue(0)
    val queue = mutable.Queue(inDegree.filter((_, inDegree) => inDegree == 0).keys.toSeq : _*)
    assert(queue.nonEmpty)
    val maxDegreeForDag = inDegree.size * (inDegree.size - 1)
    while queue.nonEmpty do
      val node = queue.dequeue()
      for neighbor <- getNeighbors(node) do
        maxIncomingPathLengths(neighbor) = max(maxIncomingPathLengths(node) + 1, maxIncomingPathLengths(neighbor))
        if maxIncomingPathLengths(neighbor) > maxDegreeForDag then throw IllegalArgumentException()
        queue.enqueue(neighbor)
    maxIncomingPathLengths.toMap.withDefaultValue(0)

extension (s: String)
  def split2(regex: String) = s.split(regex).asInstanceOf[Array[String]]

extension[T] (inline t: T)
  inline def debug: T =
    println(stringify(t) + " = " + t)
    t

  inline def print: T =
    println(t)
    t

  inline def printIf(condition: Boolean): T =
    if condition then println(t)
    t
