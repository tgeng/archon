package com.github.tgeng.archon.common

import java.io.{BufferedWriter, File, FileWriter}
import java.nio.charset.StandardCharsets
import java.nio.file.Files
import scala.collection.mutable
import scala.math.max
import scala.util.control.NonLocalReturns.*

trait Ref[T]:
  def value: T

  def value_=(t: T): Unit

  override def toString: String = s"Ref@${hashCode}=$value"

class MutableRef[T](var value: T) extends Ref[T]

class ImmutableRef[T](val value: T) extends Ref[T] :
  override def value_=(t: T) = throw UnsupportedOperationException()

object Ref:
  given[T]: Conversion[T, Ref[T]] = MutableRef(_)

  given[T]: Conversion[Ref[T], T] = _.value

extension[T] (t: T | Null)
  inline def !! : T =
    assert(t != null)
    t.asInstanceOf[T]

  inline def ifNullUse(default: T) = if (t == null) default else t
  inline def ifNotNull[R](fn: T => R) = if (t == null) null else fn(t)

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
  def use[S](block: T => S): S =
    try
      block(t)
    finally
      t.close()

extension[E] (startingNodes: IterableOnce[E])
  def bfs(
    getNeighbors: E => IterableOnce[E],
    seen: mutable.Set[E] = mutable.Set[E]()
  ): IterableOnce[E] =
    val queue = mutable.Queue(startingNodes.iterator.toSeq: _*)
    seen.addAll(queue)
    new Iterator[E] :
      def hasNext: Boolean = queue.nonEmpty

      def next(): E =
        val e = queue.dequeue()
        queue.enqueueAll(getNeighbors(e).iterator.filter(e => seen.add(e)))
        e

/** [[nodes]] may or may not contain every single nodes in the graph. */
extension[E] (nodes: IterableOnce[E])
  def detectLoop(getNeighbors: E => IterableOnce[E]): Option[Seq[E]] =
    val stack = mutable.Stack[(E, Int)](nodes.iterator.map(n => (n, 0)).toSeq: _*)
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
    for node <- allNodes.iterator do
      for neighbor <- getNeighbors(node).iterator do
        inDegree(neighbor) += 1
      if !inDegree.contains(node) then inDegree(node) = 0
    val maxIncomingPathLengths = mutable.Map[E, Int]().withDefaultValue(0)
    val queue = mutable.Queue(inDegree.filter((_, inDegree) => inDegree == 0).keys.toSeq: _*)
    assert(queue.nonEmpty)
    val maxDegreeForDag = inDegree.size * (inDegree.size - 1)
    while queue.nonEmpty do
      val node = queue.dequeue()
      for neighbor <- getNeighbors(node).iterator do
        maxIncomingPathLengths(neighbor) = max(
          maxIncomingPathLengths(node) + 1,
          maxIncomingPathLengths(neighbor)
        )
        if maxIncomingPathLengths(neighbor) > maxDegreeForDag then throw IllegalArgumentException()
        queue.enqueue(neighbor)
    maxIncomingPathLengths.toMap.withDefaultValue(0)

extension (s: String)
  def split2(regex: String) = s.split(regex).asInstanceOf[Array[String]]

extension[T] (inline t: T)
  inline def show: T =
    println(stringify(t) + " = " + t)
    t

  inline def print: T =
    println(t)
    t

  inline def printIf(predicate: T => Boolean): T =
    if predicate(t) then println(t)
    t

  inline def systemId: Int = System.identityHashCode(t)

def caching[A, B](f: A => B): A => B =
  val cache = mutable.Map[A, B]()
  a => cache.getOrElseUpdate(a, f(a))

extension[T] (elems: IterableOnce[T])
  def first[R](f: T => Option[R]): Option[R] = returning {
    for elem <- elems.iterator do
      f(elem) match
        case r: Some[R] => throwReturn[Option[R]](r)
        case _ =>
    None
  }

  def getFirstOrDefault(predicate: T => Boolean, default: => T): T = returning {
    for elem <- elems.iterator do
      if predicate(elem) then throwReturn[T](elem)
    default
  }

  def associatedBy[K](keyExtractor: T => K): Map[K, T] =
    val result = mutable.Map[K, T]()
    for elem <- elems.iterator do
      result(keyExtractor(elem)) = elem
    result.toMap

  def associatedBy[K, V](keyExtractor: T => K, valueExtractor: T => V): Map[K, V] =
    val result = mutable.Map[K, V]()
    for elem <- elems.iterator do
      result(keyExtractor(elem)) = valueExtractor(elem)
    result.toMap

def swap[A, B](t: (A, B)): (B, A) = t match
  case (a, b) => (b, a)

def transpose[A](l: List[Option[A]]): Option[List[A]] = l match
  case Nil => Some(Nil)
  case e :: l => e match
    case None => None
    case Some(e) => transpose(l).map(l => e :: l)

def transpose[A](l: IndexedSeq[Option[A]]): Option[IndexedSeq[A]] = transpose(l.toList).map(_.toIndexedSeq)

def transpose[L, R](l: List[Either[L, R]]): Either[L, List[R]] = l match
  case Nil => Right(Nil)
  case e :: l => e match
    case Left(l) => Left(l)
    case Right(r) => transpose(l).map(l => r :: l)

def transpose[L, R](l: Set[Either[L, R]]): Either[L, Set[R]] =
  transpose(l.toList).map(Set(_: _*))

def transposeValues[K, L, R](m: Map[K, Either[L, R]]): Either[L, Map[K, R]] =
  transpose(
    m.toList.map { (k, v) =>
      v match
        case Right(r) => Right((k, r))
        case Left(l) => Left(l)
    }
  ).map(Map.from)

def topologicalSort[T](ts: Seq[T])
  (getDeps: T => Seq[T]): Either[ /* cycle */ Seq[T], /* sorted */ Seq[T]] =
  object CycleException extends Exception
  val visited = mutable.ArrayBuffer[T]()
  val visitedSet = mutable.Set[T]()
  val visiting = mutable.ArrayBuffer[T]()
  val visitingSet = mutable.Set[T]()

  def dfs(t: T): Unit =
    if visitedSet(t) then return
      if visitingSet(t) then throw CycleException
    visiting.addOne(t)
    visitedSet.add(t)
    val deps = getDeps(t)
    for dep <- deps do
      dfs(dep)
    visiting.dropRightInPlace(1)
    visitingSet.remove(t)
    visited.addOne(t)
    visitedSet.add(t)

  try {
    for t <- ts do dfs(t)
    Right(visited.toSeq)
  } catch {
    case _: CycleException.type => Left(visiting.toSeq)
  }

/**
 * Non negative int. Note that this is only a visual hint and nothing actually checks this.
 */
type Nat = Int

type Multiset[T] = Map[T, Nat]

extension[T] (ts: Iterable[T])
  def toMultiset: Multiset[T] = ts.groupMapReduce(t => t)(_ => 1)(_ + _)

extension[T] (ms: Multiset[T])
  def multiMap[R](f: T => R): Multiset[R] = ms.map((k, v) => (f(k), v))
  def multiToSeq: Seq[T] = ms.toSeq.flatMap((t, count) => Seq.fill(count)(t))

def flattenMultisets[T](ms: Iterable[Multiset[T]]): Multiset[T] =
  ms.flatten.groupMapReduce(_._1)(_._2)(_ + _)

def multisetOf[T](ts: T*): Multiset[T] = ts.groupMapReduce(t => t)(_ => 1)(_ + _)
