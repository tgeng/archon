package com.github.tgeng.archon.common

import scala.collection.immutable.SeqMap
import scala.collection.mutable.Builder
import scala.collection.{IterableOps, mutable}
import scala.math.max
import scala.util.boundary
import scala.util.boundary.break

trait Ref[T]:
  def value: T

  def value_=(t: T): Unit

  override def toString: String = s"Ref@${hashCode}=$value"

class MutableRef[T](var value: T) extends Ref[T]

class ImmutableRef[T](val value: T) extends Ref[T]:
  override def value_=(t: T) = throw UnsupportedOperationException()

object Ref:
  given [T]: Conversion[T, Ref[T]] = MutableRef(_)

  given [T]: Conversion[Ref[T], T] = _.value

def indexToLineColumn(input: IndexedSeq[Char], index: Int): (Int, Int) =
  var line = 0
  var column = 0
  for (i <- 0 until scala.math.min(index, input.size)) {
    column += 1
    if (input(i) == '\n') line += 1
    if (input(i) == '\n' || input(i) == '\r') column = 0
  }
  (line, column)

extension [T <: AutoCloseable](t: T)
  def use[S](block: T => S): S =
    try
      block(t)
    finally
      t.close()

extension [E](startingNodes: IterableOnce[E])
  def bfs
    (
      getNeighbors: E => IterableOnce[E],
      seen: mutable.Set[E] = mutable.Set[E](),
    )
    : IterableOnce[E] =
    val queue = mutable.Queue(startingNodes.iterator.toSeq: _*)
    seen.addAll(queue)
    new Iterator[E]:
      def hasNext: Boolean = queue.nonEmpty

      def next(): E =
        val e = queue.dequeue()
        queue.enqueueAll(getNeighbors(e).iterator.filter(e => seen.add(e)))
        e

/** [[nodes]] may or may not contain every single nodes in the graph. */
extension [E](nodes: IterableOnce[E])
  def detectLoop(getNeighbors: E => IterableOnce[E]): Option[Seq[E]] =
    val stack =
      mutable.Stack[(E, Int)](nodes.iterator.map(n => (n, 0)).toSeq: _*)
    val parents = mutable.LinkedHashSet[E]()
    val safeNodes = mutable.Set[E]()
    while stack.nonEmpty do
      val (t, index) = stack.pop()
      while index != parents.size do
        safeNodes.add(parents.last)
        parents.remove(parents.last)
      if parents.contains(t) then return Some(parents.dropWhile(_ != t).toSeq)
      parents.add(t)
      getNeighbors(t).iterator
        .filterNot(safeNodes)
        .foreach(t => stack.push((t, index + 1)))
    None

extension [E](allNodes: IterableOnce[E])
  def getMaxIncomingPathLength(getNeighbors: E => IterableOnce[E]): Map[E, Int] =
    val inDegree = mutable.Map[E, Int]().withDefaultValue(0)
    for node <- allNodes.iterator do
      for neighbor <- getNeighbors(node).iterator do inDegree(neighbor) += 1
      if !inDegree.contains(node) then inDegree(node) = 0
    val maxIncomingPathLengths = mutable.Map[E, Int]().withDefaultValue(0)
    val queue = mutable.Queue(
      inDegree.filter((_, inDegree) => inDegree == 0).keys.toSeq: _*,
    )
    assert(queue.nonEmpty)
    val maxDegreeForDag = inDegree.size * (inDegree.size - 1)
    while queue.nonEmpty do
      val node = queue.dequeue()
      for neighbor <- getNeighbors(node).iterator do
        maxIncomingPathLengths(neighbor) = max(
          maxIncomingPathLengths(node) + 1,
          maxIncomingPathLengths(neighbor),
        )
        if maxIncomingPathLengths(neighbor) > maxDegreeForDag then throw IllegalArgumentException()
        queue.enqueue(neighbor)
    maxIncomingPathLengths.toMap.withDefaultValue(0)

extension (s: String) def split2(regex: String) = s.split(regex).asInstanceOf[Array[String]]

extension [T](inline t: T)
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

extension [T](elems: IterableOnce[T])
  def first[R](f: T => Option[R]): Option[R] = boundary {
    for elem <- elems.iterator do
      f(elem) match
        case r: Some[R] => break[Option[R]](r)
        case _          =>
    None
  }

  def associatedBy[K](keyExtractor: T => K): SeqMap[K, T] =
    val result = mutable.SeqMap[K, T]()
    for elem <- elems.iterator do result(keyExtractor(elem)) = elem
    result.to(SeqMap)

  def associatedBy[K, V]
    (
      keyExtractor: T => K,
      valueExtractor: T => V,
    )
    : SeqMap[K, V] =
    val result = mutable.SeqMap[K, V]()
    for elem <- elems.iterator do result(keyExtractor(elem)) = valueExtractor(elem)
    result.to(SeqMap)

def swap[A, B](t: (A, B)): (B, A) = t match
  case (a, b) => (b, a)

def transpose[A](l: List[Option[A]]): Option[List[A]] = l match
  case Nil => Some(Nil)
  case e :: l =>
    e match
      case None    => None
      case Some(e) => transpose(l).map(l => e :: l)

def transpose[A](l: IndexedSeq[Option[A]]): Option[IndexedSeq[A]] =
  transpose(l.toList).map(_.toIndexedSeq)

def transpose[A](l: Seq[Option[A]]): Option[Seq[A]] =
  transpose(l.toList).map(_.toSeq)

def transpose[L, R](l: List[Either[L, R]]): Either[L, List[R]] = l match
  case Nil => Right(Nil)
  case e :: l =>
    e match
      case Left(l)  => Left(l)
      case Right(r) => transpose(l).map(l => r :: l)

def transpose[L, R](l: Option[Either[L, R]]): Either[L, Option[R]] =
  l match
    case None => Right(None)
    case Some(l) =>
      l match
        case Left(l)  => Left(l)
        case Right(r) => Right(Some(r))

def transpose[L, R](l: Iterable[Either[L, R]]): Either[L, Seq[R]] =
  transpose(l.toList).map(Seq(_: _*))

def transpose[L, R](l: Set[Either[L, R]]): Either[L, Set[R]] =
  transpose(l.toList).map(Set(_: _*))

def transposeValues[K, L, R](m: SeqMap[K, Either[L, R]]): Either[L, SeqMap[K, R]] =
  transpose(
    m.toList.map { (k, v) =>
      v match
        case Right(r) => Right((k, r))
        case Left(l)  => Left(l)
    },
  ).map(SeqMap.from)

def topologicalSort[T]
  (ts: Seq[T])
  (getDeps: T => Seq[T])
// TODO: recursion check during totality check will have to be done on all mutual recursive
//  definitions together. So the sorted result must be Seq[Set[T]] instead.
//  Notes
//  1. recursion check should be done regardless of the declared effects, any presence of
//  (potentially) diverging recursive calls should show up as `div` effect. In other words, one
//  can not omit `div` effect on effectful computation because handlers can swallow non-div
//  effects.
//  2. non-divergemce is much stronger than saying a function is not self-recursive. A
//  non-recursive function may still diverge if it invoke some other divergen computation. It's
//  non-divergence is only true when all computations are non-divergent (also non-recursive).
//  3. there is a problem with heap and parameterized handler: user can store self-reference into
//  a heap var (or emulate heap with handler parameter) and makes a seemingly total function
//  divergent. For example, following f is considered total because it reads a cell value of a
//  total function and invoke it.
//
//  def f: (h: Heap) => (v: Cell (U <total> Nat)) -> Nat
//      f h => return force (getCellValue h v)
//
//  But one can store `f` itself into a cell and pass this cell to `f` to make the function
//  divergent. Maybe it's possible to track some size information in the type so that for a
//  computation to be non-divergent, its component computations must all be "smaller". Also
//  the size of a computation may be considered to be parameterized by the argument. So
//  `fib 1` is "bigger" than `fib 0`. In other words, divergence can arise from non-divergent
//  computations if one or more of the nested computations are "equal size" or "bigger".
//
//  Updated notes:
//  * The issue with self-referencing computations is solved by flagging any `force` as divergent.
//  * In addition to allowing casts to workaround termination checker, it's possible to add some
//    special `timeout` function that takes a duration and a computation, and return an option of
//    the computation result it finishes within the given amount of time.
//  * termination checking can be lazy: if the functions to be checked is already marked divergent,
//    we can just skip the check.
  : Either[ /* cycle */ Seq[T], /* sorted */ Seq[T]] =
  object CycleException extends Exception
  val visited = mutable.ArrayBuffer[T]()
  val visitedSet = mutable.Set[T]()
  val visiting = mutable.ArrayBuffer[T]()
  val visitingSet = mutable.Set[T]()

  def dfs(t: T): Unit =
    if visitedSet(t) then return if visitingSet(t) then throw CycleException
    visiting.addOne(t)
    visitedSet.add(t)
    val deps = getDeps(t)
    for dep <- deps do dfs(dep)
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

/** Non negative int. Note that this is only a visual hint and nothing actually checks this.
  */
type Nat = Int

type Multiset[T] = SeqMap[T, Nat]

extension [T](ts: Iterable[T])
  def toMultiset: Multiset[T] = groupMapReduce(ts)(t => t)(_ => 1)(_ + _)

extension [T](ms: Multiset[T])
  def multiMap[R](f: T => R): Multiset[R] = ms.map((k, v) => (f(k), v))
  def multiToSeq: Seq[T] = ms.toSeq.flatMap((t, count) => Seq.fill(count)(t))

def flattenMultisets[T](ms: Iterable[Multiset[T]]): Multiset[T] =
  groupMapReduce(ms.flatten)(_._1)(_._2)(_ + _)

def multisetOf[T](ts: T*): Multiset[T] =
  groupMapReduce(ts)(t => t)(_ => 1)(_ + _)

def groupMapReduce[A, CC[_], C, K, B]
  (elems: IterableOps[A, CC, C])
  (key: A => K)
  (f: A => B)
  (reduce: (B, B) => B)
  : SeqMap[K, B] = {
  val m = mutable.SeqMap.empty[K, B]
  for (elem <- elems) {
    val k = key(elem)
    val v =
      m.get(k) match {
        case Some(b) => reduce(b, f(elem))
        case None    => f(elem)
      }
    m.put(k, v)
  }
  m.to(SeqMap)
}

def groupMap[A, CC[_], C, K, B]
  (elems: IterableOps[A, CC, C])
  (key: A => K)
  (f: A => B)
  : SeqMap[K, CC[B]] = {
  val m = mutable.SeqMap.empty[K, mutable.Builder[B, CC[B]]]
  for (elem <- elems) {
    val k = key(elem)
    val bldr = m.getOrElseUpdate(k, elems.iterableFactory.newBuilder[B])
    bldr += f(elem)
  }
  class Result extends runtime.AbstractFunction1[(K, mutable.Builder[B, CC[B]]), Unit] {
    var built = SeqMap.empty[K, CC[B]]
    def apply(kv: (K, mutable.Builder[B, CC[B]])) =
      built = built.updated(kv._1, kv._2.result())
  }
  val result = new Result
  m.foreach(result)
  result.built
}

package eitherFilter {
  extension [L, R](e: Either[L, R])
    inline def withFilter(inline predicate: R => Boolean): Either[L, R] = e match
      case Right(r) if predicate(r) => e
      case Right(_) =>
        throw Exception("please use irrefutable pattern with Either")
      case Left(_) => e
}

def toBoolean(e: Either[?, ?]): Boolean = e match
  case Right(_) => true
  case Left(_)  => false
