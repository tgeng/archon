package io.github.tgeng.archon.parser.combinators

import io.github.tgeng.archon.common.{*, given}

import scala.collection.mutable
import scala.math.min

case class ParseError(index: Int, description: String, targets: Seq[String] = Nil)

/**
 * [[committed]] means at which level backtracking should be disabled. Levels correspond to
 * target names (i.e. one additional target creates one level), so lower levels are more severe
 * than upper levels because a lower level means back tracking is disabled closer to the root of
 * the parser hierarchy.
 */
// TODO: consider generalizing `Seq` to some traversable so that one can provide an implementation
//  that simply drops any error message for fast passing. Then failure messages can be recovered
//  by running the parser again, with possible a `Boolean` monad plus that drops parse result.
abstract class ParseResult[M[+_], +T] :
  def result: M[T]
  def errors: Seq[ParseError]
  def committed: Boolean

  def commit: ParseResult[M, T] = ParseResult.WrappedParseResult(this, None, true)
  def onExitFromTarget(targetName: Option[String]): ParseResult[M, T] = targetName match
    case None => this
    case Some(_) => ParseResult.WrappedParseResult(this, targetName, false)

object ParseResult:
  def success[M[+_], T](result: M[T], committed: Boolean = false): ParseResult[M, T] = ParseResult(result, Seq(), committed)
  def failure[M[+_] : Monad : Alternative, T](errors: Seq[ParseError], committed: Boolean = false): ParseResult[M, Nothing] = ParseResult(Alternative.empty, errors, committed)
  def apply[M[+_], T](result: M[T], errors: Seq[ParseError], committed: Boolean = false) : ParseResult[M, T] =
    new USimpleLevelParseResult(result, trimErrors(errors), committed)
  def unapply[M[+_], T](r: ParseResult[M, T]): Option[(M[T], Seq[ParseError], Boolean)] = Some((r.result, r.errors, r.committed))

  private def trimErrors(errors: Seq[ParseError]) : Seq[ParseError] =
    val maxTargetProgress = errors.map(e => e.index).maxOption.getOrElse(0)
    errors.filter(e => e.index == maxTargetProgress).take(5)

  private case class USimpleLevelParseResult[M[+_], +T](
    override val result: M[T],
    override val errors: Seq[ParseError],
    override val committed: Boolean
  ) extends ParseResult[M, T]
  private case class WrappedParseResult[M[+_], +T](base: ParseResult[M, T], targetName: Option[String], override val committed: Boolean) extends ParseResult[M, T]:
    override def result = base.result
    override def errors = base.errors.map(e => ParseError(e.index, e.description, targetName ++: e.targets))

import ParseResult.*

abstract class ParserT[-I, +T, M[+_]]:
  final def doParse(index: Int)(using input: IndexedSeq[I]): ParseResult[M, (Int, T)] =
    parseImpl(index).onExitFromTarget(targetName)

  def parseImpl(index: Int)(using input: IndexedSeq[I]): ParseResult[M, (Int, T)]

  def targetName: Option[String] = None

  def isFailureParser: Boolean = false

object P

type Parser[-I, +T] = ParserT[I, T, Option]
type MultiParser[-I, +T] = ParserT[I, T, List]

extension[I, T, M[+_]](e: P.type)
  inline def apply(inline parser: =>ParserT[I, T, M], name : String | Null = null, lazily: Boolean = false) : ParserT[I, T, M] =
    val nameToUse = if (name == null) enclosingName(parser).stripSuffix("Parser") else name
    lazy val p = parser
    if !lazily && p.isFailureParser then parser
    else new ParserT[I, T, M]:
      override def parseImpl(index: Int)(using input: IndexedSeq[I]): ParseResult[M, (Int, T)] = p.parseImpl(index)

      override def targetName: Option[String] = Some(nameToUse)

extension[I, T, M[+_]](using ap: Applicative[ParserT[I, *, M]])(using mm: Monad[M])(using am: Applicative[M])(using Alternative[M])(e: P.type)
  def pure(t: T) : ParserT[I, T, M] = ap.pure(t)
  def fail(description: String) = FailureParser(description)

  def satisfy(description: String, action: IndexedSeq[I] => Option[(Int, T)]) = new ParserT[I, T, M] :
    override def parseImpl(index: Int)(using input: IndexedSeq[I]): ParseResult[M, (Int, T)] =
      action(input.slice(index, input.length)) match
        case Some((advance, t)) => success(am.pure((advance, t)))
        case None => failure(Seq(ParseError(index, description)))

  def info(action: (IndexedSeq[I], Int) => T) : ParserT[I, T, M] = new ParserT[I, T, M] :
    override def parseImpl(index: Int)(using input: IndexedSeq[I]): ParseResult[M, (Int, T)] =
      success(am.pure((0, action(input, index))))

extension[I, T, M[+_] : Alternative : Monad](p: ParserT[I, T, M])
  infix def asAtom(description: String) = new ParserT[I, T, M]:
    override def parseImpl(index: Int)(using input: IndexedSeq[I]): ParseResult[M, (Int, T)] =
      val ParseResult(results, errors, committed) = p.parseImpl(index)
      if results == Alternative.empty then
        failure(Seq(ParseError(index, description)), committed)
      else
        success(results, committed)

  def unary_! = new ParserT[I, T, M]:
    override def parseImpl(index: Int)(using input: IndexedSeq[I]): ParseResult[M, (Int, T)] =
      val parseResult = p.parseImpl(index)
      val ParseResult(results, errors, committed) = parseResult
      if results == Alternative.empty then
        parseResult.commit
      else
        parseResult

  def ! = new ParserT[I, T, M]:
    override def parseImpl(index: Int)(using input: IndexedSeq[I]): ParseResult[M, (Int, T)] =
      val parseResult = p.parseImpl(index)
      val ParseResult(results, errors, committed) = parseResult
      if results == Alternative.empty then
        parseResult
      else
        parseResult.commit

  def debugResult = new ParserT[I, T, M] :
    override def parseImpl(index: Int)(using input: IndexedSeq[I]): ParseResult[M, (Int, T)] =
      val parseResult = p.parseImpl(index)
      println(parseResult)
      parseResult

extension[I, T, M[+_]]
  (using ap: Alternative[ParseResult[M, *]])
  (using am: Alternative[M])(p: ParserT[I, T, M])
  /**
   * Similar to `or` in `Alternative[ParserT]`, but this operator does not invoke the second parser
   * if the first is successful, even if `M` is a `List` for non-deterministic parsing.
   */
  infix def ||(q: =>ParserT[I, T, M]) : ParserT[I, T, M] =
    if p.isFailureParser then q
    else new ParserT[I, T, M]:
      override def parseImpl(index: Int)(using input: IndexedSeq[I]): ParseResult[M, (Int, T)] =
        val pResult = p.doParse(index)
        // Only continue if first failed and is not committed says do not abort
        if pResult.result == am.empty && !pResult.committed then ap.or(pResult, q.doParse(index))
        else pResult

extension[I, T] (p: Parser[I, T])
  def parse(input: IndexedSeq[I], index: Int = 0, targets: List[String] = Nil): Either[Seq[ParseError], (Int, T)] =
    val ParseResult(result, errors, _) = p.doParse(index)(using input)
    result match
      case Some(result) => Right(result)
      case None => Left(errors)

extension[I, T] (p: MultiParser[I, T])
  def multiParse(input: IndexedSeq[I], index: Int = 0, targets: List[String] = Nil): Either[Seq[ParseError], List[(Int, T)]] =
    val ParseResult(results, errors, _) = p.doParse(index)(using input)
    results match
      case Nil => Left(errors)
      case _ => Right(results)

package multi:
  given Flattener[List] with
    override def flatten[T](seqs: List[Seq[T]]): Seq[T] = seqs.flatten.toSeq

    override def or(m: List[Boolean], base: Boolean): Boolean = base || m.exists(b => b)

package single:
  given Flattener[Option] with
    override def flatten[T](seqs: Option[Seq[T]]): Seq[T] = seqs match
      case Some(seq) => seq
      case None => Seq()

    override def or(m: Option[Boolean], base: Boolean): Boolean = base || m.getOrElse(false)

given [I, M[+_]] (using Functor[ParseResult[M, *]]): Functor[ParserT[I, *, M]] with
  override def map[T, S](f: ParserT[I, T, M], g: T => S): ParserT[I, S, M] =
    if f.isFailureParser then f.asInstanceOf[ParserT[I, S, M]]
    else new ParserT[I, S, M] :
      override def parseImpl(index: Int)(using input: IndexedSeq[I]): ParseResult[M, (Int, S)] =
        Functor.map(f.doParse(index), (advance, t) => (advance, g(t)))

given [I, M[+_]] (using Functor[ParseResult[M, *]])(using Applicative[ParseResult[M, *]])(using Monad[ParseResult[M, *]]): Applicative[ParserT[I, *, M]] with
  override def pure[S](s: S): ParserT[I, S, M] = new ParserT[I, S, M] :
    override def parseImpl(index: Int)(using input: IndexedSeq[I]): ParseResult[M, (Int, S)] =
      Applicative.pure(0, s)

  override def starApply[T, S](f: ParserT[I, T => S, M], m: ParserT[I, T, M]): ParserT[I, S, M] =
    if f.isFailureParser then f.asInstanceOf[ParserT[I, S, M]]
    else if m.isFailureParser then m.asInstanceOf[ParserT[I, S, M]]
    else flatMapImpl(f, f => summon[Functor[ParserT[I, *, M]]].map(m, m => f(m)))

given [I, M[+_]] (using Functor[ParseResult[M, *]])(using Applicative[ParseResult[M, *]])(using Monad[ParseResult[M, *]]): Monad[ParserT[I, *, M]] with
  override def flatMap[T, S](m: ParserT[I, T, M], f: T => ParserT[I, S, M]) : ParserT[I, S, M] = flatMapImpl(m, f)

private def flatMapImpl[I, M[+_], T, S]
  (m: ParserT[I, T, M], f: T => ParserT[I, S, M])
  (using fp: Functor[ParseResult[M, *]])
  (using ap: Applicative[ParseResult[M, *]])
  (using mp: Monad[ParseResult[M, *]])
  : ParserT[I, S, M] =
  val cachingF = caching(f)
  if m.isFailureParser then m.asInstanceOf[ParserT[I, S, M]]
  else new ParserT[I, S, M] :
    override def parseImpl(index: Int)(using input: IndexedSeq[I]): ParseResult[M, (Int, S)] =
      mp.flatMap(
        m.doParse(index),
        (advance, t) => fp.map(cachingF(t).doParse(index + advance), (advance2, s) => (advance + advance2, s))
      )

given [I, M[+_]]
  (using Applicative[ParserT[I, *, M]])
  (using Applicative[ParseResult[M, *]])
  (using ap: Alternative[ParseResult[M, *]])
  (using Applicative[M])
  (using Monad[M])
  (using am: Alternative[M])
  : Alternative[ParserT[I, *, M]] with
  override def empty[S]: ParserT[I, S, M] = FailureParser()

  override def or[T](a: ParserT[I, T, M], lazyB: => ParserT[I, T, M]): ParserT[I, T, M] =
    lazy val b = lazyB
    if a.isFailureParser then b
    else new ParserT[I, T, M] :
      override def parseImpl(index: Int)(using input: IndexedSeq[I]): ParseResult[M, (Int, T)] =
        val aResult = a.doParse(index)
        // Do not continue if commit level from `a` says we should abort
        if aResult.result == am.empty && aResult.committed then aResult
        else ap.or(aResult, b.doParse(index))

private class FailureParser[-I, M[+_]: Monad : Alternative](description: String | Null = null) extends ParserT[I, Nothing, M] :
  override def parseImpl(index: Int)(using input: IndexedSeq[I]): ParseResult[M, (Int, Nothing)] =
    if description == null then failure(Seq())
    else failure(Seq(ParseError(index, description)))

  override def isFailureParser: Boolean = true

trait Flattener[M[_]]:
  def flatten[T](seqs: M[Seq[T]]) : Seq[T]
  def or(m: M[Boolean], base: Boolean) : Boolean

given [M[+_]] (using flattener: Flattener[M])(using Functor[M]): Functor[ParseResult[M, *]] with
  override def map[T, S](f: ParseResult[M, T], g: T => S): ParseResult[M, S] = ParseResult(Functor.map(f.result, g), f.errors, f.committed)

given [M[+_]] (using Functor[ParseResult[M, *]])(using flattener: Flattener[M])(using Functor[M])(using Applicative[M])(using Monad[M]): Applicative[ParseResult[M, *]] with
  override def pure[T](t: T): ParseResult[M, T] = success(Applicative.pure(t))

  override def starApply[T, S](f: ParseResult[M, T => S], m: ParseResult[M, T]): ParseResult[M, S] =
    flatMapImpl(f, f => Functor.map(m, m => f(m)))

given [M[+_]] (using Functor[ParseResult[M, *]])(using Applicative[ParseResult[M, *]])(using flattener: Flattener[M])(using Functor[M])(using Applicative[M])(using Monad[M]): Monad[ParseResult[M, *]] with
  override def flatMap[T, S](m: ParseResult[M, T], f: T => ParseResult[M, S]): ParseResult[M, S] = flatMapImpl(m, f)

private def flatMapImpl[M[+_], T, S]
  (m: ParseResult[M, T], f: T => ParseResult[M, S])
  (using flattener: Flattener[M])
  (using Functor[M])
  (using Monad[M])
  (using Applicative[M])
  : ParseResult[M, S] =
  val parseResults = Monad.flatMap(m.result, r => Applicative.pure(f(r)))
  ParseResult(
    Monad.flatMap(parseResults, r => r.result),
    m.errors ++ flattener.flatten(Monad.flatMap(parseResults, r => Applicative.pure(r.errors))),
    flattener.or(Functor.map(parseResults, _.committed), m.committed)
  )

given [M[+_]] (using Applicative[ParseResult[M, *]])(using flattener: Flattener[M])(using Monad[M])(using Alternative[M]): Alternative[ParseResult[M, *]] with
  override def empty[T]: ParseResult[M, T] = failure(Seq())

  override def or[T](a: ParseResult[M, T], b: => ParseResult[M, T]): ParseResult[M, T] =
    var evaluatedB: Option[ParseResult[M, T]] = None
    val result = Alternative.or(a.result, {
      evaluatedB = Some(b)
      evaluatedB.get.result
    })
    evaluatedB match
      case Some(b) => ParseResult(result, a.errors ++ b.errors, a.committed || b.committed)
      case _ => a

class ParserCache[I, M[+_]]:
  private val map = mutable.WeakHashMap[IndexedSeq[I], mutable.Map[(Any, Int), ParseResult[M, (Int, ?)]]]()
  def load[T](key: Any, index: Int, action: => ParseResult[M, (Int, T)])(using input: IndexedSeq[I]) : ParseResult[M, (Int, T)] =
    map.getOrElseUpdate(input, mutable.WeakHashMap()).getOrElseUpdate((key, index), action).asInstanceOf[ParseResult[M, (Int, T)]]

extension[I, T, M[+_]](e: P.type)(using cache: ParserCache[I, M])
  inline def cached(key: Any, p: =>ParserT[I, T, M]) : ParserT[I, T, M] = new ParserT[I, T, M] :
    override def parseImpl(index: Int)(using input: IndexedSeq[I]): ParseResult[M, (Int, T)] =
      cache.load(key, index, p.parseImpl(index))
