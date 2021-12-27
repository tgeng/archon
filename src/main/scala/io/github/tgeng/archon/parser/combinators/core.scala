package io.github.tgeng.archon.parser.combinators

import io.github.tgeng.archon.common.{*, given}

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
  def failure[M[+_], T](errors: Seq[ParseError], committed: Boolean = false)(using m: MonadPlus[M]): ParseResult[M, Nothing] = ParseResult(m.empty, errors, committed)
  def apply[M[+_], T](result: M[T], errors: Seq[ParseError], committed: Boolean = false) : ParseResult[M, T] =
    new SimpleParseResult(result, trimErrors(errors), committed)
  def unapply[M[+_], T](r: ParseResult[M, T]): Option[(M[T], Seq[ParseError], Boolean)] = Some((r.result, r.errors, r.committed))

  private def trimErrors(errors: Seq[ParseError]) : Seq[ParseError] =
    val maxTargetProgress = errors.map(e => e.index).maxOption.getOrElse(0)
    errors.filter(e => e.index == maxTargetProgress).take(5)

  private case class SimpleParseResult[M[+_], +T](
    override val result: M[T],
    override val errors: Seq[ParseError],
    override val committed: Boolean
  ) extends ParseResult[M, T]
  private case class WrappedParseResult[M[+_], +T](base: ParseResult[M, T], targetName: Option[String], override val committed: Boolean) extends ParseResult[M, T]:
    override def result = base.result
    override def errors = base.errors.map(e => ParseError(e.index, e.description, targetName ++: e.targets))

import ParseResult.*

type ParseResultM[M[+_]] = [T] =>> ParseResult[M, T]

trait ParserT[-I, +T, M[+_]]:
  final def doParse(index: Int)(using input: IndexedSeq[I]): ParseResult[M, (Int, T)] =
    // TODO: consider adding caching for created parsers and parsed results. For the latter `targets`
    // probably need to be removed and commit depth should be implemented as an index that is
    // lowered each time a named parser returns.
    parseImpl(index).onExitFromTarget(targetName)

  def parseImpl(index: Int)(using input: IndexedSeq[I]): ParseResult[M, (Int, T)]

  def targetName: Option[String] = None

  def isFailureParser: Boolean = false

type ParserM[-I, M[+_]] = [T] =>> ParserT[I, T, M]

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

extension[I, T, M[+_]](using pm: MonadPlus[ParserM[I, M]])(using mm: MonadPlus[M])(e: P.type)
  def pure(t: T) : ParserT[I, T, M] = pm.pure(t)
  def fail(description: String) = FailureParser(description)(using mm)

  def satisfy(description: String, action: IndexedSeq[I] => Option[(Int, T)]) = new ParserT[I, T, M] :
    override def parseImpl(index: Int)(using input: IndexedSeq[I]): ParseResult[M, (Int, T)] =
      action(input.slice(index, input.length)) match
        case Some((advance, t)) => success(mm.pure((advance, t)))
        case None => failure(Seq(ParseError(index, description)))

  def info(action: (IndexedSeq[I], Int) => T) : ParserT[I, T, M] = new ParserT[I, T, M] :
    override def parseImpl(index: Int)(using input: IndexedSeq[I]): ParseResult[M, (Int, T)] =
      success(mm.pure((0, action(input, index))))

extension[I, T, M[+_]] (using env: MonadPlus[ParserM[I, M]])(using m: MonadPlus[M])(p: ParserT[I, T, M])
  infix def asAtom(description: String) = new ParserT[I, T, M]:
    override def parseImpl(index: Int)(using input: IndexedSeq[I]): ParseResult[M, (Int, T)] =
      val ParseResult(results, errors, committed) = p.parseImpl(index)
      if results == m.empty then
        failure(Seq(ParseError(index, description)), committed)
      else
        success(results, committed)

  def unary_! = new ParserT[I, T, M]:
    override def parseImpl(index: Int)(using input: IndexedSeq[I]): ParseResult[M, (Int, T)] =
      val parseResult = p.parseImpl(index)
      val ParseResult(results, errors, committed) = parseResult
      if results == m.empty then
        parseResult.commit
      else
        parseResult

  def ! = new ParserT[I, T, M]:
    override def parseImpl(index: Int)(using input: IndexedSeq[I]): ParseResult[M, (Int, T)] =
      val parseResult = p.parseImpl(index)
      val ParseResult(results, errors, committed) = parseResult
      if results == m.empty then
        parseResult
      else
        parseResult.commit

  def debugResult = new ParserT[I, T, M] :
    override def parseImpl(index: Int)(using input: IndexedSeq[I]): ParseResult[M, (Int, T)] =
      val parseResult = p.parseImpl(index)
      println(parseResult)
      parseResult

extension[I, T, M[+_]] (using env: MonadPlus[ParseResultM[M]])(using m: MonadPlus[M])(p: ParserT[I, T, M])
  /**
   * Similar to `or` in `MonadPlus[ParserT]`, but this operator does not invoke the second parser
   * if the first is successful, even if `M` is a `List` for non-deterministic parsing.
   */
  infix def ||(q: =>ParserT[I, T, M]) : ParserT[I, T, M] =
    if p.isFailureParser then q
    else new ParserT[I, T, M]:
      override def parseImpl(index: Int)(using input: IndexedSeq[I]): ParseResult[M, (Int, T)] =
        val pResult = p.doParse(index)
        // Only continue if first failed and is not committed says do not abort
        if pResult.result == m.empty && !pResult.committed then env.or(pResult, q.doParse(index))
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

given ParserTMonadPlus [I, M[+_]] (using env: MonadPlus[ParseResultM[M]])(using m: MonadPlus[M]): MonadPlus[ParserM[I, M]] with
  override def map[T, S](f: ParserT[I, T, M], g: T => S): ParserT[I, S, M] =
    if f.isFailureParser then f.asInstanceOf[ParserT[I, S, M]]
    else new ParserT[I, S, M] :
      override def parseImpl(index: Int)(using input: IndexedSeq[I]): ParseResult[M, (Int, S)] =
        env.map(f.doParse(index), (advance, t) => (advance, g(t)))

  override def pure[S](s: S): ParserT[I, S, M] = new ParserT[I, S, M] :
    override def parseImpl(index: Int)(using input: IndexedSeq[I]): ParseResult[M, (Int, S)] =
      env.pure(0, s)

  override def starApply[T, S](f: ParserM[I, M][T => S], m: ParserM[I, M][T]): ParserT[I, S, M] =
    if f.isFailureParser then f.asInstanceOf[ParserT[I, S, M]]
    else if m.isFailureParser then m.asInstanceOf[ParserT[I, S, M]]
    else super.starApply(f, m)


  override def flatMap[T, S](m: ParserT[I, T, M], f: T => ParserT[I, S, M]): ParserT[I, S, M] =
    val cachedF = cacheLastOutput(f)
    if m.isFailureParser then m.asInstanceOf[ParserT[I, S, M]]
    else new ParserT[I, S, M] :
      override def parseImpl(index: Int)(using input: IndexedSeq[I]): ParseResult[M, (Int, S)] =
        env.flatMap(
          m.doParse(index),
          (advance, t) => env.map(cachedF(t).doParse(index + advance), (advance2, s) => (advance + advance2, s))
        )

  override def empty[S]: ParserT[I, S, M] = FailureParser()

  override def or[T](a: ParserT[I, T, M], lazyB: => ParserT[I, T, M]): ParserT[I, T, M] =
    lazy val b = lazyB
    if a.isFailureParser then b
    else new ParserT[I, T, M] :
      override def parseImpl(index: Int)(using input: IndexedSeq[I]): ParseResult[M, (Int, T)] =
        val aResult = a.doParse(index)
        // Do not continue if commit level from `a` says we should abort
        if aResult.result == m.empty && aResult.committed then aResult
        else env.or(aResult, b.doParse(index))

private class FailureParser[-I, M[+_]](description: String | Null = null)(using m: MonadPlus[M]) extends ParserT[I, Nothing, M] :
  override def parseImpl(index: Int)(using input: IndexedSeq[I]): ParseResult[M, (Int, Nothing)] =
    if description == null then failure(Seq())
    else failure(Seq(ParseError(index, description)))

  override def isFailureParser: Boolean = true

trait Flattener[M[_]]:
  def flatten[T](seqs: M[Seq[T]]) : Seq[T]
  def or(m: M[Boolean], base: Boolean) : Boolean

given ParseResultMonadPlus [M[+_]] (using flattener: Flattener[M])(using env: MonadPlus[M]): MonadPlus[ParseResultM[M]] with
  override def map[T, S](f: ParseResult[M, T], g: T => S): ParseResult[M, S] = ParseResult(env.map(f.result, g), f.errors, f.committed)

  override def pure[T](t: T): ParseResult[M, T] = success(env.pure(t))

  override def flatMap[T, S](m: ParseResult[M, T], f: T => ParseResult[M, S]): ParseResult[M, S] =
    val parseResults = env.flatMap(m.result, r => env.pure(f(r)))
    ParseResult(env.flatMap(parseResults, r => r.result), m.errors ++ flattener.flatten(env.flatMap(parseResults, r => env.pure(r.errors))), flattener.or(env.map(parseResults, _.committed), m.committed))

  override def empty[T]: ParseResult[M, T] = failure(Seq())

  override def or[T](a: ParseResult[M, T], b: => ParseResult[M, T]): ParseResult[M, T] =
    var evaluatedB: Option[ParseResult[M, T]] = None
    val result = env.or(a.result, {
      evaluatedB = Some(b)
      evaluatedB.get.result
    })
    evaluatedB match
      case Some(b) => ParseResult(result, a.errors ++ b.errors, a.committed || b.committed)
      case _ => a
