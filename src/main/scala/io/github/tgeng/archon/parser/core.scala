package io.github.tgeng.archon.parser

import io.github.tgeng.archon.common.{*, given}
import scala.math.min

case class ParseError(index: Int, description: String, targets: Seq[String])

/**
 * [[commitLevel]] means at which level backtracking should be disabled. Levels correspond to
 * target names (i.e. one additional target creates one level), so lower levels are more severe
 * than upper levels because a lower level means back tracking is disabled closer to the root of
 * the parser hierarchy.
 */
case class ParseResult[M[+_], +T](result: M[T], errors: Seq[ParseError], commitLevel: Int) :
  def withLevel(level: Int): ParseResult[M, T] = ParseResult(result, errors, level)

object ParseResult:
  def success[M[+_], T](result: M[T], commitLevel: Int = Int.MaxValue): ParseResult[M, T] = ParseResult(result, Seq(), commitLevel)
  def failure[M[+_], T](errors: Seq[ParseError], commitLevel: Int = Int.MaxValue)(using m: MonadPlus[M]): ParseResult[M, Nothing] = ParseResult(m.empty, errors, commitLevel)
  def apply[M[+_], T](result: M[T], errors: Seq[ParseError], commitLevel: Int = Int.MaxValue) =
    new ParseResult(result, trimErrors(errors), commitLevel)

  private def trimErrors(errors: Seq[ParseError]) : Seq[ParseError] =
    val maxTargetProgress = errors.map(e => e.index).maxOption.getOrElse(0)
    errors.filter(e => e.index == maxTargetProgress)

import ParseResult.*

type ParseResultM[M[+_]] = [T] =>> ParseResult[M, T]

trait ParserT[-I, +T, M[+_]]:
  final def doParse(index: Int)(using input: IndexedSeq[I])(using targets: List[String]): ParseResult[M, (Int, T)] =
    parseImpl(index)(using input)(using targetName ++: targets)

  def parseImpl(index: Int)(using input: IndexedSeq[I])(using targets: List[String]): ParseResult[M, (Int, T)]

  def targetName: Option[String] = None

type ParserM[-I, M[+_]] = [T] =>> ParserT[I, T, M]

object P

type Parser[-I, +T] = ParserT[I, T, Option]
type MultiParser[-I, +T] = ParserT[I, T, List]

extension[I, T, M[+_]](using pm: MonadPlus[ParserM[I, M]])(using mm: MonadPlus[M])(e: P.type)
  inline def apply(inline parser: MonadPlus[ParserM[I, M]] ?=> ParserT[I, T, M], name : String | Null = null) = createNamedParser(parser, name)
  def pure(t: T) : ParserT[I, T, M] = pm.pure(t)
  def fail(description: String) = new ParserT[I, T, M] :
    override def parseImpl(index: Int)(using input: IndexedSeq[I])(using targets: List[String]): ParseResult[M, (Int, T)] =
      failure(Seq(ParseError(index, description, targets)))

  def satisfy(description: String, action: IndexedSeq[I] => Option[(Int, T)]) = new ParserT[I, T, M] :
    override def parseImpl(index: Int)(using input: IndexedSeq[I])(using targets: List[String]): ParseResult[M, (Int, T)] =
      action(input.slice(index, input.length)) match
        case Some((advance, t)) => success(mm.pure((advance, t)))
        case None => failure(Seq(ParseError(index, description, targets)))

extension[I, T, M[+_]] (using env: MonadPlus[ParserM[I, M]])(using m: MonadPlus[M])(p: ParserT[I, T, M])
  infix def asAtom(description: String) = new ParserT[I, T, M]:
    override def parseImpl(index: Int)(using input: IndexedSeq[I])(using targets: List[String]): ParseResult[M, (Int, T)] =
      val ParseResult(results, errors, commitLevel) = p.parseImpl(index)
      if results == m.empty then
        failure(Seq(ParseError(index, description, targets)), commitLevel)
      else
        success(results, commitLevel)

  def unary_! = new ParserT[I, T, M]:
    override def parseImpl(index: Int)(using input: IndexedSeq[I])(using targets: List[String]): ParseResult[M, (Int, T)] =
      val parseResult = p.parseImpl(index)
      val ParseResult(results, errors, commitLevel) = parseResult
      if results == m.empty then
        parseResult.withLevel(targets.size)
      else
        parseResult

  def ! = new ParserT[I, T, M]:
    override def parseImpl(index: Int)(using input: IndexedSeq[I])(using targets: List[String]): ParseResult[M, (Int, T)] =
      val parseResult = p.parseImpl(index)
      val ParseResult(results, errors, commitLevel) = parseResult
      if results == m.empty then
        parseResult
      else
        parseResult.withLevel(targets.size)

extension[I, T] (p: Parser[I, T])
  def parse(input: IndexedSeq[I], index: Int = 0, targets: List[String] = Nil): Either[Seq[ParseError], (Int, T)] =
    val ParseResult(result, errors, _) = p.doParse(index)(using input)(using targets)
    result match
      case Some(result) => Right(result)
      case None => Left(errors)

extension[I, T] (p: MultiParser[I, T])
  def multiParse(input: IndexedSeq[I], index: Int = 0, targets: List[String] = Nil): Either[Seq[ParseError], List[(Int, T)]] =
    val ParseResult(results, errors, _) = p.doParse(index)(using input)(using targets)
    results match
      case Nil => Left(errors)
      case _ => Right(results)

package multi:
  given Flattener[List] with
    override def flatten[T](seqs: List[Seq[T]]): Seq[T] = seqs.flatten.toSeq

package single:
  given Flattener[Option] with
    override def flatten[T](seqs: Option[Seq[T]]): Seq[T] = seqs match
      case Some(seq) => seq
      case None => Seq()

given ParserTMonadPlus [I, M[+_]] (using env: MonadPlus[ParseResultM[M]])(using m: MonadPlus[M]): MonadPlus[ParserM[I, M]] with
  override def map[T, S](f: ParserT[I, T, M], g: T => S): ParserT[I, S, M] = new ParserT[I, S, M] :
    override def parseImpl(index: Int)(using input: IndexedSeq[I])(using targets: List[String]): ParseResult[M, (Int, S)] =
      env.map(f.doParse(index), (advance, t) => (advance, g(t)))

  override def pure[S](s: S): ParserT[I, S, M] = new ParserT[I, S, M] :
    override def parseImpl(index: Int)(using input: IndexedSeq[I])(using targets: List[String]): ParseResult[M, (Int, S)] =
      env.pure(0, s)

  override def flatMap[T, S](m: ParserT[I, T, M], f: T => ParserT[I, S, M]): ParserT[I, S, M] = new ParserT[I, S, M] :
    override def parseImpl(index: Int)(using input: IndexedSeq[I])(using targets: List[String]): ParseResult[M, (Int, S)] =
      env.flatMap(
        m.doParse(index),
        (advance, t) => env.map(f(t).doParse(index + advance), (advance2, s) => (advance + advance2, s))
      )

  override def empty[S]: ParserT[I, S, M] = new ParserT[I, S, M] :
    override def parseImpl(index: Int)(using input: IndexedSeq[I])(using targets: List[String]): ParseResult[M, (Int, S)] = env.empty

  override def or[T](a: ParserT[I, T, M], b: => ParserT[I, T, M]): ParserT[I, T, M] = new ParserT[I, T, M] :
    override def parseImpl(index: Int)(using input: IndexedSeq[I])(using targets: List[String]): ParseResult[M, (Int, T)] =
      val aResult = a.doParse(index)
      // Do not continue if commit level from `a` says we should abort
      if aResult.result == m.empty && aResult.commitLevel <= targets.size then aResult
      else env.or(aResult, b.doParse(index))

trait Flattener[M[_]]:
  def flatten[T](seqs: M[Seq[T]]) : Seq[T]

given ParseResultMonadPlus [M[+_]] (using flattener: Flattener[M])(using env: MonadPlus[M]): MonadPlus[ParseResultM[M]] with
  override def map[T, S](f: ParseResult[M, T], g: T => S): ParseResult[M, S] = ParseResult(env.map(f.result, g), f.errors, f.commitLevel)

  override def pure[T](t: T): ParseResult[M, T] = success(env.pure(t))

  override def flatMap[T, S](m: ParseResult[M, T], f: T => ParseResult[M, S]): ParseResult[M, S] =
    val parseResults = env.flatMap(m.result, r => env.pure(f(r)))
    ParseResult(env.flatMap(parseResults, r => r.result), m.errors ++ flattener.flatten(env.flatMap(parseResults, r => env.pure(r.errors))) , m.commitLevel)

  override def empty[T]: ParseResult[M, T] = failure(Seq())

  override def or[T](a: ParseResult[M, T], b: => ParseResult[M, T]): ParseResult[M, T] =
    var evaluatedB: Option[ParseResult[M, T]] = None
    val result = env.or(a.result, {
      evaluatedB = Some(b)
      evaluatedB.get.result
    })
    evaluatedB match
      case Some(b) => ParseResult(result, a.errors ++ b.errors, min(a.commitLevel, b.commitLevel))
      case _ => a

private inline def createNamedParser[I, T, M[+_]](inline parser: MonadPlus[ParserM[I, M]] ?=> ParserT[I, T, M], name : String | Null)(using env: MonadPlus[ParserM[I, M]]) =
  val nameToUse = if (name == null) enclosingName(parser) else name
  new ParserT[I, T, M]:
    override def parseImpl(index: Int)(using input: IndexedSeq[I])(using targets: List[String]): ParseResult[M, (Int, T)] = parser.parseImpl(index)
    override def targetName: Option[String] = Some(nameToUse)
