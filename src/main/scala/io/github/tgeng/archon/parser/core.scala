package io.github.tgeng.archon.parser

import io.github.tgeng.archon.common.{*, given}
import scala.math.min

case class ParseError(index: Int, description: String, targets: Seq[String])

enum ParseResult[M[+_], +T]:
  case Success[M[+_], +T](result: M[T], commitLevel: Int = Int.MaxValue) extends ParseResult[M, T]

  /**
   * [[commitLevel]] means at which level backtracking should be disabled. Levels correspond to
   * target names (i.e. one additional target creates one level), so lower levels are more severe
   * than upper levels because a lower level means back tracking is disabled closer to the root of
   * the parser hierarchy.
   */
  case Failure[M[+_], +T](errors: Seq[ParseError], commitLevel: Int = Int.MaxValue) extends ParseResult[M, T]

type ParseResultM[M[+_]] = [T] =>> ParseResult[M, T]

import io.github.tgeng.archon.parser.ParseResult.*

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
      Failure(Seq(ParseError(index, description, targets)))

  def satisfy(description: String, action: IndexedSeq[I] => Option[(Int, T)]) = new ParserT[I, T, M] :
    override def parseImpl(index: Int)(using input: IndexedSeq[I])(using targets: List[String]): ParseResult[M, (Int, T)] =
      action(input.slice(index, input.length)) match
        case Some((advance, t)) => Success(mm.pure((advance, t)))
        case None => Failure(Seq(ParseError(index, description, targets)))

extension[I, T, M[+_]] (using env: MonadPlus[ParserM[I, M]])(using MonadPlus[M])(p: ParserT[I, T, M])
  infix def withDescription(description: String) = new ParserT[I, T, M]:
    override def parseImpl(index: Int)(using input: IndexedSeq[I])(using targets: List[String]): ParseResult[M, (Int, T)] =
      p.parseImpl(index) match
        case Success(results, commitLevel) => Success(results, commitLevel)
        case Failure(_, commitLevel) => Failure(Seq(ParseError(index, description, targets)), commitLevel)

  def unary_! = new ParserT[I, T, M]:
    override def parseImpl(index: Int)(using input: IndexedSeq[I])(using targets: List[String]): ParseResult[M, (Int, T)] =
      p.parseImpl(index) match
        case Success(results, commitLevel) => Success(results, commitLevel)
        case Failure(errors, _) => Failure(errors, targets.size)

  def ! = new ParserT[I, T, M]:
    override def parseImpl(index: Int)(using input: IndexedSeq[I])(using targets: List[String]): ParseResult[M, (Int, T)] =
      p.parseImpl(index) match
        case Success(results, _) => Success(results, targets.size)
        case Failure(errors, commitLevel) => Failure(errors, commitLevel)

extension[I, T] (p: Parser[I, T])
  def parse(input: IndexedSeq[I], index: Int = 0, targets: List[String] = Nil): Either[Seq[ParseError], (Int, T)] =
    p.doParse(index)(using input)(using targets) match
      case Success(result, _) => Right(result.get)
      case Failure(errors, _) => Left(errors)

extension[I, T] (p: MultiParser[I, T])
  def multiParse(input: IndexedSeq[I], index: Int = 0, targets: List[String] = Nil): Either[Seq[ParseError], List[(Int, T)]] =
    p.doParse(index)(using input)(using targets) match
      case Success(results, _) => Right(results)
      case Failure(errors, _) => Left(errors)

package multi:
  given ListParseResultDistributor: Distributor[List, ParseResultM[List]] with
    override def distribute[T](m: List[ParseResult[List, T]]): ParseResult[List, List[T]] =
      m.partition(r => r.isInstanceOf[Success[?, ?]]) match
        case (Nil, Nil) => throw IllegalStateException("List in this usage should never be empty.")
        case (Nil, l) => Failure(
          trimErrors(l.flatMap(e => e match
            case Success(_, _) => throw IllegalStateException()
            case Failure(errors, _) => errors
          )),
          l.map(
            e => e match
              case Success(_, _) => throw IllegalStateException()
              case Failure(_, commitLevel) => commitLevel)
            // use max to allow collecting all possible results
           .maxOption.getOrElse(Int.MaxValue)
        )
        case (l, _) => Success(
          l.map(r => r match
            case Success(results, _) => results
            case Failure(_, _) => throw IllegalStateException()),
          l.map(
            e => e match
              case Success(_, commitLevel) => commitLevel
              case Failure(_, _) => throw IllegalStateException())
           // use max to allow collecting all possible results
           .maxOption.getOrElse(Int.MaxValue)
        )

package single:
  given OptionParseResultDistributor: Distributor[Option, ParseResultM[Option]] with
    override def distribute[T](m: Option[ParseResult[Option, T]]): ParseResult[Option, Option[T]] = m match
      case Some(r) => r match
        case Success(r, l) => Success(Some(r), l)
        case Failure(e, l) => Failure(e, l)
      case None => throw IllegalStateException("Option in this usage should never be empty.")

given ParserTMonadPlus [I, M[+_]] (using env: MonadPlus[ParseResultM[M]]): MonadPlus[ParserM[I, M]] with
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
      a.doParse(index) match
        case s:Success[_, _] => env.or(s, b.doParse(index)) match
          case Success(results, l) => Success(results, l)
          case Failure(errors, l) => Failure(errors, l)
        case f@Failure(errors, commitLevel) =>
          // If commit level is lower or equal to the current level (i.e. targets.size), don't back
          // track and just return the first failure
          if commitLevel <= targets.size then f
          else env.or(f, b.doParse(index))

given ParseResultMonadPlus [M[+_]] (using dist: Distributor[M, ParseResultM[M]])(using env: MonadPlus[M]): MonadPlus[ParseResultM[M]] with
  override def map[T, S](f: ParseResult[M, T], g: T => S): ParseResult[M, S] = f match
    case Success(results, commitLevel) => Success(env.map(results, g), commitLevel)
    case Failure(errors, commitLevel) => Failure(errors, commitLevel)

  override def pure[T](t: T): ParseResult[M, T] = Success(env.pure(t))

  override def flatMap[T, S](m: ParseResult[M, T], f: T => ParseResult[M, S]): ParseResult[M, S] = m match
    case Success(results, commitLevel) =>
      dist.distribute(env.flatMap(results, t => env.pure(f(t)))) match
        case Success(results, commitLevel2) => Success(env.flatten(results), min(commitLevel, commitLevel2))
        case Failure(errors, commitLevel2) => Failure(errors, min(commitLevel, commitLevel2))
    case Failure(errors, commitLevel) => Failure(errors, commitLevel)

  override def empty[T]: ParseResult[M, T] = Failure(Seq())

  override def or[T](a: ParseResult[M, T], b: => ParseResult[M, T]): ParseResult[M, T] = a match
    case Success(a, la) =>
      val result = env.or(a, b match
        case Success(b, _) => b
        case Failure(_, _) => env.empty)
      Success(result, la)
    case Failure(a, la) => b match
      // respect the more severe error
      case Success(b, lb) => Success(b, min(la, lb))
      case Failure(b, lb) => Failure(trimErrors(a ++ b), min(la, lb))

private inline def createNamedParser[I, T, M[+_]](inline parser: MonadPlus[ParserM[I, M]] ?=> ParserT[I, T, M], name : String | Null)(using env: MonadPlus[ParserM[I, M]]) =
  val nameToUse = if (name == null) enclosingName(parser) else name
  new ParserT[I, T, M]:
    override def parseImpl(index: Int)(using input: IndexedSeq[I])(using targets: List[String]): ParseResult[M, (Int, T)] = parser.parseImpl(index)
    override def targetName: Option[String] = Some(nameToUse)

private def trimErrors(errors: Seq[ParseError]) : Seq[ParseError] =
  val maxTargetProgress = errors.map(e => (e.targets.size, e.index)).maxOption.getOrElse((0, 0))
  errors.filter(e => (e.targets.size, e.index) == maxTargetProgress)
