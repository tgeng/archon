package io.github.tgeng.archon.parser

import io.github.tgeng.archon.common.{*, given}

case class ParseError(index: Int, description: String, targets: Seq[String])

enum ParseResult[M[+_], +T]:
  case Success[M[+_], +T](result: M[T]) extends ParseResult[M, T]
  case Failure[M[+_], +T](errors: Seq[ParseError]) extends ParseResult[M, T]

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
  def pure(t: T) = pm.pure(t)
  def fail(message: String) = new ParserT[I, T, M] :
    override def parseImpl(index: Int)(using input: IndexedSeq[I])(using targets: List[String]): ParseResult[M, (Int, T)] =
      Failure(Seq(ParseError(index, message, targets)))

    def satisfy(description: String)(action: IndexedSeq[I] => Option[(Int, T)]) = new ParserT[I, T, M] :
      override def parseImpl(index: Int)(using input: IndexedSeq[I])(using targets: List[String]): ParseResult[M, (Int, T)] =
        action(input.slice(index, input.length)) match
          case Some((advance, t)) => Success(mm.pure((advance, t)))
          case None => Failure(Seq(ParseError(index, description, targets)))


  inline def apply(inline parser: MonadPlus[ParserM[I, M]] ?=> ParserT[I, T, M], name : String | Null = null) = createNamedParser(parser, name)

extension[I, T] (p: Parser[I, T])
  def parse(input: IndexedSeq[I], index: Int = 0, targets: List[String] = Nil): Either[Seq[ParseError], (Int, T)] =
    p.doParse(index)(using input)(using targets) match
      case Success(result) => Right(result.get)
      case Failure(errors) => Left(errors)

extension[I, T] (p: MultiParser[I, T])
  def multiParse(input: IndexedSeq[I], index: Int = 0, targets: List[String] = Nil): Either[Seq[ParseError], List[(Int, T)]] =
    p.doParse(index)(using input)(using targets) match
      case Success(results) => Right(results)
      case Failure(errors) => Left(errors)

package multi:
  given ListParseResultDistributor: Distributor[List, ParseResultM[List]] with
    override def distribute[T](m: List[ParseResult[List, T]]): ParseResult[List, List[T]] =
      m.partition(r => r.isInstanceOf[Success[?, ?]]) match
        case (Nil, Nil) => throw IllegalStateException("List in this usage should never be empty.")
        case (Nil, l) => Failure(l.flatMap(e => e match
          case Success(_) => throw IllegalStateException()
          case Failure(errors) => errors
        ))
        case (l, _) => Success(l.map(r => r match
          case Success(results) => results
          case Failure(_) => throw IllegalStateException()
        ))

package single:
  given OptionParseResultDistributor: Distributor[Option, ParseResultM[Option]] with
    override def distribute[T](m: Option[ParseResult[Option, T]]): ParseResult[Option, Option[T]] = m match
      case Some(r) => r match
        case Success(r) => Success(Some(r))
        case Failure(e) => Failure(e)
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
      env.or(a.doParse(index), b.doParse(index))

given ParseResultMonadPlus [M[+_]] (using dist: Distributor[M, ParseResultM[M]])(using env: MonadPlus[M]): MonadPlus[ParseResultM[M]] with
  override def map[T, S](f: ParseResult[M, T], g: T => S): ParseResult[M, S] = f match
    case Success(results) => Success(results.map(g))
    case Failure(errors) => Failure(errors)

  override def pure[T](t: T): ParseResult[M, T] = Success(env.pure(t))

  override def flatMap[T, S](m: ParseResult[M, T], f: T => ParseResult[M, S]): ParseResult[M, S] = m match
    case Success(results) =>
      dist.distribute(results.flatMap(t => env.pure(f(t)))) match
        case Success(results) => Success(results.flatten)
        case Failure(errors) => Failure(errors)
    case Failure(errors) => Failure(errors)

  override def empty[T]: ParseResult[M, T] = Failure(Seq())

  override def or[T](a: ParseResult[M, T], b: => ParseResult[M, T]): ParseResult[M, T] = a match
    case Success(a) =>
      val result = a <|> (b match
        case Success(b) => b
        case Failure(_) => env.empty)
      Success(result)
    case Failure(a) => b match
      case Success(b) => Success(b)
      case Failure(b) =>
        val allErrors = a ++ b
        val maxTargetLength = allErrors.map(_.targets.size).maxOption.getOrElse(0)
        Failure(allErrors.filter(_.targets.size == maxTargetLength))

private inline def createNamedParser[I, T, M[+_]](inline parser: MonadPlus[ParserM[I, M]] ?=> ParserT[I, T, M], name : String | Null)(using env: MonadPlus[ParserM[I, M]]) =
  val nameToUse = if (name == null) enclosingName(parser) else name
  new ParserT[I, T, M]:
    override def parseImpl(index: Int)(using input: IndexedSeq[I])(using targets: List[String]): ParseResult[M, (Int, T)] = parser.parseImpl(index)
    override def targetName: Option[String] = Some(nameToUse)

private inline def enclosingName(inline e: Any): String = ${
enclosingNameImpl('e)
}

import scala.quoted.*

private def enclosingNameImpl(e: Expr[Any])(using Quotes) : Expr[String] = {
  import quotes.reflect.*
  Expr(Symbol.spliceOwner.owner.owner.name)
}
