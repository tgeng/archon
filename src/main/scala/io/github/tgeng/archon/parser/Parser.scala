package io.github.tgeng.archon.parser

import io.github.tgeng.archon.common.{*, given}

case class ParseError(message: String, targets: Seq[String])

given Ordering[ParseError] with
  override def compare(x: ParseError, y: ParseError): Int = x.targets.size.compareTo(x.targets.size)

enum ParseResult[M[+_] : MonadPlus, +T]:
  case Success[M[+_] : MonadPlus, +T](result: M[T]) extends ParseResult[M, T]
  case Failure[M[+_] : MonadPlus, +T](errors: Seq[ParseError]) extends ParseResult[M, T]

import io.github.tgeng.archon.parser.ParseResult.*

private type ParseResultM[M[+_]] = [T] =>> ParseResult[M, T]

given[M[+_]] (using env: MonadPlus[M])(using dist: Distributor[M, ParseResultM[M]]): MonadPlus[ParseResultM[M]] with
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
      case Failure(b) => Failure(a ++ b)

given Distributor[List, ParseResultM[List]] with
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

given Distributor[Option, ParseResultM[Option]] with
  override def distribute[T](m: Option[ParseResult[Option, T]]): ParseResult[Option, Option[T]] = m match
    case Some(r) => r match
      case Success(r) => Success(Some(r))
      case Failure(e) => Failure(e)
    case None => throw IllegalStateException("Option in this usage should never be empty.")

trait ParserT[-I, +T, M[+_] : MonadPlus]:
  final def parse(input: IndexedSeq[I], index: Int = 0, targets: List[String] = Nil): ParseResult[M, (Int, T)] =
    doParse(index)(using input)(using targets)

  final def doParse(index: Int)(using input: IndexedSeq[I])(using targets: List[String]): ParseResult[M, (Int, T)] =
    parseImpl(index)(using input)(using targetName ++: targets)

  protected def parseImpl(index: Int)(using input: IndexedSeq[I])(using targets: List[String]): ParseResult[M, (Int, T)]

  def targetName: Option[String] = None

private type ParserM[-I, M[+_]] = [T] =>> ParserT[I, T, M]

given[I, M[+_] : MonadPlus] (using env: MonadPlus[ParseResultM[M]]): MonadPlus[ParserM[I, M]] with
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
