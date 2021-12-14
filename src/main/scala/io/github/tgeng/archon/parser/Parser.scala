package io.github.tgeng.archon.parser

import io.github.tgeng.archon.common.{*, given}

case class ParseError(message: String, targets: Seq[String])

given Ordering[ParseError] with
  override def compare(x: ParseError, y: ParseError): Int = x.targets.size.compareTo(x.targets.size)

enum ParseResult[M[_] : MonadPlus, T]:
  case Success[M[_] : MonadPlus, T](result: M[T]) extends ParseResult[M, T]
  case Failure[M[_] : MonadPlus, T](errors: Seq[ParseError]) extends ParseResult[M, T]

import ParseResult.*

type ParseResultM[M[_]] = [T] =>> ParseResult[M, T]

given[M[_]] (using env: MonadPlus[M])(using dist: Distributor[M, ParseResultM[M]]): MonadPlus[ParseResultM[M]] with
  override def map[T, S](f: ParseResult[M, T], g: T => S): ParseResult[M, S] = f match
    case Success(results) => Success(results.map(g))
    case Failure(errors) => Failure(errors)

  override def pure[T](t: T): ParseResult[M, T] = Success(env.pure(t))

  override def flatMap[T, S](m: ParseResult[M, T], f: T => ParseResult[M, S]): ParseResult[M, S] = m match
      case Success(results) =>
        val distributed: ParseResult[M, M[S]] = dist.distribute(results.flatMap(t => env.pure(f(t))))
        distributed match
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

trait ParserT[-I, T, M[_] : MonadPlus]:
  def parse(index: Int)(input: IndexedSeq[I]): (Int, ParseResult[M, T])

given Distributor[List, ParseResultM[List]] with
  override def distribute[T](m: List[ParseResult[List, T]]): ParseResult[List, List[T]] =
    m.partition(r => r.isInstanceOf[Success[?, ?]]) match
      case (Nil, Nil) => Failure(Seq())
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
    case None => Failure(Seq())


//given[I, R[+_]] (using ParserResult[R]): MonadPlus[[T] =>> ParserT[I, T, R]] with
//  override def pure[S](s: S): ParserT[I, S, R] = new ParserT[I, S, R] :
//    override def parse(input: Seq[I]): (Seq[I], R[S]) = (input, pure(s))
//
//  override def empty[S]: ParserT[I, S, R] = ???
//
//  extension[T] (p: ParserT[I, T, R])
//    override def fmap[S](g: T => S): ParserT[I, S, R] = ???
//    override def bind[S](g: T => ParserT[I, S, R]): ParserT[I, S, R] = ???
//    override def <|>(q: => ParserT[I, T, R]): ParserT[I, T, R] = ???
