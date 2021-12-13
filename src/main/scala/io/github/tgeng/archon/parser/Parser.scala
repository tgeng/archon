package io.github.tgeng.archon.parser

import io.github.tgeng.archon.common.{*, given}

case class ParseError(message: String, targets: Seq[String])

given Ordering[ParseError] with
  override def compare(x: ParseError, y: ParseError): Int = x.targets.size.compareTo(x.targets.size)

enum ParseResult[M[_] : MonadPlus, +T]:
  case Success[M[_] : MonadPlus, T](result: M[T]) extends ParseResult[M, T]
  case Failure[M[_] : MonadPlus, T](errors: Seq[ParseError]) extends ParseResult[M, T]

given[M[_]] (using env: MonadPlus[M]): MonadPlus[[T] =>> ParseResult[M, T]] with
  override def map[T, S](f: ParseResult[M, T], g: T => S): ParseResult[M, S] = ???

  override def pure[T](t: T): ParseResult[M, T] = ParseResult.Success(env.pure(t))

  override def flatMap[T, S](m: ParseResult[M, T], f: T => ParseResult[M, S]): ParseResult[M, S] = ???

  override def empty[T]: ParseResult[M, T] = ParseResult.Failure(Seq())

  override def or[T](a: ParseResult[M, T], b: => ParseResult[M, T]): ParseResult[M, T] = ???

trait ParserT[I, +T, M[_] : MonadPlus]:
  def parse(index: Int)(input: IndexedSeq[I]): (Int, ParseResult[M, T])

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
