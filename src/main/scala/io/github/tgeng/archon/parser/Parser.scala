package io.github.tgeng.archon.parser

import io.github.tgeng.archon.common.{*, given}

trait ParserT[I, +T, R[+_]]:
  def parse(input: Seq[I]): (Seq[I], R[T])

given [I, R[+_]]: MonadPlus[[T] =>> ParserT[I, T, R]] with
  override def pure[S](s: S): ParserT[I, S, R] = ???

  override def empty[S]: ParserT[I, S, R] = ???

  extension [T] (p: ParserT[I, T, R])
    override def map[S](g: T => S): ParserT[I, S, R] = ???
    override def flatMap[S](g: T => ParserT[I, S, R]): ParserT[I, S, R] = ???
    override def <|>(q: ParserT[I, T, R]): ParserT[I, T, R] = ???
