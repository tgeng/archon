package io.github.tgeng.archon.parser

import io.github.tgeng.archon.common.{*, given}
import io.github.tgeng.archon.parser.{*, given}
import io.github.tgeng.archon.parser.ParseResult.*

extension[I, T, M[+_]] (using env: MonadPlus[ParserM[I, M]])(p: ParserT[I, T, M])
  def map[S](g: T => S) = env.map(p, g)

  infix def <*>[S](f: =>ParserT[I, T => S, M]) = env.starApply(p, f)

  def flatMap[S](f: T => ParserT[I, S, M]) = env.flatMap(p, f)

  infix def |(q: => ParserT[I, T, M]): ParserT[I, T, M] = env.or(p, q)

  inline def withFilter(inline predicate: T => Boolean) : ParserT[I, T, M] =
    for
      t <- p
      filtered <- if predicate(t) then P.pure(t) else P.fail(s"'$t' need to satisfy `${stringify(predicate)}`")
    yield filtered

