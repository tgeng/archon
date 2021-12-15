package io.github.tgeng.archon.parser

import io.github.tgeng.archon.common.{*, given}
import io.github.tgeng.archon.parser.given
import io.github.tgeng.archon.parser.ParseResult.*

extension[I, T, M[+_]] (using env: MonadPlus[ParserM[I, M]])(p: ParserT[I, T, M])
  def parse(input: IndexedSeq[I], index: Int = 0, targets: List[String] = Nil): ParseResult[M, (Int, T)] =
    p.doParse(index)(using input)(using targets)

  infix def |(q: => ParserT[I, T, M]): ParserT[I, T, M] = p <|> q
