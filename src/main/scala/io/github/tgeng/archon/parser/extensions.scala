package io.github.tgeng.archon.parser

import io.github.tgeng.archon.common.{*, given}
import io.github.tgeng.archon.parser.given
import io.github.tgeng.archon.parser.ParseResult.*

extension[I, T, M[+_]] (using env: MonadPlus[ParserM[I, M]])(p: ParserT[I, T, M])
  infix def |(q: => ParserT[I, T, M]): ParserT[I, T, M] = p <|> q
