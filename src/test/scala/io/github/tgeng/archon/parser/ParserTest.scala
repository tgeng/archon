package io.github.tgeng.archon.parser

import io.github.tgeng.archon.common.{*, given}
import io.github.tgeng.archon.parser.{*, given}
import org.scalatest.freespec.AnyFreeSpec

class ParserTest extends AnyFreeSpec {
  "name" in {
    val foobar: ParserT[Char, String, Option] = P(P.pure("a"))
    assert(foobar.targetName == Some("foobar"))
  }
}