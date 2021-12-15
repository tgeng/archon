package io.github.tgeng.archon.parser

import io.github.tgeng.archon.common.*
import io.github.tgeng.archon.common.ListGivens.given
import io.github.tgeng.archon.parser.{*, given}
import org.scalatest.freespec.AnyFreeSpec

class ParserTest extends AnyFreeSpec {
  "name" in {
    val foobar = P(P.pure("a"))
    assert(foobar.targetName == Some("foobar"))
    foobar.multiParse("")
  }
}