package io.github.tgeng.archon.parser

import io.github.tgeng.archon.common.{*, given}
import io.github.tgeng.archon.parser.{*, given}
import io.github.tgeng.archon.parser.single.given
import org.scalatest.freespec.AnyFreeSpec

class ParserTest extends AnyFreeSpec {
  "name" in {
    val foobar = P(
      for
        a <- P.pure("a")
        if a == "b"
      yield
        "x"
    )
    assert(foobar.targetName == Some("foobar"))
    println(foobar.parse("").toString())
  }
}