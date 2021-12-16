package io.github.tgeng.archon.parser

import io.github.tgeng.archon.common.{*, given}
import io.github.tgeng.archon.parser.{*, given}
import io.github.tgeng.archon.parser.single.given
import org.scalatest.freespec.AnyFreeSpec

class ParserTest extends AnyFreeSpec {
  "name" in {
    val foobar: Parser[Any, String] = P(
      for
        (a, b) <- (P.pure("aa"), P.pure("bb"))
      yield
        a + b
    )
    assert(foobar.targetName == Some("foobar"))
    println(foobar.parse("").toString())
  }
}