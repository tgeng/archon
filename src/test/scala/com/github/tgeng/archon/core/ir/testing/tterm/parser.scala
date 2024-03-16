package com.github.tgeng.archon.core.ir.testing.tterm

import fastparse.NoWhitespace.{*, given}
import fastparse.{*, given}

import scala.language.unsafeNulls

object Parser {
  private def id[$: P]: P[String] = P((CharIn("a-zA-Z_") ~ CharIn("a-zA-Z0-9_").rep).!)
}
