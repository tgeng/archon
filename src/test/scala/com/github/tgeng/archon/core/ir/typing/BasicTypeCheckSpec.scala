package com.github.tgeng.archon.core.ir.typing

import com.github.tgeng.archon.core.ir.*
import com.github.tgeng.archon.core.ir.VTerm.*
import com.github.tgeng.archon.core.ir.testing.*
import org.scalatest.freespec.AnyFreeSpec

class BasicTypeCheckSpec extends AnyFreeSpec:
  given Context = Context.empty
  given Signature = SimpleSignature()
  given TypingContext = TypingContext()
  given SourceInfo = SourceInfo.SiEmpty
  "In empty context and signature" - {
    "Check literals" in:
      assertType(LevelLiteral(0), LevelType())
  }
