package com.github.tgeng.archon.core.ir.typing

import com.github.tgeng.archon.core.ir.*
import com.github.tgeng.archon.core.ir.EqDecidability.{EqDecidable, EqUnknown}
import com.github.tgeng.archon.core.ir.HandlerType.*
import com.github.tgeng.archon.core.ir.Usage.*
import com.github.tgeng.archon.core.ir.VTerm.*
import com.github.tgeng.archon.core.ir.testing.*
import org.scalatest.freespec.AnyFreeSpec

class BasicTypeCheckSpec extends AnyFreeSpec:
  given Context = Context.empty
  given Signature = SimpleSignature()
  given TypingContext = TypingContext()
  given SourceInfo = SourceInfo.SiEmpty
  "in empty context and signature" - {
    "check level literals" in:
      assertType(LevelLiteral(0), LevelType())
      assertType(LevelLiteral(1), LevelType())
      assertNotType(LevelLiteral(1, 1), LevelType())
      assertType(LevelLiteral(1, 0), LevelType(LevelLiteral(1, 1)))
      assertNotType(UsageLiteral(U0), LevelType())

    "check usage literals" in:
      assertType(UsageLiteral(U0), UsageType())
      assertType(UsageLiteral(U1), UsageType())
      assertType(UsageLiteral(UAny), UsageType(Some(UsageLiteral(U1))))
      assertType(UsageLiteral(UAny), UsageType(Some(UsageLiteral(U0))))
      assertType(UsageLiteral(UAny), UsageType(Some(UsageLiteral(UAff))))
      assertType(UsageLiteral(UAny), UsageType(Some(UsageLiteral(URel))))
      assertType(UsageLiteral(UAff), UsageType(Some(UsageLiteral(U0))))
      assertType(UsageLiteral(UAff), UsageType(Some(UsageLiteral(U1))))
      assertType(UsageLiteral(URel), UsageType(Some(UsageLiteral(U1))))
      assertNotType(UsageLiteral(U1), UsageType(Some(UsageLiteral(UAny))))
      assertNotType(UsageLiteral(U1), UsageType(Some(UsageLiteral(URel))))
      assertNotType(UsageLiteral(U1), UsageType(Some(UsageLiteral(UAff))))
      assertNotType(UsageLiteral(U1), UsageType(Some(UsageLiteral(U0))))
      assertNotType(LevelLiteral(1), UsageType())

    "check eq decidability literals" in:
      assertType(EqDecidabilityLiteral(EqDecidable), EqDecidabilityType())
      assertType(EqDecidabilityLiteral(EqUnknown), EqDecidabilityType())
      assertNotType(LevelLiteral(1), EqDecidabilityType())

    "check handler type literals" in:
      assertType(HandlerTypeLiteral(Simple), HandlerTypeType())
      assertType(HandlerTypeLiteral(Complex), HandlerTypeType())
      assertNotType(LevelLiteral(1), HandlerTypeType())

    "check type types" in:
      assertType(UsageType(), Type(UsageType()))
      assertType(UsageType(), Type(Top(LevelLiteral(0))))
      assertType(LevelType(), Type(LevelType()))
      assertNotType(LevelType(), Type(Top(LevelLiteral(0))))
      assertType(LevelType(), Type(Top(LevelLiteral(1, 0))))
  }
