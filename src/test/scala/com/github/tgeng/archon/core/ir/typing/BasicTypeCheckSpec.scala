package com.github.tgeng.archon.core.ir.typing

import com.github.tgeng.archon.common.Ref.given
import com.github.tgeng.archon.core.common.n
import com.github.tgeng.archon.core.ir.*
import com.github.tgeng.archon.core.ir.CTerm.*
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
      assertVType(LevelLiteral(0), LevelType())
      assertVType(LevelLiteral(1), LevelType())
      assertNotVType(LevelLiteral(1, 1), LevelType())
      assertVType(LevelLiteral(1, 0), LevelType(LevelLiteral(1, 1)))
      assertNotVType(UsageLiteral(U0), LevelType())

    "check usage literals" in:
      assertVType(UsageLiteral(U0), UsageType())
      assertVType(UsageLiteral(U1), UsageType())
      assertVType(UsageLiteral(UAny), UsageType(Some(UsageLiteral(U1))))
      assertVType(UsageLiteral(UAny), UsageType(Some(UsageLiteral(U0))))
      assertVType(UsageLiteral(UAny), UsageType(Some(UsageLiteral(UAff))))
      assertVType(UsageLiteral(UAny), UsageType(Some(UsageLiteral(URel))))
      assertVType(UsageLiteral(UAff), UsageType(Some(UsageLiteral(U0))))
      assertVType(UsageLiteral(UAff), UsageType(Some(UsageLiteral(U1))))
      assertVType(UsageLiteral(URel), UsageType(Some(UsageLiteral(U1))))
      assertNotVType(UsageLiteral(U1), UsageType(Some(UsageLiteral(UAny))))
      assertNotVType(UsageLiteral(U1), UsageType(Some(UsageLiteral(URel))))
      assertNotVType(UsageLiteral(U1), UsageType(Some(UsageLiteral(UAff))))
      assertNotVType(UsageLiteral(U1), UsageType(Some(UsageLiteral(U0))))
      assertNotVType(LevelLiteral(1), UsageType())

    "check eq decidability literals" in:
      assertVType(EqDecidabilityLiteral(EqDecidable), EqDecidabilityType())
      assertVType(EqDecidabilityLiteral(EqUnknown), EqDecidabilityType())
      assertNotVType(LevelLiteral(1), EqDecidabilityType())

    "check handler type literals" in:
      assertVType(HandlerTypeLiteral(Simple), HandlerTypeType())
      assertVType(HandlerTypeLiteral(Complex), HandlerTypeType())
      assertNotVType(LevelLiteral(1), HandlerTypeType())

    "check vtype types" in:
      assertVType(UsageType(), Type(UsageType()))
      assertVType(UsageType(), Type(Top(LevelLiteral(0))))
      assertVType(LevelType(), Type(LevelType()))
      assertNotVType(LevelType(), Type(Top(LevelLiteral(0))))
      assertVType(LevelType(), Type(Top(LevelLiteral(1, 0))))

    "check return type" in:
      assertCType(Return(LevelLiteral(0), UsageLiteral(U1)), F(LevelType()))
      assertCType(Return(LevelLiteral(0), UsageLiteral(U1)), F(LevelType(), Div()))
      assertNotCType(
        Return(LevelLiteral(0), UsageLiteral(U1)),
        F(LevelType(), Total(), VTerm.UsageLiteral(U0)),
      )
      assertNotCType(Return(LevelLiteral(0), UsageLiteral(U1)), F(UsageType()))

    "check ctype types" in:
      assertCType(
        FunctionType(Binding(LevelType(), UsageLiteral(U0))(n"a"), F(UsageType())),
        CType(CTop(LevelLiteral(1, 0))),
      )
      assertNotCType(
        FunctionType(Binding(LevelType(), UsageLiteral(U0))(n"a"), F(UsageType())),
        CType(CTop(LevelLiteral(0, 2))),
      )
  }
