package io.github.tgeng.archon.ir

import io.github.tgeng.archon.common.*
import io.github.tgeng.archon.common.ir.*
import io.github.tgeng.archon.common.ir.TermBuilders.{given, *}

import VTerm.*
import CTerm.*
import ULevel.*

class BasicTypeCheckingSpec extends SignatureSpec {
  "builtins" in ~ {
    +Binding(LevelType)(n"l")
    !0 hasType LevelType
    !0 doesNotHaveType  EffectsType
    0L hasType LevelType
    0L doesNotHaveType EffectsType
  }
}
