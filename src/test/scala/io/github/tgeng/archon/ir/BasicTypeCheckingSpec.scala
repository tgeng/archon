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
    v(Type(0L)) hasType v(Type(1L))
    v(Type(0L)) hasType v(Type(2L))
    v(Type(0L)) doesNotHaveType  v(Type(0L))
    c(Type(0L)) hasType c(Type(1L))
    c(Type(0L)) hasType c(Type(2L))
    c(Type(0L)) doesNotHaveType  c(Type(0L))

    v(Type(0L)) ⪯ v(Type(1L))
    c(Type(0L)) ⪯ c(Type(1L))
  }
}
