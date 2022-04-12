package io.github.tgeng.archon.ir

import io.github.tgeng.archon.common.*
import io.github.tgeng.archon.common.ir.*
import io.github.tgeng.archon.common.ir.TermBuilders.{*, given}
import VTerm.*
import CTerm.*
import ULevel.*
import Declaration.*
import Builtins.*

import scala.collection.immutable.ListSet

class BasicTypeCheckingSpec extends SignatureSpec {
  +Effect(HeapEffQn)(Binding(HeapType)(n"heap") :: Nil)

  "builtins" in ~ {
    +Binding(LevelType)(n"l")
    !0 hasType LevelType
    !0 doesNotHaveType EffectsType
    0L hasType LevelType
    0L doesNotHaveType EffectsType
    v(Type(0L)) hasType Type(1L)
    v(Type(0L)) hasType Type(2L)
    v(Type(0L)) doesNotHaveType Type(0L)
    c(Type(0L)) hasType Type(1L)
    c(Type(0L)) hasType Type(2L)
    c(Type(0L)) doesNotHaveType Type(0L)

    v(Type(0L)) ⪯ Type(1L)
    c(Type(0L)) ⪯ Type(1L)

    0L ⋠ 1L

    HeapType hasType Type(0L)
    Heap(GlobalHeapKey) hasType HeapType

    CellType(Heap(GlobalHeapKey), LevelType, CellStatus.Uninitialized) hasType Type(UωLevel(0))
    CellType(Heap(GlobalHeapKey), LevelType, CellStatus.Uninitialized) doesNotHaveType Type(0L)

    EqualityType(LevelType, 0L, 0L) doesNotHaveType Type(0L)
    EqualityType(LevelType, 0L, 0L) hasType Type(UωLevel(0))
    Refl hasType EqualityType(LevelType, 0L, 0L)
    Refl doesNotHaveType EqualityType(LevelType, 0L, 1L)

    EqualityType(
      EffectsType,
      HeapEffQn(Heap(GlobalHeapKey)),
      HeapEffQn(Heap(GlobalHeapKey)),
    ) hasType Type(0L)

    F(LevelType) hasType Type(UωLevel(0))
    F(LevelType) doesNotHaveType Type(0L)

    EffectsType ->: F(EffectsType) hasType Type(0L)
    EffectsType ->: EffectsType ->: F(EffectsType) hasType Type(0L)
    LevelType ->: F(EffectsType) hasType Type(UωLevel(0))
  }

  "basic data type" - ~ {
    val natQn = qn"archon/data/Nat"
    +Data(natQn)()
      + constructor(n"Z")()
      + constructor(n"S", natQn())()
    "nat" in ~ {
      n"Z"() hasType natQn()
      n"Z"() doesNotHaveType LevelType
      n"S"(n"Z"()) hasType natQn()
    }
  }
}
