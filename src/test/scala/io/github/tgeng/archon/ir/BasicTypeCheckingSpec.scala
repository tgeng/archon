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
    val nat = qn"archon/data/Nat"
    val z = n"Z"
    val s = n"S"

    +data(nat)()
      + constructor(z)()
      + constructor(s, nat())()

    "nat" in ~ {
      z() hasType nat()
      z() doesNotHaveType LevelType
      s(z()) hasType nat()

      nat() ->: F(nat()) hasType Type(0L)
    }

    val vector = qn"archon/data/Vector"
    val nil = n"Nil"
    val cons = n"Cons"
    +data(vector, LevelType, v(Type(!0)), v(nat()))(!2)
      + constructor(nil)(EqualityType(nat(), !0, z()))
      + constructor(cons, !1, nat(), vector(!4, !3, !0))(EqualityType(nat(), !1, !3))
  }
}
