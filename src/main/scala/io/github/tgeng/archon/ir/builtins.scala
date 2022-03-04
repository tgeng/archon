package io.github.tgeng.archon.ir

import io.github.tgeng.archon.common.*

import QualifiedName.*
import VTerm.*

object Builtins:
  val UnitTy = DataType(Builtin/"Unit")
  val Unit = Con(Name.Normal("Unit"))
  
  val VUniverseQn = Builtin / "VUniverse"
  val VTopQn = Builtin / "VTop"
  val EqualityQn = Builtin / "Equality"
  val EffectsQn = Builtin / "Effects"
  val LevelQn = Builtin / "Level"
  val HeapQn = Builtin / "Heap"
  val CellQn = Builtin / "Cell"

