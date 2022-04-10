package io.github.tgeng.archon.ir

import io.github.tgeng.archon.common.*

import QualifiedName.*
import VTerm.*

object Builtins:
  val BuiltinType = Builtin / "type"
  val UnitTy = DataType(BuiltinType / "Unit")
  val Unit = Con(Name.Normal("Unit"))

  val VTypeQn = BuiltinType / "VType"
  val VTopQn = BuiltinType / "VTop"
  val PureQn = BuiltinType / "Pure"
  val EqualityQn = BuiltinType / "Equality"
  val EffectsQn = BuiltinType / "Effects"
  val LevelQn = BuiltinType / "Level"
  val HeapQn = BuiltinType / "Heap"
  val CellQn = BuiltinType / "Cell"
  val UnitQn = BuiltinType / "Unit"
  
  val BuiltinEffects = Builtin / "effect"
  val HeapEffQn = BuiltinEffects / "HeapEff"

