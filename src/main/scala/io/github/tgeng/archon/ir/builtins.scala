package io.github.tgeng.archon.ir

import io.github.tgeng.archon.common.*

import QualifiedName.*
import VTerm.*

object Builtins:
  val BuiltinType = Builtin / "type"
  val UnitTyQn = BuiltinType / "Unit"
  val UnitTy = DataType(UnitTyQn)
  val UnitQn = UnitTyQn / "Unit"
  val Unit = Con(Name.Normal("Unit"))

  val TypeQn = BuiltinType / "Type"
  val TopQn = BuiltinType / "Top"
  val PureQn = BuiltinType / "Pure"
  val CTypeQn = BuiltinType / "CType"
  val CTopQn = BuiltinType / "CTop"
  val EqualityQn = BuiltinType / "Equality"
  val EffectsQn = BuiltinType / "Effects"
  val LevelQn = BuiltinType / "Level"
  val HeapQn = BuiltinType / "Heap"
  val CellQn = BuiltinType / "Cell"
  
  val BuiltinEffects = Builtin / "effects"
  val HeapEffQn = BuiltinEffects / "HeapEff"
  val EffectsUnion = BuiltinEffects / "|"

  val BuiltinLevel = Builtin / "level"
  val LevelSuc = BuiltinLevel / "suc"
  val LevelMax = BuiltinLevel / "max"



