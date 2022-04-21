package io.github.tgeng.archon.ir

import io.github.tgeng.archon.common.*

import QualifiedName.*
import VTerm.*

object Builtins:
  val BuiltinType = Builtin / "type"
  val BuiltinCType = Builtin / "ctype"
  val UnitTyQn = BuiltinType / "Unit"
  val UnitTy = DataType(UnitTyQn)
  val UnitQn = UnitTyQn / "Unit"
  val Unit = Con(Name.Normal("Unit"))

  val TypeQn = BuiltinType / "Type"
  val SubtypeOfQn = BuiltinType / "SubtypeOf"
  val TopQn = BuiltinType / "Top"
  val PureQn = BuiltinType / "Pure"
  val EqualityQn = BuiltinType / "Equality"
  val EffectsQn = BuiltinType / "Effects"
  val LevelQn = BuiltinType / "Level"
  val HeapQn = BuiltinType / "Heap"
  val CellQn = BuiltinType / "Cell"

  val CTypeQn = BuiltinCType / "Type"
  val CSubtypeOfQn = BuiltinCType / "SubtypeOf"
  val CTopQn = BuiltinCType / "Top"

  val BuiltinEffects = Builtin / "effects"
  val HeapEffQn = BuiltinEffects / "HeapEff"
  val EffectsUnion = BuiltinEffects / "|"

  val BuiltinLevel = Builtin / "level"
  val LevelSucQn = BuiltinLevel / "suc"
  val LevelMaxQn = BuiltinLevel / "max"

  import Declaration.*
  import CTerm.*
  import VTerm.*
  import ULevel.*

  val builtinDefinitions: Map[QualifiedName, (Definition, IndexedSeq[CheckedClause])] = Seq(

    /**
     * Type : (l : LevelType) -> Type(l + 1, Top(l + 1))
     * {l : LevelType} |- l := .return Type(l, Top(l))
     */
    (Builtins.TypeQn,
      FunctionType(
        Binding(LevelType)(n"l"),
        {
          val ul = USimpleLevel(LevelSuc(Var(0)))
          F(Type(ul, Top(ul)))
        }
      ),
      IndexedSeq(
        CheckedClause(
          ???, ???, ???, ???
        )
      )),

  ).map { case (qn, ty, clauses) => (qn, (new Definition(qn)(ty), clauses)) }.toMap

