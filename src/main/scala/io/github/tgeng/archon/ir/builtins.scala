package io.github.tgeng.archon.ir

import io.github.tgeng.archon.common.*

import QualifiedName.*
import VTerm.*

object Builtins:
  val BuiltinType = Builtin / "type"
  val BuiltinCType = Builtin / "ctype"

  val TypeQn = BuiltinType / "Type"
  val SubtypeOfQn = BuiltinType / "SubtypeOf"
  val TopQn = BuiltinType / "Top"
  val PureQn = BuiltinType / "Pure"

  val EqualityQn = BuiltinType / "Equality"
  val EffectsQn = BuiltinType / "Effects"
  val LevelQn = BuiltinType / "Level"
  val HeapQn = BuiltinType / "Heap"
  val CellQn = BuiltinType / "Cell"

  val UnitTyQn = BuiltinType / "Unit"
  val UnitTy = DataType(UnitTyQn)
  val UnitQn = UnitTyQn / "Unit"
  val Unit = Con(Name.Normal("Unit"))


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
  import CoPattern.*
  import Pattern.*

  val builtinDefinitions: Map[QualifiedName, (Definition, IndexedSeq[CheckedClause])] = Seq(

    /**
     * Type : (level : LevelType) -> Type(level + 1, Top(level + 1))
     * {level : LevelType} |- level := .return Type(level, Top(l))
     */
    (Builtins.TypeQn,
      FunctionType(
        Binding(LevelType)(n"level"),
        F(Type(USimpleLevel(LevelSuc(Var(0))), Top(USimpleLevel(LevelSuc(Var(0))))))
      ),
      IndexedSeq(
        CheckedClause(
          Binding(LevelType)(n"level") :: Nil,
          CPattern(PVar(0)) :: Nil,
          Return(Type(USimpleLevel(Var(0)), Top(USimpleLevel(Var(0))))),
          F(Type(USimpleLevel(LevelSuc(Var(0))), Top(USimpleLevel(LevelSuc(Var(0))))))
        )
      )),

    /**
     * SubTypeOf : (level : LevelType) -> Type(level, Top(level)) -> Type(level + 1, Top(level + 1))
     * {level : LevelType, upperBound: Type(level, Top(level))} |- level upperBound := .return Type(level, upperBound)
     */
    (Builtins.SubtypeOfQn,
      FunctionType(
        Binding(LevelType)(n"level"),
        FunctionType(
          Binding(Type(USimpleLevel(Var(0)), Top(USimpleLevel(Var(0)))))(n"upperBound"),
          F(Type(USimpleLevel(LevelSuc(Var(1))), Top(USimpleLevel(LevelSuc(Var(1))))))
        )
      ),
      IndexedSeq(
        CheckedClause(
          Binding(LevelType)(n"level") ::
            Binding(Type(USimpleLevel(Var(0)), Top(USimpleLevel(Var(0)))))(n"upperBound") ::
            Nil,
          CPattern(PVar(1)) :: CPattern(PVar(0)) :: Nil,
          Return(Type(USimpleLevel(Var(1)), Var(0))),
          F(Type(USimpleLevel(LevelSuc(Var(1))), Top(USimpleLevel(LevelSuc(Var(1))))))
        )
      )
    ),

    /**
     * Top : (level : LevelType) -> Type(level, Top(level))
     * {level : LevelType} |- level := .return Top(level)
     */
    (
      Builtins.TopQn,
      FunctionType(
        Binding(LevelType)(n"level"),
        F(Type(USimpleLevel(Var(0)), Top(USimpleLevel(Var(0)))))
      ),
      IndexedSeq(
        CheckedClause(
          Binding(LevelType)(n"level") :: Nil,
          CPattern(PVar(0)) :: Nil,
          Return(Top(USimpleLevel(Var(0)))),
          F(Type(USimpleLevel(Var(0)), Top(USimpleLevel(Var(0)))))
        )
      )
    ),

    /**
     * Pure : (level : LevelType) -> Type(level, Pure(level))
     * {level : LevelType} |- level := .return Pure(level)
     */
    (
      Builtins.PureQn,
      FunctionType(
        Binding(LevelType)(n"level"),
        F(Type(USimpleLevel(Var(0)), Pure(USimpleLevel(Var(0)))))
      ),
      IndexedSeq(
        CheckedClause(
          Binding(LevelType)(n"level") :: Nil,
          CPattern(PVar(0)) :: Nil,
          Return(Pure(USimpleLevel(Var(0)))),
          F(Type(USimpleLevel(Var(0)), Pure(USimpleLevel(Var(0)))))
        )
      )
    ),

    /**
     * Equality : (level : LevelType) -> (ty : Type(level, Top(level)) -> (x : ty) -> (y : ty) -> Type(level, Equality(ty, x, y))
     * {level: Level, ty : Type... , x : ty, y : ty} |- _ ty x y = Equality(ty, x, y)
     */
    (
      Builtins.EqualityQn,
      FunctionType(
        Binding(LevelType)(n"level"),
        FunctionType(
          Binding(Type(USimpleLevel(Var(0)), Top(USimpleLevel(Var(0)))))(n"type"),
          FunctionType(
            Binding(Var(0))(n"x"),
            FunctionType(
              Binding(Var(1))(n"y"),
              F(Type(USimpleLevel(Var(3)), EqualityType(Var(2), Var(1), Var(0))))
            )
          )
        )
      ),
      IndexedSeq(
        CheckedClause(
          Binding(LevelType)(n"level") ::
            Binding(Type(USimpleLevel(Var(0)), Top(USimpleLevel(Var(0)))))(n"type") ::
            Binding(Var(0))(n"x") ::
            Binding(Var(1))(n"y") :: Nil,
          CPattern(PVar(2)) :: CPattern(PVar(1)) :: CPattern(PVar(0)) :: Nil,
          Return(EqualityType(Var(2), Var(1), Var(0))),
          F(Type(USimpleLevel(Var(3)), EqualityType(Var(2), Var(1), Var(0))))
        )
      )
    ),

    /**
     * Effects : Type(0, Effects)
     * {} |- := Effects
     */
    (
      Builtins.EffectsQn,
      F(Type(USimpleLevel(LevelLiteral(0)), EffectsType)),
      IndexedSeq(
        CheckedClause(
          Nil,
          Nil,
          Return(EffectsType),
          F(Type(USimpleLevel(LevelLiteral(0)), EffectsType))
        )
      )
    ),

    /**
     * Level : TYPE0
     * {} |- := Level
     */
    (
      Builtins.LevelQn,
      F(Type(UωLevel(0), LevelType)),
      IndexedSeq(
        CheckedClause(
          Nil,
          Nil,
          Return(LevelType),
          F(Type(UωLevel(0), LevelType))
        )
      )
    ),

    /**
     * Heap : Type(0, Heap)
     * {} |- := Heap
     */
    (
      Builtins.HeapQn,
      F(Type(USimpleLevel(LevelLiteral(0)), HeapType)),
      IndexedSeq(
        CheckedClause(
          Nil,
          Nil,
          Return(HeapType),
          F(Type(USimpleLevel(LevelLiteral(0)), HeapType))
        )
      )
    ),

  ).map { case (qn, ty, clauses) => (qn, (new Definition(qn)(ty), clauses)) }.toMap

  def getBigType(qn: QualifiedName): Option[(Definition, IndexedSeq[CheckedClause])] =
    // TODO: it seems big SubtypeOf is not that useful so I will skip it for now.
    import Name.*
    import QualifiedName.*
    for
      (isComputation, layer) <-
        qn match
          case Node(BuiltinType, Normal(name)) if name.startsWith("TYPE") =>
            name.drop(4).toIntOption.map((false, _))
          case Node(BuiltinCType, Normal(name)) if name.startsWith("TYPE") =>
            name.drop(4).toIntOption.map((true, _))
          case _ => None
      if layer >= 0
    yield (
      new Definition(qn)(
        if isComputation then
          CType(UωLevel(layer + 1), CType(UωLevel(layer), CTop(UωLevel(layer))))
        else
          F(Type(UωLevel(layer + 1), Type(UωLevel(layer), Top(UωLevel(layer)))))
      ),
      IndexedSeq(
        CheckedClause(
          Nil,
          Nil,
          if isComputation then
            CType(UωLevel(layer), CTop(UωLevel(layer)))
          else
            Return(Type(UωLevel(layer), Top(UωLevel(layer)))),
          if isComputation then
            CType(UωLevel(layer + 1), CType(UωLevel(layer), CTop(UωLevel(layer))))
          else
            F(Type(UωLevel(layer + 1), Type(UωLevel(layer), Top(UωLevel(layer)))))

        )
      )
    )
