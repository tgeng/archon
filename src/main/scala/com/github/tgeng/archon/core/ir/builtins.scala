package com.github.tgeng.archon.core.ir

import com.github.tgeng.archon.core.common.*
import collection.immutable.ListSet

import QualifiedName.*
import VTerm.*

object Builtins:
  val BuiltinType = Builtin / "type"

  val TypeQn = BuiltinType / "Type"
  val SubtypeOfQn = BuiltinType / "SubtypeOf"
  val TopQn = BuiltinType / "Top"
  val PureQn = BuiltinType / "Pure"
  val CTypeQn = BuiltinType / "CType"
  val CSubtypeOfQn = BuiltinType / "CSubtypeOf"
  val CTopQn = BuiltinType / "CTop"

  val EqualityQn = BuiltinType / "Equality"
  val CellQn = BuiltinType / "Cell"
  val UCellQn = BuiltinType / "UCell"
  val EffectsQn = BuiltinType / "Effects"
  val LevelQn = BuiltinType / "Level"
  val HeapQn = BuiltinType / "Heap"

  val UnitTypeQn = BuiltinType / "Unit"
  val UnitQn = UnitTypeQn / "MkUnit"

  val BuiltinEffects = Builtin / "effects"
  val HeapEffQn = BuiltinEffects / "heap"
  val AllocOpQn = HeapEffQn / "alloc"
  val GetOpQn = HeapEffQn / "get"
  val SetOpQn = HeapEffQn / "set"
  val GlobalHeapKeyQn = HeapEffQn / "global"
  val EffectsUnionQn = BuiltinEffects / "union"
  val TotalQn = BuiltinEffects / "total"

  val BuiltinLevel = Builtin / "level"
  val LevelSucQn = BuiltinLevel / "suc"
  val LevelMaxQn = BuiltinLevel / "max"

  import Declaration.*
  import CTerm.*
  import VTerm.*
  import ULevel.*
  import CoPattern.*
  import Pattern.*

  val builtinData: Map[QualifiedName, (Data, IndexedSeq[Constructor])] = Seq(
    b(
      Builtins.UnitTypeQn, (
        /* tParamTys*/ Nil,
        /* ul */ USimpleLevel(LevelLiteral(0)),
        /* numParams */ 0,
        /* isPure */ true,
        /* constructors */ IndexedSeq(
        Constructor(n"MkUnit", Nil, Nil)
      ))
    ),
    b(
      Builtins.EqualityQn, (
        /* tParamTys*/
        (Binding(LevelType())(n"level"), Variance.COVARIANT) ::
          (Binding(
            Type(
              USimpleLevel(Var(0)),
              Top(USimpleLevel(Var(0)))
            )
          )(n"A"), Variance.COVARIANT) ::
          (Binding(Var(0))(n"x"), Variance.COVARIANT) ::
          (Binding(Var(1))(n"y"), Variance.COVARIANT) ::
          Nil,
        /* ul */ USimpleLevel(Var(3)),
        /* numParams */ 3,
        /* isPure */ true,
        /* constructors */ IndexedSeq(
        Constructor(n"Refl", Nil, Var(3) :: Var(2) :: Var(1) :: Var(1) :: Nil)
      ))
    ),
    b(
      Builtins.CellQn, (
        /* tParamTys*/
        (Binding(LevelType())(n"level"), Variance.COVARIANT) ::
          (Binding(HeapType())(n"h"), Variance.COVARIANT) ::
          (Binding(
            Type(
              USimpleLevel(Var(1)),
              Top(USimpleLevel(Var(1)))
            )
          )(n"A"), Variance.INVARIANT) ::
          Nil,
        /* ul */ USimpleLevel(Var(2)),
        /* numParams */ 3,
        /* isPure */ true,
        /* constructors */ IndexedSeq(
        Constructor(
          n"MkCell",
          Binding(CellType(Var(1), Var(0), CellStatus.Initialized))(n"delegate") :: Nil,
          Var(3) :: Var(2) :: Var(1) :: Nil
        )
      ))
    ),
    b(
      Builtins.UCellQn, (
        /* tParamTys*/
        (Binding(LevelType())(n"level"), Variance.COVARIANT) ::
          (Binding(HeapType())(n"h"), Variance.COVARIANT) ::
          (Binding(
            Type(
              USimpleLevel(Var(1)),
              Top(USimpleLevel(Var(1)))
            )
          )(n"A"), Variance.INVARIANT) ::
          Nil,
        /* ul */ USimpleLevel(Var(2)),
        /* numParams */ 3,
        /* isPure */ true,
        /* constructors */ IndexedSeq(
        Constructor(
          n"MkUCell",
          Binding(CellType(Var(1), Var(0), CellStatus.Uninitialized))(n"delegate") :: Nil,
          Var(3) :: Var(2) :: Var(1) :: Nil
        )
      ))
    ),
  ).map {
    case (qn, (tParamTys, ul, numParams, isPure, constructors)) =>
      (qn, (new Data(qn)(tParamTys, ul, numParams, isPure), constructors))
  }.toMap

  val builtinRecords: Map[QualifiedName, (Record, IndexedSeq[Field])] = Seq(
    // There does not seem to be any essential records that should included here.
    //    (???,
    //      /* tParamTys*/ ???,
    //      /* ul */ ???,
    //      /* fields */ ???)
  ).map {
    case (qn, (tParamTys, ul, fields)) =>
      (qn, (new Record(qn)(tParamTys, ul), fields))
  }.toMap

  val builtinDefinitions: Map[QualifiedName, (Definition, IndexedSeq[Clause])] = Seq(

    /**
     * Type : (level : LevelType) -> Type(level + 1, Type(level, Top(l)))
     * {level : LevelType} |- level := .return Type(level, Top(l))
     */
    b(
      Builtins.TypeQn, (
        FunctionType(
          Binding(LevelType())(n"level"),
          F(
            Type(
              USimpleLevel(LevelSuc(Var(0))),
              Type(USimpleLevel(Var(0)), Top(USimpleLevel(Var(0))))
            )
          )
        ),
        IndexedSeq(
          Clause(
            Binding(LevelType())(n"level") :: Nil,
            CPattern(PVar(0)) :: Nil,
            Return(Type(USimpleLevel(Var(0)), Top(USimpleLevel(Var(0))))),
            F(
              Type(
                USimpleLevel(LevelSuc(Var(0))),
                Type(USimpleLevel(Var(0)), Top(USimpleLevel(Var(0))))
              )
            )
          )
        ))
    ),

    /**
     * SubtypeOf : (level : LevelType) -> (upperBound : Type(level, Top(level))) -> Type(level + 1, Type(level, upperBound))
     * {level : LevelType, upperBound: Type(level, Top(level))} |- level upperBound := .return Type(level, upperBound)
     */
    b(
      Builtins.SubtypeOfQn, (
        FunctionType(
          Binding(LevelType())(n"level"),
          FunctionType(
            Binding(
              Type(
                USimpleLevel(Var(0)),
                Top(USimpleLevel(Var(0)))
              )
            )(n"upperBound"),
            F(Type(USimpleLevel(LevelSuc(Var(1))), Type(USimpleLevel(Var(1)), Var(0))))
          )
        ),
        IndexedSeq(
          Clause(
            Binding(LevelType())(n"level") ::
              Binding(
                Type(
                  USimpleLevel(Var(0)),
                  Top(USimpleLevel(Var(0)))
                )
              )(n"upperBound") ::
              Nil,
            CPattern(PVar(1)) :: CPattern(PVar(0)) :: Nil,
            Return(Type(USimpleLevel(Var(1)), Var(0))),
            F(Type(USimpleLevel(LevelSuc(Var(1))), Type(USimpleLevel(Var(1)), Var(0))))
          )
        )
      )
    ),

    /**
     * Top : (level : LevelType) -> Type(level, Top(level))
     * {level : LevelType} |- level := .return Top(level)
     */
    b(
      Builtins.TopQn, (
        FunctionType(
          Binding(LevelType())(n"level"),
          F(Type(USimpleLevel(Var(0)), Top(USimpleLevel(Var(0)))))
        ),
        IndexedSeq(
          Clause(
            Binding(LevelType())(n"level") :: Nil,
            CPattern(PVar(0)) :: Nil,
            Return(Top(USimpleLevel(Var(0)))),
            F(Type(USimpleLevel(Var(0)), Top(USimpleLevel(Var(0)))))
          )
        )
      )
    ),

    /**
     * Pure : (level : LevelType) -> Type(level, Pure(level))
     * {level : LevelType} |- level := .return Pure(level)
     */
    b(
      Builtins.PureQn, (
        FunctionType(
          Binding(LevelType())(n"level"),
          F(Type(USimpleLevel(Var(0)), Pure(USimpleLevel(Var(0)))))
        ),
        IndexedSeq(
          Clause(
            Binding(LevelType())(n"level") :: Nil,
            CPattern(PVar(0)) :: Nil,
            Return(Pure(USimpleLevel(Var(0)))),
            F(Type(USimpleLevel(Var(0)), Pure(USimpleLevel(Var(0)))))
          )
        )
      )
    ),

    /**
     * Effects : Type(0, Effects)
     * {} |- := Effects
     */
    b(
      Builtins.EffectsQn, (
        F(Type(USimpleLevel(LevelLiteral(0)), EffectsType())),
        IndexedSeq(
          Clause(
            Nil,
            Nil,
            Return(EffectsType()),
            F(Type(USimpleLevel(LevelLiteral(0)), EffectsType()))
          )
        )
      )
    ),

    /**
     * Level : TYPE0
     * {} |- := Level
     */
    b(
      Builtins.LevelQn, (
        F(Type(UωLevel(0), LevelType())),
        IndexedSeq(
          Clause(
            Nil,
            Nil,
            Return(LevelType()),
            F(Type(UωLevel(0), LevelType()))
          )
        )
      )
    ),

    /**
     * Heap : Type(0, Heap)
     * {} |- := Heap
     */
    b(
      Builtins.HeapQn, (
        F(Type(USimpleLevel(LevelLiteral(0)), HeapType())),
        IndexedSeq(
          Clause(
            Nil,
            Nil,
            Return(HeapType()),
            F(Type(USimpleLevel(LevelLiteral(0)), HeapType()))
          )
        )
      )
    ),

    /**
     * CType : (level : LevelType) -> (effects: EffectsType) -> CType(level + 1, CType(level, effects), Total)
     * {level : LevelType, effects : EffectsType} level effects := CType(level, CTop(level), effects)
     */
    b(
      Builtins.CTypeQn, (
        FunctionType(
          Binding(LevelType())(n"level"),
          FunctionType(
            Binding(EffectsType())(n"effects"),
            CType(
              USimpleLevel(LevelSuc(Var(1))),
              CType(USimpleLevel(Var(1)), CTop(USimpleLevel(Var(1)), Var(0)))
            )
          )
        ),
        IndexedSeq(
          Clause(
            Binding(LevelType())(n"level") :: Binding(EffectsType())(n"effects") :: Nil,
            CPattern(PVar(1)) :: CPattern(PVar(0)) :: Nil,
            CType(USimpleLevel(Var(1)), CTop(USimpleLevel(Var(1)), Var(0))),
            CType(
              USimpleLevel(LevelSuc(Var(1))),
              CType(USimpleLevel(Var(1)), CTop(USimpleLevel(Var(1)), Var(0)))
            )
          )
        )
      )
    ),

    /**
     * CSubtypeOf : (level : LevelType) -> (effects: EffectsType) -> (upperBound : U(CType(level, CTop(level, effects)))) -> CType(level + 1, .force upperBound, Total)
     * {level : LevelType, effects: Effects, upperBound: U(CType(level + 1, CTop(level, effects)))} |- level effects upperBound := CType(level, .force upperBound, effects)
     */
    b(
      Builtins.CSubtypeOfQn, (
        FunctionType(
          Binding(LevelType())(n"level"),
          FunctionType(
            Binding(EffectsType())(n"effects"),
            FunctionType(
              Binding(
                U(CType(USimpleLevel(Var(1)), CTop(USimpleLevel(Var(1)), Var(0))))
              )(n"upperBound"),
              CType(
                USimpleLevel(LevelSuc(Var(2))),
                CType(USimpleLevel(Var(2)), Force(Var(0)), Var(1))
              )
            )
          )
        ),
        IndexedSeq(
          Clause(
            Binding(LevelType())(n"level") ::
              Binding(EffectsType())(n"effects") ::
              Binding(
                U(CType(USimpleLevel(Var(1)), CTop(USimpleLevel(Var(1)), Var(0))))
              )(n"upperBound") ::
              Nil,
            CPattern(PVar(2)) :: CPattern(PVar(1)) :: CPattern(PVar(0)) :: Nil,
            CType(USimpleLevel(Var(2)), Force(Var(0)), Var(1)),
            CType(
              USimpleLevel(LevelSuc(Var(2))),
              CType(USimpleLevel(Var(2)), Force(Var(0)), Var(1))
            )
          )
        )
      )
    ),

    /**
     * CTop : (level : LevelType) -> (effects : EffectsType) -> CType(level, CTop(level, effects))
     * {level : LevelType, effects : EffectsType} |- level effects := CTop(level, effects)
     */
    b(
      Builtins.CTopQn, (
        FunctionType(
          Binding(LevelType())(n"level"),
          FunctionType(
            Binding(EffectsType())(n"effects"),
            CType(USimpleLevel(Var(1)), CTop(USimpleLevel(Var(1)), Var(0)))
          ),
        ),
        IndexedSeq(
          Clause(
            Binding(LevelType())(n"level") :: Binding(EffectsType())(n"effects") :: Nil,
            CPattern(PVar(1)) :: CPattern(PVar(0)) :: Nil,
            CTop(USimpleLevel(Var(1)), Var(0)),
            CType(USimpleLevel(Var(1)), CTop(USimpleLevel(Var(1)), Var(0)))
          )
        )
      )
    ),

    /**
     * union : (eff1 : EffectsType) -> (eff2 : EffectsType) -> EffectsType
     * {eff1 : EffectsType, eff2 : EffectsType} |- eff1 eff2 := EffectsUnion(eff1, eff2)
     */
    b(
      Builtins.EffectsUnionQn, (
        FunctionType(
          Binding(EffectsType())(n"eff1"),
          FunctionType(
            Binding(EffectsType())(n"eff2"),
            F(EffectsType())
          )
        ),
        IndexedSeq(
          Clause(
            Binding(EffectsType())(n"eff1") :: Binding(EffectsType())(n"eff2") :: Nil,
            CPattern(PVar(1)) :: CPattern(PVar(0)) :: Nil,
            Return(EffectsUnion(Var(1), Var(0))),
            F(EffectsType())
          )
        )
      )
    ),

    /**
     * suc : (level : LevelType) -> LevelType
     * {level : LevelType} |- level := level + 1
     */
    b(
      Builtins.LevelSucQn, (
        FunctionType(
          Binding(LevelType())(n"level"),
          F(LevelType())
        ),
        IndexedSeq {
          Clause(
            Binding(LevelType())(n"level") :: Nil,
            CPattern(PVar(0)) :: Nil,
            Return(LevelSuc(Var(0))),
            F(LevelType())
          )
        }
      )
    ),

    /**
     * max : (level1 : LevelType) -> (level2 : LevelType) -> LevelType
     * {eff1 : LevelType, eff2 : LevelType} |- eff1 eff2 := EffectsUnion(eff1, eff2)
     */
    b(
      Builtins.LevelMaxQn, (
        FunctionType(
          Binding(LevelType())(n"level1"),
          FunctionType(
            Binding(LevelType())(n"level2"),
            F(LevelType())
          )
        ),
        IndexedSeq(
          Clause(
            Binding(LevelType())(n"level1") :: Binding(LevelType())(n"level2") :: Nil,
            CPattern(PVar(1)) :: CPattern(PVar(0)) :: Nil,
            Return(LevelMax(Var(1), Var(0))),
            F(LevelType())
          )
        )
      )
    ),

    b(
      Builtins.TotalQn, (
        F(EffectsType()),
        IndexedSeq(
          Clause(
            Nil,
            Nil,
            Return(EffectsLiteral(ListSet())),
            F(EffectsType())
          )
        )
      )
    ),

    b(
      Builtins.AllocOpQn, (
        FunctionType(
          Binding(LevelType())(n"level"),
          FunctionType(
            Binding(HeapType())(n"h"),
            FunctionType(
              Binding(Type(USimpleLevel(Var(1)), Top(USimpleLevel(Var(1)))))(n"A"),
              F(
                DataType(Builtins.UCellQn, Var(2) :: Var(1) :: Var(0) :: Nil),
                EffectsLiteral(ListSet((Builtins.HeapEffQn, Var(1) :: Nil)))
              )
            )
          )
        ),
        IndexedSeq(
          Clause(
            Binding(LevelType())(n"level") ::
              Binding(HeapType())(n"h") ::
              Binding(Type(USimpleLevel(Var(1)), Top(USimpleLevel(Var(1)))))(n"A") ::
              Nil,
            CPattern(PVar(2)) :: CPattern(PVar(1)) :: CPattern(PVar(0)) :: Nil,
            Let(
              AllocOp(Var(1), Var(0)),
              Application(
                Application(
                  Application(
                    Application(
                      Def(Builtins.UCellQn / n"MkUCell"), Var(3)
                    ),
                    Var(2)
                  ),
                  Var(1)
                ),
                Var(0)
              )
            )(n"cell"),
            F(
              DataType(Builtins.UCellQn, Var(2) :: Var(1) :: Var(0) :: Nil),
              EffectsLiteral(ListSet((Builtins.HeapEffQn, Var(1) :: Nil)))
            )
          )
        )
      )
    ),
    b(
      Builtins.GetOpQn, (
        FunctionType(
          Binding(LevelType())(n"level"),
          FunctionType(
            Binding(HeapType())(n"h"),
            FunctionType(
              Binding(Type(USimpleLevel(Var(1)), Top(USimpleLevel(Var(1)))))(n"A"),
              FunctionType(
                Binding(DataType(Builtins.CellQn, Var(2) :: Var(1) :: Var(0) :: Nil))(n"cell"),
                F(
                  Var(1),
                  EffectsLiteral(ListSet((Builtins.HeapEffQn, Var(2) :: Nil)))
                )
              )
            )
          )
        ),
        IndexedSeq(
          Clause(
            Binding(LevelType())(n"level") ::
              Binding(HeapType())(n"h") ::
              Binding(Type(USimpleLevel(Var(1)), Top(USimpleLevel(Var(1)))))(n"A") ::
              Binding(CellType(Var(1), Var(0), CellStatus.Initialized))(n"cell") ::
              Nil,
            CPattern(PVar(3)) ::
              CPattern(PVar(2)) ::
              CPattern(PVar(1)) ::
              CPattern(PConstructor(n"MkCell", PVar(0) :: Nil)) ::
              Nil,
            GetOp(Var(0)),
            F(
              Var(1),
              EffectsLiteral(ListSet((Builtins.HeapEffQn, Var(2) :: Nil)))
            )
          )
        )
      )
    ),
    b(
      Builtins.SetOpQn, (
        FunctionType(
          Binding(LevelType())(n"level"),
          FunctionType(
            Binding(HeapType())(n"h"),
            FunctionType(
              Binding(Type(USimpleLevel(Var(1)), Top(USimpleLevel(Var(1)))))(n"A"),
              FunctionType(
                Binding(DataType(Builtins.UCellQn, Var(2) :: Var(1) :: Var(0) :: Nil))(n"cell"),
                FunctionType(
                  Binding(Var(1))(n"value"),
                  F(
                    DataType(Builtins.CellQn, Var(4) :: Var(3) :: Var(2) :: Nil),
                    EffectsLiteral(ListSet((Builtins.HeapEffQn, Var(3) :: Nil)))
                  )
                )
              )

            )
          )
        ),
        IndexedSeq(
          Clause(
            Binding(LevelType())(n"level") ::
              Binding(HeapType())(n"h") ::
              Binding(Type(USimpleLevel(Var(1)), Top(USimpleLevel(Var(1)))))(n"A") ::
              Binding(CellType(Var(1), Var(0), CellStatus.Uninitialized))(n"cell") ::
              Binding(Var(1))(n"value") ::
              Nil,
            CPattern(PVar(4)) ::
              CPattern(PVar(3)) ::
              CPattern(PVar(2)) ::
              CPattern(PConstructor(n"MkUCell", PVar(1) :: Nil)) ::
              CPattern(PVar(0)) :: Nil,
            Let(
              SetOp(Var(1), Var(0)),
              Application(
                Application(
                  Application(
                    Application(
                      Def(Builtins.CellQn / n"MkCell"), Var(5)
                    ),
                    Var(4)
                  ),
                  Var(3)
                ),
                Var(0)
              )
            )(n"cell"),
            F(
              DataType(Builtins.CellQn, Var(4) :: Var(3) :: Var(2) :: Nil),
              EffectsLiteral(ListSet((Builtins.HeapEffQn, Var(3) :: Nil)))
            )
          )
        )
      )
    ),
    b(
      Builtins.GlobalHeapKeyQn, (
        F(HeapType()),
        IndexedSeq(
          Clause(
            Nil,
            Nil,
            Return(Heap(GlobalHeapKey)),
            F(HeapType())
          )
        )
      )
    ),
  ).map { case (qn, (ty, clauses)) => (qn, (new Definition(qn)(ty), clauses)) }.toMap

  def getBigType(qn: QualifiedName): Option[(Definition, IndexedSeq[Clause])] =
    // TODO: it seems big SubtypeOf is not that useful so I will skip it for now.
    import Name.*
    import QualifiedName.*
    for
      (isComputation, layer) <-
        qn match
          case Node(BuiltinType, Normal(name)) if name.startsWith("TYPE") =>
            name.drop(4).toIntOption.map((false, _))
          case Node(BuiltinType, Normal(name)) if name.startsWith("CTYPE") =>
            name.drop(5).toIntOption.map((true, _))
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
        Clause(
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

  val builtinEffects: Map[QualifiedName, (Effect, IndexedSeq[Operator])] = Seq(
    b(
      Builtins.HeapEffQn, (
        /* tParamTys*/ Binding(HeapType())(n"h") :: Nil,
        /* operators */ IndexedSeq(
        // Note: we declare no operations here because operations of heap effect is represented
        // specially in CTerm. Instead, the derived definitions for these operations (alloc, set, get)
        // are directly added as builtin definitions.
      ))
    )
  ).map {
    case (qn, (tParamTys, operators)) =>
      (qn, (new Effect(qn)(tParamTys), operators))
  }.toMap

  private def b[T](qn: QualifiedName, f: SourceInfo ?=> T): (QualifiedName, T) =
    (qn, f(using SourceInfo.SiEmpty))
