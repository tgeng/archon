package com.github.tgeng.archon.core.ir

import com.github.tgeng.archon.core.common.*

import QualifiedName.*
import VTerm.*
import Essentiality.*

object Builtins:
  val BuiltinType = Builtin / "type"

  val TypeQn = BuiltinType / "Type"
  val SubtypeOfQn = BuiltinType / "SubtypeOf"
  val TopQn = BuiltinType / "Top"

  val LinearQn = BuiltinType / "Linear"
  val AffineQn = BuiltinType / "Affine"
  val RelevantQn = BuiltinType / "RelevantQn"
  val UnrestrictedQn = BuiltinType / "Unrestricted"
  val CTypeQn = BuiltinType / "CType"
  val CSubtypeOfQn = BuiltinType / "CSubtypeOf"
  val CTopQn = BuiltinType / "CTop"

  val UsageQn = BuiltinType / "Usage"

  val EqDecidabilityQn = BuiltinType / "EqDecidability"

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
  import Usage.*
  import EqDecidability.*
  import CaseTree.*

  // TODO: add all of these through elaboration.

  val builtinData: Map[QualifiedName, (Data, IndexedSeq[Constructor])] = Seq(
    b(
      Builtins.UnitTypeQn,
      (
        /* tParamTys*/ Nil,
        /* ul */ USimpleLevel(LevelLiteral(0)),
        /* numParams */ 0,
        /* inherentUsage */ UsageLiteral(UUnres),
        /* inherentEqDecidability */ EqDecidabilityLiteral(EqDecidable),
        /* constructors */ IndexedSeq(
          Constructor(n"MkUnit", Nil, Nil)
        )
      )
    ),
    b(
      Builtins.EqualityQn,
      (
        /* tParamTys*/
        (Binding(LevelType(), U0)(n"level"), Variance.COVARIANT) ::
          (Binding(Type(Top(USimpleLevel(Var(0)))), U1)(n"A"), Variance.COVARIANT) ::
          (Binding(Var(0), U1)(n"x"), Variance.COVARIANT) ::
          (Binding(Var(1), U1)(n"y"), Variance.COVARIANT) ::
          Nil,
        /* ul */ USimpleLevel(Var(3)),
        /* numParams */ 3,
        /* inherentUsage */ UsageLiteral(U0),
        /* inherentEqDecidability */ EqDecidabilityLiteral(EqDecidable),
        /* constructors */ IndexedSeq(
          Constructor(n"Refl", Nil, Var(3) :: Var(2) :: Var(1) :: Var(1) :: Nil)
        )
      )
    )
  ).map {
    case (
        qn,
        (
          tParamTys,
          ul,
          numParams,
          inherentUsage,
          inherentEqDecidability,
          constructors
        )
      ) =>
      (
        qn,
        (
          new Data(qn)(
            numParams,
            tParamTys.toIndexedSeq,
            ul,
            inherentUsage,
            inherentEqDecidability
          ),
          constructors
        )
      )
  }.toMap

  val builtinRecords: Map[QualifiedName, (Record, IndexedSeq[Field])] = Seq(
    // There does not seem to be any essential records that should included here.
    //    (?,
    //      /* tParamTys*/ ?,
    //      /* ul */ ?,
    //      /* fields */ ?)
  ).map { case (qn, (tParamTys, ul, fields)) =>
    (qn, (new Record(qn)(tParamTys, ul), fields))
  }.toMap

  val builtinDefinitions: Map[QualifiedName, (Definition, IndexedSeq[Clause])] =
    Seq(
      /** Type : (level : LevelType) -> Type(level + 1, Type(level, Top(l))) {level : LevelType}
        * \|- level := .return Type(level, Top(l))
        */
      b(
        Builtins.TypeQn,
        (
          FunctionType(
            Binding(LevelType(), U1)(n"level"),
            F(Type(Type(Top(USimpleLevel(Var(0))))))
          ),
          IndexedSeq(
            Clause(
              IndexedSeq(Binding(LevelType(), U1)(n"level")),
              CPattern(PVar(0)) :: Nil,
              Return(Type(Top(USimpleLevel(Var(0))))),
              F(Type(Type(Top(USimpleLevel(Var(0))))))
            )
          )
        )
      ),

      /** SubtypeOf : (level : LevelType) -> (upperBound : Type(level, Top(level))) -> Type(level
        * + 1, Type(level, upperBound)) {level : LevelType, upperBound: Type(level, Top(level))}
        * \|- level upperBound := .return Type(level, upperBound)
        */
      b(
        Builtins.SubtypeOfQn,
        (
          FunctionType(
            Binding(LevelType(), U1)(n"level"),
            FunctionType(
              Binding(Type(Top(USimpleLevel(Var(0)))), U1)(n"upperBound"),
              F(Type(Type(Var(0))))
            )
          ),
          IndexedSeq(
            Clause(
              IndexedSeq(
                Binding(LevelType(), U1)(n"level"),
                Binding(Type(Top(USimpleLevel(Var(0)))), U1)(n"upperBound")
              ),
              CPattern(PVar(1)) :: CPattern(PVar(0)) :: Nil,
              Return(Type(Var(0))),
              F(Type(Type(Var(0))))
            )
          )
        )
      ),

      /** Top : (level : LevelType) -> Type(level, Top(level)) {level : LevelType} |- level :=
        * .return Top(level)
        */
      b(
        Builtins.TopQn,
        (
          FunctionType(
            Binding(LevelType(), U1)(n"level"),
            F(Type(Top(USimpleLevel(Var(0)))))
          ),
          IndexedSeq(
            Clause(
              IndexedSeq(Binding(LevelType(), U1)(n"level")),
              CPattern(PVar(0)) :: Nil,
              Return(Top(USimpleLevel(Var(0)))),
              F(Type(Top(USimpleLevel(Var(0)))))
            )
          )
        )
      ),

      /** Effects : Type(0, Effects) {} |- := Effects
        */
      b(
        Builtins.EffectsQn,
        (
          F(Type(EffectsType())),
          IndexedSeq(
            Clause(
              IndexedSeq(),
              Nil,
              Return(EffectsType()),
              F(Type(EffectsType()))
            )
          )
        )
      ),

      /** Level : TYPE0 {} |- := Level
        */
      b(
        Builtins.LevelQn,
        (
          F(Type(LevelType())),
          IndexedSeq(Clause(IndexedSeq(), Nil, Return(LevelType()), F(Type(LevelType()))))
        )
      ),

      /** Heap : Type(0, Heap) {} |- := Heap
        */
      b(
        Builtins.HeapQn,
        (
          F(Type(HeapType())),
          IndexedSeq(Clause(IndexedSeq(), Nil, Return(HeapType()), F(Type(HeapType()))))
        )
      ),

      /** CType : (level : LevelType) -> (effects: EffectsType) -> CType(level + 1, CType(level,
        * effects), Total) {level : LevelType, effects : EffectsType} level effects :=
        * CType(level, CTop(level), effects)
        */
      b(
        Builtins.CTypeQn,
        (
          FunctionType(
            Binding(LevelType(), U1)(n"level"),
            FunctionType(
              Binding(EffectsType(), U1)(n"effects"),
              CType(CType(CTop(USimpleLevel(Var(1)), Var(0))))
            )
          ),
          IndexedSeq(
            Clause(
              IndexedSeq(
                Binding(LevelType(), U1)(n"level"),
                Binding(EffectsType(), U1)(n"effects")
              ),
              CPattern(PVar(1)) :: CPattern(PVar(0)) :: Nil,
              CType(CTop(USimpleLevel(Var(1)), Var(0))),
              CType(
                CType(CTop(USimpleLevel(Var(1)), Var(0)))
              )
            )
          )
        )
      ),

      /** CSubtypeOf : (level : LevelType) -> (effects: EffectsType) -> (upperBound :
        * U(CType(level, CTop(level, effects)))) -> CType(level + 1, .force upperBound, Total)
        * {level : LevelType, effects: Effects, upperBound: U(CType(level + 1, CTop(level,
        * effects)))} |- level effects upperBound := CType(level, .force upperBound, effects)
        */
      b(
        Builtins.CSubtypeOfQn,
        (
          FunctionType(
            Binding(LevelType(), U1)(n"level"),
            FunctionType(
              Binding(EffectsType(), U1)(n"effects"),
              FunctionType(
                Binding(
                  U(CType(CTop(USimpleLevel(Var(1)), Var(0)))),
                  U1
                )(n"upperBound"),
                CType(CType(Force(Var(0)), Var(1)))
              )
            )
          ),
          IndexedSeq(
            Clause(
              IndexedSeq(
                Binding(LevelType(), U1)(n"level"),
                Binding(EffectsType(), U1)(n"effects"),
                Binding(U(CType(CTop(USimpleLevel(Var(1)), Var(0)))), U1)(n"upperBound")
              ),
              CPattern(PVar(2)) :: CPattern(PVar(1)) :: CPattern(
                PVar(0)
              ) :: Nil,
              CType(Force(Var(0)), Var(1)),
              CType(CType(Force(Var(0)), Var(1)))
            )
          )
        )
      ),

      /** CTop : (level : LevelType) -> (effects : EffectsType) -> CType(level, CTop(level,
        * effects)) {level : LevelType, effects : EffectsType} |- level effects := CTop(level,
        * effects)
        */
      b(
        Builtins.CTopQn,
        (
          FunctionType(
            Binding(LevelType(), U1)(n"level"),
            FunctionType(
              Binding(EffectsType(), U1)(n"effects"),
              CType(CTop(USimpleLevel(Var(1)), Var(0)))
            )
          ),
          IndexedSeq(
            Clause(
              IndexedSeq(
                Binding(LevelType(), U1)(n"level"),
                Binding(EffectsType(), U1)(n"effects")
              ),
              CPattern(PVar(1)) :: CPattern(PVar(0)) :: Nil,
              CTop(USimpleLevel(Var(1)), Var(0)),
              CType(CTop(USimpleLevel(Var(1)), Var(0)))
            )
          )
        )
      ),

      /** union : (eff1 : EffectsType) -> (eff2 : EffectsType) -> EffectsType {eff1 : EffectsType,
        * eff2 : EffectsType} |- eff1 eff2 := EffectsUnion(eff1, eff2)
        */
      b(
        Builtins.EffectsUnionQn,
        (
          FunctionType(
            Binding(EffectsType(), U1)(n"eff1"),
            FunctionType(
              Binding(EffectsType(), U1)(n"eff2"),
              F(EffectsType())
            )
          ),
          IndexedSeq(
            Clause(
              IndexedSeq(
                Binding(EffectsType(), U1)(n"eff1"),
                Binding(EffectsType(), U1)(n"eff2")
              ),
              CPattern(PVar(1)) :: CPattern(PVar(0)) :: Nil,
              Return(EffectsUnion(Var(1), Var(0))),
              F(EffectsType())
            )
          )
        )
      ),

      /** suc : (level : LevelType) -> LevelType {level : LevelType} |- level := level + 1
        */
      b(
        Builtins.LevelSucQn,
        (
          FunctionType(
            Binding(LevelType(), U1)(n"level"),
            F(LevelType())
          ),
          IndexedSeq {
            Clause(
              IndexedSeq(Binding(LevelType(), U1)(n"level")),
              CPattern(PVar(0)) :: Nil,
              Return(LevelSuc(Var(0))),
              F(LevelType())
            )
          }
        )
      ),

      /** max : (level1 : LevelType) -> (level2 : LevelType) -> LevelType {eff1 : LevelType, eff2
        * : LevelType} |- eff1 eff2 := EffectsUnion(eff1, eff2)
        */
      b(
        Builtins.LevelMaxQn,
        (
          FunctionType(
            Binding(LevelType(), U1)(n"level1"),
            FunctionType(
              Binding(LevelType(), U1)(n"level2"),
              F(LevelType())
            )
          ),
          IndexedSeq(
            Clause(
              IndexedSeq(
                Binding(LevelType(), U1)(n"level1"),
                Binding(LevelType(), U1)(n"level2")
              ),
              CPattern(PVar(1)) :: CPattern(PVar(0)) :: Nil,
              Return(LevelMax(Var(1), Var(0))),
              F(LevelType())
            )
          )
        )
      ),
      b(
        Builtins.TotalQn,
        (
          F(EffectsType()),
          IndexedSeq(
            Clause(
              IndexedSeq(),
              Nil,
              Return(EffectsLiteral(Set())),
              F(EffectsType())
            )
          )
        )
      ),
      b(
        Builtins.CellQn,
        (
          FunctionType(
            Binding(LevelType(), U0)(n"level"),
            FunctionType(
              Binding(HeapType(), U1)(n"h"),
              FunctionType(
                Binding(Type(Top(USimpleLevel(Var(1)))), U1)(n"A"),
                F(Type(CellType(Var(1), Var(0), CellStatus.Initialized)))
              )
            )
          ),
          IndexedSeq(
            Clause(
              IndexedSeq(
                Binding(LevelType(), U0)(n"level"),
                Binding(HeapType(), U1)(n"h"),
                Binding(Type(Top(USimpleLevel(Var(1)))), U1)(n"A")
              ),
              CPattern(PVar(2)) :: CPattern(PVar(1)) :: CPattern(
                PVar(0)
              ) :: Nil,
              Return(CellType(Var(1), Var(0), CellStatus.Initialized)),
              F(Type(CellType(Var(1), Var(0), CellStatus.Initialized)))
            )
          )
        )
      ),
      b(
        Builtins.UCellQn,
        (
          FunctionType(
            Binding(LevelType(), U0)(n"level"),
            FunctionType(
              Binding(HeapType(), U1)(n"h"),
              FunctionType(
                Binding(Type(Top(USimpleLevel(Var(1)))), U1)(n"A"),
                F(Type(CellType(Var(1), Var(0), CellStatus.Uninitialized)))
              )
            )
          ),
          IndexedSeq(
            Clause(
              IndexedSeq(
                Binding(LevelType(), U0)(n"level"),
                Binding(HeapType(), U1)(n"h"),
                Binding(Type(Top(USimpleLevel(Var(1)))), U1)(n"A")
              ),
              CPattern(PVar(2)) :: CPattern(PVar(1)) :: CPattern(PVar(0)) :: Nil,
              Return(CellType(Var(1), Var(0), CellStatus.Uninitialized)),
              F(Type(CellType(Var(1), Var(0), CellStatus.Uninitialized)))
            )
          )
        )
      ),
      b(
        Builtins.AllocOpQn,
        (
          FunctionType(
            Binding(LevelType(), U0)(n"level"),
            FunctionType(
              Binding(HeapType(), U1)(n"h"),
              FunctionType(
                Binding(Type(Top(USimpleLevel(Var(1)))), U1)(n"A"),
                F(
                  CellType(Var(1), Var(0), CellStatus.Uninitialized),
                  EffectsLiteral(Set((Builtins.HeapEffQn, Var(1) :: Nil)))
                )
              )
            )
          ),
          IndexedSeq(
            Clause(
              IndexedSeq(
                Binding(LevelType(), U0)(n"level"),
                Binding(HeapType(), U1)(n"h"),
                Binding(Type(Top(USimpleLevel(Var(1)))), U1)(n"A")
              ),
              CPattern(PVar(2)) :: CPattern(PVar(1)) :: CPattern(
                PVar(0)
              ) :: Nil,
              AllocOp(Var(1), Var(0)),
              F(
                CellType(Var(1), Var(0), CellStatus.Uninitialized),
                EffectsLiteral(Set((Builtins.HeapEffQn, Var(1) :: Nil)))
              )
            )
          )
        )
      ),
      // return UUnres?
      b(
        Builtins.GetOpQn,
        (
          FunctionType(
            Binding(LevelType(), U0)(n"level"),
            FunctionType(
              Binding(HeapType(), U0)(n"h"),
              FunctionType(
                Binding(Type(Top(USimpleLevel(Var(1)))), U0)(n"A"),
                FunctionType(
                  Binding(CellType(Var(1), Var(0), CellStatus.Initialized), U1)(
                    n"cell"
                  ),
                  F(
                    Var(1),
                    EffectsLiteral(Set((Builtins.HeapEffQn, Var(2) :: Nil)))
                  )
                )
              )
            )
          ),
          IndexedSeq(
            Clause(
              IndexedSeq(
                Binding(LevelType(), U0)(n"level"),
                Binding(HeapType(), U0)(n"h"),
                Binding(Type(Top(USimpleLevel(Var(1)))), U0)(n"A"),
                Binding(CellType(Var(1), Var(0), CellStatus.Initialized), U1)(n"cell")
              ),
              CPattern(PVar(3)) ::
                CPattern(PVar(2)) ::
                CPattern(PVar(1)) ::
                CPattern(PVar(0)) ::
                Nil,
              GetOp(Var(0)),
              F(
                Var(1),
                EffectsLiteral(Set((Builtins.HeapEffQn, Var(2) :: Nil)))
              )
            )
          )
        )
      ),
      // take URel?
      b(
        Builtins.SetOpQn,
        (
          FunctionType(
            Binding(LevelType(), U0)(n"level"),
            FunctionType(
              Binding(HeapType(), U0)(n"h"),
              FunctionType(
                Binding(Type(Top(USimpleLevel(Var(1)))), U0)(n"A"),
                FunctionType(
                  Binding(
                    CellType(Var(1), Var(0), CellStatus.Uninitialized),
                    U1
                  )(n"cell"),
                  FunctionType(
                    Binding(Var(1), U1)(n"value"),
                    F(
                      CellType(Var(3), Var(2), CellStatus.Initialized),
                      EffectsLiteral(Set((Builtins.HeapEffQn, Var(3) :: Nil)))
                    )
                  )
                )
              )
            )
          ),
          IndexedSeq(
            Clause(
              IndexedSeq(
                Binding(LevelType(), U0)(n"level"),
                Binding(HeapType(), U0)(n"h"),
                Binding(Type(Top(USimpleLevel(Var(1)))), U0)(n"A"),
                Binding(CellType(Var(1), Var(0), CellStatus.Uninitialized), U1)(n"cell"),
                Binding(Var(1), U1)(n"value")
              ),
              CPattern(PVar(4)) ::
                CPattern(PVar(3)) ::
                CPattern(PVar(2)) ::
                CPattern(PVar(1)) ::
                CPattern(PVar(0)) :: Nil,
              SetOp(Var(1), Var(0)),
              F(
                CellType(Var(3), Var(2), CellStatus.Initialized),
                EffectsLiteral(Set((Builtins.HeapEffQn, Var(3) :: Nil)))
              )
            )
          )
        )
      ),
      b(
        Builtins.GlobalHeapKeyQn,
        (
          F(HeapType()),
          IndexedSeq(
            Clause(
              IndexedSeq(),
              Nil,
              Return(Heap(GlobalHeapKey)),
              F(HeapType())
            )
          )
        )
      )
    ).map { case (qn, (ty, clauses)) =>
      (qn, (new Definition(qn)(ty), clauses))
    }.toMap

  val builtinEffects: Map[QualifiedName, (Effect, IndexedSeq[Operator])] = Seq(
    b(
      Builtins.HeapEffQn,
      (
        /* tParamTys*/ IndexedSeq(Binding(HeapType(), U1)(n"h")),
        /* operators */ IndexedSeq(
          // Note: we declare no operations here because operations of heap effect is represented
          // specially in CTerm. Instead, the derived definitions for these operations (alloc, set, get)
          // are directly added as builtin definitions.
        )
      )
    )
  ).map { case (qn, (tParamTys, operators)) =>
    (qn, (new Effect(qn)(tParamTys), operators))
  }.toMap

  private def b[T](qn: QualifiedName, f: SourceInfo ?=> T): (QualifiedName, T) =
    (qn, f(using SourceInfo.SiEmpty))
