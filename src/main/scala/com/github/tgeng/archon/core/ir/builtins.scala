package com.github.tgeng.archon.core.ir

import com.github.tgeng.archon.core.common.*

import QualifiedName.*
import VTerm.*
import Essentiality.*
import Declaration.*
import scala.annotation.meta.param
import java.util.prefs.PreferenceChangeListener

private case class SimpleSignature
  (
    declarations: Map[QualifiedName, Declaration] = Map(),
    constructors: Map[QualifiedName, IndexedSeq[Constructor]] = Map(),
    fields: Map[QualifiedName, IndexedSeq[Field]] = Map(),
    clauses: Map[QualifiedName, IndexedSeq[Clause]] = Map(),
    caseTrees: Map[QualifiedName, CaseTree] = Map(),
    operators: Map[QualifiedName, IndexedSeq[Operator]] = Map(),
  )
  extends DerivedSignature:

  override type S = SimpleSignature

  override def addDeclaration(d: Declaration): SimpleSignature =
    copy(declarations = declarations + (d.qn -> d))
  override def addConstructor(qn: QualifiedName, c: Constructor): SimpleSignature =
    copy(constructors = constructors + (qn -> (constructors.getOrElse(qn, IndexedSeq()) :+ c)))
  override def addField(qn: QualifiedName, f: Field): SimpleSignature =
    copy(fields = fields + (qn -> (fields.getOrElse(qn, IndexedSeq()) :+ f)))
  override def addClause(qn: QualifiedName, c: Clause): SimpleSignature =
    copy(clauses = clauses + (qn -> (clauses.getOrElse(qn, IndexedSeq()) :+ c)))
  override def addCaseTree(qn: QualifiedName, ct: CaseTree): SimpleSignature =
    copy(caseTrees = caseTrees + (qn -> ct))
  override def addOperator(qn: QualifiedName, o: Operator): SimpleSignature =
    copy(operators = operators + (qn -> (operators.getOrElse(qn, IndexedSeq()) :+ o)))

  override def getDeclaredDefinitionOption(qn: QualifiedName): Option[Definition] =
    declarations.get(qn).collect { case d: Definition => d }
  override def getDeclaredClausesOption(qn: QualifiedName): Option[IndexedSeq[Clause]] =
    clauses.get(qn)
  override def getDeclaredCaseTreeOption(qn: QualifiedName): Option[CaseTree] =
    caseTrees.get(qn)
  override def getDataOption(qn: QualifiedName): Option[Data] =
    declarations.get(qn).collect { case d: Data => d }
  override def getConstructorsOption(qn: QualifiedName): Option[IndexedSeq[Constructor]] =
    constructors.get(qn)
  override def getRecordOption(qn: QualifiedName): Option[Record] =
    declarations.get(qn).collect { case d: Record => d }
  override def getFieldsOption(qn: QualifiedName): Option[IndexedSeq[Field]] =
    fields.get(qn)
  override def getEffectOption(qn: QualifiedName): Option[Effect] =
    declarations.get(qn).collect { case d: Effect => d }
  override def getOperatorsOption(qn: QualifiedName): Option[IndexedSeq[Operator]] =
    operators.get(qn)

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

  def Σ(using ctx: TypingContext): Signature =
    elaborateAll(builtins)(using SimpleSignature()) match
      case Right(_Σ) => _Σ
      case Left(e)   => throw IllegalStateException(e.toString())

  import PreDeclaration.*
  import CTerm.*
  import VTerm.*
  import ULevel.*
  import CoPattern.*
  import Pattern.*
  import Usage.*
  import EqDecidability.*
  import CaseTree.*
  import ULevel.*

  private def binding(name: Name, t: VTerm, usage: VTerm = UsageLiteral(U1)): Binding[CTerm] =
    Binding(Return(t), Return(usage))(name)

  private val L0 = ULevel.USimpleLevel(LevelLiteral(0))

  // TODO: move all of these builtin declarations here. Also create a new EqualityType from Data.
  private val builtins: Seq[PreDeclaration] = Seq(
    PreData(UnitTypeQn)(
      tParamTys = Nil,
      ty = F(Type(Top(L0))),
      constructors = List(PreConstructor(n"MkUnit", F(DataType(UnitTypeQn, Nil)))),
    ),
    PreData(EqualityQn)(
      // Invariance of level is OK because user should almost never provide this. Instead, this is
      // inferred by compiler for each compilation unit to be some large enough level.
      tParamTys = List(
        (binding(n"level", LevelType()), Variance.INVARIANT),
        (binding(n"A", Type(Top(Var(0)))), Variance.COVARIANT),
        (binding(n"x", Var(0)), Variance.INVARIANT),
      ),
      ty = FunctionType(Binding(Var(1), U1)(n"y"), F(Type(Top(Var(2))))),
      constructors = List(
        PreConstructor(n"Refl", F(DataType(EqualityQn, List(Var(2), Var(1), Var(0), Var(0))))),
      ),
    ),
    /** Type (level : LevelType): Type(Type(Top(level))))
      *
      * {} |- := .return Type(Top(level))
      */
    PreDefinition(TypeQn)(
      paramTys = List(binding(n"level", LevelType())),
      ty = F(Type(Type(Top(Var(0))))),
      clauses = List(
        PreClause(
          boundNames = Nil,
          lhs = Nil,
          rhs = Some(Return(Type(Top(USimpleLevel(Var(0)))))),
        ),
      ),
    ),

    /** SubtypeOf (level : LevelType) (upperBound : Type(Top(level))) -> Type(Type(upperBound))
      *
      * {} |- := .return Type(upperBound)
      */
    PreDefinition(SubtypeOfQn)(
      paramTys = List(
        binding(n"level", LevelType()),
        binding(n"upperBound", Type(Type(Top(Var(0))))),
      ),
      ty = F(Type(Type(Var(0)))),
      clauses = List(
        PreClause(
          boundNames = Nil,
          lhs = Nil,
          rhs = Some(Return(Type(Var(0)))),
        ),
      ),
    ),
    /** Top (level : LevelType) : Type(Top(level))
      *
      * {} |- level := .return Top(level)
      */
    PreDefinition(TypeQn)(
      paramTys = List(binding(n"level", LevelType())),
      ty = F(Type(Top(Var(0)))),
      clauses = List(
        PreClause(
          boundNames = Nil,
          lhs = Nil,
          rhs = Some(Return(Top(Var(0)))),
        ),
      ),
    ),

    /** Effects : Type(Effects)
      *
      * {} |- := Effects
      */
    PreDefinition(EffectsQn)(
      paramTys = Nil,
      ty = F(Type(EffectsType())),
      clauses = List(
        PreClause(
          boundNames = Nil,
          lhs = Nil,
          rhs = Some(Return(EffectsType())),
        ),
      ),
    ),

    /** Level : Type(Level)
      *
      * {} |- := Level
      */
    PreDefinition(LevelQn)(
      paramTys = Nil,
      ty = F(Type(LevelType())),
      clauses = List(
        PreClause(
          boundNames = Nil,
          lhs = Nil,
          rhs = Some(Return(LevelType())),
        ),
      ),
    ),

    /** Heap : Type(Heap)
      *
      * {} |- := Heap
      */
    PreDefinition(HeapQn)(
      paramTys = Nil,
      ty = F(Type(HeapType())),
      clauses = List(
        PreClause(
          boundNames = Nil,
          lhs = Nil,
          rhs = Some(Return(HeapType())),
        ),
      ),
    ),

    /** CType (level : LevelType) (effects: EffectsType) : CType(CType(CTop(level, effects))
      *
      * {} |- := CType(CTop(level, effects))
      */
    PreDefinition(CTypeQn)(
      paramTys = List(
        binding(n"level", LevelType()),
        binding(n"effects", EffectsType()),
      ),
      ty = CType(CType(CTop(Var(1), Var(0)))),
      clauses = List(
        PreClause(
          boundNames = Nil,
          lhs = Nil,
          rhs = Some(CType(CTop(Var(1), Var(0)))),
        ),
      ),
    ),

    /** CSubtypeOf (level : LevelType) (effects: EffectsType) (upperBound : U(CType(CTop(level,
      * effects)))) : CType(CType(.force upperBound, effects))
      *
      * {} |- := CType(.force upperBound, effects)
      */
    PreDefinition(CSubtypeOfQn)(
      paramTys = List(
        binding(n"level", LevelType()),
        binding(n"effects", EffectsType()),
        binding(n"upperBound", U(CType(CTop(Var(1), Var(0))))),
      ),
      ty = CType(CType(Force(Var(0)), Var(1))),
      clauses = List(
        PreClause(
          boundNames = Nil,
          lhs = Nil,
          rhs = Some(CType(Force(Var(0)), Var(1))),
        ),
      ),
    ),

    /** CTop (level : LevelType) (effects : EffectsType) : CType(CTop(level, effects))
      *
      * {} |- level effects := CTop(level, effects)
      */

    PreDefinition(CTopQn)(
      paramTys = List(
        binding(n"level", LevelType()),
        binding(n"effects", EffectsType()),
      ),
      ty = CType(CTop(Var(1), Var(0))),
      clauses = List(
        PreClause(
          boundNames = Nil,
          lhs = Nil,
          rhs = Some(CTop(Var(1), Var(0))),
        ),
      ),
    ),

    /** union (eff1 : EffectsType) (eff2 : EffectsType) : EffectsType
      *
      * {} |- := EffectsUnion(eff1, eff2)
      */
    PreDefinition(EffectsUnionQn)(
      paramTys = List(
        binding(n"eff1", EffectsType()),
        binding(n"eff2", EffectsType()),
      ),
      ty = F(EffectsType()),
      clauses = List(
        PreClause(
          boundNames = Nil,
          lhs = Nil,
          rhs = Some(Return(EffectsUnion(Var(1), Var(0)))),
        ),
      ),
    ),
    /** suc (level : LevelType) : LevelType
      *
      * {} |- := level + 1
      */
    PreDefinition(LevelSucQn)(
      paramTys = List(
        binding(n"level", LevelType()),
      ),
      ty = F(LevelType()),
      clauses = List(
        PreClause(
          boundNames = Nil,
          lhs = Nil,
          rhs = Some(Return(LevelSuc(Var(0)))),
        ),
      ),
    ),

    /** max (level1 : LevelType) (level2 : LevelType) : LevelType
      *
      * {} |- := LevelMax(level1, level2)
      */
    PreDefinition(LevelMaxQn)(
      paramTys = List(
        binding(n"level1", LevelType()),
        binding(n"level2", LevelType()),
      ),
      ty = F(LevelType()),
      clauses = List(
        PreClause(
          boundNames = Nil,
          lhs = Nil,
          rhs = Some(Return(LevelMax(Var(1), Var(0)))),
        ),
      ),
    ),
    PreDefinition(TotalQn)(
      paramTys = Nil,
      ty = F(EffectsType()),
      clauses = List(
        PreClause(
          boundNames = Nil,
          lhs = Nil,
          rhs = Some(Return(Total)),
        ),
      ),
    ),
    PreDefinition(CellQn)(
      paramTys = List(
        binding(n"level", LevelType()),
        binding(n"heap", HeapType()),
        binding(n"A", Type(Top(Var(1)))),
      ),
      ty = F(Type(CellType(Var(1), Var(0), CellStatus.Initialized))),
      clauses = List(
        PreClause(
          boundNames = Nil,
          lhs = Nil,
          rhs = Some(Return(CellType(Var(1), Var(0), CellStatus.Initialized))),
        ),
      ),
    ),
    PreDefinition(UCellQn)(
      paramTys = List(
        binding(n"level", LevelType()),
        binding(n"heap", HeapType()),
        binding(n"A", Type(Top(Var(1)))),
      ),
      ty = F(Type(CellType(Var(1), Var(0), CellStatus.Uninitialized))),
      clauses = List(
        PreClause(
          boundNames = Nil,
          lhs = Nil,
          rhs = Some(Return(CellType(Var(1), Var(0), CellStatus.Uninitialized))),
        ),
      ),
    ),
    PreDefinition(AllocOpQn)(
      paramTys = List(
        binding(n"level", LevelType()),
        binding(n"heap", HeapType()),
        binding(n"A", Type(Top(Var(1)))),
      ),
      ty = F(CellType(Var(1), Var(0), CellStatus.Uninitialized)),
      clauses = List(
        PreClause(
          boundNames = Nil,
          lhs = Nil,
          rhs = Some(AllocOp(Var(1), Var(0))),
        ),
      ),
    ),
    PreDefinition(GetOpQn)(
      paramTys = List(
        binding(n"level", LevelType()),
        binding(n"heap", HeapType()),
        binding(n"A", Type(Top(Var(1)))),
        binding(n"cell", CellType(Var(1), Var(0), CellStatus.Initialized)),
      ),
      ty =
        F(Var(1), EffectsLiteral(Set((Builtins.HeapEffQn, List(Var(2))))), UsageLiteral(UUnres)),
      clauses = List(
        PreClause(
          boundNames = Nil,
          lhs = Nil,
          rhs = Some(GetOp(Var(0))),
        ),
      ),
    ),
    PreDefinition(SetOpQn)(
      paramTys = List(
        binding(n"level", LevelType()),
        binding(n"heap", HeapType()),
        binding(n"A", Type(Top(Var(1)))),
        binding(n"cell", CellType(Var(1), Var(0), CellStatus.Uninitialized)),
        binding(n"value", Var(1), UsageLiteral(UUnres)),
      ),
      ty = F(
        CellType(Var(3), Var(2), CellStatus.Initialized),
        EffectsLiteral(Set((Builtins.HeapEffQn, List(Var(3))))),
      ),
      clauses = List(
        PreClause(
          boundNames = Nil,
          lhs = Nil,
          rhs = Some(SetOp(Var(1), Var(0))),
        ),
      ),
    ),
    PreDefinition(GlobalHeapKeyQn)(
      paramTys = Nil,
      ty = F(HeapType()),
      clauses = List(
        PreClause(
          boundNames = Nil,
          lhs = Nil,
          rhs = Some(Return(Heap(GlobalHeapKey))),
        ),
      ),
    ),
    PreEffect(HeapEffQn)(
      tParamTys = List(binding(n"heap", HeapType())),
      // Note: we declare no operations here because operations of heap effect is represented
      // specially in CTerm. Instead, the derived definitions for these operations (alloc, set, get)
      // are directly added as builtin definitions.
      operators = Nil,
    ),
  )

  private def b[T](qn: QualifiedName, f: SourceInfo ?=> T): (QualifiedName, T) =
    (qn, f(using SourceInfo.SiEmpty))
