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
    operations: Map[QualifiedName, IndexedSeq[Operation]] = Map(),
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
  override def addOperation(qn: QualifiedName, o: Operation): SimpleSignature =
    copy(operations = operations + (qn -> (operations.getOrElse(qn, IndexedSeq()) :+ o)))

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
  override def getOperationsOption(qn: QualifiedName): Option[IndexedSeq[Operation]] =
    operations.get(qn)

object Builtins:

  val BuiltinType = Builtin / "type"

  val TypeQn = BuiltinType / "Type"
  val SubtypeOfQn = BuiltinType / "SubtypeOf"
  val TopQn = BuiltinType / "Top"

  val CTypeQn = BuiltinType / "CType"
  val CSubtypeOfQn = BuiltinType / "CSubtypeOf"
  val CTopQn = BuiltinType / "CTop"

  val EqDecidabilityQn = BuiltinType / "EqDecidability"
  val EqDecidableQn = EqDecidabilityQn / "Decidable"
  val EqUnknownQn = EqDecidabilityQn / "Unknown"

  val EqualityQn = BuiltinType / "Equality"
  val CellQn = BuiltinType / "Cell"
  val UCellQn = BuiltinType / "UCell"
  val EffectsQn = BuiltinType / "Effects"
  val LevelQn = BuiltinType / "Level"

  val UsageQn = BuiltinType / "Usage"

  val UnitQn = BuiltinType / "Unit"
  val MkUnitQn = UnitQn / "MkUnit"

  val PairQn = BuiltinType / "Pair"
  val MkPairQn = PairQn / "MkPair"

  val ContinuationQn = BuiltinType / "Continuation"
  val ResumeQn = ContinuationQn / "resume"
  val DisposeQn = ContinuationQn / "dispose"
  val ReplicateQn = ContinuationQn / "replicate"

  val BuiltinEffects = Builtin / "effects"
  val HeapEffQn = BuiltinEffects / "heap"
  val AllocOpQn = HeapEffQn / "alloc"
  val GetOpQn = HeapEffQn / "get"
  val SetOpQn = HeapEffQn / "set"
  val GlobalHeapKeyQn = HeapEffQn / "global"
  val EffectsUnionQn = BuiltinEffects / "union"
  val TotalQn = BuiltinEffects / "total"
  val DivQn = BuiltinEffects / "div"
  val MaybeDivQn = BuiltinEffects / "mdiv"

  val BuiltinLevel = Builtin / "level"
  val LevelSucQn = BuiltinLevel / "suc"
  val LevelMaxQn = BuiltinLevel / "max"

  private val PredicateQn = BuiltinType / "predicate"
  private val UsagePredicateQn = PredicateQn / "usage"
  val IsDisposableQn = UsagePredicateQn / "IsDisposable"
  val IsReplicableQn = UsagePredicateQn / "IsReplicable"
  val IsResumableQn = UsagePredicateQn / "IsResumable"

  def Σ(using ctx: TypingContext): Signature =
    elaborateAll(builtins)(using SimpleSignature()) match
      case Right(_Σ) => _Σ
      case Left(e)   => throw IllegalStateException(e.toString())

  import PreDeclaration.*
  import CTerm.*
  import VTerm.*
  import CoPattern.*
  import Pattern.*
  import Usage.*
  import EqDecidability.*
  import CaseTree.*

  private def binding(name: Name, t: VTerm, usage: VTerm = UsageLiteral(U1)): Binding[CTerm] =
    Binding(Return(t), Return(usage))(name)

  private val L0 = LevelLiteral(0)

  private val builtins: Seq[PreDeclaration] = Seq(
    PreData(UnitQn)(
      tParamTys = Nil,
      ty = F(Type(Top(L0))),
      constructors = List(PreConstructor(n"MkUnit", F(DataType(UnitQn, Nil)))),
    ),
    PreData(EqualityQn)(
      // Invariance of level is OK because user should almost never provide this. Instead, this is
      // inferred by compiler for each compilation unit to be some large enough level.
      tParamTys = List(
        (binding(n"level", LevelType()), Variance.INVARIANT),
        (binding(n"A", Type(Top(Var(0)))), Variance.COVARIANT),
        (binding(n"x", Var(0), UsageLiteral(UAny)), Variance.INVARIANT),
      ),
      ty = FunctionType(Binding(Var(1))(n"y"), F(Type(Top(Var(2))))),
      constructors = List(
        PreConstructor(n"Refl", F(DataType(EqualityQn, List(Var(2), Var(1), Var(0), Var(0))))),
      ),
    ),
    PreData(PairQn)(
      tParamTys = List(
        (binding(n"level", LevelType()), Variance.INVARIANT),
        (binding(n"eqDec", EqDecidabilityType()), Variance.INVARIANT),
        (binding(n"usage1", UsageType()), Variance.INVARIANT),
        (binding(n"A1", Top(Var(2), Var(1))), Variance.COVARIANT),
        (binding(n"usage2", EqDecidabilityType()), Variance.INVARIANT),
        (binding(n"A2", Top(Var(4), Var(3))), Variance.COVARIANT),
      ),
      ty = F(Type(Top(Var(5), Var(4)))),
      constructors = List(
        PreConstructor(
          n"MkPair",
          FunctionType(
            Binding(Var(2), Var(3))(n"x"),
            FunctionType(Binding(Var(1), Var(2))(n"y"), F(DataType(PairQn, vars(4, 2)))),
          ),
        ),
      ),
    ),
    PreData(IsDisposableQn)(
      tParamTys = Nil,
      ty = FunctionType(Binding(UsageType())(n"usage"), F(Type(Top(LevelLiteral(0))))),
      constructors = List(
        PreConstructor(n"ZeroIsDisposable", F(DataType(IsDisposableQn, List(UsageLiteral(U0))))),
        PreConstructor(
          n"AffineIsDisposable",
          F(DataType(IsDisposableQn, List(UsageLiteral(UAff)))),
        ),
      ),
    ),
    PreData(IsReplicableQn)(
      tParamTys = Nil,
      ty = FunctionType(Binding(UsageType())(n"usage"), F(Type(Top(LevelLiteral(0))))),
      constructors = List(
        PreConstructor(
          n"RelevantIsReplicable",
          F(DataType(IsReplicableQn, List(UsageLiteral(U0)))),
        ),
        PreConstructor(
          n"UnrestrictedIsReplicable",
          F(DataType(IsReplicableQn, List(UsageLiteral(UAny)))),
        ),
      ),
    ),
    PreData(IsResumableQn)(
      tParamTys = Nil,
      ty = FunctionType(Binding(UsageType())(n"usage"), F(Type(Top(LevelLiteral(0))))),
      constructors = List(
        PreConstructor(
          n"LinearIsResumable",
          F(DataType(IsResumableQn, List(UsageLiteral(U1)))),
        ),
        PreConstructor(
          n"AffineIsResumable",
          F(DataType(IsResumableQn, List(UsageLiteral(UAff)))),
        ),
        PreConstructor(
          n"RelevantIsResumable",
          F(DataType(IsResumableQn, List(UsageLiteral(URel)))),
        ),
        PreConstructor(
          n"UnrestrictedIsResumable",
          F(DataType(IsResumableQn, List(UsageLiteral(UAny)))),
        ),
      ),
    ),
    PreRecord(ContinuationQn)(
      tParamTys = List(
        (binding(n"level", LevelType()), Variance.INVARIANT),
        (binding(n"continuationUsage", UsageType()), Variance.INVARIANT),
        (binding(n"paramUsage", UsageType()), Variance.INVARIANT),
        (binding(n"paramType", Type(Top(Var(1)))), Variance.INVARIANT),
        (binding(n"resultUsage", UsageType()), Variance.INVARIANT),
        (binding(n"resultType", Type(Top(Var(2)))), Variance.CONTRAVARIANT),
        (binding(n"outputEffects", EffectsType()), Variance.INVARIANT),
        (binding(n"outputUsage", UsageType()), Variance.INVARIANT),
        (binding(n"outputType", Type(Top(Var(5)))), Variance.COVARIANT),
      ),
      ty = CTop(Var(9)),
      fields = List(
        Field(
          n"resume",
          Binding(DataType(IsResumableQn, List(Var(5))))(n"isResumable") ->:
            Binding(Var(6), Var(7))(n"param") ->:
            Binding(Var(5), Var(6))(n"result") ->:
            F(Var(3), Var(5), Var(4)),
        ),
        Field(
          n"dispose",
          Binding(DataType(IsDisposableQn, List(Var(5))))(n"isDisposable") ->:
            Binding(Var(6), Var(7))(n"param") ->:
            F(DataType(UnitQn, Nil), Var(4)),
        ),
        Field(
          n"replicate",
          Binding(DataType(IsReplicableQn, List(Var(6))))(n"isReplicable") ->:
            Binding(Var(6), Var(7))(n"param") ->:
            F(
              DataType(
                PairQn,
                List(
                  Var(10),
                  EqDecidabilityLiteral(EqUnknown),
                  Var(8),
                  U(RecordType(ContinuationQn, vars(10, 2))),
                  Var(8),
                  U(RecordType(ContinuationQn, vars(10, 2))),
                ),
              ),
              Var(4),
            ),
        ),
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
          rhs = Some(Return(Type(Top(Var(0))))),
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
    PreDefinition(UsageQn)(
      paramTys = Nil,
      ty = F(Type(UsageType())),
      clauses = List(
        PreClause(
          boundNames = Nil,
          lhs = Nil,
          rhs = Some(Return(UsageType())),
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

    /** CSubtypeOf (level : LevelType) (effects: EffectsType) (upperBound : U(CType(CTop(level, effects)))) :
      * CType(CType(.force upperBound, effects))
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
          rhs = Some(Return(Total())),
        ),
      ),
    ),
  )

  private def b[T](qn: QualifiedName, f: SourceInfo ?=> T): (QualifiedName, T) =
    (qn, f(using SourceInfo.SiEmpty))
