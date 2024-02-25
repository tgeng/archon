package com.github.tgeng.archon.core.ir

import com.github.tgeng.archon.core.common.*
import com.github.tgeng.archon.core.common.QualifiedName.*
import com.github.tgeng.archon.core.ir.Declaration.*

import scala.collection.immutable.SeqMap

private case class SimpleSignature
  (
    declarations: SeqMap[QualifiedName, Declaration] = SeqMap(),
    constructors: SeqMap[QualifiedName, IndexedSeq[Constructor]] = SeqMap(),
    fields: SeqMap[QualifiedName, IndexedSeq[Field]] = SeqMap(),
    clauses: SeqMap[QualifiedName, IndexedSeq[Clause]] = SeqMap(),
    caseTrees: SeqMap[QualifiedName, CaseTree] = SeqMap(),
    operations: SeqMap[QualifiedName, IndexedSeq[Operation]] = SeqMap(),
  )
  extends Signature:

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

  override def getDefinitionOption(qn: QualifiedName): Option[Definition] =
    declarations.get(qn).collect { case d: Definition => d }
  override def getClausesOption(qn: QualifiedName): Option[IndexedSeq[Clause]] =
    clauses.get(qn)
  override def getCaseTreeOption(qn: QualifiedName): Option[CaseTree] =
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

  val BuiltinType: QualifiedName = Builtin / "type"

  val TypeQn: QualifiedName = BuiltinType / "Type"
  val SubtypeOfQn: QualifiedName = BuiltinType / "SubtypeOf"
  val TopQn: QualifiedName = BuiltinType / "Top"

  val CTypeQn: QualifiedName = BuiltinType / "CType"
  val CSubtypeOfQn: QualifiedName = BuiltinType / "CSubtypeOf"
  val CTopQn: QualifiedName = BuiltinType / "CTop"

  val EqDecidabilityQn: QualifiedName = BuiltinType / "EqDecidability"
  val EqDecidableQn: QualifiedName = EqDecidabilityQn / "Decidable"
  val EqUnknownQn: QualifiedName = EqDecidabilityQn / "Unknown"

  val HandlerTypeQn: QualifiedName = BuiltinType / "HandlerType"
  val HtSimpleQn: QualifiedName = HandlerTypeQn / "Simple"
  val HtComplexQn: QualifiedName = HandlerTypeQn / "Complex"

  val EqualityQn: QualifiedName = BuiltinType / "Equality"
  val CellQn: QualifiedName = BuiltinType / "Cell"
  val UCellQn: QualifiedName = BuiltinType / "UCell"
  val EffectsQn: QualifiedName = BuiltinType / "Effects"
  val LevelQn: QualifiedName = BuiltinType / "Level"

  val UsageQn: QualifiedName = BuiltinType / "Usage"

  val UnitQn: QualifiedName = BuiltinType / "Unit"
  val MkUnitQn: QualifiedName = UnitQn / "MkUnit"

  val PairQn: QualifiedName = BuiltinType / "Pair"
  val MkPairQn: QualifiedName = PairQn / "MkPair"

  val EitherQn: QualifiedName = BuiltinType / "Either"
  val LeftQn: QualifiedName = EitherQn / "Left"
  val RightQn: QualifiedName = EitherQn / "Right"

  val ContinuationQn: QualifiedName = BuiltinType / "Continuation"
  val ResumeQn: QualifiedName = ContinuationQn / "resume"
  val DisposeQn: QualifiedName = ContinuationQn / "dispose"
  val ReplicateQn: QualifiedName = ContinuationQn / "replicate"

  val BuiltinEffects: QualifiedName = Builtin / "effects"
  val HeapEffQn: QualifiedName = BuiltinEffects / "heap"
  val AllocOpQn: QualifiedName = HeapEffQn / "alloc"
  val GetOpQn: QualifiedName = HeapEffQn / "get"
  val SetOpQn: QualifiedName = HeapEffQn / "set"
  val GlobalHeapKeyQn: QualifiedName = HeapEffQn / "global"
  val EffectsUnionQn: QualifiedName = BuiltinEffects / "union"
  val TotalQn: QualifiedName = BuiltinEffects / "total"
  val DivQn: QualifiedName = BuiltinEffects / "div"
  val MaybeDivQn: QualifiedName = BuiltinEffects / "mdiv"

  val BuiltinLevel: QualifiedName = Builtin / "level"
  val LevelSucQn: QualifiedName = BuiltinLevel / "suc"
  val LevelMaxQn: QualifiedName = BuiltinLevel / "max"

  private val PredicateQn = BuiltinType / "predicate"
  private val UsagePredicateQn = PredicateQn / "usage"
  val IsDisposableQn: QualifiedName = UsagePredicateQn / "IsDisposable"
  val IsReplicableQn: QualifiedName = UsagePredicateQn / "IsReplicable"
  val IsResumableQn: QualifiedName = UsagePredicateQn / "IsResumable"

  def Σ(using ctx: TypingContext): Signature =
    elaborateAll(builtins)(using Context.empty)(using SimpleSignature())

  import CTerm.*
  import EqDecidability.*
  import PreDeclaration.*
  import Usage.*
  import VTerm.*

  private def binding(name: Name, ty: VTerm, usage: VTerm = UsageLiteral(U1)): Binding[CTerm] =
    Binding(Return(ty, uAny), Return(usage, uAny))(name)

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
        (binding(n"A1", Type(Top(Var(2), Var(1)))), Variance.COVARIANT),
        (binding(n"usage2", EqDecidabilityType()), Variance.INVARIANT),
        (binding(n"A2", Type(Top(Var(4), Var(3)))), Variance.COVARIANT),
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
    PreData(EitherQn)(
      tParamTys = List(
        (binding(n"level", LevelType()), Variance.INVARIANT),
        (binding(n"eqDec", EqDecidabilityType()), Variance.INVARIANT),
        (binding(n"usageL", UsageType()), Variance.INVARIANT),
        (binding(n"AL", Type(Top(Var(2), Var(1)))), Variance.COVARIANT),
        (binding(n"usageR", EqDecidabilityType()), Variance.INVARIANT),
        (binding(n"AR", Type(Top(Var(4), Var(3)))), Variance.COVARIANT),
      ),
      ty = F(Type(Top(Var(5), Var(4)))),
      constructors = List(
        PreConstructor(
          n"Left",
          FunctionType(Binding(Var(2), Var(3))(n"value"), F(DataType(EitherQn, vars(4, 2)))),
        ),
        PreConstructor(
          n"Right",
          FunctionType(Binding(Var(0), Var(1))(n"value"), F(DataType(EitherQn, vars(4, 2)))),
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
      selfUsage = Return(u0, uAny),
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
            F(DataType(UnitQn, Nil), EffectsRetainSimpleLinear(Var(4))),
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
              EffectsRetainSimpleLinear(Var(4)),
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
          rhs = Some(Return(Type(Top(Var(0))), uAny)),
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
          rhs = Some(Return(Type(Var(0)), uAny)),
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
          rhs = Some(Return(Top(Var(0)), uAny)),
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
          rhs = Some(Return(EffectsType(), uAny)),
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
          rhs = Some(Return(LevelType(), uAny)),
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
          rhs = Some(Return(UsageType(), uAny)),
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
          rhs = Some(Return(EffectsUnion(Var(1), Var(0)), uAny)),
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
          rhs = Some(Return(LevelSuc(Var(0)), uAny)),
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
          rhs = Some(Return(LevelMax(Var(1), Var(0)), uAny)),
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
          rhs = Some(Return(Total(), uAny)),
        ),
      ),
    ),
  )

  private def b[T](qn: QualifiedName, f: SourceInfo ?=> T): (QualifiedName, T) =
    (qn, f(using SourceInfo.SiEmpty))
