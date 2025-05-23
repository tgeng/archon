package com.github.tgeng.archon.core.ir

import com.github.tgeng.archon.common.ref.given
import com.github.tgeng.archon.core.common.*
import com.github.tgeng.archon.core.common.QualifiedName.*
import com.github.tgeng.archon.core.ir.CTerm.*
import com.github.tgeng.archon.core.ir.Declaration.*
import com.github.tgeng.archon.core.ir.EscapeStatus.EsReturned
import com.github.tgeng.archon.core.ir.PreDeclaration.*
import com.github.tgeng.archon.core.ir.Usage.*
import com.github.tgeng.archon.core.ir.VTerm.*

import scala.collection.immutable.SeqMap

private case class SimpleSignature
  (
    declarations: SeqMap[QualifiedName, Declaration] = SeqMap(),
    constructors: SeqMap[QualifiedName, IndexedSeq[Constructor]] = SeqMap(),
    cofields: SeqMap[QualifiedName, IndexedSeq[Cofield]] = SeqMap(),
    clauses: SeqMap[QualifiedName, IndexedSeq[Clause]] = SeqMap(),
    caseTrees: SeqMap[QualifiedName, CaseTree] = SeqMap(),
    operations: SeqMap[QualifiedName, IndexedSeq[Operation]] = SeqMap(),
  )
  extends Signature:

  override type S = SimpleSignature

  override def addDeclaration(d: Declaration): SimpleSignature =
    assert(!declarations.contains(d.qn))
    copy(declarations = declarations + (d.qn -> d))
  override def replaceDeclaration(d: Declaration): SimpleSignature =
    assert(declarations.contains(d.qn))
    copy(declarations = declarations + (d.qn -> d))
  override def addConstructor(qn: QualifiedName, c: Constructor): SimpleSignature =
    copy(constructors = constructors + (qn -> (constructors.getOrElse(qn, IndexedSeq()) :+ c)))
  override def addCofield(qn: QualifiedName, f: Cofield): SimpleSignature =
    copy(cofields = cofields + (qn -> (cofields.getOrElse(qn, IndexedSeq()) :+ f)))
  override def addClause(qn: QualifiedName, c: Clause): SimpleSignature =
    copy(clauses = clauses + (qn -> (clauses.getOrElse(qn, IndexedSeq()) :+ c)))
  override def addCaseTree(qn: QualifiedName, ct: CaseTree): SimpleSignature =
    copy(caseTrees = caseTrees + (qn -> ct))
  override def addOperation(qn: QualifiedName, o: Operation): SimpleSignature =
    copy(operations = operations + (qn -> (operations.getOrElse(qn, IndexedSeq()) :+ o)))

  override def getDefinitionOptionImpl(qn: QualifiedName): Option[Definition] =
    declarations.get(qn).collect { case d: Definition => d }
  override def getClausesOptionImpl(qn: QualifiedName): Option[IndexedSeq[Clause]] =
    clauses.get(qn)
  override def getCaseTreeOptionImpl(qn: QualifiedName): Option[CaseTree] =
    caseTrees.get(qn)
  override def getDataOptionImpl(qn: QualifiedName): Option[Data] =
    declarations.get(qn).collect { case d: Data => d }
  override def getConstructorsOptionImpl(qn: QualifiedName): Option[IndexedSeq[Constructor]] =
    constructors.get(qn)
  override def getCorecordOptionImpl(qn: QualifiedName): Option[Corecord] =
    declarations.get(qn).collect { case d: Corecord => d }
  override def getCofieldsOptionImpl(qn: QualifiedName): Option[IndexedSeq[Cofield]] =
    cofields.get(qn)
  override def getEffectOptionImpl(qn: QualifiedName): Option[Effect] =
    declarations.get(qn).collect { case d: Effect => d }
  override def getOperationsOptionImpl(qn: QualifiedName): Option[IndexedSeq[Operation]] =
    operations.get(qn)

object Builtins:

  val BuiltinType: QualifiedName = Builtin / "type"

  val TypeQn: QualifiedName = BuiltinType / "Type"
  val TypeOfQn: QualifiedName = BuiltinType / "TypeOf"
  val TopQn: QualifiedName = BuiltinType / "Top"

  val CTypeQn: QualifiedName = BuiltinType / "CType"
  val CTypeOfQn: QualifiedName = BuiltinType / "CTypeOf"
  val CTopQn: QualifiedName = BuiltinType / "CTop"

  val EqDecidabilityQn: QualifiedName = BuiltinType / "EqDecidability"
  val EqDecidableQn: QualifiedName = EqDecidabilityQn / "Decidable"
  val EqUnknownQn: QualifiedName = EqDecidabilityQn / "Unknown"

  val HandlerTypeQn: QualifiedName = BuiltinType / "HandlerType"
  val HtSimpleQn: QualifiedName = HandlerTypeQn / "Simple"
  val HtComplexQn: QualifiedName = HandlerTypeQn / "Complex"

  val EqualityQn: QualifiedName = BuiltinType / "Equality"
  val EffectsQn: QualifiedName = BuiltinType / "Effects"
  val LevelQn: QualifiedName = BuiltinType / "Level"

  val UsageQn: QualifiedName = BuiltinType / "Usage"
  val UsageProdQn: QualifiedName = UsageQn / "uProd"
  val UsageSumQn: QualifiedName = UsageQn / "uSum"
  val UsageJoinQn: QualifiedName = UsageQn / "uJoin"
  val UsageAnyQn: QualifiedName = UsageQn / "uAny"
  val UsageAffQn: QualifiedName = UsageQn / "uAff"
  val UsageRelQn: QualifiedName = UsageQn / "uRel"
  val UsageOneQn: QualifiedName = UsageQn / "u1"
  val UsageZeroQn: QualifiedName = UsageQn / "u0"

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
  val EffectsUnionQn: QualifiedName = BuiltinEffects / "union"
  val EffectsRetainSimpleLinearQn: QualifiedName = BuiltinEffects / "retainSimpleLinear"
  val TotalQn: QualifiedName = BuiltinEffects / "total"
  val DivQn: QualifiedName = BuiltinEffects / "div"
  val NdetQn: QualifiedName = BuiltinEffects / "ndet"
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
    val conflictingDefs = builtins
      .groupBy(_.qn)
      .filter:
        case (qn, values) => values.size > 1
    if conflictingDefs.nonEmpty then
      throw new IllegalArgumentException(s"Conflicting definitions: $conflictingDefs")
    elaborateAll(builtins)(using Context.empty)(using SimpleSignature())

  private def eBinding
    (
      name: Name,
      ty: VTerm,
      usage: VTerm = uAny,
      escapeStatus: EscapeStatus = EscapeStatus.EsReturned,
    )
    : (Binding[CTerm], EscapeStatus) =
    (Binding(Return(ty, uAny), Return(usage, uAny))(name), escapeStatus)

  private def binding
    (
      name: Name,
      ty: VTerm,
      usage: VTerm = uAny,
    )
    : Binding[CTerm] =
    Binding(Return(ty, uAny), Return(usage, uAny))(name)

  private val L0 = LevelLiteral(0)

  val builtins: Seq[PreDeclaration] = Seq(
    PreData(
      UnitQn,
      tParamTys = Nil,
      ty = F(Type(Top(L0))),
      constructors = List(PreConstructor(n"MkUnit", F(DataType(UnitQn, Nil)))),
    ),
    PreData(
      EqualityQn,
      // Invariance of level is OK because user should almost never provide this. Instead, this is
      // inferred by compiler for each compilation unit to be some large enough level.
      tParamTys = List(
        (binding(n"level", LevelType()), Variance.INVARIANT),
        (binding(n"A", Type(Top(Var(0)))), Variance.COVARIANT),
        (binding(n"x", Var(0), UsageLiteral(UAny)), Variance.INVARIANT),
      ),
      ty = FunctionType(
        Binding(Var(1))(n"y"),
        F(Type(Top(Var(3)))),
      ),
      constructors = List(
        PreConstructor(n"Refl", F(DataType(EqualityQn, List(Var(2), Var(1), Var(0), Var(0))))),
      ),
    ),
    PreData(
      PairQn,
      tParamTys = List(
        (binding(n"level", LevelType()), Variance.INVARIANT),
        (binding(n"usage1", UsageType(Some(u1))), Variance.INVARIANT),
        (binding(n"A1", Type(Top(Var(1)))), Variance.COVARIANT),
        (binding(n"usage2", UsageType(Some(u1))), Variance.INVARIANT),
        (binding(n"A2", Type(Top(Var(3)))), Variance.COVARIANT),
      ),
      ty = F(Type(Top(Var(4)))),
      constructors = List(
        PreConstructor(
          n"MkPair",
          FunctionType(
            Binding(Var(2), Var(3))(n"x"),
            FunctionType(Binding(Var(1), Var(2))(n"y"), F(DataType(PairQn, vars(6, 2)))),
          ),
        ),
      ),
    ),
    PreData(
      EitherQn,
      tParamTys = List(
        (binding(n"level", LevelType()), Variance.INVARIANT),
        (binding(n"usageL", UsageType(Some(u1))), Variance.INVARIANT),
        (binding(n"AL", Type(Top(Var(1)))), Variance.COVARIANT),
        (binding(n"usageR", UsageType(Some(u1))), Variance.INVARIANT),
        (binding(n"AR", Type(Top(Var(3)))), Variance.COVARIANT),
      ),
      ty = F(Type(Top(Var(4)))),
      constructors = List(
        PreConstructor(
          n"Left",
          FunctionType(Binding(Var(2), Var(3))(n"value"), F(DataType(EitherQn, vars(5, 1)))),
        ),
        PreConstructor(
          n"Right",
          FunctionType(Binding(Var(0), Var(1))(n"value"), F(DataType(EitherQn, vars(5, 1)))),
        ),
      ),
    ),
    PreData(
      IsDisposableQn,
      tParamTys = Nil,
      ty = FunctionType(Binding(UsageType())(n"usage"), F(Type(Top(l0)))),
      constructors = List(
        PreConstructor(n"ZeroIsDisposable", F(DataType(IsDisposableQn, List(UsageLiteral(U0))))),
        PreConstructor(
          n"AffineIsDisposable",
          F(DataType(IsDisposableQn, List(UsageLiteral(UAff)))),
        ),
      ),
    ),
    PreData(
      IsReplicableQn,
      tParamTys = Nil,
      ty = FunctionType(Binding(UsageType())(n"usage"), F(Type(Top(l0)))),
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
    PreData(
      IsResumableQn,
      tParamTys = Nil,
      ty = FunctionType(Binding(UsageType())(n"usage"), F(Type(Top(l0)))),
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
    PreCorecord(
      ContinuationQn,
      tParamTys = List(
        (binding(n"level", LevelType()), Variance.INVARIANT),
        (binding(n"continuationUsage", UsageType()), Variance.INVARIANT),
        (binding(n"paramUsage", UsageType(Some(u1))), Variance.INVARIANT),
        (binding(n"paramType", Type(Top(Var(2)))), Variance.INVARIANT),
        (binding(n"resultUsage", UsageType(Some(u1))), Variance.INVARIANT),
        (binding(n"resultType", Type(Top(Var(4)))), Variance.CONTRAVARIANT),
        (binding(n"otherEffects", EffectsType()), Variance.INVARIANT),
        (binding(n"handlerEffects", EffectsType()), Variance.INVARIANT),
        (binding(n"outputUsage", UsageType(Some(u1))), Variance.INVARIANT),
        (binding(n"outputType", Type(Top(Var(8)))), Variance.COVARIANT),
      ),
      ty = CType(CTop(Var(9))),
      cofields = List(
        Cofield(
          n"resume",
          Binding(DataType(IsResumableQn, List(Var(6))))(n"isResumable") ->:
            Binding(Var(8), Var(9))(n"param") ->:
            Binding(Var(7), Var(8))(n"result") ->:
            F(Var(4), EffectsUnion(Var(6), Var(7)), Var(5)),
        ),
        Cofield(
          n"dispose",
          Binding(DataType(IsDisposableQn, List(Var(6))))(n"isDisposable") ->:
            Binding(Var(8), Var(9))(n"param") ->:
            F(DataType(UnitQn, Nil), EffectsRetainSimpleLinear(Var(5))),
        ),
        Cofield(
          n"replicate",
          Binding(DataType(IsReplicableQn, List(Var(6))))(n"isReplicable") ->:
            Binding(Var(8), Var(9))(n"param") ->:
            F(
              DataType(
                PairQn,
                List(
                  Var(12),
                  Var(10),
                  U(CorecordType(ContinuationQn, vars(12, 3))),
                  Var(10),
                  U(CorecordType(ContinuationQn, vars(12, 3))),
                ),
              ),
              EffectsRetainSimpleLinear(Var(6)),
            ),
        ),
      ),
    ),
    /** Type (level : LevelType): Type(Type(Top(level))))
      *
      * {} |- := .return Type(Top(level))
      */
    PreDefinition(
      TypeQn,
      paramTys = List(eBinding(n"level", LevelType())),
      ty = F(Type(Type(Top(Var(0))))),
      clauses = List(
        PreClause(
          boundNames = Nil,
          lhs = Nil,
          rhs = Some(Return(Type(Top(Var(0))), uAny)),
        ),
      ),
    ),

    /** TypeOf (level : LevelType) (upperBound : Type(Top(level))) -> Type(Type(upperBound))
      *
      * {} |- := .return Type(upperBound)
      */
    PreDefinition(
      TypeOfQn,
      paramTys = List(
        eBinding(n"level", LevelType()),
        eBinding(n"upperBound", Type(Type(Top(Var(0))))),
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
    PreDefinition(
      TopQn,
      paramTys = List(eBinding(n"level", LevelType())),
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
    PreDefinition(
      EffectsQn,
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
    PreDefinition(
      LevelQn,
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
    PreDefinition(
      UsageQn,
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
    /** prod (usage1 : UsageType) (usage2 : UsageType) : UsageType
      *
      * {} |- := UsageProd(usage1, usage2)
      */
    PreDefinition(
      UsageProdQn,
      paramTys = List(
        eBinding(n"usage1", UsageType(), escapeStatus = EsReturned),
        eBinding(n"usage2", UsageType(), escapeStatus = EsReturned),
      ),
      ty = F(UsageType()),
      clauses = List(
        PreClause(
          boundNames = Nil,
          lhs = Nil,
          rhs = Some(Return(UsageProd(Var(1), Var(0)), uAny)),
        ),
      ),
    ),
    /** prod (usage1 : UsageType) (usage2 : UsageType) : UsageType
      *
      * {} |- := UsageSum(usage1, usage2)
      */
    PreDefinition(
      UsageSumQn,
      paramTys = List(
        eBinding(n"usage1", UsageType(), escapeStatus = EsReturned),
        eBinding(n"usage2", UsageType(), escapeStatus = EsReturned),
      ),
      ty = F(UsageType()),
      clauses = List(
        PreClause(
          boundNames = Nil,
          lhs = Nil,
          rhs = Some(Return(UsageSum(Var(1), Var(0)), uAny)),
        ),
      ),
    ),
    /** prod (usage1 : UsageType) (usage2 : UsageType) : UsageType
      *
      * {} |- := UsageJoin(usage1, usage2)
      */
    PreDefinition(
      UsageJoinQn,
      paramTys = List(
        eBinding(n"usage1", UsageType(), escapeStatus = EsReturned),
        eBinding(n"usage2", UsageType(), escapeStatus = EsReturned),
      ),
      ty = F(UsageType()),
      clauses = List(
        PreClause(
          boundNames = Nil,
          lhs = Nil,
          rhs = Some(Return(UsageJoin(Var(1), Var(0)), uAny)),
        ),
      ),
    ),
    PreDefinition(
      UsageAnyQn,
      paramTys = Nil,
      ty = F(UsageType()),
      clauses = List(
        PreClause(
          boundNames = Nil,
          lhs = Nil,
          rhs = Some(Return(uAny, uAny)),
        ),
      ),
    ),
    PreDefinition(
      UsageAffQn,
      paramTys = Nil,
      ty = F(UsageType()),
      clauses = List(
        PreClause(
          boundNames = Nil,
          lhs = Nil,
          rhs = Some(Return(uAff, uAny)),
        ),
      ),
    ),
    PreDefinition(
      UsageRelQn,
      paramTys = Nil,
      ty = F(UsageType()),
      clauses = List(
        PreClause(
          boundNames = Nil,
          lhs = Nil,
          rhs = Some(Return(uRel, uAny)),
        ),
      ),
    ),
    PreDefinition(
      UsageOneQn,
      paramTys = Nil,
      ty = F(UsageType()),
      clauses = List(
        PreClause(
          boundNames = Nil,
          lhs = Nil,
          rhs = Some(Return(u1, uAny)),
        ),
      ),
    ),
    PreDefinition(
      UsageZeroQn,
      paramTys = Nil,
      ty = F(UsageType()),
      clauses = List(
        PreClause(
          boundNames = Nil,
          lhs = Nil,
          rhs = Some(Return(u0, uAny)),
        ),
      ),
    ),

    /** CType (level : LevelType) (effects: EffectsType) : CType(CType(CTop(level, effects))
      *
      * {} |- := CType(CTop(level, effects))
      */
    PreDefinition(
      CTypeQn,
      paramTys = List(
        eBinding(n"level", LevelType()),
        eBinding(n"effects", EffectsType()),
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

    /** CTypeOf (level : LevelType) (effects: EffectsType) (upperBound : U(CType(CTop(level,
      * effects)))) : CType(CType(.force upperBound, effects))
      *
      * {} |- := CType(.force upperBound, effects)
      */
    PreDefinition(
      CTypeOfQn,
      paramTys = List(
        eBinding(n"level", LevelType()),
        eBinding(n"effects", EffectsType()),
        eBinding(n"upperBound", U(CType(CTop(Var(1), Var(0))))),
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

    PreDefinition(
      CTopQn,
      paramTys = List(
        eBinding(n"level", LevelType()),
        eBinding(n"effects", EffectsType()),
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
    PreDefinition(
      EffectsUnionQn,
      paramTys = List(
        eBinding(n"eff1", EffectsType()),
        eBinding(n"eff2", EffectsType()),
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
    /** filter (eff : EffectsType) : EffectsType
      *
      * {} |- := EffectsRetainSimpleLinear(eff1, eff2)
      */
    PreDefinition(
      EffectsRetainSimpleLinearQn,
      paramTys = List(
        eBinding(n"eff", EffectsType()),
      ),
      ty = F(EffectsType()),
      clauses = List(
        PreClause(
          boundNames = Nil,
          lhs = Nil,
          rhs = Some(Return(EffectsRetainSimpleLinear(Var(0)), uAny)),
        ),
      ),
    ),
    /** suc (level : LevelType) : LevelType
      *
      * {} |- := level + 1
      */
    PreDefinition(
      LevelSucQn,
      paramTys = List(
        eBinding(n"level", LevelType()),
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
    PreDefinition(
      LevelMaxQn,
      paramTys = List(
        eBinding(n"level1", LevelType()),
        eBinding(n"level2", LevelType()),
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
    PreDefinition(
      TotalQn,
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
    PreEffect(
      DivQn,
      Nil,
      Nil,
      Return(u0, uAny),
    ),
    PreEffect(
      MaybeDivQn,
      Nil,
      Nil,
      Return(uAff, uAny),
    ),
  )
