package io.github.tgeng.archon.ir

import io.github.tgeng.archon.common.*

enum Variance:
  case INVARIANT, COVARIANT, CONTRAVARIANT

type TTelescope = List[(Binding[VTerm], Variance)]

enum Declaration:
  case Data(val qn: QualifiedName)
    (
      val tParamTys: TTelescope = Nil,
      /* binding + tParamTys */ val ul: ULevel = ULevel.USimpleLevel(VTerm.LevelLiteral(0)),
      val isPure: Boolean = true,
    )
  case Record(val qn: QualifiedName)
    (
      val tParamTys: TTelescope = Nil, /* binding + tParamTys */
      val ul: ULevel = ULevel.USimpleLevel(VTerm.LevelLiteral(0)),
    )
  case Definition(val qn: QualifiedName)
    (
      val ty: CTerm,
    )

  /**
   * Note: `tParamTys` can only contain pure value terms. That is, `U` or types that nest `U` are
   * not allowed. This is necessary because type-based handler matching needs a "simple" way to
   * efficiently locate the corresponding handler. Arbitrary logic that can happen during conversion
   * would make it very difficult to implement dynamic handlers efficiently. Also note that this
   * means we also need to conservatively reject `tParamTys` like `[A: Type, a: A]` because
   * there is no way to statically know if `A` could be `U`. In addition, this also rules out any
   * data type that wraps impure computation inside.
   */
  case Effect(val qn: QualifiedName)(val tParamTys: Telescope = Nil)

  def qn: QualifiedName

import Declaration.*

case class Constructor(
  name: Name,
  paramTys: Telescope = Nil, /* + tParamTys */
  idTys: List[Binding[VTerm.EqualityType]] = Nil /* + tParamTys + paramTys */
)

case class Operator(
  name: Name,
  paramTys: Telescope, /* + tParamTys */
  resultTy: VTerm /* + tParamTys + paramTys */
)

case class Field(name: Name, /* + tParamTys + 1 for self */ ty: CTerm)

case class CheckedClause(
  bindings: Telescope,
  lhs: List[CoPattern], /* + bindings */
  rhs: CTerm, /* + bindings */
  ty: CTerm /* + bindings */
)

trait Signature:
  def getDataOption(qn: QualifiedName): Option[Data]

  def getData(qn: QualifiedName): Data = getDataOption(qn).get

  def getConstructorsOption(qn: QualifiedName): Option[IndexedSeq[Constructor]]

  def getConstructors(qn: QualifiedName): IndexedSeq[Constructor] = getConstructorsOption(qn).get


  def getRecordOption(qn: QualifiedName): Option[Record]

  def getRecord(qn: QualifiedName): Record = getRecordOption(qn).get

  def getFieldsOption(qn: QualifiedName): Option[IndexedSeq[Field]]

  def getFields(qn: QualifiedName): IndexedSeq[Field] = getFieldsOption(qn).get


  def getDefinitionOption(qn: QualifiedName): Option[Definition]

  def getDefinition(qn: QualifiedName): Definition = getDefinitionOption(qn).get

  def getClausesOption(qn: QualifiedName): Option[IndexedSeq[CheckedClause]]

  def getClauses(qn: QualifiedName): IndexedSeq[CheckedClause] = getClausesOption(qn).get

  def getCaseTreeOption(qn: QualifiedName): Option[CaseTree]

  def getCaseTree(qn: QualifiedName): CaseTree = getCaseTreeOption(qn).get


  def getEffectOption(qn: QualifiedName): Option[Effect]

  def getEffect(qn: QualifiedName): Effect = getEffectOption(qn).get

  def getOperatorsOption(qn: QualifiedName): Option[IndexedSeq[Operator]]

  def getOperators(qn: QualifiedName): IndexedSeq[Operator] = getOperatorsOption(qn).get

  def getOperator(qn: QualifiedName, name: Name): Operator =
    getOperators(qn).getFirstOrDefault(_.name == name, throw IllegalArgumentException())

trait BuiltinSignature extends Signature :
  override def getDataOption(qn: QualifiedName): Option[Declaration.Data] =
    Builtins.builtinData.get(qn).map(_._1)
      .orElse(getUserDataOption(qn))

  def getUserDataOption(qn: QualifiedName): Option[Declaration.Data]

  override def getConstructorsOption(qn: QualifiedName): Option[IndexedSeq[Constructor]] =
    Builtins.builtinData.get(qn).map(_._2)
      .orElse(getUserConstructorsOption(qn))

  def getUserConstructorsOption(qn: QualifiedName): Option[IndexedSeq[Constructor]]


  override def getRecordOption(qn: QualifiedName): Option[Declaration.Record] =
    Builtins.builtinRecords.get(qn).map(_._1)
      .orElse(getUserRecordOption(qn))

  def getUserRecordOption(qn: QualifiedName): Option[Declaration.Record]

  override def getFieldsOption(qn: QualifiedName): Option[IndexedSeq[Field]] =
    Builtins.builtinRecords.get(qn).map(_._2)
      .orElse(getUserFieldsOption(qn))

  def getUserFieldsOption(qn: QualifiedName): Option[IndexedSeq[Field]]


  override def getDefinitionOption(qn: QualifiedName): Option[Declaration.Definition] =
    Builtins.builtinDefinitions.get(qn).map(_._1)
      // TODO: return derived definitions from record, data, and effects.
      .orElse(getUserDefinitionOption(qn))

  def getUserDefinitionOption(qn: QualifiedName): Option[Declaration.Definition]

  override def getClausesOption(qn: QualifiedName): Option[IndexedSeq[CheckedClause]] =
    Builtins.builtinDefinitions.get(qn).map(_._2)
      // TODO: return derived clauses from record, data, and effects.
      .orElse(getUserClausesOption(qn))

  def getUserClausesOption(qn: QualifiedName): Option[IndexedSeq[CheckedClause]]

  // TODO: getUserCaseTree...

  override def getEffectOption(qn: QualifiedName): Option[Declaration.Effect] =
    Builtins.builtinEffects.get(qn).map(_._1)
      .orElse(getUserEffectOption(qn))

  def getUserEffectOption(qn: QualifiedName): Option[Declaration.Effect]

  override def getOperatorsOption(qn: QualifiedName): Option[IndexedSeq[Operator]] =
    Builtins.builtinEffects.get(qn).map(_._2)
      .orElse(getUserOperatorsOption(qn))

  def getUserOperatorsOption(qn: QualifiedName): Option[IndexedSeq[Operator]]


