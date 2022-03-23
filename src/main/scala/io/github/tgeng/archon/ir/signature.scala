package io.github.tgeng.archon.ir

import io.github.tgeng.archon.common.*

enum Variance:
  case INVARIANT, COVARIANT, CONTRAVARIANT

type TTelescope = List[(Binding[VTerm], Variance)]

enum Declaration:
  case Data(val qn: QualifiedName)
    (
      val tParamTys: TTelescope = Nil, /* binding + paramTys */
      val ul: ULevel = ULevel.USimpleLevel(VTerm.LevelLiteral(0)),
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
   * means we also need to conservatively reject `tParamTys` like `[A: VUniverse, a: A]` because
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
  def getData(qn: QualifiedName): Data

  def getConstructors(qn: QualifiedName): IndexedSeq[Constructor]


  def getRecord(qn: QualifiedName): Record

  def getFields(qn: QualifiedName): IndexedSeq[Field]


  def getDefinition(qn: QualifiedName): Definition

  def getClauses(qn: QualifiedName): IndexedSeq[CheckedClause]

  def getCaseTree(qn: QualifiedName): CaseTree


  def getEffect(qn: QualifiedName): Effect

  def getOperators(qn: QualifiedName): IndexedSeq[Operator]