package io.github.tgeng.archon.ir

import io.github.tgeng.archon.common.*

enum Variance:
  case INVARIANT, COVARIANT, CONTRAVARIANT

type TTelescope = List[(Binding[VTerm], Variance)]

enum Declaration:
  case Data(val qn: QualifiedName)
    (
      val tParamTys: TTelescope, /* binding + paramTys */
      val ul: ULevel,
      val cons: IndexedSeq[Constructor]
    )

  /**
   * Note: `tParamTys` can only contain pure value terms. That is, `U` and `Thunk` are not allowed.
   * This is necessary because type-based handler matching needs a "simple" way to efficiently
   * locate the corresponding handler. Arbitrary logic that can happen during conversion would make
   * it very difficult to implement dynamic handlers efficiently. Also note that this means we also
   * need to conservatively reject `tParamTys` like `[A: VUniverse, a: A]` because there is no way
   * to statically know if `A` could be `U`. In addition, this also rules out any data type that
   * wraps impure computation inside.
   */
  case Effect(val qn: QualifiedName)
    (val tParamTys: Telescope, val operators: IndexedSeq[Operator])
  case Record(val qn: QualifiedName)
    (val tParamTys: TTelescope, /* binding + tParamTys */ val ul: ULevel, val fields: IndexedSeq[Field])
  case Definition(val qn: QualifiedName)
    (val ty: CTerm, val clauses: IndexedSeq[CheckedClause], val caseTree: CaseTree)

  def qn: QualifiedName

import Declaration.*

case class Constructor(
  name: Name,
  paramTys: Telescope, /* + tParamTys */
  idTys: List[Binding[VTerm.EqualityType]] /* + tParamTys + paramTys */
)

case class Operator(
  name: Name,
  paramTys: Telescope, /* + tParamTys */
  resultTy: VTerm /* + tParamTys + paramTys */
)

case class Field(name: Name, /* + tParamTys + 1 for self */ ty: CTerm)

case class CheckedClause(
  bindings: Telescope,
  lhs: List[Pattern], /* + bindings */
  rhs: CTerm, /* + bindings */
  ty: CTerm /* + bindings */
)

trait Signature:
  def getData(qn: QualifiedName): Data

  def getRecord(qn: QualifiedName): Record

  def getDef(qn: QualifiedName): Definition

  def getEffect(qn: QualifiedName): Effect