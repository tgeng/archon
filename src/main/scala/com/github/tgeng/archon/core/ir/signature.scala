package com.github.tgeng.archon.core.ir

import com.github.tgeng.archon.common.*
import com.github.tgeng.archon.core.common.*

import SourceInfo.*

enum Variance:
  case INVARIANT, COVARIANT, CONTRAVARIANT

enum Essentiality:
  case ESSENTIAL, AUXILIARY

type TContext = collection.IndexedSeq[(Binding[VTerm], Variance)]

given SourceInfo = SiEmpty

enum Declaration:
  case Data
    (val qn: QualifiedName)
    (
      val tParamTys: TContext,
      /* binding + tParamTys */
      val tIndexTys: Telescope,
      /* binding + tParamTys + tIndexTys */
      val level: VTerm,
      /* binding + tParamTys + tIndexTys */
      val inherentEqDecidability: VTerm,
    )
  case Record
    (val qn: QualifiedName)
    (
      val tParamTys: TContext = IndexedSeq(),
      val level: VTerm, // binding + tParamTys
      val selfBinding: Binding[VTerm],
    )
  case Definition(val qn: QualifiedName)(val ty: CTerm)

  /** Note: `tParamTys` can only contain eqDecidable value terms. That is, `U` or types that nest `U` are not allowed.
    * This is necessary because type-based handler matching needs a "simple" way to efficiently locate the corresponding
    * handler. Arbitrary logic that can happen during conversion would make it very difficult to implement dynamic
    * handlers efficiently. Also note that this means we also need to conservatively reject `tParamTys` like `[A: Type,
    * a: A]` because there is no way to statically know if `A` could be `U`. In addition, this also rules out any data
    * type that wraps non-eqDecidable computation inside.
    */
  case Effect
    (val qn: QualifiedName)
    (
      val tParamTys: Context = IndexedSeq(),
      /** This value must be the join of the continuation usages of all operations. If control mode is simple, this
        * effect is a simple effect. Otherwise it's a complex effect.
        */
      val continuationUsage: ContinuationUsage,
    )

  def qn: QualifiedName

import Declaration.*

case class Constructor
  (
    name: Name,
    paramTys: Telescope = Nil, /* + tParamTys */
    /** Arguments passed to the data type constructor. The length should be identical with `tIndexTys`. Hence, for
      * non-indexed type this should just be `Nil`. For indexed families, the argument here can be any expressions. For
      * example, for `Vec (A: Type) : (n: Nat) -> Type`, this would be [0] for constructor `Nil` and `[n + 1]` for
      * constructor `Cons`.
      */
    tArgs: Arguments = Nil, /* + tParamTys + paramTys */
  )

case class Field(name: Name, /* + tParamTys + 1 for self */ ty: CTerm)

case class Clause
  (
    bindings: Context,
    lhs: List[CoPattern], /* + bindings */
    rhs: CTerm, /* + bindings */
    ty: CTerm, /* + bindings */
  )

case class Operation
  (
    name: Name,
    continuationUsage: ContinuationUsage,
    paramTys: Telescope, /* + tParamTys */
    resultTy: VTerm /* + tParamTys + paramTys */,
    resultUsage: VTerm, /* + tParamTys + paramTys */
  )

trait Signature:
  type S <: Signature
  def addDeclaration(d: Declaration): S

  def addConstructor(qn: QualifiedName, c: Constructor): S

  def addField(qn: QualifiedName, f: Field): S

  def addClause(qn: QualifiedName, c: Clause): S

  def addCaseTree(qn: QualifiedName, ct: CaseTree): S

  def addOperation(qn: QualifiedName, o: Operation): S

  def getDataOption(qn: QualifiedName): Option[Data]

  def getData(qn: QualifiedName): Data = getDataOption(qn).get

  def getConstructorsOption(qn: QualifiedName): Option[IndexedSeq[Constructor]]

  def getConstructors(qn: QualifiedName): IndexedSeq[Constructor] =
    getConstructorsOption(qn).get

  def getConstructorOption(qn: QualifiedName, conName: Name): Option[Constructor] =
    for
      constructors <- getConstructorsOption(qn)
      r <- constructors.collectFirst {
        case con if con.name == conName => con
      }
    yield r

  def getConstructor(qn: QualifiedName, conName: Name): Constructor =
    getConstructorOption(qn, conName).getOrElse(
      throw IllegalArgumentException(s"missing constructor $conName"),
    )

  def getRecordOption(qn: QualifiedName): Option[Record]

  def getRecord(qn: QualifiedName): Record = getRecordOption(qn).get

  def getFieldsOption(qn: QualifiedName): Option[IndexedSeq[Field]]

  def getFields(qn: QualifiedName): IndexedSeq[Field] = getFieldsOption(qn).get

  def getFieldOption(qn: QualifiedName, fieldName: Name): Option[Field] =
    for
      fields <- getFieldsOption(qn)
      r <- fields.collectFirst {
        case field if field.name == fieldName => field
      }
    yield r

  def getField(qn: QualifiedName, fieldName: Name): Field =
    getFieldOption(qn, fieldName).getOrElse(
      throw IllegalArgumentException(s"missing field $fieldName"),
    )

  def getDefinitionOption(qn: QualifiedName): Option[Definition]

  def getDefinition(qn: QualifiedName): Definition = getDefinitionOption(qn).get

  def getClausesOption(qn: QualifiedName): Option[IndexedSeq[Clause]]

  def getClauses(qn: QualifiedName): IndexedSeq[Clause] = getClausesOption(
    qn,
  ).get

  def getCaseTreeOption(qn: QualifiedName): Option[CaseTree]

  def getCaseTree(qn: QualifiedName): CaseTree = getCaseTreeOption(qn).get

  def getEffectOption(qn: QualifiedName): Option[Effect]

  def getEffect(qn: QualifiedName): Effect = getEffectOption(qn).get

  def getOperationsOption(qn: QualifiedName): Option[IndexedSeq[Operation]]

  def getOperations(qn: QualifiedName): IndexedSeq[Operation] =
    getOperationsOption(qn).get

  def getOperationOption(qn: QualifiedName, opName: Name): Option[Operation] =
    for
      operations <- getOperationsOption(qn)
      r <- operations.collectFirst {
        case op if op.name == opName => op
      }
    yield r

  def getOperation(qn: QualifiedName, opName: Name): Operation =
    getOperationOption(qn, opName).getOrElse(
      throw IllegalArgumentException(s"missing operation $opName"),
    )
