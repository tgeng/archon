package com.github.tgeng.archon.core.ir

import com.github.tgeng.archon.common.*
import com.github.tgeng.archon.core.common.*
import com.github.tgeng.archon.core.ir.ULevel.USimpleLevel

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
      val ul: ULevel,
      /* binding + tParamTys + tIndexTys */
      val inherentUsage: VTerm,
      /* binding + tParamTys + tIndexTys */
      val inherentEqDecidability: VTerm,
    )
  case Record
    (val qn: QualifiedName)
    (
      val tParamTys: TContext = IndexedSeq(), /* binding + tParamTys */
      val ul: ULevel = ULevel.USimpleLevel(VTerm.LevelLiteral(0)),
      val selfName: Ref[Name] = n"self",
    )
  case Definition(val qn: QualifiedName)(val ty: CTerm)

  /** Note: `tParamTys` can only contain eqDecidable value terms. That is, `U` or types that nest
    * `U` are not allowed. This is necessary because type-based handler matching needs a "simple"
    * way to efficiently locate the corresponding handler. Arbitrary logic that can happen during
    * conversion would make it very difficult to implement dynamic handlers efficiently. Also note
    * that this means we also need to conservatively reject `tParamTys` like `[A: Type, a: A]`
    * because there is no way to statically know if `A` could be `U`. In addition, this also rules
    * out any data type that wraps non-eqDecidable computation inside.
    */
  case Effect
    (val qn: QualifiedName)
    (
      val tParamTys: Context = IndexedSeq(),
      /** Semantic:
        *
        *   - None: operators don't manipulate continuations at all (hence won't have access to a
        *     continuation argument). Instead, implementation of an operation simply returns the
        *     operation result. Semantically None subsumes `U1` because it's a more restricted
        *     case of U1.
        *   - Some(u): operations can manipulate continuations in ways according to `u`.
        *     Specifically, for each value of `u` as the following
        *     - U0: continuation can only be disposed
        *     - U1: continuation can only be resumed. Difference from `None` is that output of
        *       continuation can be inspected and more computation can be done after the
        *       continuation is resumed.
        *     - UAff: continuation can be resumed or disposed
        *     - URel: continuation can be resumed or replicated
        *     - UUnres: continuation an be resumed, disposed, or replicated.
        *    Note that continuation is always captured linearly in `U`. It's difficult to sugarize
        *    the record type `U U1 Continuation` as a function type with various usages and
        *    automatically insert dispose and replicate wherever needed. This is because dispose
        *    and replicate can be effectful. The effect is captured by the `Continuation` record
        *    type, though such effects can only have `None` continuation usage so that the
        *    operation semantic is simple. 
        */
      val continuationUsage: Option[Usage] = None,
    )

  def qn: QualifiedName

import Declaration.*

case class Constructor
  (
    name: Name,
    paramTys: Telescope = Nil, /* + tParamTys */
    /** Arguments passed to the data type constructor. The length should be identical with
      * `tIndexTys`. Hence, for non-indexed type this should just be `Nil`. For indexed families,
      * the argument here can be any expressions. For example, for `Vec (A: Type) : (n: Nat) ->
      * Type`, this would be [0] for constructor `Nil` and `[n + 1]` for constructor `Cons`.
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

case class Operator
  (
    name: Name,
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

  def addOperator(qn: QualifiedName, o: Operator): S

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

  def getOperatorsOption(qn: QualifiedName): Option[IndexedSeq[Operator]]

  def getOperators(qn: QualifiedName): IndexedSeq[Operator] =
    getOperatorsOption(qn).get

  def getOperatorOption(qn: QualifiedName, opName: Name): Option[Operator] =
    for
      operators <- getOperatorsOption(qn)
      r <- operators.collectFirst {
        case op if op.name == opName => op
      }
    yield r

  def getOperator(qn: QualifiedName, opName: Name): Operator =
    getOperatorOption(qn, opName).getOrElse(
      throw IllegalArgumentException(s"missing operator $opName"),
    )
