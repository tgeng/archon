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
      /** Number of parameters among `tParamTys`, the rest are index arguments. This parameter
        * also affects how many arguments should be present in the derived constructor function:
        * only parameter arguments are needed while index arguments are set by constructors.
        */
      val numParams: Nat,
      val tParamTys: TContext,
      /* binding + tParamTys */
      val ul: ULevel,
      /* binding + tParamTys */
      val inherentUsage: VTerm,
      /* binding + tParamTys */
      val inherentEqDecidability: VTerm
    )
  case Record
    (val qn: QualifiedName)
    (
      val tParamTys: TContext = IndexedSeq(), /* binding + tParamTys */
      val ul: ULevel = ULevel.USimpleLevel(VTerm.LevelLiteral(0)),
      val selfName: Ref[Name] = n"self"
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
      /* + tParamTys.size */ val continuationUsage: VTerm = VTerm.UsageLiteral(Usage.U1)
    )

  def qn: QualifiedName

import Declaration.*

case class Constructor
  (
    name: Name,
    paramTys: Telescope = Nil, /* + tParamTys */
    /** Arguments passed to the data type constructor. For non-indexed type this should just be a
      * sequence of variables referencing the `tParamTys`. For indexed families, the argument here
      * can be any expressions. For example, for `Vec : (A: Type) -> (n: Nat) -> Type`, this would
      * be [A, 0] for `Nil` and `[A, n + 1]` for `Cons`.
      *
      * Semantically, this is simply adding some equality constraints that requires `tParamTys` to
      * be convertible to these args.
      */
    tArgs: Arguments = Nil /* + tParamTys + paramTys */
  )

case class Field(name: Name, /* + tParamTys + 1 for self */ ty: CTerm)

case class Clause
  (
    bindings: Context,
    lhs: List[CoPattern], /* + bindings */
    rhs: CTerm, /* + bindings */
    ty: CTerm /* + bindings */
  )

case class Operator
  (
    name: Name,
    paramTys: Telescope, /* + tParamTys */
    resultTy: VTerm /* + tParamTys + paramTys */,
    resultUsage: VTerm /* + tParamTys + paramTys */
  )

trait Signature:
  def addDeclaration(d: Declaration): this.type

  def addConstructor(qn: QualifiedName, c: Constructor): this.type

  def addField(qn: QualifiedName, f: Field): this.type

  def addClause(qn: QualifiedName, c: Clause): this.type

  def addCaseTree(qn: QualifiedName, ct: CaseTree): this.type

  def addOperator(qn: QualifiedName, o: Operator): this.type

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
      throw IllegalArgumentException(s"missing constructor $conName")
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
      throw IllegalArgumentException(s"missing field $fieldName")
    )

  def getDefinitionOption(qn: QualifiedName): Option[Definition]

  def getDefinition(qn: QualifiedName): Definition = getDefinitionOption(qn).get

  def getClausesOption(qn: QualifiedName): Option[IndexedSeq[Clause]]

  def getClauses(qn: QualifiedName): IndexedSeq[Clause] = getClausesOption(
    qn
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
      throw IllegalArgumentException(s"missing operator $opName")
    )
