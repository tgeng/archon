package com.github.tgeng.archon.core.ir

import com.github.tgeng.archon.common.*
import com.github.tgeng.archon.core.common.*
import com.github.tgeng.archon.core.ir.SourceInfo.*

enum Variance:
  case INVARIANT, COVARIANT, CONTRAVARIANT
  def flip: Variance = this match
    case INVARIANT     => INVARIANT
    case COVARIANT     => CONTRAVARIANT
    case CONTRAVARIANT => COVARIANT

given SourceInfo = SiEmpty

enum Declaration:
  case Data
    (
      qn: QualifiedName,
      context: TContext,
      /* binding: + context */
      tIndexTys: Telescope,
      /* binding: + context */
      level: VTerm,
    )
  case Record
    (
      qn: QualifiedName,
      context: TContext,
      /* binding: + context + tIndexTys */
      level: VTerm,
      selfBinding: Binding[VTerm],
    )

  case Definition(qn: QualifiedName, context: Context, ty: CTerm /* binding += context */ )

  case Effect
    (
      qn: QualifiedName,
      context: Context,
      continuationUsage: VTerm, // binding += tParamTys
    )

  def qn: QualifiedName

import com.github.tgeng.archon.core.ir.Declaration.*

case class Constructor
  (
    name: Name,
    paramTys: Telescope = Nil, /* binding += context */
    /** Arguments passed to the data type constructor. The length should be identical with
      * `tIndexTys`. Hence, for non-indexed type this should just be `Nil`. For indexed families,
      * the argument here can be any expressions. For example, for `Vec (A: Type) : (n: Nat) ->
      * Type`, this would be [0] for constructor `Nil` and `[n + 1]` for constructor `Cons`.
      */
    tArgs: Arguments = Nil, /* binding += context + paramTys */
  )

case class Field(name: Name, /* + tParamTys + 1 for self */ ty: CTerm)

case class Clause
  (
    // contains def.context
    context: Context,
    lhs: List[CoPattern], /* bindings += clause.context */
    rhs: CTerm, /* bindings += clause.context */
    ty: CTerm, /* bindings += clause.context */
  )

case class Operation
  (
    name: Name,
    paramTys: Telescope, /* + context */
    resultTy: VTerm /* + context + paramTys */,
    resultUsage: VTerm, /* + context + paramTys */
  )

trait Signature:
  type S <: Signature
  def addDeclaration(d: Declaration): S
  def replaceDeclaration(d: Declaration): S

  def addConstructor(qn: QualifiedName, c: Constructor): S

  def addField(qn: QualifiedName, f: Field): S

  def addClause(qn: QualifiedName, c: Clause): S

  def addCaseTree(qn: QualifiedName, ct: CaseTree): S

  def addOperation(qn: QualifiedName, o: Operation): S

  def getDataOption(qn: QualifiedName): Option[Data]

  def getData(qn: QualifiedName): Data = getDataOption(qn).getOrElse(
    throw IllegalArgumentException(s"Missing data for '$qn'"),
  )

  def getConstructorsOption(qn: QualifiedName): Option[IndexedSeq[Constructor]]

  def getConstructors(qn: QualifiedName): IndexedSeq[Constructor] =
    getConstructorsOption(qn).getOrElse(
      throw IllegalArgumentException(s"Missing constructors for '$qn'"),
    )

  def getConstructorOption(qn: QualifiedName, conName: Name): Option[Constructor] =
    for
      constructors <- getConstructorsOption(qn)
      r <- constructors.collectFirst:
        case con if con.name == conName => con
    yield r

  def getConstructor(qn: QualifiedName, conName: Name): Constructor =
    getConstructorOption(qn, conName).getOrElse(
      throw IllegalArgumentException(s"Missing constructor $conName"),
    )

  def getConstructorOption(constructorQn: QualifiedName): Option[Constructor] = constructorQn match
    case QualifiedName.Node(dataQn, conName) => getConstructorOption(dataQn, conName)
    case _ => throw IllegalArgumentException(s"Not a constructor $constructorQn")

  def getRecordOption(qn: QualifiedName): Option[Record]

  def getRecord(qn: QualifiedName): Record =
    getRecordOption(qn).getOrElse(throw IllegalArgumentException(s"Missing record for '$qn'"))

  def getFieldsOption(qn: QualifiedName): Option[IndexedSeq[Field]]

  def getFields(qn: QualifiedName): IndexedSeq[Field] =
    getFieldsOption(qn).getOrElse(throw IllegalArgumentException(s"Missing fields for '$qn'"))

  def getFieldOption(qn: QualifiedName, fieldName: Name): Option[Field] =
    for
      fields <- getFieldsOption(qn)
      r <- fields.collectFirst:
        case field if field.name == fieldName => field
    yield r

  def getField(qn: QualifiedName, fieldName: Name): Field =
    getFieldOption(qn, fieldName).getOrElse(
      throw IllegalArgumentException(s"Missing field '$fieldName' for '$qn'"),
    )

  def getFieldOption(fieldQn: QualifiedName): Option[Field] = fieldQn match
    case QualifiedName.Node(recordQn, fieldName) => getFieldOption(recordQn, fieldName)
    case _ => throw IllegalArgumentException(s"Not a field '$fieldQn'")

  def getDefinitionOption(qn: QualifiedName): Option[Definition] =
    getDefinitionOptionImpl(qn).orElse(getDerivedDefinitionOption(qn))

  def getDefinitionOptionImpl(qn: QualifiedName): Option[Definition]

  def getDefinition(qn: QualifiedName): Definition = getDefinitionOption(qn).getOrElse(
    throw IllegalArgumentException(s"Missing definition for '$qn'"),
  )

  def getClausesOption(qn: QualifiedName): Option[IndexedSeq[Clause]] =
    getClausesOptionImpl(qn).orElse(getDerivedClausesOption(qn))

  def getClausesOptionImpl(qn: QualifiedName): Option[IndexedSeq[Clause]]

  def getClauses(qn: QualifiedName): IndexedSeq[Clause] = getClausesOption(
    qn,
  ).getOrElse(throw IllegalArgumentException(s"Missing clauses for '$qn'"))

  def getCaseTreeOption(qn: QualifiedName): Option[CaseTree]

  def getCaseTree(qn: QualifiedName): CaseTree = getCaseTreeOption(qn).getOrElse(
    throw IllegalArgumentException(s"Missing case tree for '$qn'"),
  )

  def getEffectOption(qn: QualifiedName): Option[Effect]

  def getEffect(qn: QualifiedName): Effect = getEffectOption(qn).getOrElse(
    throw IllegalArgumentException(s"Missing effect for '$qn'"),
  )

  def getOperationsOption(qn: QualifiedName): Option[IndexedSeq[Operation]]

  def getOperations(qn: QualifiedName): IndexedSeq[Operation] =
    getOperationsOption(qn).getOrElse(
      throw IllegalArgumentException(s"Missing operations for '$qn'"),
    )

  def getOperationOption(qn: QualifiedName, opName: Name): Option[Operation] =
    for
      operations <- getOperationsOption(qn)
      r <- operations.collectFirst:
        case op if op.name == opName => op
    yield r

  def getOperation(qn: QualifiedName): Operation =
    qn match
      case QualifiedName.Node(qn, name) => getOperation(qn, name)
      case _                            => throw IllegalArgumentException(s"missing operation $qn")

  def getOperation(qn: QualifiedName, opName: Name): Operation =
    getOperationOption(qn, opName).getOrElse(
      throw IllegalArgumentException(s"missing operation $opName"),
    )

  // TODO[P2]: remove all these derived defs from data, record, and effects. Instead, data type and
  //  value constructors, record type constructors, and effect type constructors and operators
  //  directly contribute to global names that are recognized by the global mix-fix parser. This
  //  way, type checking is much simpler and more predictable. Also, any name conflicts are caught
  //  during parsing. Record field will have a special syntax for projection. Type class also
  //  contributes to the mix-fix parser and it's basically syntax sugar of records under the hood.
  private def getDerivedDefinitionOption(qn: QualifiedName): Option[Definition] =
    getDataDerivedDefinitionOption(qn)
      .orElse(getDataConDerivedDefinitionOption(qn))
      .orElse(getRecordDerivedDefinitionOption(qn))
      .orElse(getRecordFieldDerivedDefinitionOption(qn))

  private def getDerivedClausesOption(qn: QualifiedName): Option[IndexedSeq[Clause]] =
    getDataDerivedClausesOption(qn)
      .orElse(getDataConDerivedClausesOption(qn))
      .orElse(getRecordDerivedClausesOption(qn))
      .orElse(getRecordFieldDerivedClausesOption(qn))

  import CTerm.*
  import QualifiedName.*
  import VTerm.*

  given SourceInfo = SiEmpty
  given Signature = this

  def getDataDerivedDefinitionOption(qn: QualifiedName): Option[Declaration.Definition] =
    getDataOption(qn).map { data =>
      val context = data.context.map(_._1) ++ data.tIndexTys
      Definition(qn, context, F(Type(DataType(qn, vars(context.size - 1))), total, uAny))
    }

  def getDataDerivedClausesOption(qn: QualifiedName): Option[IndexedSeq[Clause]] =
    getDataOption(qn)
      .map(data => {
        val context = data.context.map(_._1) ++ data.tIndexTys
        val dataType = DataType(qn, vars(context.size - 1))
        IndexedSeq(
          Clause(
            context,
            Nil,
            Return(dataType, uAny),
            F(Type(dataType), total, uAny),
          ),
        )
      })

  def getDataConDerivedDefinitionOption(qn: QualifiedName): Option[Declaration.Definition] =
    qn match
      case Node(dataQn, conName) =>
        for
          data <- getDataOption(dataQn)
          constructor <- getConstructorOption(dataQn, conName)
        yield
          val context = data.context.map(_._1) ++ data.tIndexTys
          // Synthesize a usage parameter for polymorphic usages in data types.
          val conContext =
            (context :+ Binding(UsageType(), uAny)(gn"usage")) ++
              constructor.paramTys.zipWithIndex.map((b, i) =>
                Binding(
                  b.ty.weakened,
                  // multiply the usage by the synthesized usage parameter
                  UsageProd(b.usage.weakened, Var(i)),
                )(b.name),
              )
          Definition(
            qn / conName,
            conContext,
            F(
              DataType(
                dataQn,
                vars(conContext.size - 1, constructor.paramTys.size + 1) ++
                  // weaken due to the synthesized usage parameter
                  constructor.tArgs.map(_.weaken(1, constructor.paramTys.size)),
              ),
              total,
              Var(constructor.paramTys.size), // reference the synthesized usage parameter
            ),
          )
      case _ => None

  def getDataConDerivedClausesOption(qn: QualifiedName): Option[IndexedSeq[Clause]] =
    qn match
      case Node(dataQn, conName) =>
        for
          data <- getDataOption(dataQn)
          constructor <- getConstructorOption(dataQn, conName)
        yield
          val context = data.context.map(_._1) ++ data.tIndexTys
          // Synthesize a usage parameter for polymorphic usages in data types.
          val conContext =
            (context :+ Binding(UsageType(), uAny)(gn"usage")) ++
              constructor.paramTys.zipWithIndex.map((b, i) =>
                Binding(
                  b.ty.weakened,
                  // multiply the usage by the synthesized usage parameter
                  UsageProd(b.usage.weakened, Var(i)),
                )(b.name),
              )
          IndexedSeq(
            Clause(
              conContext,
              Nil,
              Return(
                Con(
                  conName,
                  vars(constructor.paramTys.size - 1),
                ),
                Var(constructor.paramTys.size), // reference the synthesized usage parameter
              ),
              F(
                DataType(
                  dataQn,
                  vars(conContext.size - 1, constructor.paramTys.size + 1) ++
                    // weaken due to the synthesized usage parameter
                    constructor.tArgs.map(_.weaken(1, constructor.paramTys.size)),
                ),
                total,
                Var(constructor.paramTys.size), // reference the synthesized usage parameter
              ),
            ),
          )
      case _ => None

  def getRecordDerivedDefinitionOption(qn: QualifiedName): Option[Declaration.Definition] =
    getRecordOption(qn)
      .map(record =>
        Definition(
          qn,
          record.context.map(_._1) :+ Binding(EffectsType(), uAny)(gn"effects"),
          // The effect should be parametrically polymorphic so that one is able to construct record
          // type with different effects.
          CType(RecordType(qn, vars(record.context.size, 1), Var(0))),
        ),
      )

  def getRecordDerivedClausesOption(qn: QualifiedName): Option[IndexedSeq[Clause]] =
    getRecordOption(qn)
      .map(record => {
        val recordType = RecordType(qn, vars(record.context.size, 1), Var(0))
        IndexedSeq(
          Clause(
            record.context.map(_._1) :+ Binding(EffectsType(), uAny)(gn"effects"),
            Nil,
            recordType,
            CType(recordType),
          ),
        )
      })

  def getRecordFieldDerivedDefinitionOption(qn: QualifiedName): Option[Declaration.Definition] =
    qn match
      case Node(qn, fieldName) =>
        for
          record <- getRecordOption(qn)
          field <- getFieldOption(qn, fieldName)
        yield Definition(qn, record.context.map(_._1) :+ record.selfBinding, field.ty)
      case _ => None

  def getRecordFieldDerivedClausesOption(qn: QualifiedName): Option[IndexedSeq[Clause]] =
    qn match
      case Node(qn, fieldName) =>
        for
          record <- getRecordOption(qn)
          field <- getFieldOption(qn, fieldName)
        yield IndexedSeq(
          Clause(
            record.context.map(_._1) :+ record.selfBinding,
            Nil,
            redex(Force(Var(0)), fieldName),
            field.ty,
          ),
        )
      case _ => None
