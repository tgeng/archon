package com.github.tgeng.archon.core.ir

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
  case Corecord
    (
      qn: QualifiedName,
      context: TContext,
      /* binding += context */
      level: VTerm,
      selfBinding: Binding[VTerm],
    )

  case Definition(qn: QualifiedName, context: EContext, ty: CTerm /* binding += context */ )

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

case class Cofield(name: Name, /* binding += context + 1 for self */ ty: CTerm)

case class Clause
  (
    // contains def.context + elaborated variables from lhs co-patterns
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

  def addCofield(qn: QualifiedName, f: Cofield): S

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

  def getCorecordOption(qn: QualifiedName): Option[Corecord]

  def getCorecord(qn: QualifiedName): Corecord =
    getCorecordOption(qn).getOrElse(throw IllegalArgumentException(s"Missing corecord for '$qn'"))

  def getCofieldsOption(qn: QualifiedName): Option[IndexedSeq[Cofield]]

  def getCofields(qn: QualifiedName): IndexedSeq[Cofield] =
    getCofieldsOption(qn).getOrElse(throw IllegalArgumentException(s"Missing cofields for '$qn'"))

  def getCofieldOption(qn: QualifiedName, cofieldName: Name): Option[Cofield] =
    for
      cofields <- getCofieldsOption(qn)
      r <- cofields.collectFirst:
        case cofield if cofield.name == cofieldName => cofield
    yield r

  def getCofield(qn: QualifiedName, cofieldName: Name): Cofield =
    getCofieldOption(qn, cofieldName).getOrElse(
      throw IllegalArgumentException(s"Missing cofield '$cofieldName' for '$qn'"),
    )

  def getCofieldOption(cofieldQn: QualifiedName): Option[Cofield] = cofieldQn match
    case QualifiedName.Node(corecordQn, cofieldName) => getCofieldOption(corecordQn, cofieldName)
    case _ => throw IllegalArgumentException(s"Not a cofield '$cofieldQn'")

  // In a previous design I had derived definitions for effects, data, and corecord. But that turns
  // out to be not good. Instead, data type and value constructors, corecord type constructors, and
  // effect type constructors and operators directly contribute to global names that are recognized
  // by the global mix-fix parser. This way, type checking is much simpler and more predictable.
  // Also, any name conflicts are caught during parsing. Corecord cofield will have a special syntax for
  // projection. Type class also contributes to the mix-fix parser and it's basically syntax sugar
  // of corecords under the hood.
  def getDefinitionOption(qn: QualifiedName): Option[Definition] =
    getDefinitionOptionImpl(qn)

  def getDefinitionOptionImpl(qn: QualifiedName): Option[Definition]

  def getDefinition(qn: QualifiedName): Definition = getDefinitionOption(qn).getOrElse(
    throw IllegalArgumentException(s"Missing definition for '$qn'"),
  )

  def getClausesOption(qn: QualifiedName): Option[IndexedSeq[Clause]] =
    getClausesOptionImpl(qn)

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
