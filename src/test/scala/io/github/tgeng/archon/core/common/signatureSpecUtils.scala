package io.github.tgeng.archon.core.common

import collection.mutable
import org.scalatest.freespec.AnyFreeSpec
import io.github.tgeng.archon.core.ir.*
import io.github.tgeng.archon.common.*
import io.github.tgeng.archon.core.common.*
import Declaration.*

import scala.annotation.targetName

type MutableContext = mutable.ArrayBuffer[Binding[VTerm]]

class SignatureSpec extends AnyFreeSpec :
  given TypingContext = new TypingContext {}

  given Γ: MutableContext = mutable.ArrayBuffer()

  given TestSignature = TestSignature(
    mutable.Map(),
    mutable.Map(),
    mutable.Map(),
    mutable.Map(),
    mutable.Map(),
    mutable.Map(),
    mutable.Map(),
    mutable.Map(),
  )

  extension (tm: VTerm)
    infix def hasType(ty: VTerm)(using Context)(using Signature)(using TypingContext) =
      checkType(tm, ty) match
        case Right(_) =>
        case Left(e) => fail(e.toString)

    infix def doesNotHaveType(ty: VTerm)(using Context)(using Signature)(using TypingContext) =
      checkType(tm, ty) match
        case Right(_) => fail(s"expect $tm to not have type $ty")
        case Left(e) =>

    infix def ⪯(tm2: VTerm)(using Context)(using Signature)(using TypingContext) =
      checkSubsumption(tm, tm2, None)(using CheckSubsumptionMode.SUBSUMPTION) match
        case Right(_) =>
        case Left(e) => fail(e.toString)

    infix def ⋠(tm2: VTerm)(using Context)(using Signature)(using TypingContext) =
      checkSubsumption(tm, tm2, None)(using CheckSubsumptionMode.SUBSUMPTION) match
        case Right(_) => fail(s"expect $tm ⋠ $tm2")
        case Left(e) =>

    infix def ≡(tm2: VTerm)(using Context)(using Signature)(using TypingContext) =
      checkSubsumption(tm, tm2, None)(using CheckSubsumptionMode.CONVERSION) match
        case Right(_) =>
        case Left(e) => fail(e.toString)

    infix def ≢(tm2: VTerm)(using Context)(using Signature)(using TypingContext) =
      checkSubsumption(tm, tm2, None)(using CheckSubsumptionMode.CONVERSION) match
        case Right(_) => fail(s"expect $tm ≢ $tm2")
        case Left(e) =>

  extension (tm: CTerm)
    infix def hasType(ty: CTerm)(using Context)(using Signature)(using TypingContext) =
      checkType(tm, ty) match
        case Right(_) =>
        case Left(e) => fail(e.toString)

    infix def doesNotHaveType(ty: CTerm)(using Context)(using Signature)(using TypingContext) =
      checkType(tm, ty) match
        case Right(_) => fail(s"expect $tm to not have type $ty")
        case Left(e) =>

    infix def ⪯(tm2: CTerm)(using Context)(using Signature)(using TypingContext) =
      checkSubsumption(tm, tm2, None)(using CheckSubsumptionMode.SUBSUMPTION) match
        case Right(_) =>
        case Left(e) => fail(e.toString)

    infix def ⋠(tm2: CTerm)(using Context)(using Signature)(using TypingContext) =
      checkSubsumption(tm, tm2, None)(using CheckSubsumptionMode.SUBSUMPTION) match
        case Right(_) => fail(s"expect $tm ⋠ $tm2")
        case Left(e) =>

    infix def ≡(tm2: CTerm)(using Context)(using Signature)(using TypingContext) =
      checkSubsumption(tm, tm2, None)(using CheckSubsumptionMode.CONVERSION) match
        case Right(_) =>
        case Left(e) => fail(e.toString)

    infix def ≢(tm2: CTerm)(using Context)(using Signature)(using TypingContext) =
      checkSubsumption(tm, tm2, None)(using CheckSubsumptionMode.CONVERSION) match
        case Right(_) => fail(s"expect $tm ≢ $tm2")
        case Left(e) =>

class TestSignature(
  val allData: mutable.Map[QualifiedName, Data],
  val allConstructors: mutable.Map[QualifiedName, IndexedSeq[Constructor]],
  val allRecords: mutable.Map[QualifiedName, Record],
  val allFields: mutable.Map[QualifiedName, IndexedSeq[Field]],
  val allDefinitions: mutable.Map[QualifiedName, Definition],
  val allClauses: mutable.Map[QualifiedName, IndexedSeq[CheckedClause]],
  val allEffects: mutable.Map[QualifiedName, Effect],
  val allOperators: mutable.Map[QualifiedName, IndexedSeq[Operator]],
) extends BuiltinSignature :
  override def getUserDataOption(qn: QualifiedName) = allData.get(qn)

  override def getUserConstructorsOption(qn: QualifiedName) = allConstructors.get(qn)

  override def getUserRecordOption(qn: QualifiedName) = allRecords.get(qn)

  override def getUserFieldsOption(qn: QualifiedName) = allFields.get(qn)

  override def getUserDefinitionOption(qn: QualifiedName) = allDefinitions.get(qn)

  override def getUserClausesOption(qn: QualifiedName) = allClauses.get(qn)

  override def getCaseTreeOption(qn: QualifiedName) = ???

  override def getUserEffectOption(qn: QualifiedName) = allEffects.get(qn)

  override def getUserOperatorsOption(qn: QualifiedName) = allOperators.get(qn)

  def copy: TestSignature = TestSignature(
    allData,
    allConstructors,
    allRecords,
    allFields,
    allDefinitions,
    allClauses,
    allEffects,
    allOperators,
  )

extension (b: MutableContext ?=> TestSignature ?=> Unit)
  def unary_~(using Γ: MutableContext)
    (using Σ: TestSignature) = b(using mutable.ArrayBuffer(Γ.toArray: _*))(using Σ.copy)

extension (declaration: Declaration)
  def unary_+(using Σ: TestSignature)(using ctx: TypingContext): QualifiedName =
    val checkResult = declaration match
      case data: Data =>
        Σ.allData(declaration.qn) = data
        checkDataType(declaration.qn)
      case record: Record =>
        Σ.allRecords(declaration.qn) = record
        checkRecordType(declaration.qn)
      case definition: Definition =>
        Σ.allDefinitions(declaration.qn) = definition
        checkDef(declaration.qn)
      case effect: Effect =>
        Σ.allEffects(declaration.qn) = effect
        checkEffect(declaration.qn)

    checkResult match
      case Left(error) => throw IllegalArgumentException(s"error when checking ${declaration.qn}: $error")
      case _ =>
    declaration.qn

extension (binding: Binding[VTerm])
  def unary_+(using Γ: MutableContext) = Γ.addOne(binding)

extension (qn: QualifiedName)
  @targetName("addConstructors")
  infix def +(constructor: Constructor)
    (using Σ: TestSignature)
    (using ctx: TypingContext): QualifiedName =
    checkDataConstructor(qn, constructor) match
      case Left(error) => throw IllegalArgumentException(s"error when checking constructor ${constructor.name}: $error")
      case _ =>
    Σ.allConstructors(qn) = Σ.allConstructors.getOrElseUpdate(qn, IndexedSeq()) :+ constructor
    qn

  @targetName("addFields")
  infix def +(field: Field)
    (using Σ: TestSignature)
    (using ctx: TypingContext)
  : QualifiedName =
    checkRecordField(qn, field) match
      case Left(error) => throw IllegalArgumentException(s"error when checking field ${field.name}: $error")
      case _ =>
    Σ.allFields(qn) = Σ.allFields.getOrElseUpdate(qn, IndexedSeq()) :+ field
    qn

  @targetName("addClauses")
  infix def +(clause: CheckedClause)
    (using Σ: TestSignature)
    (using ctx: TypingContext)
  : QualifiedName =
    checkClause(qn, clause) match
      case Left(error) => throw IllegalArgumentException(s"error when checking clause ${clause}: $error")
      case _ =>
    Σ.allClauses(qn) = Σ.allClauses.getOrElseUpdate(qn, IndexedSeq()) :+ clause
    qn

  @targetName("addOperators")
  infix def +(operator: Operator)
    (using Σ: TestSignature)
    (using ctx: TypingContext)
  : QualifiedName =
    checkOperator(qn, operator) match
      case Left(error) => throw IllegalArgumentException(s"error when checking operator ${operator}: $error")
      case _ =>
    Σ.allOperators(qn) = Σ.allOperators.getOrElseUpdate(qn, IndexedSeq()) :+ operator
    qn

def data(qn: QualifiedName, tArgs: (Binding[VTerm], Variance)*)
  (
    ul: ULevel = ULevel.USimpleLevel(VTerm.LevelLiteral(0)),
    isPure: Boolean = true
  ) : Data = Data(qn)(tArgs.toList, ul, isPure)

def constructor(name: Name, args: Binding[VTerm]*)
  (tArgs: VTerm*): Constructor =
  Constructor(name, args.toList, tArgs.toList)


extension (ty: VTerm)
  def unary_+ = (Binding(ty)(gn"arg"), Variance.COVARIANT)
  def unary_- = (Binding(ty)(gn"arg"), Variance.CONTRAVARIANT)
