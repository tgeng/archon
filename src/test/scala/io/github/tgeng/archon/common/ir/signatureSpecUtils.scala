package io.github.tgeng.archon.common.ir

import collection.mutable
import org.scalatest.freespec.AnyFreeSpec
import io.github.tgeng.archon.ir.*
import io.github.tgeng.archon.common.*
import Declaration.*

import scala.annotation.targetName

class SignatureSpec extends AnyFreeSpec :
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

class TestSignature(
  val allData: mutable.Map[QualifiedName, Data],
  val allConstructors: mutable.Map[QualifiedName, IndexedSeq[Constructor]],
  val allRecords: mutable.Map[QualifiedName, Record],
  val allFields: mutable.Map[QualifiedName, IndexedSeq[Field]],
  val allDefinitions: mutable.Map[QualifiedName, Definition],
  val allClauses: mutable.Map[QualifiedName, IndexedSeq[CheckedClause]],
  val allEffects: mutable.Map[QualifiedName, Effect],
  val allOperators: mutable.Map[QualifiedName, IndexedSeq[Operator]],
) extends Signature :
  override def getDataOption(qn: QualifiedName) = allData.get(qn)

  override def getConstructorsOption(qn: QualifiedName) = allConstructors.get(qn)

  override def getRecordOption(qn: QualifiedName) = allRecords.get(qn)

  override def getFieldsOption(qn: QualifiedName) = allFields.get(qn)

  override def getDefinitionOption(qn: QualifiedName) = allDefinitions.get(qn)

  override def getClausesOption(qn: QualifiedName) = allClauses.get(qn)

  override def getCaseTreeOption(qn: QualifiedName) = ???

  override def getEffectOption(qn: QualifiedName) = allEffects.get(qn)

  override def getOperatorsOption(qn: QualifiedName) = allOperators.get(qn)

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

extension (b: TestSignature ?=> Unit)
  def unary_!(using Σ: TestSignature): () => Unit = () => b(using Σ.copy)

extension (declaration: Declaration)
  def unary_+(using Σ: TestSignature): QualifiedName =
    declaration match
      case data: Data => Σ.allData(declaration.qn) = data
      case record: Record => Σ.allRecords(declaration.qn) = record
      case definition: Definition => Σ.allDefinitions(declaration.qn) = definition
      case effect: Effect => Σ.allEffects(declaration.qn) = effect
    declaration.qn

extension (qn: QualifiedName)
  @targetName("addConstructors")
  infix def +(constructor: Constructor)
    (using Σ: TestSignature): QualifiedName =
    Σ.allConstructors(qn) = Σ.allConstructors.getOrElseUpdate(qn, IndexedSeq()) :+ constructor
    qn

  @targetName("addFields")
  infix def +(field: Field)
    (using Σ: TestSignature): QualifiedName =
    Σ.allFields(qn) = Σ.allFields.getOrElseUpdate(qn, IndexedSeq()) :+ field
    qn

  @targetName("addClauses")
  infix def +(clause: CheckedClause)
    (using Σ: TestSignature): QualifiedName =
    Σ.allClauses(qn) = Σ.allClauses.getOrElseUpdate(qn, IndexedSeq()) :+ clause
    qn

  @targetName("addOperators")
  infix def +(operator: Operator)
    (using Σ: TestSignature): QualifiedName =
    Σ.allOperators(qn) = Σ.allOperators.getOrElseUpdate(qn, IndexedSeq()) :+ operator
    qn
