package com.github.tgeng.archon.core.ast

import com.github.tgeng.archon.common.*
import com.github.tgeng.archon.core.common.*
import com.github.tgeng.archon.core.ir.*
import com.github.tgeng.archon.core.ir.Declaration.*
import org.scalatest.freespec.AnyFreeSpec

import scala.annotation.targetName
import scala.collection.mutable

type MutableContext = mutable.ArrayBuffer[Binding[VTerm]]

trait TestContext:
  def testName: String

  def fail(message: String): Nothing

class SignatureSpec extends AnyFreeSpec :
  given TypingContext = new TypingContext {}

  given TestContext = new TestContext :
    override def testName: String = SignatureSpec.this.getClass.getSimpleName.!!

    override def fail(message: String) = SignatureSpec.this.fail(message)

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

  extension (tm: AstTerm)
    infix def hasType(ty: AstTerm)(using Context)(using TestSignature)(using TypingContext) =
      val cTm = astToIr(tm).asRight
      val cTy = astToIr(ty).asRight
      checkType(cTm, cTy) match
        case Right(_) =>
        case Left(e) => fail(e.toString, e.exception)

    infix def doesNotHaveType(ty: AstTerm)
      (using Context)
      (using TestSignature)
      (using TypingContext) =
      val cTm = astToIr(tm).asRight
      val cTy = astToIr(ty).asRight
      checkType(cTm, cTy) match
        case Right(_) => fail(s"expect $tm to not have type $ty")
        case Left(e) =>

    infix def ⪯(tm2: AstTerm)(using Context)(using TestSignature)(using TypingContext) =
      val cTm = astToIr(tm).asRight
      val cTm2 = astToIr(tm2).asRight
      checkSubsumption(cTm, cTm2, None)(using CheckSubsumptionMode.SUBSUMPTION) match
        case Right(_) =>
        case Left(e) => fail(e.toString, e.exception)

    infix def ⋠(tm2: AstTerm)(using Context)(using TestSignature)(using TypingContext) =
      val cTm = astToIr(tm).asRight
      val cTm2 = astToIr(tm2).asRight
      checkSubsumption(cTm, cTm2, None)(using CheckSubsumptionMode.SUBSUMPTION) match
        case Right(_) => fail(s"expect $tm ⋠ $tm2")
        case Left(e) =>

    infix def ≡(tm2: AstTerm)(using Context)(using TestSignature)(using TypingContext) =
      val cTm = astToIr(tm).asRight
      val cTm2 = astToIr(tm2).asRight
      checkSubsumption(cTm, cTm2, None)(using CheckSubsumptionMode.CONVERSION) match
        case Right(_) =>
        case Left(e) => fail(e.toString, e.exception)

    infix def ≢(tm2: AstTerm)(using Context)(using TestSignature)(using TypingContext) =
      val cTm = astToIr(tm).asRight
      val cTm2 = astToIr(tm2).asRight
      checkSubsumption(cTm, cTm2, None)(using CheckSubsumptionMode.CONVERSION) match
        case Right(_) => fail(s"expect $tm ≢ $tm2")
        case Left(e) =>


class TestSignature(
  private val allData: mutable.Map[QualifiedName, Data],
  private val allConstructors: mutable.Map[QualifiedName, IndexedSeq[Constructor]],
  private val allRecords: mutable.Map[QualifiedName, Record],
  private val allFields: mutable.Map[QualifiedName, IndexedSeq[Field]],
  private val allDefinitions: mutable.Map[QualifiedName, Definition],
  private val allClauses: mutable.Map[QualifiedName, IndexedSeq[Clause]],
  private val allEffects: mutable.Map[QualifiedName, Effect],
  private val allOperators: mutable.Map[QualifiedName, IndexedSeq[Operator]],
) extends BuiltinSignature :

  private val qnByName = mutable.Map[Name, QualifiedName]()

  private def updateQnByName(qn: QualifiedName) = qn match
    case QualifiedName.Root => throw IllegalArgumentException()
    case QualifiedName.Node(_, name) =>
      assert(!qnByName.contains(name), s"$qnByName already contains $name")
      qnByName(name) = qn

  Builtins.builtinData.values.foreach {
    case (data, constructors) =>
      updateQnByName(data.qn)
      constructors.foreach { constructor =>
        updateQnByName(data.qn / constructor.name)
      }
  }

  Builtins.builtinRecords.values.foreach {
    case (record, fields) =>
      updateQnByName(record.qn)
      fields.foreach { field =>
        updateQnByName(record.qn / field.name)
      }
  }

  Builtins.builtinDefinitions.keys.foreach(updateQnByName)
  Builtins.builtinEffects.keys.foreach(updateQnByName)

  allData.keys.foreach(updateQnByName)
  allConstructors.foreach((qn, constructors) => constructors.foreach(c => updateQnByName(qn / c.name)))
  allRecords.keys.foreach(updateQnByName)
  allFields.foreach((qn, fields) => fields.foreach(f => updateQnByName(qn / f.name)))
  allDefinitions.keys.foreach(updateQnByName)
  allEffects.keys.foreach(updateQnByName)

  override def getUserDataOption(qn: QualifiedName) = allData.get(qn)

  override def getUserConstructorsOption(qn: QualifiedName) = allConstructors.get(qn)

  override def getUserRecordOption(qn: QualifiedName) = allRecords.get(qn)

  override def getUserFieldsOption(qn: QualifiedName) = allFields.get(qn)

  override def getUserDefinitionOption(qn: QualifiedName) = allDefinitions.get(qn)

  override def getUserClausesOption(qn: QualifiedName) = allClauses.get(qn)

  override def getCaseTreeOption(qn: QualifiedName) = ???

  override def getUserEffectOption(qn: QualifiedName) = allEffects.get(qn)

  override def getUserOperatorsOption(qn: QualifiedName) = allOperators.get(qn)

  def resolve(name: Name): QualifiedName = qnByName(name)

  def resolveOption(name: Name): Option[QualifiedName] = qnByName.get(name)

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

  def addDeclarations(astDeclarations: List[AstDeclaration])
    (using TypingContext)
    (using tCtx: TestContext) =
    given TestSignature = this
    import AstDeclaration.*
    import QualifiedName.*
    import PreDeclaration.*
    import DeclarationPart.*
    val testModuleQn = Root / tCtx.testName
    astDeclarations.foreach {
      case AstData(name, _, _, _, constructors) =>
        val dataQn = testModuleQn / name
        updateQnByName(dataQn)
        constructors.foreach { constructor =>
          updateQnByName(dataQn / constructor.name)
        }
      case AstRecord(name, _, _, fields) =>
        val recordQn = testModuleQn / name
        updateQnByName(recordQn)
        fields.foreach { field =>
          updateQnByName(recordQn / field.name)
        }
      case AstDefinition(name, _, _) => updateQnByName(testModuleQn / name)
      case AstEffect(name, _, _) => updateQnByName(testModuleQn / name)
    }
    val declarations = transpose(
      astDeclarations.map { decl =>
        astToIr(testModuleQn, decl)
      }
    ) match
      case Left(e) => tCtx.fail(s"error during ast->pre conversion: $e")
      case Right(declarations) => declarations

    sortPreDeclarations(declarations) match
      case Left(cycle) => tCtx.fail(s"detected cycles in declarations: $cycle")
      case Right(sortedDeclarations) => transpose(
        sortedDeclarations.map {
          case (SIGNATURE, data: PreData) =>
            for data <- elaborateSignature(data)
                _ = allData(data.qn) = data
                r <- checkData(data.qn)
            yield r
          case (BODY, data: PreData) =>
            for constructors <- elaborateBody(data)
               _ = allConstructors(data.qn) = constructors.toIndexedSeq
               r <- checkDataConstructors(data.qn)
            yield r
          case (SIGNATURE, record: PreRecord) =>
            for record <- elaborateSignature(record)
                _ = allRecords(record.qn) = record
                r <- checkRecord(record.qn)
            yield r
          case (BODY, record: PreRecord) =>
            for fields <- elaborateBody(record)
                _ = allFields(record.qn) = fields.toIndexedSeq
                r <- checkRecordFields(record.qn)
            yield r
          case (SIGNATURE, definition: PreDefinition) =>
            for definition <- elaborateSignature(definition)
                _ = allDefinitions(definition.qn) = definition
                r <- checkRecord(definition.qn)
            yield r
          case (BODY, definition: PreDefinition) =>
            for clauses <- elaborateBody(definition)
                _ = allClauses(definition.qn) = clauses.toIndexedSeq
                r <- checkClauses(definition.qn)
            yield r
          case (SIGNATURE, effect: PreEffect) =>
            for effect <- elaborateSignature(effect)
                _ = allEffects(effect.qn) = effect
                r <- checkRecord(effect.qn)
            yield r
          case (BODY, effect: PreEffect) =>
            for operators <- elaborateBody(effect)
                _ = allOperators(effect.qn) = operators.toIndexedSeq
                r <- checkOperators(effect.qn)
            yield r
        }.toList
      )

extension (b: MutableContext ?=> TestSignature ?=> Unit)
  def unary_~(using Γ: MutableContext)
    (using Σ: TestSignature) = b(using mutable.ArrayBuffer(Γ.toArray: _*))(using Σ.copy)

given Conversion[Context, NameContext] = NameContext.fromContext

extension (binding: Binding[AstTerm])
  def unary_+(using Γ: MutableContext)(using Context)(using TestSignature)(using TypingContext) =
    val ty = astToIr(binding.ty).asRight
    val vTy = reduceVType(ty).asRight
    Γ.addOne(Binding(vTy)(binding.name))

extension (declarations: List[AstDeclaration])
  def unary_+(using Σ: TestSignature)(using TypingContext)(using TestContext) = Σ.addDeclarations(
    declarations
  )
