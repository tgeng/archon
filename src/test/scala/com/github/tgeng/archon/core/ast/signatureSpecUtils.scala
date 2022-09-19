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

  def fail(message: String, cause: Throwable): Nothing

class SignatureSpec extends AnyFreeSpec:
  given TypingContext = new TypingContext(0, false) {}

  given TestContext = new TestContext:
    override def testName: String = SignatureSpec.this.getClass.getSimpleName.!!

    override def fail(message: String) = SignatureSpec.this.fail(message)

    override def fail(message: String, cause: Throwable) =
      SignatureSpec.this.fail(message, cause)

def debug[T](block: TypingContext ?=> T)(using ctx: TypingContext): T =
  ctx.enableDebugging = true
  try {
    block
  } finally {
    ctx.enableDebugging = false
  }

extension
  (using Γ: Context)
  (using TestSignature)
  (using TypingContext)
  (using TestContext)
  (tm: AstTerm)
  infix def hasType(ty: AstTerm): Unit =
    given NameContext = Γ

    val cTm = astToIr(tm).asRight
    val cTy = astToIr(ty).asRight
    assertRight(checkType(cTm, cTy))

  infix def doesNotHaveType(ty: AstTerm): Unit =
    given NameContext = Γ

    val cTm = astToIr(tm).asRight
    val cTy = astToIr(ty).asRight
    assertLeft(checkType(cTm, cTy))

  infix def ⪯(tm2: AstTerm): Unit =
    given NameContext = Γ

    val cTm = astToIr(tm).asRight
    val cTm2 = astToIr(tm2).asRight
    val cTy = assertRight(inferType(cTm2))
    assertRight(
      checkSubsumption(cTm, cTm2, Some(cTy))(using
        CheckSubsumptionMode.SUBSUMPTION
      )
    )

  infix def ⋠(tm2: AstTerm): Unit =
    given NameContext = Γ

    val cTm = astToIr(tm).asRight
    val cTm2 = astToIr(tm2).asRight
    val cTy = assertRight(inferType(cTm2))
    assertLeft(
      checkSubsumption(cTm, cTm2, Some(cTy))(using
        CheckSubsumptionMode.SUBSUMPTION
      )
    )

  infix def ≡(tm2: AstTerm): Unit =
    given NameContext = Γ

    val cTm = astToIr(tm).asRight
    val cTm2 = astToIr(tm2).asRight
    val cTy = assertRight(inferType(cTm2))
    assertRight(
      checkSubsumption(cTm, cTm2, Some(cTy))(using
        CheckSubsumptionMode.CONVERSION
      )
    )

  infix def ≢(tm2: AstTerm): Unit =
    given NameContext = Γ

    val cTm = astToIr(tm).asRight
    val cTm2 = astToIr(tm2).asRight
    val cTy = assertRight(inferType(cTm2))
    assertLeft(
      checkSubsumption(cTm, cTm2, Some(cTy))(using
        CheckSubsumptionMode.CONVERSION
      )
    )

def assertRight[L, R]
  (action: => Either[L, R])
  (using TypingContext)
  (using ctx: TestContext)
  : R =
  val r: Either[L, R] =
    try {
      action
    } catch {
      case _: Any =>
        debug {
          action
          ctx.fail("should throw above")
        }
    }
  r match
    case Right(r) => r
    case Left(l) =>
      debug {
        action
        if l.isInstanceOf[HasException] then
          ctx.fail(l.toString, l.asInstanceOf[HasException].exception)
        else ctx.fail(l.toString)
      }

def assertLeft[L, R]
  (action: => Either[L, R])
  (using TypingContext)
  (using ctx: TestContext)
  : L =
  val r: Either[L, R] =
    try {
      action
    } catch {
      case _: Any =>
        debug {
          action
          ctx.fail("should throw above")
        }
    }
  r match
    case Left(l) => l
    case Right(_) =>
      debug {
        action
        ctx.fail("Expect to fail, but succeeded.")
      }

class TestSignature
  (
    private val allData: mutable.Map[QualifiedName, Data] = mutable.Map(),
    private val allConstructors: mutable.Map[QualifiedName, IndexedSeq[
      Constructor
    ]] = mutable.Map(),
    private val allRecords: mutable.Map[QualifiedName, Record] = mutable.Map(),
    private val allFields: mutable.Map[QualifiedName, IndexedSeq[Field]] =
      mutable.Map(),
    private val allDefinitions: mutable.Map[QualifiedName, Definition] =
      mutable.Map(),
    private val allClauses: mutable.Map[QualifiedName, IndexedSeq[Clause]] =
      mutable.Map(),
    private val allEffects: mutable.Map[QualifiedName, Effect] = mutable.Map(),
    private val allOperators: mutable.Map[QualifiedName, IndexedSeq[Operator]] =
      mutable.Map()
  )
  extends BuiltinSignature:

  override def toString: String =
    s"""
       |data:    ${allData.keys}
       |records: ${allRecords.keys}
       |defs:    ${allDefinitions.keys}
       |effects: ${allEffects.keys}
       |""".stripMargin

  private val qnByName = mutable.Map[Name, QualifiedName]()

  private def updateQnByName(qn: QualifiedName): Unit = qn match
    case QualifiedName.Root => throw IllegalArgumentException()
    case QualifiedName.Node(_, name) =>
      assert(!qnByName.contains(name), s"$qnByName already contains $name")
      qnByName(name) = qn

  Builtins.builtinData.values.foreach { case (data, constructors) =>
    updateQnByName(data.qn)
    constructors.foreach { constructor =>
      updateQnByName(data.qn / constructor.name)
    }
  }

  Builtins.builtinRecords.values.foreach { case (record, fields) =>
    updateQnByName(record.qn)
    fields.foreach { field =>
      updateQnByName(record.qn / field.name)
    }
  }

  Builtins.builtinDefinitions.keys.foreach(updateQnByName)
  Builtins.builtinEffects.values.foreach { case (effect, operators) =>
    updateQnByName(effect.qn)
    operators.foreach { operator =>
      updateQnByName(effect.qn / operator.name)
    }
  }

  allData.keys.foreach(updateQnByName)
  allConstructors.foreach((qn, constructors) =>
    constructors.foreach(c => updateQnByName(qn / c.name))
  )
  allRecords.keys.foreach(updateQnByName)
  allFields.foreach((qn, fields) =>
    fields.foreach(f => updateQnByName(qn / f.name))
  )
  allDefinitions.keys.foreach(updateQnByName)
  allEffects.keys.foreach(updateQnByName)
  allOperators.foreach((qn, operators) =>
    operators.foreach(o => updateQnByName(qn / o.name))
  )

  override def getUserDataOption(qn: QualifiedName) = allData.get(qn)

  override def getUserConstructorsOption(qn: QualifiedName) =
    allConstructors.get(qn)

  override def getUserRecordOption(qn: QualifiedName) = allRecords.get(qn)

  override def getUserFieldsOption(qn: QualifiedName) = allFields.get(qn)

  override def getUserDefinitionOption(qn: QualifiedName) =
    allDefinitions.get(qn)

  override def getUserClausesOption(qn: QualifiedName) = allClauses.get(qn)

  override def getCaseTreeOption(qn: QualifiedName) = ???

  override def getUserEffectOption(qn: QualifiedName) = allEffects.get(qn)

  override def getUserOperatorsOption(qn: QualifiedName) = allOperators.get(qn)

  def resolve(name: Name): QualifiedName = resolveOption(name).get

  def resolveOption(name: Name): Option[QualifiedName] = name match
    case Name.Normal(n) if n.stripPrefix("TYPE").toIntOption.nonEmpty =>
      Some(Builtins.BuiltinType / n)
    case Name.Normal(n) if n.stripPrefix("CTYPE").toIntOption.nonEmpty =>
      Some(Builtins.BuiltinType / n)
    case _ => qnByName.get(name)

  def copy: TestSignature = TestSignature(
    allData,
    allConstructors,
    allRecords,
    allFields,
    allDefinitions,
    allClauses,
    allEffects,
    allOperators
  )

  def addDeclarations
    (astDeclarations: List[AstDeclaration])
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
      case AstDefinition(name, _, _, _) => updateQnByName(testModuleQn / name)
      case AstEffect(name, _, operators) =>
        val effectQn = testModuleQn / name
        updateQnByName(effectQn)
        operators.foreach { operator =>
          updateQnByName(effectQn / operator.name)
        }
    }
    val declarations = transpose(
      astDeclarations.map { decl =>
        astToIr(testModuleQn, decl)
      }
    ).asRight

    sortPreDeclarations(declarations) match
      case Left(cycle) => tCtx.fail(s"detected cycles in declarations: $cycle")
      case Right(sortedDeclarations) =>
        sortedDeclarations.foreach {
          case (SIGNATURE, preData: PreData) =>
            val data = assertRight(elaborateSignature(preData))
            assertRight(checkData(data))
            allData(data.qn) = data
          case (BODY, preData: PreData) =>
            val constructors = assertRight(elaborateBody(preData))
            assertRight(checkDataConstructors(preData.qn, constructors))
            allConstructors(preData.qn) = constructors.toIndexedSeq
          case (SIGNATURE, preRecord: PreRecord) =>
            val record = assertRight(elaborateSignature(preRecord))
            assertRight(checkRecord(record))
            allRecords(record.qn) = record
          case (BODY, preRecord: PreRecord) =>
            val fields = assertRight(elaborateBody(preRecord))
            assertRight(checkRecordFields(preRecord.qn, fields))
            allFields(preRecord.qn) = fields.toIndexedSeq
          case (SIGNATURE, preDefinition: PreDefinition) =>
            val definition = assertRight(elaborateSignature(preDefinition))
            assertRight(checkDef(definition))
            allDefinitions(definition.qn) = definition
          case (BODY, preDefinition: PreDefinition) =>
            val clauses = assertRight(elaborateBody(preDefinition))
            assertRight(checkClauses(preDefinition.qn, clauses))
            allClauses(preDefinition.qn) = clauses.toIndexedSeq
          case (SIGNATURE, preEffect: PreEffect) =>
            val effect = assertRight(elaborateSignature(preEffect))
            assertRight(checkEffect(effect))
            allEffects(effect.qn) = effect
          case (BODY, preEffect: PreEffect) =>
            val operators = assertRight(elaborateBody(preEffect))
            assertRight(checkOperators(preEffect.qn, operators))
            allOperators(preEffect.qn) = operators.toIndexedSeq
        }

def scope
  (b: (MutableContext, TestSignature) ?=> Unit)
  (using Γ: MutableContext)
  (using Σ: TestSignature) =
  val newContext: MutableContext = mutable.ArrayBuffer(Γ.toArray: _*)
  val newSignature: TestSignature = Σ.copy
  b(using newContext, newSignature)

given Conversion[Context, NameContext] = NameContext.fromContext

extension(binding: Binding[AstTerm])
  def unary_+
    (using Γ: MutableContext)
    (using TestSignature)
    (using TypingContext) =
    given NameContext = Γ

    val ty = astToIr(binding.ty).asRight
    val vTy = reduceVType(ty).asRight
    Γ.addOne(Binding(vTy)(binding.name))

extension(declarations: List[AstDeclaration])
  def unary_+(using Σ: TestSignature)(using TypingContext)(using TestContext) =
    Σ.addDeclarations(declarations)
