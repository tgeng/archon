package com.github.tgeng.archon.core.ir

import com.github.tgeng.archon.common.*
import com.github.tgeng.archon.core.common.*
import com.github.tgeng.archon.core.ir.PreDeclaration.{PreDefinition, PreEffect}
import Reducible.reduce
import SourceInfo.*

type PreTTelescope = List[(Binding[CTerm], Variance)]
type PreTelescope = List[Binding[CTerm]]

enum PreDeclaration:
  case PreData
    (val qn: QualifiedName)
    (
      val tParamTys: PreTTelescope,
      // This could be a eqDecidable function type that ends with `F Type` for indexed families. In this
      // case, during elaboration, all constructors are weakened by the number of args in the
      // declared function type. That is, indexed families are converted to parameterized inductive
      // types with equality types representing the constraints.
      val ty: CTerm,
      val isEqDecidable: Boolean,
      val constructors: List[PreConstructor]
    )
  case PreRecord
    (val qn: QualifiedName)
    (
      val tParamTys: PreTTelescope,
      // Unlike data, for record, this `ty` is expected to be a simple computation type.
      val ty: CTerm,
      val fields: List[PreField]
    )
  case PreDefinition
    (val qn: QualifiedName)
    (
      val paramTys: PreTelescope,
      val ty: CTerm,
      val clauses: List[PreClause]
    )
  case PreEffect
    (val qn: QualifiedName)
    (
      val tParamTys: PreTelescope,
      val operators: List[PreOperator]
    )

  def qn: QualifiedName

import PreDeclaration.*

case class PreConstructor(name: Name, ty: CTerm)

type PreField = Field // There is no difference for field

case class PreClause
  (
    bindings: PreTelescope, // TODO: remove `binding` after elaboration is implemented
    lhs: List[CoPattern],
    rhs: Option[CTerm], // `None` for absurd pattern
    ty: CTerm // TODO: remove `ty` after elaboration is implemented
  )

case class PreOperator(name: Name, ty: CTerm)

enum DeclarationPart:
  case SIGNATURE, BODY

import DeclarationPart.*

def sortPreDeclarations
  (declarations: Seq[PreDeclaration])
  (using Σ: Signature)
  : Either[ /* cycle */ Seq[
      (DeclarationPart, PreDeclaration)
    ], /* sorted */ Seq[
      (DeclarationPart, PreDeclaration)
    ]] =
  given Unit = ()

  val declByQn = declarations.associatedBy(_.qn)
  val sigRefQn = declarations
    .associatedBy(
      _.qn,
      {
        case data: PreData =>
          QualifiedNameVisitor.combine(
            QualifiedNameVisitor.visitPreTTelescope(data.tParamTys),
            data.ty.visitWith(QualifiedNameVisitor)
          )
        case record: PreRecord =>
          QualifiedNameVisitor.combine(
            QualifiedNameVisitor.visitPreTTelescope(record.tParamTys),
            record.ty.visitWith(QualifiedNameVisitor)
          )
        case definition: PreDefinition =>
          definition.ty.visitWith(QualifiedNameVisitor)
        case effect: PreEffect =>
          QualifiedNameVisitor.visitPreTelescope(effect.tParamTys)
      }
    )
    .view
    .mapValues(_ & declByQn.keySet)
    .toMap

  val bodyRefQn = declarations
    .associatedBy(
      _.qn,
      {
        case data: PreData =>
          QualifiedNameVisitor.combine(
            data.constructors.map { constructor =>
              constructor.ty.visitWith(QualifiedNameVisitor)
            }: _*
          ) + data.qn
        case record: PreRecord =>
          QualifiedNameVisitor.combine(
            record.fields.map { field =>
              field.ty.visitWith(QualifiedNameVisitor)
            }: _*
          ) + record.qn
        case definition: PreDefinition =>
          QualifiedNameVisitor.combine(
            definition.clauses.map { clause =>
              QualifiedNameVisitor.combine(
                clause.ty.visitWith(QualifiedNameVisitor)
              )
            }: _*
          ) + definition.qn
        case effect: PreEffect =>
          QualifiedNameVisitor.combine(
            effect.operators.map { operator =>
              operator.ty.visitWith(QualifiedNameVisitor)
            }: _*
          ) + effect.qn
      }
    )
    .view
    .mapValues(_ & declByQn.keySet)
    .toMap

  // rule:
  //   1. any reference of A needs the signature of A, regardless whether it's in the signature or body of some declarations
  //   2. any reference of A in a signature means the accompanied body needs full definition of A
  topologicalSort(
    declarations.flatMap(decl => Seq((SIGNATURE, decl), (BODY, decl)))
  ) {
    case (SIGNATURE, decl) =>
      sigRefQn.get(decl.qn) match
        case Some(qns) => qns.toSeq.sorted.map(qn => (SIGNATURE, declByQn(qn)))
        case None      => Seq()
    case (BODY, decl) =>
      sigRefQn.get(decl.qn) match
        case Some(qns) =>
          qns.toSeq.sorted.map(qn => (BODY, declByQn(qn))) ++
            (bodyRefQn(decl.qn) -- qns).toSeq.sorted.map(qn =>
              (SIGNATURE, declByQn(qn))
            )
        case None => Seq()
  }

private object QualifiedNameVisitor extends Visitor[Unit, Set[QualifiedName]]:

  override def combine
    (rs: Set[QualifiedName]*)
    (using ctx: Unit)
    (using
      Σ: Signature
    )
    : Set[QualifiedName] = rs.flatten.toSet

  override def visitQualifiedName
    (qn: QualifiedName)
    (using ctx: Unit)
    (using Σ: Signature)
    : Set[QualifiedName] = Set(qn)

end QualifiedNameVisitor

import Declaration.*
import CTerm.*
import VTerm.*
import IrError.*
import Variance.*

private given Γ0: Context = IndexedSeq()

def elaborateSignature
  (data: PreData)
  (using Signature)
  (using ctx: TypingContext)
  : Either[IrError, Data] =
  ctx.trace(s"elaborating data signature ${data.qn}") {
    def elaborateTy
      (ty: CTerm)
      (using Γ: Context)
      (using Signature)
      (using ctx: TypingContext)
      : Either[IrError, (TTelescope, ULevel)] =
      for
        ty <- reduceCType(ty)
        r <- ty match
          // Here and below we do not care the declared effect types because data type constructors
          // are always total. Declaring non-total signature is not necessary (nor desirable) but
          // acceptable.
          case F(Type(ul, _), _, _) => Right((Nil, ul))
          case F(t, _, _)           => Left(ExpectVType(t))
          case FunctionType(binding, bodyTy, _) =>
            elaborateTy(bodyTy)(using Γ :+ binding).map {
              case (telescope, ul) => ((binding, INVARIANT) :: telescope, ul)
            }
          case _ => Left(NotDataTypeType(ty))
      yield r

    for
      tParamTys <- elaborateTTelescope(data.tParamTys)
      elaboratedTy <- elaborateTy(data.ty)(using Γ0 ++ tParamTys.map(_._1))
    yield elaboratedTy match
      case (tIndices, ul) =>
        Data(data.qn)(tParamTys.size, tParamTys ++ tIndices, ul, ???, ???)
  }

def elaborateBody
  (preData: PreData)
  (using Σ: Signature)
  (using ctx: TypingContext)
  : Either[IrError, List[Constructor]] =
  ctx.trace(s"elaborating data body ${preData.qn}") {
    val data = Σ.getData(preData.qn)

    def elaborateTy
      (ty: CTerm)
      (using Γ: Context)
      (using Signature)
      (using ctx: TypingContext)
      : Either[IrError, (Telescope, /* args */ List[VTerm])] =
      for
        ty <- reduceCType(ty)
        r <- ty match
          // Here and below we do not care the declared effect types because data type constructors
          // are always total. Declaring non-total signature is not necessary (nor desirable) but
          // acceptable.
          case F(DataType(qn, args), _, _)
            if qn == data.qn && args.size == data.tParamTys.size =>
            Right((Nil, args))
          case F(t, _, _) => Left(ExpectDataType(t, Some(data.qn)))
          case FunctionType(binding, bodyTy, _) =>
            elaborateTy(bodyTy)(using Γ :+ binding).map {
              case (telescope, ul) => (binding :: telescope, ul)
            }
          case _ => Left(NotDataTypeType(ty))
      yield r

    // number of index arguments
    given Context = data.tParamTys.map(_._1).toIndexedSeq

    val indexCount = data.tParamTys.size - preData.tParamTys.size
    transpose(
      preData.constructors.map { constructor =>
        ctx.trace(s"elaborating constructor ${constructor.name}") {
          // weaken to accommodate data type indices
          val ty = constructor.ty.weaken(indexCount, 0)
          elaborateTy(ty).map { case (paramTys, args) =>
            Constructor(constructor.name, paramTys, args)
          }
        }
      }
    )
  }

def elaborateSignature
  (record: PreRecord)
  (using Signature)
  (using ctx: TypingContext)
  : Either[IrError, Record] =
  ctx.trace(s"elaborating record signature ${record.qn}") {
    for
      tParamTys <- elaborateTTelescope(record.tParamTys)
      ty <- reduceCType(record.ty)(using tParamTys.map(_._1).toIndexedSeq)
      r <- ty match
        case CType(ul, _, _) => Right(new Record(record.qn)(tParamTys, ul))
        case t               => Left(ExpectCType(t))
    yield r
  }

def elaborateBody
  (preRecord: PreRecord)
  (using Σ: Signature)
  (using ctx: TypingContext)
  : Either[IrError, List[Field]] =
  ctx.trace(s"elaborating record body ${preRecord.qn}") {
    val record = Σ.getRecord(preRecord.qn)

    given SourceInfo = SiEmpty

    given Context = record.tParamTys.map(_._1).toIndexedSeq :+
      Binding(U(RecordType(record.qn, vars(record.tParamTys.size - 1))), ???)(
        record.selfName
      )

    transpose(
      preRecord.fields.map { field =>
        ctx.trace(s"elaborating field ${field.name}") {
          for ty <- reduceCType(field.ty)
          yield Field(field.name, ty)
        }
      }
    )
  }

def elaborateSignature
  (definition: PreDefinition)
  (using Signature)
  (using ctx: TypingContext)
  : Either[IrError, Definition] =
  given SourceInfo = SiEmpty

  ctx.trace(s"elaborating def signature ${definition.qn}") {
    for
      paramTys <- elaborateTelescope(definition.paramTys)
      ty <- reduceCType(definition.ty)(using paramTys.toIndexedSeq)
    yield Definition(definition.qn)(
      paramTys.foldRight(ty) { (binding, bodyTy) =>
        FunctionType(binding, bodyTy)
      }
    )
  }

def elaborateBody
  (preDefinition: PreDefinition)
  (using Σ: Signature)
  (using ctx: TypingContext)
  : Either[IrError, List[Clause]] =
  ctx.trace(s"elaborating def body ${preDefinition.qn}") {
    for
      paramTys <- elaborateTelescope(preDefinition.paramTys)
      r <- {
        given Γ: Context = paramTys.toIndexedSeq

        transpose(
          preDefinition.clauses.zipWithIndex.flatMap { (clause, index) =>
            clause.rhs match
              case None => List()
              case Some(rhs) =>
                List(
                  ctx.trace(s"elaborating clause $index") {
                    for
                      bindings <- elaborateTelescope(clause.bindings)
                      ty <- reduceCType(clause.ty)(using Γ ++ bindings)
                    yield
                      val allBindings = paramTys ++ bindings
                      Clause(
                        allBindings,
                        CoPattern.pVars(
                          allBindings.size - 1,
                          bindings.size
                        ) ++ clause.lhs,
                        rhs,
                        ty
                      )
                  }
                )
          }
        )
      }
    yield r
  }

def elaborateSignature
  (effect: PreEffect)
  (using Signature)
  (using ctx: TypingContext)
  : Either[IrError, Effect] =
  ctx.trace(s"elaborating effect signature ${effect.qn}") {
    elaborateTelescope(effect.tParamTys).map(Effect(effect.qn)(_))
  }

def elaborateBody
  (preEffect: PreEffect)
  (using Σ: Signature)
  (using ctx: TypingContext)
  : Either[IrError, List[Operator]] =
  val effect = Σ.getEffect(preEffect.qn)

  given Context = effect.tParamTys.toIndexedSeq

  ctx.trace(s"elaborating effect body ${effect.qn}") {
    def elaborateTy
      (ty: CTerm)
      (using Γ: Context)
      (using Signature)
      (using ctx: TypingContext)
      : Either[IrError, (Telescope, /* operator return type */ VTerm)] =
      for
        ty <- reduceCType(ty)
        r <- ty match
          // Here and below we do not care the declared effect types because data type constructors
          // are always total. Declaring non-total signature is not necessary (nor desirable) but
          // acceptable.
          case F(ty, _, _) => Right((Nil, ty))
          case FunctionType(binding, bodyTy, _) =>
            elaborateTy(bodyTy)(using Γ :+ binding).map {
              case (telescope, ul) => (binding :: telescope, ul)
            }
          case _ => Left(ExpectFType(ty))
      yield r

    transpose(
      preEffect.operators.map { operator =>
        ctx.trace(s"elaborating operator ${operator.name}") {
          elaborateTy(operator.ty).map { case (paramTys, resultTy) =>
            Operator(operator.name, paramTys, resultTy, ???)
          }
        }
      }
    )
  }

private def elaborateTTelescope
  (tTelescope: PreTTelescope)
  (using Γ: Context)
  (using Signature)
  (using ctx: TypingContext)
  : Either[IrError, TTelescope] =
  elaborateTelescope(tTelescope.map(_._1)).map(_.zip(tTelescope.map(_._2)))

private def elaborateTelescope
  (telescope: PreTelescope)
  (using Γ: Context)
  (using Signature)
  (using ctx: TypingContext)
  : Either[IrError, Telescope] = telescope match
  case Nil => Right(Nil)
  case binding :: telescope =>
    ctx.trace("elaborating telescope") {
      for
        ty <- reduceVType(binding.ty)
        newBinding = Binding(ty, ???)(binding.name)
        telescope <- elaborateTelescope(telescope)(using Γ :+ newBinding)
      yield newBinding :: telescope
    }
