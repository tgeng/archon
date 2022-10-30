package com.github.tgeng.archon.core.ir

import com.github.tgeng.archon.common.*
import com.github.tgeng.archon.core.common.*
import com.github.tgeng.archon.core.ir.PreDeclaration.{PreDefinition, PreEffect}
import Reducible.reduce
import SourceInfo.*

type PreTContext = List[(Binding[CTerm], Variance)]
type PreContext = List[Binding[CTerm]]

enum PreDeclaration:
  case PreData
    (val qn: QualifiedName)
    (
      val tParamTys: PreTContext,
      // This could be a eqDecidable function type that ends with `F Type` for indexed families. In this
      // case, during elaboration, all constructors are weakened by the number of args in the
      // declared function type. That is, indexed families are converted to parameterized inductive
      // types with equality types representing the constraints.
      val ty: CTerm,
      val constructors: List[PreConstructor]
    )
  case PreRecord
    (val qn: QualifiedName)
    (
      val tParamTys: PreTContext,
      // Unlike data, for record, this `ty` is expected to be a simple computation type.
      val ty: CTerm,
      val fields: List[PreField]
    )
  case PreDefinition
    (val qn: QualifiedName)
    (
      val paramTys: PreContext,
      val ty: CTerm,
      val clauses: List[PreClause]
    )
  case PreEffect
    (val qn: QualifiedName)
    (
      val tParamTys: PreContext,
      val operators: List[PreOperator]
    )

  def qn: QualifiedName

import PreDeclaration.*

case class PreConstructor(name: Name, ty: CTerm)

type PreField = Field // There is no difference for field

case class PreClause
  (
    boundNames: List[Ref[Name]],
    lhs: List[CoPattern],
    rhs: Option[CTerm] // `None` for absurd pattern
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
            QualifiedNameVisitor.visitPreTContext(data.tParamTys),
            data.ty.visitWith(QualifiedNameVisitor)
          )
        case record: PreRecord =>
          QualifiedNameVisitor.combine(
            QualifiedNameVisitor.visitPreTContext(record.tParamTys),
            record.ty.visitWith(QualifiedNameVisitor)
          )
        case definition: PreDefinition =>
          definition.ty.visitWith(QualifiedNameVisitor)
        case effect: PreEffect =>
          QualifiedNameVisitor.visitPreContext(effect.tParamTys)
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
            definition.clauses.flatMap { clause =>
              clause.lhs.map(QualifiedNameVisitor.visitCoPattern(_)) ++
                clause.rhs.map(QualifiedNameVisitor.visitCTerm(_))
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
            (bodyRefQn(decl.qn) -- qns).toSeq.sorted.map(qn => (SIGNATURE, declByQn(qn)))
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
