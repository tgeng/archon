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
      // This could be a function type that ends with `F Type` for indexed families. In this
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
