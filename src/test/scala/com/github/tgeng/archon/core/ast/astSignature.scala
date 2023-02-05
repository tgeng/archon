package com.github.tgeng.archon.core.ast

import com.github.tgeng.archon.common.*
import com.github.tgeng.archon.core.common.*
import com.github.tgeng.archon.core.ir.*

type AstTContext = List[(Binding[AstTerm], Variance)]
type AstTelescope = List[Binding[AstTerm]]

enum AstDeclaration:
  case AstData
    (
      override val name: Name,
      val tParamTys: AstTContext,
      val ty: AstTerm,
      val isPure: Boolean,
      val constructors: List[AstConstructor]
    )
  case AstRecord
    (
      override val name: Name,
      val tParamTys: AstTContext,
      val ty: AstTerm,
      val fields: List[AstField]
    )
  case AstDefinition
    (
      override val name: Name,
      val paramTys: AstTelescope,
      val ty: AstTerm,
      val clauses: List[AstClause]
    )
  case AstEffect
    (
      override val name: Name,
      val tParamTys: AstTelescope,
      val operations: List[AstOperation]
    )

  def name: Name

case class AstConstructor(name: Name, ty: AstTerm)

case class AstField(name: Name, ty: AstTerm)

case class AstClause
  (
    bindings: AstTelescope, // TODO[P3]: remove `binding` after elaboration is implemented
    lhs: List[AstCoPattern],
    rhs: Option[AstTerm], // `None` for absurd pattern
    ty: AstTerm // TODO[P3]: remove `ty` after elaboration is implemented
  )

case class AstOperation(name: Name, ty: AstTerm)
