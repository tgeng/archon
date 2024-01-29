package com.github.tgeng.archon.core.ir

import com.github.tgeng.archon.common.*
import com.github.tgeng.archon.core.common.*
import com.github.tgeng.archon.core.ir.PreDeclaration.{PreDefinition, PreEffect}

type PreTTelescope = List[(Binding[CTerm], Variance)]
type PreTelescope = List[Binding[CTerm]]

enum PreDeclaration:
  case PreData
    (qn: QualifiedName)
    (
      val tParamTys: PreTTelescope,
      // This could be a function type that ends with `F Type` for indexed families. In this
      // case, during elaboration, all constructors are weakened by the number of args in the
      // declared function type. That is, indexed families are converted to parameterized inductive
      // types with equality types representing the constraints.
      val ty: CTerm,
      val constructors: List[PreConstructor],
    )
  case PreRecord
    (qn: QualifiedName)
    (
      val tParamTys: PreTTelescope,
      // Unlike data, for record, this `ty` is expected to be a simple computation type.
      val ty: CTerm,
      val selfUsage: CTerm,
      // There is no difference for field
      val fields: List[Field],
      val selfName: Name = n"self",
    )
  case PreDefinition
    (qn: QualifiedName)
    (
      val paramTys: PreTelescope,
      val ty: CTerm,
      val clauses: List[PreClause],
    )
  case PreEffect
    (qn: QualifiedName)
    (
      val tParamTys: PreTelescope,
      val operations: List[PreOperation],
      val continuationUsage: CTerm,
      val handlerType: CTerm,
    )

  def qn: QualifiedName

import com.github.tgeng.archon.core.ir.PreDeclaration.*

case class PreConstructor(name: Name, ty: CTerm)

case class PreClause
  (
    boundNames: List[Ref[Name]],
    lhs: List[CoPattern],
    rhs: Option[CTerm], // `None` for absurd pattern
  )

case class PreOperation(name: Name, ty: CTerm)
