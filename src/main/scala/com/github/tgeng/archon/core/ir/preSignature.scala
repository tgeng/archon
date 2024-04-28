package com.github.tgeng.archon.core.ir

import com.github.tgeng.archon.common.*
import com.github.tgeng.archon.core.common.*
import com.github.tgeng.archon.core.ir.PreDeclaration.{PreDefinition, PreEffect}

type PreTTelescope = List[(Binding[CTerm], Variance)]
type PreTelescope = List[Binding[CTerm]]

enum PreDeclaration:
  case PreData
    (
      qn: QualifiedName,
      tParamTys: PreTTelescope,
      // This could be a function type that ends with `F Type` for indexed families. In this
      // case, during elaboration, all constructors are weakened by the number of args in the
      // declared function type. That is, indexed families are converted to parameterized inductive
      // types with equality types representing the constraints.
      ty: CTerm,
      constructors: List[PreConstructor],
    )
  case PreRecord
    (
      qn: QualifiedName,
      tParamTys: PreTTelescope,
      // There is no difference for field
      fields: List[Field],
      selfName: Name = n"self",
    )
  case PreDefinition(qn: QualifiedName, paramTys: PreTelescope, ty: CTerm, clauses: List[PreClause])
  case PreEffect
    (
      qn: QualifiedName,
      tParamTys: PreTelescope,
      operations: List[PreOperation],
      continuationUsage: CTerm,
      handlerType: CTerm,
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
