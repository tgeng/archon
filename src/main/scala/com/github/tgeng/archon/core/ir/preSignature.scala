package com.github.tgeng.archon.core.ir

import com.github.tgeng.archon.core.common.*

type PreTTelescope = List[(Binding[CTerm], Variance)]
type PreTelescope = List[Binding[CTerm]]

enum PreDeclaration:
  case PreData(val qn: QualifiedName)
    (
      val tParamTys: PreTTelescope,
      val ty: CTerm,
      val isPure: Boolean,
      val constructors: List[PreConstructor]
    )
  case PreRecord(val qn: QualifiedName)
    (
      val tParamTys: PreTTelescope,
      val ty: CTerm,
      val field: List[PreField]
    )
  case PreDefinition(val qn: QualifiedName)
    (
      val ty: CTerm,
      val clauses: List[PreClause]
    )
  case PreEffect(val qn: QualifiedName)
    (
      val tParamTys: PreTelescope,
      val operators: List[PreOperator]
    )

case class PreConstructor(
  name: Name,
  ty: CTerm,
)

type PreField = Field // There is no difference for field

case class PreClause(
  bindings: PreTelescope, // TODO: remove `binding` after elaboration is implemented
  lhs: List[CoPattern],
  rhs: Some[CTerm], // `None` for absurd pattern
  ty: CTerm, // TODO: remove `ty` after elaboration is implemented
)

case class PreOperator(
  name: Name,
  ty: CTerm,
)