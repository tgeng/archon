package com.github.tgeng.archon.core.ir

import com.github.tgeng.archon.common.*
import com.github.tgeng.archon.core.common.*
import com.github.tgeng.archon.core.common.QualifiedName.Root
import com.github.tgeng.archon.core.ir.PreDeclaration.{PreDefinition, PreEffect}

type PreTTelescope = List[(Binding[CTerm], Variance)]
type PreDTelescope = List[(Binding[CTerm], EscapeStatus)]
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
      interfaceScope: QualifiedName = Root,
      implementationScope: QualifiedName = Root,
    )
  case PreCorecord
    (
      qn: QualifiedName,
      tParamTys: PreTTelescope,
      // Unlike data, for corecord, this `ty` is expected to be a simple computation type in
      // indicating the computation type of this corecord type.
      // Note that this type is not the type of `self`. It's the type of the corecord type! Hence this
      // cannot be simplified to a `Binding[CTerm` as in `PreData`.
      ty: CTerm,
      // There is no difference for cofield
      cofields: List[Cofield],
      selfName: Name = n"self",
      interfaceScope: QualifiedName = Root,
      implementationScope: QualifiedName = Root,
    )
  case PreDefinition
    (
      qn: QualifiedName,
      paramTys: PreDTelescope,
      ty: CTerm,
      clauses: List[PreClause],
      interfaceScope: QualifiedName = Root,
      implementationScope: QualifiedName = Root,
    )
  case PreEffect
    (
      qn: QualifiedName,
      tParamTys: PreTelescope,
      operations: List[PreOperation],
      continuationUsage: CTerm,
      interfaceScope: QualifiedName = Root,
      implementationScope: QualifiedName = Root,
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
