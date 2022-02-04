package io.github.tgeng.archon.bir

import io.github.tgeng.archon.common.QualifiedName

enum Declaration {
  case Data(val qn: QualifiedName)(val paramTys: Telescope, val ty: VTerm, val cons: Seq[Constructor])
  case Record(val qn: QualifiedName)(val paramTys: Telescope, val ty: VTerm, val fields: Seq[Field])
  case Definition(val qn: QualifiedName)(val ty: VTerm, val clauses: Seq[CheckedClause], val ct: CTerm)

  def qn: QualifiedName
}

import Declaration._

case class Constructor(name: String, argTys: List[Binding[VTerm]], idTys: List[Binding[VTerm]])

case class Field(name: String, ty: VTerm)

case class CheckedClause(bindings: Telescope, lhs: List[Pattern], rhs: CTerm, ty: VTerm)

enum UncheckedRhs {
  case UTerm(t: CTerm)
  case UImpossible
}

import UncheckedRhs._