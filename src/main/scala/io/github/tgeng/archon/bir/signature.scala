package io.github.tgeng.archon.bir

import io.github.tgeng.archon.common.QualifiedName

enum Declaration:
  case Data(val qn: QualifiedName)(val paramTys: Telescope, val ty: VTerm, val cons: Vector[Constructor])
  case Effect(val qn: QualifiedName)(val paramTys: Telescope, operations: Vector[Operation])
  case Record(val qn: QualifiedName)(val paramTys: Telescope, val ty: CTerm, val fields: Vector[Field])
  case Definition(val qn: QualifiedName)(val ty: CTerm, val clauses: Vector[CheckedClause], val caseTree: CTerm)

  def qn: QualifiedName

import Declaration._

case class Constructor(name: String, argTys: List[Binding[VTerm]])
case class Operation(name: String, ty: CTerm)
case class Field(name: String, ty: CTerm)
case class CheckedClause(bindings: Telescope, lhs: List[Pattern], rhs: CTerm, ty: CTerm)

trait Signature:
  def getData(qn: QualifiedName): Data
  def getRecord(qn: QualifiedName): Record
  def getDef(qn: QualifiedName): Definition
  def getEffect(qn: QualifiedName): Effect