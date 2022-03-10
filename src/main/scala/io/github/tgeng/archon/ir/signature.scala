package io.github.tgeng.archon.ir

import io.github.tgeng.archon.common.*

enum Declaration:
  case Data(val qn: QualifiedName)(val tParamTys: Telescope, /* binding + paramTys */ val ty: VTerm, val cons: Vector[Constructor])
  case Effect(val qn: QualifiedName)(val tParamTys: Telescope, operations: Vector[Operator])
  case Record(val qn: QualifiedName)(val tParamTys: Telescope, /* binding + tParamTys */ val ty: CTerm, val fields: Vector[Field])
  case Definition(val qn: QualifiedName)(val ty: CTerm, val clauses: Vector[CheckedClause], val caseTree: CaseTree)

  def qn: QualifiedName

import Declaration.*

case class Constructor(name: Name, /* binding + tParamTys */ paramTys: Telescope, /* binding + tParamTys + paramTys */  idTys: Telescope)
case class Operator(name: Name, paramTys: Telescope, /* binding + paramTys */ resultTy: VTerm)
case class Field(name: Name, /* binding + tParamTys + 1 for self */ ty: CTerm)
case class CheckedClause(bindings: Telescope, lhs: List[Pattern], /* binding + bindings */ rhs: CTerm, /* binding + bindings */ ty: CTerm)

trait Signature:
  def getData(qn: QualifiedName): Data
  def getRecord(qn: QualifiedName): Record
  def getDef(qn: QualifiedName): Definition
  def getEffect(qn: QualifiedName): Effect