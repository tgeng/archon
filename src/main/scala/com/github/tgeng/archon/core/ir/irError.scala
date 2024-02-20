package com.github.tgeng.archon.core.ir

import com.github.tgeng.archon.core.common.*
import com.github.tgeng.archon.core.ir.*

enum IrError extends Exception:
  case CannotFindCTypeUnion(a: CTerm, b: CTerm)
  case CannotFindVTypeUnion(a: VTerm, b: VTerm)
  case CollapsingEffectfulTerm(ctm: CTerm)
  case CollapsingU0Term(ctm: CTerm)
  case CyclicDeclarations(cycle: Seq[(DeclarationPart, PreDeclaration)])
  case EffectTermTooComplex(term: VTerm)
  // type of `ty` is some `CType` such that `cty.effects != Total`
  case EffectfulCTermAsType(ty: CTerm)
  case ExpectReturnAValue(cTy: CTerm)
  case ExpectCType(cTy: CTerm)
  case ExpectDataType(ty: VTerm, qn: Option[QualifiedName] = None)
  case ExpectFType(cTy: CTerm)
  case ExpectFunction(c: CTerm)
  case ExpectParameterDisposer(h: CTerm.Handler)
  case ExpectParameterReplicator(h: CTerm.Handler)
  case ExpectRecord(c: CTerm)
  case ExpectU1Effect(operationQn: QualifiedName)
  case ExpectUType(vTy: VTerm)
  case ExpectUnrestrictedTypeParameterBinding(binding: Binding[VTerm])
  case ExpectVType(vTy: VTerm)
  case HandlerOperationsMismatch
    (handler: CTerm.Handler, expected: Set[QualifiedName], actual: Set[QualifiedName])
  case IllegalVarianceInData(qn: QualifiedName, violatingVars: collection.Seq[VTerm.Var])
  case IllegalVarianceInRecord(qn: QualifiedName, violatingVars: collection.Seq[VTerm.Var])
  case IncompleteClauses(qn: QualifiedName)
  case InsufficientResourceForSplit(x: VTerm.Var, binding: Binding[VTerm])
  case LeakedReferenceToEffectfulComputationResult(effectfulTerm: CTerm)
  case MissingConstructor(name: Name, qn: QualifiedName)
  case MissingConstructorCase(dataQn: QualifiedName, conName: Name)
  case MissingDeclaration(qn: QualifiedName)
  case MissingDefaultTypeCase()
  case MissingDefinition(qn: QualifiedName)
  case MissingField(name: Name, qn: QualifiedName)
  case MissingFieldsInCoPattern(clause: PreClause)
  case MissingOperation(name: Name, qn: QualifiedName)
  case MissingUserCoPattern(clause: PreClause)
  case NonEmptyType(ty: VTerm, source: PreClause)
  case NotCConvertible(sub: CTerm, sup: CTerm, ty: Option[CTerm])
  case NotCSubtype(sub: CTerm, sup: CTerm)
  case NotCTypeError(tm: CTerm)
  case NotCollapsable(ctm: CTerm)
  case NotDataTypeType(tm: CTerm)
  case NotEffectSubsumption(sub: VTerm, sup: VTerm)
  case NotEqDecidabilitySubsumption(sub: VTerm, sup: VTerm)
  case NotHandlerTypeSubsumption(sub: VTerm, sup: VTerm)
  case NotEqDecidableDueToConstructor
    (qn: QualifiedName, conName: Name, badBindings: Seq[Binding[VTerm]])
  case NotEqDecidableType(ty: VTerm)
  case NotLevelSubsumption(sub: VTerm, sup: VTerm)
  case NotTypeError(tm: VTerm)
  case NotUsageSubsumption(sub: VTerm, sup: VTerm)
  case NotVConvertible(left: VTerm, right: VTerm, ty: Option[VTerm])
  case NotVSubtype(sub: VTerm, sup: VTerm)
  case TelescopeLengthMismatch(tms: Seq[VTerm], tys: Telescope)
  case UnexpectedAbsurdPattern(p: Pattern)
  case UnexpectedCPattern(q: CoPattern)
  case UnexpectedCProjection(q: CoPattern)
  case UnexpectedUserCoPattern(clause: PreClause, q: CoPattern)
  case UnificationFailure(uRes: UnificationResult)
  case UnmatchedDataIndex(con: VTerm.Con, dataType: VTerm.DataType)
  case UnmatchedPattern(p: Pattern, ty: VTerm, unsolvedConstraints: Set[Constraint])
  case UnsatisfiedUsageRequirements(unsolvedConstraints: Set[Constraint])
  case UnsolvedElaboration(clause: PreClause)
