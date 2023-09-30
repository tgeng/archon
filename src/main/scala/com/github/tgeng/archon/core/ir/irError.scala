package com.github.tgeng.archon.core.ir

import com.github.tgeng.archon.common.*
import com.github.tgeng.archon.core.common.*
import com.github.tgeng.archon.core.ir.*
import com.github.tgeng.archon.parser.mixfix.PrecedenceGraphBuilder.Precedence
import com.github.tgeng.archon.core.ir.UnificationResult

// TODO[P0]: clean up unused cases
enum IrError extends HasException:
  case Unknown
  case EffectfulCTermAsType(ty: CTerm) // type of `ty` is some `CType` such that `cty.effects != Total`
  case ExpectDataType(ty: VTerm, qn: Option[QualifiedName] = None)
  case ExpectEqualityType(ty: VTerm)
  case ExpectFType(cTy: CTerm)
  case ExpectFunction(c: CTerm)
  case ExpectRecord(c: CTerm)
  case ExpectUType(vTy: VTerm)
  case ExpectVType(vTy: VTerm)
  case ExpectCType(cTy: CTerm)
  case NotDataTypeType(tm: CTerm)
  case NotCTypeError(tm: CTerm)
  case NotTypeError(tm: VTerm)
  case ReductionStuck(stuckTerm: CTerm)
  case TelescopeLengthMismatch(tms: Seq[VTerm], tys: Telescope)
  case UninitializedCell(stuckTerm: CTerm)
  case HandlerOperationsMismatch(handler: CTerm.Handler, expected: Set[QualifiedName], actual: Set[QualifiedName])
  case NotVSubsumption
    (
      sub: VTerm,
      sup: VTerm,
      ty: Option[VTerm],
    )
  case NotCSubsumption
    (
      sub: CTerm,
      sup: CTerm,
      ty: Option[CTerm],
    )
  case NotLevelSubsumption(sub: VTerm, sup: VTerm)
  case NotLevelConvertible(sub: VTerm, sup: VTerm)
  case LevelTooBig(level: VTerm)
  case NotEqDecidabilitySubsumption
    (
      sub: VTerm,
      sup: VTerm,
    )
  case NotUsageSubsumption(sub: VTerm, sup: VTerm)
  case NotUsageConvertible(sub: VTerm, sup: VTerm)
  case NotContinuationUsageSubsumption(sub: Option[Usage], sup: Option[Usage])
  case NotEffectSubsumption(sub: VTerm, sup: VTerm)
  case NotEffectConvertible(sub: VTerm, sup: VTerm)
  case IllegalVarianceInData
    (
      qn: QualifiedName,
      illegallyUsedBindingIndices: collection.Seq[Nat],
    )
  case IllegalVarianceInRecord
    (
      qn: QualifiedName,
      illegallyUsedBindingIndices: collection.Seq[Nat],
    )
  case NotEqDecidableType(ty: VTerm)
  case NormalizationError(ctm: CTerm)
  case CollapsingEffectfulTerm(ctm: CTerm)
  case NotCollapsable(ctm: CTerm)
  case MissingDeclaration(qn: QualifiedName)
  case MissingDefinition(qn: QualifiedName)
  case MissingConstructor(name: Name, qn: QualifiedName)
  case MissingField(name: Name, qn: QualifiedName)
  case MissingOperation(name: Name, qn: QualifiedName)
  case LeakedReferenceToEffectfulComputationResult(effectfulTerm: CTerm)
  case LeakedReferenceToHeapVariable(leakyTerm: CTerm)
  case NotEqDecidableDueToConstructor(qn: QualifiedName, conName: Name)
  case UnexpectedAbsurdPattern(p: Pattern)
  case UnexpectedCProjection(q: CoPattern)
  case UnexpectedCPattern(q: CoPattern)
  case MissingUserCoPattern(clause: PreClause)
  case UnexpectedUserCoPattern(clause: PreClause, q: CoPattern)
  case MissingFieldsInCoPattern(clause: PreClause)
  case IncompleteClauses(qn: QualifiedName)
  case UnexpectedImpossible(clause: PreClause)
  case UnsolvedElaboration(clause: PreClause)
  case UnificationFailure(uRes: UnificationResult)
  case NonEmptyType(ty: VTerm, source: PreClause)
  case MissingConstructorCase(dataQn: QualifiedName, conName: Name)
  case MissingDefaultTypeCase()
  case InsufficientResourceForSplit(x: VTerm.Var, binding: Binding[VTerm])
  case CyclicDeclarations(cycle: Seq[(DeclarationPart, PreDeclaration)])
  case EffectTermTooComplex(term: VTerm)
  case ExpectUnrestrictedTypeParameterBinding(binding: Binding[VTerm])
  case UnsatifisfiedUsageRequirements(unsolvedConstraints: Set[Constraint])
  case UnmatchedPattern(p: Pattern, ty: VTerm, unsolvedConstraints: Set[Constraint])
  case MetaVariableAlreadySolved(meta: CTerm.Meta, t: CTerm, s: MetaVariable.Solved)
  case MetaVariableCycle(meta: CTerm.Meta, t: CTerm)
  case UnmatchedDataIndex(con: VTerm.Con, dataType: VTerm.DataType)
  case NotVConvertible(sub: VTerm, sup: VTerm, ty: Option[VTerm])
  case NotCConvertible(sub: CTerm, sup: CTerm, ty: Option[CTerm])
  case NotVSubtype(sub: VTerm, sup: VTerm)
  case NotCSubtype(sub: CTerm, sup: CTerm)
  case CannotFindCTypeUnion(a: CTerm, b: CTerm)
  case CannotFindVTypeUnion(a: VTerm, b: VTerm)
  case ExpectParameterDisposer(h: CTerm.Handler)
  case ExpectParameterReplicator(h: CTerm.Handler)
