package com.github.tgeng.archon.core.ir

import com.github.tgeng.archon.common.Nat
import com.github.tgeng.archon.core.common.*
import com.github.tgeng.archon.core.ir.*

enum IrError(val Γ: Context, e: Throwable | Null = null) extends Exception(e):
  case CannotFindCTypeUnion(a: CTerm, b: CTerm)(using Γ: Context) extends IrError(Γ)
  case CannotFindVTypeUnion(a: VTerm, b: VTerm)(using Γ: Context) extends IrError(Γ)
  case CollapsingEffectfulTerm(ctm: CTerm)(using Γ: Context) extends IrError(Γ)
  case CollapsingU0Term(ctm: CTerm)(using Γ: Context) extends IrError(Γ)
  case CyclicDeclarations(cycle: Seq[(DeclarationPart, PreDeclaration)])
    extends IrError(Context.empty)
  case EffectTermTooComplex(term: VTerm)(using Γ: Context) extends IrError(Γ)
  // type of `ty` is some `CType` such that `cty.effects != Total`
  case EffectfulCTermAsType(ty: CTerm)(using Γ: Context) extends IrError(Γ)
  case ExpectReturnAValue(cTy: CTerm)(using Γ: Context) extends IrError(Γ)
  case ExpectCType(cTy: CTerm)(using Γ: Context) extends IrError(Γ)
  case ExpectDataType(ty: VTerm, qn: Option[QualifiedName] = None)(using Γ: Context)
    extends IrError(Γ)
  case ExpectFType(cTy: CTerm)(using Γ: Context) extends IrError(Γ)
  case ExpectFunction(c: CTerm)(using Γ: Context) extends IrError(Γ)
  case ExpectParameterDisposer(h: CTerm.Handler)(using Γ: Context) extends IrError(Γ)
  case ExpectParameterReplicator(h: CTerm.Handler)(using Γ: Context) extends IrError(Γ)
  case ExpectRecord(c: CTerm)(using Γ: Context) extends IrError(Γ)
  case ExpectU1Effect(operationQn: QualifiedName)(using Γ: Context) extends IrError(Γ)
  case ExpectUType(vTy: VTerm)(using Γ: Context) extends IrError(Γ)
  case ExpectUnrestrictedTypeParameterBinding(binding: Binding[VTerm])(using Γ: Context)
    extends IrError(Γ)
  case ExpectVType(vTy: VTerm)(using Γ: Context) extends IrError(Γ)
  case HandlerOperationsMismatch
    (handler: CTerm.Handler, expected: Set[QualifiedName], actual: Set[QualifiedName])
    (using Γ: Context) extends IrError(Γ)
  case IllegalVarianceInData
    (qn: QualifiedName, violatingVars: collection.Set[VTerm.Var])
    (using Γ: Context) extends IrError(Γ)
  case IllegalVarianceInRecord
    (qn: QualifiedName, violatingVars: collection.Set[VTerm.Var])
    (using Γ: Context) extends IrError(Γ)
  case IncompleteClauses(qn: QualifiedName)(using Γ: Context) extends IrError(Γ)
  case InsufficientResourceForSplit(x: VTerm.Var, binding: Binding[VTerm])(using Γ: Context)
    extends IrError(Γ)
  case LeakedReferenceToEffectfulComputationResult(effectfulTerm: CTerm)(using Γ: Context)
    extends IrError(Γ)
  case MissingConstructor(name: Name, qn: QualifiedName) extends IrError(Context.empty)
  case MissingConstructorCase(dataQn: QualifiedName, conName: Name) extends IrError(Context.empty)
  case MissingDeclaration(qn: QualifiedName) extends IrError(Context.empty)
  case MissingDefaultTypeCase() extends IrError(Context.empty)
  case MissingDefinition(qn: QualifiedName) extends IrError(Context.empty)
  case MissingField(name: Name, qn: QualifiedName) extends IrError(Context.empty)
  case MissingFieldsInCoPattern(clause: PreClause)(using Γ: Context) extends IrError(Γ)
  case MissingUserCoPattern(clause: PreClause)(using Γ: Context) extends IrError(Γ)
  case NonEmptyType(ty: VTerm, source: PreClause)(using Γ: Context) extends IrError(Γ)
  case NotCConvertible(sub: CTerm, sup: CTerm, ty: Option[CTerm])(using Γ: Context)
    extends IrError(Γ)
  case NotCSubtype(sub: CTerm, sup: CTerm)(using Γ: Context) extends IrError(Γ)
  case NotCTypeError(tm: CTerm)(using Γ: Context) extends IrError(Γ)
  case NotCollapsable(ctm: CTerm)(using Γ: Context) extends IrError(Γ)
  case NotDataTypeType(tm: CTerm)(using Γ: Context) extends IrError(Γ)
  case NotLevelType(tm: VTerm)(using Γ: Context) extends IrError(Γ)
  case NotEffectSubsumption(sub: VTerm, sup: VTerm)(using Γ: Context) extends IrError(Γ)
  case NotLevelSubsumption(sub: VTerm, sup: VTerm)(using Γ: Context) extends IrError(Γ)
  case NotTypeError(tm: VTerm)(using Γ: Context) extends IrError(Γ)
  case NotUsageSubsumption(sub: VTerm, sup: VTerm)(using Γ: Context) extends IrError(Γ)
  case NotVConvertible(left: VTerm, right: VTerm, ty: Option[VTerm])(using Γ: Context)
    extends IrError(Γ)
  case NotVSubtype(sub: VTerm, sup: VTerm)(using Γ: Context) extends IrError(Γ)
  case TelescopeLengthMismatch(tms: Seq[VTerm], tys: Telescope)(using Γ: Context) extends IrError(Γ)
  case UnexpectedAbsurdPattern(p: Pattern)(using Γ: Context) extends IrError(Γ)
  case UnexpectedCPattern(q: CoPattern)(using Γ: Context) extends IrError(Γ)
  case UnexpectedCProjection(q: CoPattern)(using Γ: Context) extends IrError(Γ)
  case UnexpectedUserCoPattern(clause: PreClause, q: CoPattern)(using Γ: Context) extends IrError(Γ)
  case UnificationFailure(uRes: UnificationResult)(using Γ: Context) extends IrError(Γ)
  case ConstraintUnificationFailure
    (unsolvedConstraints: Set[Constraint], cause: IrError)
    (using Γ: Context) extends IrError(Γ)
  case UnmatchedDataIndex(con: VTerm.Con, dataType: VTerm.DataType)(using Γ: Context)
    extends IrError(Γ)
  case UnmatchedPattern
    (p: Pattern, ty: VTerm, unsolvedConstraints: Set[Constraint])
    (using Γ: Context) extends IrError(Γ)
  case UnsatisfiedUsageRequirements(unsolvedConstraints: Set[Constraint])(using Γ: Context)
    extends IrError(Γ)
  case UnsolvedElaboration(clause: PreClause)(using Γ: Context) extends IrError(Γ)
  case ElaborationFailure
    (part: DeclarationPart, decl: PreDeclaration, cause: IrError)
    (using Γ: Context) extends IrError(Γ, cause)
  case DataLevelCannotDependOnIndexArgument(preData: PreDeclaration.PreData)(using Γ: Context)
    extends IrError(Γ)
  case DuplicatedDeclaration(qn: QualifiedName) extends IrError(Context.empty)
  case UnableToFindUsageMeetDuringUnification(lowerBounds: Set[VTerm])(using Γ: Context)
    extends IrError(Γ)
  case InternalIrError(message: String)(using Γ: Context) extends IrError(Γ)
  case ComplexOperationCall(call: CTerm.OperationCall)(using Γ: Context) extends IrError(Γ)
  case ExpectEffectInstance(badEffInstance: VTerm)(using Γ: Context) extends IrError(Γ)
  case ExpectEffectInstanceTypeSubsumption(sub: VTerm, sup: VTerm)(using Γ: Context)
    extends IrError(Γ)
  case EscapedEffectInstanceCausesNdet(handler: CTerm.Handler)(using Γ: Context) extends IrError(Γ)
  case VariableEscaped
    (
      declaredEscapeStatus: EscapeStatus,
      actualEscapeStatus: EscapeStatus,
      dbNumber: Nat,
      definition: Declaration.Definition,
      clause: Clause,
    )
    (using Γ: Context) extends IrError(Γ)
  override def getMessage: String = verbosePPrinter.apply(this).plainText
