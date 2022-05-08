package io.github.tgeng.archon.ir

import io.github.tgeng.archon.common.*
import io.github.tgeng.archon.ir.*

enum IrError:
  case Unknown
  case EffectfulCType(ty: CTerm) // type of `ty` is some `CType` such that `cty.effects != Total`
  case ExpectCell(tm: VTerm)
  case ExpectCellType(ty: VTerm)
  case ExpectCellTypeWithHeap(heapKey: HeapKey)
  case ExpectDataType(ty: VTerm)
  case ExpectEqualityType(ty: VTerm)
  case ExpectFType(cTy: CTerm)
  case ExpectFunction(c: CTerm)
  case ExpectRecord(c: CTerm)
  case ExpectUType(vTy: VTerm)
  case MissingConstructor(name: Name, qn: QualifiedName)
  case NotCTypeError(ty: CTerm)
  case NotTypeError(ty: VTerm)
  case ReductionStuck(stuckTerm: CTerm)
  case TelescopeLengthMismatch(tms: Seq[VTerm], tys: Telescope)
  case UninitializedCell(stuckTerm: CTerm)
  case UnmatchedHandlerImplementation(qn: QualifiedName, implementedOperators:Iterable[Name])
  case NotVSubsumption(sub: VTerm, sup: VTerm, ty: Option[VTerm], mode: CheckSubsumptionMode)
  case NotCSubsumption(sub: CTerm, sup: CTerm, ty: Option[CTerm], mode: CheckSubsumptionMode)
  case NotLevelSubsumption(sub: ULevel, sup: ULevel, mode: CheckSubsumptionMode)
  case NotEffectSubsumption(sub: VTerm, sup: VTerm, mode: CheckSubsumptionMode)
  case IllegalVarianceInData(qn: QualifiedName, illegallyUsedBindingIndices: List[Nat])
  case IllegalVarianceInRecord(qn: QualifiedName, illegallyUsedBindingIndices: List[Nat])
  case NotPureType(ty: VTerm)
  case NormalizationError(ctm: CTerm)
  case CollapsingEffectfulTerm(ctm: CTerm)
  case NotCollapsable(ctm: CTerm)
