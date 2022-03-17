package io.github.tgeng.archon.ir

import io.github.tgeng.archon.common.*

enum Error:
  case Unknown
  case ReductionStuck(stuckTerm: CTerm)
  case UninitializedCell(stuckTerm: CTerm)
  case TelescopeLengthMismatch(tms: Seq[VTerm], tys: Telescope)
  case VTypeError(vTerm: VTerm, vType: VTerm)
  case CTypeError(cTerm: CTerm, cType: CTerm)
  case ULevelError(sub: ULevel, sup: ULevel)
  case NotVTypeError(ty: VTerm)
  case NotCTypeError(ty: CTerm)
  case EffectfulCType(ty: CTerm) // type of `ty` is some `CType` such that `cty.effects != Total`
  case CInferenceFailure(cTerm: CTerm)
  case VInferenceFailure(vTerm: VTerm)
  case UnmatchedHandlerImplementation(qn: QualifiedName, implementedOperators:Iterable[Name])
  case ExpectUType(vTy: VTerm)
  case ExpectFType(cTy: CTerm)
  case ExpectFunction(c: CTerm)
  case ExpectRecord(c: CTerm)
