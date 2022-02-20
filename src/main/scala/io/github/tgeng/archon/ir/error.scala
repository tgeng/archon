package io.github.tgeng.archon.ir

enum Error:
  case Unknown
  case ReductionStuck(stuckTerm: CTerm)
  case UninitializedCell(stuckTerm: CTerm)
  case VTypeError(vTerm: VTerm, vType: VTerm)
  case CTypeError(cTerm: CTerm, cType: CTerm)
