package io.github.tgeng.archon.ir

enum Error:
  case Unknown
  case ReductionStuck(stuckTerm: CTerm)
  case UninitializedCell(stuckTerm: CTerm)
