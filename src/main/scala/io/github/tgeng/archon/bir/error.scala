package io.github.tgeng.archon.bir

enum Error:
  case Unknown
  case ReductionStuck(stuckTerm: CTerm)
  case UninitializedCell(stuckTerm: CTerm)
  