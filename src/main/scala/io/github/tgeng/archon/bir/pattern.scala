package io.github.tgeng.archon.bir

import io.github.tgeng.archon.common.QualifiedName

enum Pattern:
  case PRef(idx: Nat)
  case PRefl

  /**
   * Note that matching computation type is prohibited. This should simplify compilation. In addition, it's unclear how
   * type checking of effects can work if we allow matching computation because the matched effect types become unbound
   * at type level.
   */
  case PValueType(qn: QualifiedName, args: List[Pattern])
  case PConstructor(name: String, args: List[Pattern])
  case PForcedConstructor(name: String, args: List[Pattern])
  case PForced(term: VTerm)
  case PProjection(name: String)
  case PAbsurd