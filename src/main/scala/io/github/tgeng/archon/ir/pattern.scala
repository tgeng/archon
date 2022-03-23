package io.github.tgeng.archon.ir

import io.github.tgeng.archon.common.*

enum Pattern:
  case PRef(idx: Nat)
  case PRefl

  /**
   * Note that matching computation type is prohibited. This should simplify compilation. In addition, it's unclear how
   * type checking of effects can work if we allow matching computation because the matched effect types become unbound
   * at type level.
   */
  case PValueType(qn: QualifiedName, args: List[Pattern])
  case PForcedValueType(qn: QualifiedName, args: List[Pattern])
  // Note that we do not allow matching specific values of level, effect, and heap because there are no corresponding
  // eliminators. All these can only be matched with a pattern variable.
  case PConstructor(name: Name, args: List[Pattern])
  case PForcedConstructor(name: Name, args: List[Pattern])
  case PForced(term: VTerm)
  case PAbsurd

enum CoPattern:
  case CPattern(p: Pattern)
  case CProjection(name: Name)
