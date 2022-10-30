package com.github.tgeng.archon.core.ir

import com.github.tgeng.archon.common.*
import com.github.tgeng.archon.core.common.*

enum CaseTree:
  case CtTerm(term: CTerm)
  case CtLambda( /* binding + 1 */ body: CaseTree)(val boundName: Ref[Name])
  case CtRecord(fields: Map[Name, CaseTree])
  case CtTypeCase
    (
      operand: VTerm,
      cases: Map[QualifiedName, /* binding + arg count */ CaseTree],
      default: CaseTree
    )
  case CtDataCase
    (
      operand: VTerm,
      qn: QualifiedName,
      cases: Map[Name, /* binding + arg count */ CaseTree]
    )
  case CtEqualityCase
    (
      operand: VTerm,
      /** This body term is already applied with the weakening substitutor from unification. This
        * deviates from [1] but it is easier to implement visitor and transformers.
        */
      body: CaseTree
    )
  case CtEqualityEmpty(operand: VTerm)

// [1] Jesper Cockx and Andreas Abel. 2018. Elaborating dependent (co)pattern matching. Proc. ACM
// Program. Lang. 2, ICFP, Article 75 (September 2018), 30 pages. https://doi.org/10.1145/3236770
