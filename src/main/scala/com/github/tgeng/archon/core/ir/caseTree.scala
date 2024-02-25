package com.github.tgeng.archon.core.ir

import com.github.tgeng.archon.common.*
import com.github.tgeng.archon.core.common.*

import scala.collection.immutable.SeqMap

enum CaseTree:
  case CtTerm(term: CTerm)
  case CtLambda( /* binding + 1 */ body: CaseTree)(val boundName: Ref[Name])
  case CtRecord(fields: SeqMap[Name, CaseTree])
  case CtTypeCase
    (
      operand: VTerm,
      cases: SeqMap[QualifiedName, /* binding + arg count */ CaseTree],
      default: CaseTree,
    )
  case CtDataCase
    (
      operand: VTerm,
      qn: QualifiedName,
      cases: SeqMap[Name, /* binding + arg count */ CaseTree],
    )

// [1] Jesper Cockx and Andreas Abel. 2018. Elaborating dependent (co)pattern matching. Proc. ACM
// Program. Lang. 2, ICFP, Article 75 (September 2018), 30 pages. https://doi.org/10.1145/3236770
