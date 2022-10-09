package com.github.tgeng.archon.core.ir

import com.github.tgeng.archon.common.*
import com.github.tgeng.archon.core.common.*

enum CaseTree:
  case CtTerm(term: CTerm)
  case CtLambda( /* binding + 1 */ body: CTerm)(val boundName: Ref[Name])
  case CtRecord(fields: Map[Name, CTerm])
  case CtTypeCase
    (
      index: Nat,
      cases: Map[
        QualifiedName,
        /* binding + arg count */ CTerm
      ],
      default: CTerm
    )
  case CtDataCase
    (
      index: Nat,
      qn: QualifiedName,
      cases: Map[
        Name,
        /* binding + arg count */ CTerm
      ]
    )
  case CtEqualityCase
    (
      index: Nat,
      /** Weakening substitutor that recovers unused variables removed by unification. */
      substitutor: Substitutor[VTerm],
      /** Body needs to have the substitutor applied before it can be used for interpreting or
        * further lowering.
        */
      body: CTerm
    )
