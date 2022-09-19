package com.github.tgeng.archon.core.ir

import com.github.tgeng.archon.common.*
import com.github.tgeng.archon.core.common.*

enum CaseTree:
  case Term(term: CTerm)
  case Lambda( /* binding + 1 */ body: CTerm)
  case Record(fields: Map[Name, CTerm])
  case TypeCase
    (
      arg: VTerm,
      cases: Map[
        QualifiedName,
        (Nat, /* binding + 1 (for whole arg) + tuple(0) */ CTerm)
      ],
      /* binding + 1 */ default: CTerm
    )
  case DataCase
    (
      arg: VTerm,
      cases: Map[
        Name,
        (Nat, /* binding + 1 (for whole arg) + tuple(0) */ CTerm)
      ]
    )
  case EqualityCase(arg: VTerm, /* binding + 1 (for whole arg) */ body: CTerm)
