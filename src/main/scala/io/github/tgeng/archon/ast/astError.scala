package io.github.tgeng.archon.ast

import AstTerm.*

enum AstError:
  case UnresolvedVar(astVar: AstVar)
