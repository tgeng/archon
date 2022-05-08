package io.github.tgeng.archon.core.ast

import AstTerm.*
import AstPattern.*

enum AstError:
  case UnresolvedVar(astVar: AstVar)
  case UnresolvedPVar(astPVar: AstPVar)
