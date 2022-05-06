package io.github.tgeng.archon.ast

import AstTerm.*
import AstPattern.*

enum AstError:
  case UnresolvedVar(astVar: AstVar)
  case UnresolvedPVar(astPVar: AstPVar)
