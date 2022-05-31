package com.github.tgeng.archon.core.ast

import AstTerm.*
import AstPattern.*
import com.github.tgeng.archon.core.common.*

enum AstError:
  case UnresolvedIdentifier(astVar: AstIdentifier)
  case UnresolvedPVar(astPVar: AstPVar)
  case UnresolvedNameInPattern(name: Name)
