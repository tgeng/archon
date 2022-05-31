package com.github.tgeng.archon.core.ast

import com.github.tgeng.archon.core.common.*

enum AstPattern:
  case AstPVar(name: Name)
  case AstPDataType(name: Name, args: List[AstPattern])
  case AstPForcedDataType(name: Name, args: List[AstPattern])
  case AstPConstructor(name: Name, args: List[AstPattern])
  case AstPForcedConstructor(name: Name, args: List[AstPattern])
  case AstPForced(term: AstTerm)
  case AstPAbsurd

enum AstCoPattern:
  case AstCPattern(p: AstPattern)
  case AstCProjection(name: Name)
