package com.github.tgeng.archon.core.ast

import com.github.tgeng.archon.core.common.*
import com.github.tgeng.archon.core.ir.SourceInfo
import com.github.tgeng.archon.core.ir.SourceInfoOwner

enum AstPattern(val sourceInfo: SourceInfo) extends SourceInfoOwner:
  case AstPVar(name: Name)(using sourceInfo: SourceInfo) extends AstPattern(sourceInfo)
  case AstPConstructor(name: Name, args: List[AstPattern])(using sourceInfo: SourceInfo) extends AstPattern(sourceInfo)
  case AstPForcedConstructor(name: Name, args: List[AstPattern])(using sourceInfo: SourceInfo) extends AstPattern(sourceInfo)
  case AstPForced(term: AstTerm)(using sourceInfo: SourceInfo) extends AstPattern(sourceInfo)
  case AstPAbsurd()(using sourceInfo: SourceInfo) extends AstPattern(sourceInfo)

enum AstCoPattern(val sourceInfo: SourceInfo) extends SourceInfoOwner:
  case AstCPattern(p: AstPattern) extends AstCoPattern(p.sourceInfo)
  case AstCProjection(name: Name)(using sourceInfo: SourceInfo) extends AstCoPattern(sourceInfo)
