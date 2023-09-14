package com.github.tgeng.archon.core.ast

import com.github.tgeng.archon.core.common.*
import com.github.tgeng.archon.core.ir.SourceInfo
import com.github.tgeng.archon.core.ir.SourceInfoOwner

enum AstPattern(val sourceInfo: SourceInfo) extends SourceInfoOwner[AstPattern]:
  case AstPVar(name: Name)(using sourceInfo: SourceInfo) extends AstPattern(sourceInfo)
  case AstPConstructor(name: Name, args: List[AstPattern])(using sourceInfo: SourceInfo) extends AstPattern(sourceInfo)
  case AstPForcedConstructor(name: Name, args: List[AstPattern])(using sourceInfo: SourceInfo)
    extends AstPattern(sourceInfo)
  case AstPForced(term: AstTerm)(using sourceInfo: SourceInfo) extends AstPattern(sourceInfo)
  case AstPAbsurd()(using sourceInfo: SourceInfo) extends AstPattern(sourceInfo)

  override def withSourceInfo(sourceInfo: SourceInfo): AstPattern =
    given SourceInfo = sourceInfo

    this match
      case AstPVar(name)               => AstPVar(name)
      case AstPConstructor(name, args) => AstPConstructor(name, args)
      case AstPForcedConstructor(name, args) =>
        AstPForcedConstructor(name, args)
      case AstPForced(term) => AstPForced(term)
      case AstPAbsurd()     => AstPAbsurd()

enum AstCoPattern(val sourceInfo: SourceInfo) extends SourceInfoOwner[AstCoPattern]:
  case AstCPattern(p: AstPattern) extends AstCoPattern(p.sourceInfo)
  case AstCProjection(name: Name)(using sourceInfo: SourceInfo) extends AstCoPattern(sourceInfo)

  override def withSourceInfo(sourceInfo: SourceInfo): AstCoPattern =
    given SourceInfo = sourceInfo

    this match
      case AstCPattern(p)       => AstCPattern(p)
      case AstCProjection(name) => AstCProjection(name)
