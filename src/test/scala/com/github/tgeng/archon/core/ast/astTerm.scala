package com.github.tgeng.archon.core.ast

import com.github.tgeng.archon.common.*
import com.github.tgeng.archon.core.common.*
import com.github.tgeng.archon.core.ir.*

import scala.collection.immutable.SeqMap

type AstEff = (Name, List[AstTerm])

enum AstTerm(val sourceInfo: SourceInfo) extends SourceInfoOwner[AstTerm]:
  case AstDef(qn: QualifiedName)(using sourceInfo: SourceInfo) extends AstTerm(sourceInfo)
  case AstIdentifier(name: Name)(using sourceInfo: SourceInfo) extends AstTerm(sourceInfo)
  case AstCollapse(c: AstTerm)(using sourceInfo: SourceInfo) extends AstTerm(sourceInfo)
  case AstU(cty: AstTerm)(using sourceInfo: SourceInfo) extends AstTerm(sourceInfo)
  case AstThunk(c: AstTerm)(using sourceInfo: SourceInfo) extends AstTerm(sourceInfo)
  case AstLevelLiteral(level: Nat)(using sourceInfo: SourceInfo) extends AstTerm(sourceInfo)
  case AstForce(v: AstTerm)(using sourceInfo: SourceInfo) extends AstTerm(sourceInfo)
  case AstF(vTy: AstTerm, effects: AstTerm)(using sourceInfo: SourceInfo)
    extends AstTerm(sourceInfo)
  case AstFunctionType
    (argName: Name, argTy: AstTerm, bodyTy: AstTerm, effects: AstTerm)
    (using sourceInfo: SourceInfo) extends AstTerm(sourceInfo)
  case AstRedex(head: AstTerm, elims: List[Elimination[AstTerm]])(using sourceInfo: SourceInfo)
    extends AstTerm(sourceInfo)
  case AstBlock(statements: List[Statement])(using sourceInfo: SourceInfo)
    extends AstTerm(
      sourceInfo,
    )

  override def withSourceInfo(sourceInfo: SourceInfo): AstTerm =
    given SourceInfo = sourceInfo

    this match
      case AstDef(qn)             => AstDef(qn)
      case AstIdentifier(name)    => AstIdentifier(name)
      case AstCollapse(c)         => AstCollapse(c)
      case AstU(cty)              => AstU(cty)
      case AstThunk(c)            => AstThunk(c)
      case AstLevelLiteral(level) => AstLevelLiteral(level)
      case AstForce(v)            => AstForce(v)
      case AstF(vTy, effects)     => AstF(vTy, effects)
      case AstFunctionType(argName, argTy, bodyTy, effects) =>
        AstFunctionType(argName, argTy, bodyTy, effects)
      case AstRedex(head, elims) => AstRedex(head, elims)
      case AstBlock(statements)  => AstBlock(statements)

enum Statement:
  case STerm(term: AstTerm)
  case SBinding(name: Name, term: AstTerm)
  case SHandler
    (
      effect: AstEff,
      outputEffects: AstTerm,
      outputType: AstTerm,
      transformInputName: Name,
      transform: AstTerm,
      handlers: SeqMap[Name, ( /* op args */ List[Name], AstTerm)],
    )
  case SHeapHandler(outputEffects: AstTerm, heapVarName: Name)
