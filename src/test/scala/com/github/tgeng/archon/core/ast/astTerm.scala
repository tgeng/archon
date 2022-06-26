package com.github.tgeng.archon.core.ast

import com.github.tgeng.archon.common.*
import com.github.tgeng.archon.core.common.*
import com.github.tgeng.archon.core.ir.*

type AstEff = (Name, List[AstTerm])

enum AstTerm(val sourceInfo: SourceInfo) extends SourceInfoOwner:
  case AstDef(qn: QualifiedName)(using sourceInfo: SourceInfo) extends AstTerm(sourceInfo)
  case AstIdentifier(name: Name)(using sourceInfo: SourceInfo) extends AstTerm(sourceInfo)
  case AstCollapse(c: AstTerm)(using sourceInfo: SourceInfo) extends AstTerm(sourceInfo)
  case AstU(cty: AstTerm)(using sourceInfo: SourceInfo) extends AstTerm(sourceInfo)
  case AstThunk(c: AstTerm)(using sourceInfo: SourceInfo) extends AstTerm(sourceInfo)
  case AstLevelLiteral(level: Nat)(using sourceInfo: SourceInfo) extends AstTerm(sourceInfo)
  case AstForce(v: AstTerm)(using sourceInfo: SourceInfo) extends AstTerm(sourceInfo)
  case AstF(vTy: AstTerm, effects: AstTerm)(using sourceInfo: SourceInfo) extends AstTerm(sourceInfo)
  case AstFunctionType(argName: Name, argTy: AstTerm, bodyTy: AstTerm, effects: AstTerm)(using sourceInfo: SourceInfo) extends AstTerm(sourceInfo)
  case AstRedux(head: AstTerm, elims: List[Elimination[AstTerm]])(using sourceInfo: SourceInfo) extends AstTerm(sourceInfo)
  case AstBlock(statements: List[Statement])(using sourceInfo: SourceInfo) extends AstTerm(sourceInfo)

enum Statement:
  case STerm(term: AstTerm)
  case SBinding(name: Name, term: AstTerm)
  case SHandler(
    effect: AstEff,
    otherEffects: AstTerm,
    outputType: AstTerm,
    transformInputName: Name,
    transform: AstTerm,
    handlers: Map[Name, (/* op args */List[Name], /* resume */ Name, AstTerm)],
  )
  case SHeapHandler(
    otherEffects: AstTerm,
    heapVarName: Name,
  )