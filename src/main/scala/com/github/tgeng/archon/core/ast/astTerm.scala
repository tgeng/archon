package com.github.tgeng.archon.core.ast

import com.github.tgeng.archon.common.*
import com.github.tgeng.archon.core.common.*
import com.github.tgeng.archon.core.ir.*

type AstEff = (QualifiedName, List[AstTerm])

enum AstULevel:
  case AstUSimpleLevel(level: AstTerm)
  case AstUωLevel(layer: Nat)

enum AstTerm:
  case AstDef(qn: QualifiedName)
  case AstVar(name: Name)
  case AstU(cty: AstTerm)
  case AstThunk(c: AstTerm)
  case AstEffectLiteral(eff: AstEff)
  case AstLevelLiteral(level: Nat)
  case AstCellType(heap: AstTerm, ty: AstTerm, status: CellStatus)
  case AstEqualityType(ty: AstTerm, left: AstTerm, right: AstTerm)
  case AstRefl
  case AstForce(v: AstTerm)
  case AstF(vTy: AstTerm, effects: AstTerm)
  case AstReturn(v: AstTerm)
  case AstLet(boundName: Name, t: AstTerm, ctx: AstTerm)
  case AstFunctionType(argName: Name, argTy: AstTerm, bodyTy: AstTerm, effects: AstTerm)
  case AstRedux(head: AstTerm, elims: List[Elimination[AstTerm]])
  case AstOperatorCall(effect: AstEff, opName: Name, args: List[AstTerm])
  case AstHandler(
    effect: AstEff,
    otherEffects: AstTerm,
    outputType: AstTerm,
    transformInputName: Name,
    transform: AstTerm,
    handlers: Map[Name, (/* op args */List[Name], /* resume */ Name, AstTerm)],
    input: AstTerm
  )
  case AstHeapHandler(
    otherEffects: AstTerm,
    heapVarName: Name,
    input: AstTerm,
  )
  case AstExSeq(expressions: List[AstTerm])
