package io.github.tgeng.archon.ast

import io.github.tgeng.archon.common.*
import io.github.tgeng.archon.ir.*
import scala.collection.immutable.{ListMap, ListSet}

type AstEff = (QualifiedName, List[AstTerm])

enum AstULevel:
  case AstUSimpleLevel(level: AstTerm)
  case AstUωLevel(layer: Nat)

enum AstElim:
  case AstArg(arg: AstTerm)
  case AstProj(name: Name)

enum AstTerm:
  case AstType(ul: AstULevel, upperBound: AstTerm)
  case AstTop(ul: AstULevel)
  case AstPure(ul: AstULevel)
  case AstVar(name: Name)
  case AstU(cty: AstTerm)
  case AstThunk(c: AstTerm)
  case AstEffectsLiteral(effects: ListSet[AstEff])
  case AstEffectfulCType(effects: AstTerm, ty: AstTerm)
  case AstLevelLiteral(level: Nat)
  case AstCellType(heap: AstTerm, ty: AstTerm, status: CellStatus)
  case AstDef(qn: QualifiedName)
  case AstForce(v: AstTerm)
  case AstF(vTy: AstTerm, effects: AstTerm)
  case AstReturn(v: AstTerm)
  case AstLet(boundName: Name, t: AstTerm, ctx: AstTerm)
  case AstFunctionType(argName: Name, argTy: AstTerm, bodyTy: AstTerm, effects: AstTerm)
  case AstRedux(head: AstTerm, elims: List[AstElim])
  case AstOperatorCall(effect: AstEff, opName: Name, args: List[AstTerm])
  case AstHandler(
    effect: AstEff,
    otherEffects: AstTerm,
    outputType: AstTerm,
    transformInputName: Name,
    transform: AstTerm,
    handlers: Map[Name, AstTerm],
    input: AstTerm
  )
  case AstHeapHandler(
    otherEffects: AstTerm,
    heapVarName: Name,
    input: AstTerm,
  )
  case AstExSeq(expressions: List[AstTerm])
