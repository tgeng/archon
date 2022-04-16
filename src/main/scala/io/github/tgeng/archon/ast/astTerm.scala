package io.github.tgeng.archon.ast

import io.github.tgeng.archon.common.*
import io.github.tgeng.archon.ir.*
import scala.collection.immutable.{ListMap, ListSet}

type AstEff = (QualifiedName, List[AstTerm])

enum AstULevel:
  case AstUSimpleLevel(level: AstTerm)
  case AstUωLevel(layer: Nat)

enum AstTerm:
  case AstType(ul: AstULevel, upperBound: AstTerm)
  case AstTop(ul: AstULevel)
  case AstPure(ul: AstULevel)
  case AstVar(name: Name)
  case AstU(cty: AstTerm)
  case AstThunk(c: AstTerm)
  case AstDataType(qn: QualifiedName, args: List[AstTerm])
  case AstCon(conName: Name, args: List[AstTerm])
  case AstEffectsType
  case AstEffectsLiteral(effects: ListSet[AstEff])
  case AstEffectsUnion(eff1: AstTerm, eff2: AstTerm)
  case AstEffectfulCType(effects: AstTerm, ty: AstTerm)
  case AstLevelType
  case AstLevelLiteral(level: Nat)
  case AstLevelMax(l1: AstTerm, l2: AstTerm)
  case AstLevelSuc(l: AstTerm)
  case AstHeapType
  case AstCellType(heap: AstTerm, ty: AstTerm, status: CellStatus)
  case AstDef(qn: QualifiedName)
  case AstForce(v: AstTerm)
  case AstF(vTy: AstTerm, effects: AstTerm)
  case AstReturn(v: AstTerm)
  case AstLet(boundName: Name, t: AstTerm, ctx: AstTerm)
  case AstFunctionType(argName: Name, argTy: AstTerm, bodyTy: AstTerm, effects: AstTerm)
  case AstApplication(fun: AstTerm, arg: AstTerm)
  case AstRecordType(qn: QualifiedName, args: List[AstTerm], effects: AstTerm)
  case AstProjection(rec: AstTerm, fieldName: Name)
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
