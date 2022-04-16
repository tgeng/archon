package io.github.tgeng.archon.ast

import io.github.tgeng.archon.common.*
import io.github.tgeng.archon.ir.*
import scala.collection.immutable.{ListMap, ListSet}

type AstEff = (QualifiedName, List[AstTerm])

enum AstTerm:
  case AstType(level: AstTerm)
  case AstBoundedType(upperBound: AstTerm)
  case AstωType(layer: Nat)
  case AstTop(level: AstTerm)
  case AstPure(level: AstTerm)
  case AstVar(name: Name)
  case AstU(cty: AstTerm)
  case AstThunk(c: AstTerm)
  case AstDataType(qn: QualifiedName, args: List[AstTerm])
  case AstCon(conName: Name, args: List[AstTerm])
  case AstEqualityType(ty: AstTerm, left: AstTerm, right: AstTerm)
  case AstRefl
  case AstEffectsType
  case AstEffectsLiteral(effects: ListSet[AstEff])
  case AstEffectsUnion(eff1: AstTerm, eff2: AstTerm)
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
  case Handler(
    effect: AstEff,
    otherEffects: AstTerm,
    outputType: AstTerm,
    transformInputName: Name,
    transform: AstTerm,
    handlers: Map[Name, AstTerm],
    input: AstTerm
  )
  case AstAllocOp(heap: AstTerm, ty: AstTerm)
  case AstSetOp(cell: AstTerm, value: AstTerm)
  case AstGetOp(cell: AstTerm)
  case AstHeapHandler(
    otherEffects: AstTerm,
    heapVarName: Name,
    input: AstTerm,
  )
