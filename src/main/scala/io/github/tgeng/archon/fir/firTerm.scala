package io.github.tgeng.archon.fir

import io.github.tgeng.archon.common.*
import io.github.tgeng.archon.ir.*
import scala.collection.immutable.{ListMap, ListSet}

type FirEff = (QualifiedName, List[FirTerm])

enum FirTerm:
  case FirType(level: FirTerm)
  case FirBoundedType(upperBound: FirTerm)
  case FirωType(layer: Nat)
  case FirTop(level: FirTerm)
  case FirPure(level: FirTerm)
  case FirVar(name: Name)
  case FirU(cty: FirTerm)
  case FirThunk(c: FirTerm)
  case FirDataType(qn: QualifiedName, args: List[FirTerm])
  case FirCon(conName: Name, args: List[FirTerm])
  case FirEqualityType(ty: FirTerm, left: FirTerm, right: FirTerm)
  case FirRefl
  case FirEffectsType
  case FirEffectsLiteral(effects: ListSet[FirEff])
  case FirEffectsUnion(eff1: FirTerm, eff2: FirTerm)
  case FirLevelType
  case FirLevelLiteral(level: Nat)
  case FirLevelMax(l1: FirTerm, l2: FirTerm)
  case FirLevelSuc(l: FirTerm)
  case FirHeapType
  case FirCellType(heap: FirTerm, ty: FirTerm, status: CellStatus)
  case FirDef(qn: QualifiedName)
  case FirForce(v: FirTerm)
  case FirF(vTy: FirTerm, effects: FirTerm)
  case FirReturn(v: FirTerm)
  case FirLet(boundName: Name, t: FirTerm, ctx: FirTerm)
  case FirFunctionType(argName: Name, argTy: FirTerm, bodyTy: FirTerm, effects: FirTerm)
  case FirApplication(fun: FirTerm, arg: FirTerm)
  case FirRecordType(qn: QualifiedName, args: List[FirTerm], effects: FirTerm)
  case FirProjection(rec: FirTerm, fieldName: Name)
  case FirOperatorCall(effect: FirEff, opName: Name, args: List[FirTerm])
  case Handler(
    effect: FirEff,
    otherEffects: FirTerm,
    outputType: FirTerm,
    transformInputName: Name,
    transform: FirTerm,
    handlers: Map[Name, FirTerm],
    input: FirTerm
  )
  case FirAllocOp(heap: FirTerm, ty: FirTerm)
  case FirSetOp(cell: FirTerm, value: FirTerm)
  case FirGetOp(cell: FirTerm)
  case FirHeapHandler(
    otherEffects: FirTerm,
    heapVarName: Name,
    input: FirTerm,
  )
