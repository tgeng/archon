package io.github.tgeng.archon.ast

import io.github.tgeng.archon.common.*
import io.github.tgeng.archon.ir.*

import scala.collection.immutable.{ListMap, ListSet}
import AstTerm.*
import VTerm.*
import CTerm.*
import ULevel.*

def astToVTerm(ast: AstTerm): Either[Error, VTerm] = ast match
  case AstType(level) =>
    for level <- astToVTerm(ast)
    yield
      val ul = USimpleLevel(level)
      VType(ul, VTop(ul))
  case AstBoundedType(upperBound) => ???
  case AstωType(layer) => ???
  case AstTop(level) => ???
  case AstPure(level) => ???
  case AstVar(name) => ???
  case AstU(cty) => ???
  case AstThunk(c) => ???
  case AstDataType(qn, args) => ???
  case AstCon(conName, args) => ???
  case AstEffectsType => ???
  case AstEffectsLiteral(effects) => ???
  case AstEffectsUnion(eff1, eff2) => ???
  case AstLevelType => ???
  case AstLevelLiteral(level) => ???
  case AstLevelMax(l1, l2) => ???
  case AstLevelSuc(l) => ???
  case AstHeapType => ???
  case AstCellType(heap, ty, status) => ???
  case AstDef(qn) => ???
  case AstForce(v) => ???
  case AstF(vTy, effects) => ???
  case AstReturn(v) => ???
  case AstLet(boundName, t, ctx) => ???
  case AstFunctionType(argName, argTy, bodyTy, effects) => ???
  case AstApplication(fun, arg) => ???
  case AstRecordType(qn, args, effects) => ???
  case AstProjection(rec, fieldName) => ???
  case AstOperatorCall(effect, opName, args) => ???
  case AstHandler(
  effect,
  otherEffects,
  outputType,
  transformInputName,
  transform,
  handlers,
  input
  ) => ???
  case AstHeapHandler(
  otherEffects,
  heapVarName,
  input,
  ) => ???

def astToCTerm(ast: AstTerm): Either[Error, CTerm] = ast match
  case AstType(level) => ???
  case AstBoundedType(upperBound) => ???
  case AstωType(layer) => ???
  case AstTop(level) => ???
  case AstPure(level) => ???
  case AstVar(name) => ???
  case AstU(cty) => ???
  case AstThunk(c) => ???
  case AstDataType(qn, args) => ???
  case AstCon(conName, args) => ???
  case AstEffectsType => ???
  case AstEffectsLiteral(effects) => ???
  case AstEffectsUnion(eff1, eff2) => ???
  case AstLevelType => ???
  case AstLevelLiteral(level) => ???
  case AstLevelMax(l1, l2) => ???
  case AstLevelSuc(l) => ???
  case AstHeapType => ???
  case AstCellType(heap, ty, status) => ???
  case AstDef(qn) => ???
  case AstForce(v) => ???
  case AstF(vTy, effects) => ???
  case AstReturn(v) => ???
  case AstLet(boundName, t, ctx) => ???
  case AstFunctionType(argName, argTy, bodyTy, effects) => ???
  case AstApplication(fun, arg) => ???
  case AstRecordType(qn, args, effects) => ???
  case AstProjection(rec, fieldName) => ???
  case AstOperatorCall(effect, opName, args) => ???
  case AstHandler(
  effect,
  otherEffects,
  outputType,
  transformInputName,
  transform,
  handlers,
  input
  ) => ???
  case AstHeapHandler(
  otherEffects,
  heapVarName,
  input,
  ) => ???
