package io.github.tgeng.archon.ast

import io.github.tgeng.archon.common.*
import io.github.tgeng.archon.ir.*

import collection.immutable.{ListMap, ListSet}
import collection.mutable
import AstTerm.*
import VTerm.*
import CTerm.*
import ULevel.*

class NameContext(
  private val mapping: mutable.LinkedHashMap[Name, mutable.ArrayBuffer[Int]],
  private val names: mutable.ArrayBuffer[Name]):
  def apply(astVar: AstVar): Either[AstError, Var] =
    mapping.get(astVar.name) match
      case None => Left(???)
      case _ => ???

def astToVTerm(ast: AstTerm): Either[AstError | IrError, VTerm] = ast match
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

def astToCTerm(ast: AstTerm): Either[IrError, CTerm] = ast match
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
