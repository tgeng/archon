package io.github.tgeng.archon.ast

import io.github.tgeng.archon.common.*
import io.github.tgeng.archon.ir.*

import collection.immutable.{ListMap, ListSet}
import collection.mutable
import AstTerm.*
import AstULevel.*
import VTerm.*
import CTerm.*
import ULevel.*
import AstError.*

type NameContext = (Int, Map[Name, Int])

given emptyNameContext: NameContext = (1, Map.empty)

private def resolve(astVar: AstVar)(using ctx: NameContext): Either[AstError, Var] =
  ctx._2.get(astVar.name) match
    case None => Left(UnresolvedVar(astVar))
    case Some(dbNumber) => Right(Var(ctx._1 - dbNumber))

private def bind[T](name: Name)(block: NameContext ?=> T)(using ctx: NameContext): T =
  block(using (ctx._1 + 1, ctx._2.updated(name, ctx._1)))

def astToULevel(astULevel: AstULevel): Either[AstError, ULevel] = astULevel match
  case AstUSimpleLevel(level) =>
    for level <- astToVTerm(level)
    yield USimpleLevel(level)
  case AstUωLevel(layer) => Right(UωLevel(layer))

def astToVTerm(ast: AstTerm)(using NameContext): Either[AstError, VTerm] = ast match
  case AstType(ul, upperBound) =>
    for ul <- astToULevel(ul)
        upperBound <- astToVTerm(upperBound)
    yield VType(ul, upperBound)
  case AstTop(ul) =>
    for ul <- astToULevel(ul)
    yield VTop(ul)
  case AstPure(ul) => ???
  case AstVar(name) => ???
  case AstU(cty) => ???
  case AstThunk(c) => ???
  case AstEffectsLiteral(effects) => ???
  case AstEffectsUnion(eff1, eff2) => ???
  case AstEffectfulCType(effect, ty) => ???
  case AstLevelLiteral(level) => ???
  case AstLevelMax(l1, l2) => ???
  case AstLevelSuc(l) => ???
  case AstCellType(heap, ty, status) => ???
  case AstDef(qn) => ???
  case AstForce(v) => ???
  case AstF(vTy, effects) => ???
  case AstReturn(v) => ???
  case AstLet(boundName, t, ctx) => ???
  case AstFunctionType(argName, argTy, bodyTy, effects) => ???
  case AstRedux(head, elims) => ???
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
  case AstExSeq(expressions) => ???

def astToCTerm(ast: AstTerm): Either[IrError, CTerm] = ast match
  case AstType(ul, upperBound) => ???
  case AstTop(ul) => ???
  case AstPure(ul) => ???
  case AstVar(name) => ???
  case AstU(cty) => ???
  case AstThunk(c) => ???
  case AstEffectsLiteral(effects) => ???
  case AstEffectsUnion(eff1, eff2) => ???
  case AstEffectfulCType(effect, ty) => ???
  case AstLevelLiteral(level) => ???
  case AstLevelMax(l1, l2) => ???
  case AstLevelSuc(l) => ???
  case AstCellType(heap, ty, status) => ???
  case AstDef(qn) => ???
  case AstForce(v) => ???
  case AstF(vTy, effects) => ???
  case AstReturn(v) => ???
  case AstLet(boundName, t, ctx) => ???
  case AstFunctionType(argName, argTy, bodyTy, effects) => ???
  case AstRedux(head, elims) => ???
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
  case AstExSeq(expressions) => ???
