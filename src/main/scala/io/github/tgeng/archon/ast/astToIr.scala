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
  block(using ctx :+ name)

extension (ctx: NameContext)
  private def :+(name: Name) = (ctx._1 + 1, ctx._2.updated(name, ctx._1))

def astToIr(ast: AstTerm)
  (using ctx: NameContext)
  (using Σ: Signature): Either[AstError, CTerm] = ast match
  case AstDef(qn) => ???
  case v: AstVar =>
    for v <- resolve(v)
      yield Return(v)
  case AstU(cty) =>
    for cty <- astToIr(cty)
      yield Return(U(cty))
  case AstThunk(c) =>
    for c <- astToIr(c)
      yield Return(Thunk(c))
  case AstEffectsLiteral(effects) =>
    // The following is a bit convoluted. Expressions appear in effect arguments may contain
    // arbitrary computation. Hence, they must be hoisted up to let bindings. For example
    // `<eff1 computeArg1 computeArg2 | eff2 valueArg3>` is converted to
    // `let arg1 = computeArg1 in
    //  let arg2 = computeArg2 in
    //  return <eff1 arg1 arg2 | eff2 valueArg3>`

    // Step 1. Get all CTerms of all effects arguments.
    for effects <- transpose(
      effects.map {
        (qn, args) =>
          for args <- transpose(args.map(astToIr))
            yield (qn, args)
      }
    )
    yield
      // Step 2. Count the number of non-trivial computations present in the effects args. This is
      // used to populate DeBruijn index of let bound variables for these non-trivial
      // computations.
      var numBinding = 0
      effects.foreach { (_, args) =>
        args.foreach {
          case Return(_) => numBinding += 1
          case _ =>
        }
      }

      // Step 3. Transform the computations into values and track non-trivial computations that need
      // to appear in let bindings. Weakening is performed where appropriate.
      val letBoundComputations = mutable.ArrayBuffer[CTerm]()
      var nonTrivialIdx = 0
      val vEffects = effects.map { (qn, args) =>
        (qn, args.map {
          case Return(v) => v.weaken(numBinding, 0)
          case c =>
            letBoundComputations.addOne(c.weaken(nonTrivialIdx, 0))
            nonTrivialIdx += 1
            Var(numBinding - nonTrivialIdx)
        })
      }
      letBoundComputations.foldRight(Return(EffectsLiteral(ListSet(vEffects: _*))))(Let(_, _)())
  case AstLevelLiteral(level) => Right(Return(LevelLiteral(level)))
  case AstCellType(heap, ty, status) =>
    for heap <- astToIr(heap)
        r <- chain(heap) { heap =>
          for ty <- astToIr(ty)
              r <- chain(ty) { ty =>
                Right(Return(CellType(heap, ty, status)))
              }
          yield r
        }
    yield r
  case AstForce(v) =>
    for v <- astToIr(v)
        r <- chain(v) { v =>
          Right(Force(v))
        }
    yield r
  case AstF(vTy, effects) =>
    for vTy <- astToIr(vTy)
        r <- chain(vTy) { vTy =>
          for effects <- astToIr(effects)
              r <- chain(effects) { effects =>
                Right(F(vTy, effects))
              }
          yield r
        }
    yield r
  case AstReturn(v) => astToIr(v)
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

private def chain(t: CTerm)
  (ctx: NameContext ?=> VTerm => Either[AstError, CTerm])
  (using NameContext): Either[AstError, CTerm] = t match
  case Return(v) => ctx(v)
  case _ => bind(gn"v") {
    for ctx <- ctx(Var(0))
      yield Let(t, ctx)()
  }