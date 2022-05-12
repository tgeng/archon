package com.github.tgeng.archon.core.ast

import com.github.tgeng.archon.common.*
import com.github.tgeng.archon.core.common.*
import com.github.tgeng.archon.core.ir.*

import collection.immutable.{ListMap, ListSet}
import collection.mutable
import AstTerm.*
import AstULevel.*
import VTerm.*
import CTerm.*
import ULevel.*
import AstError.*
import Elimination.*
import AstPattern.*
import AstCoPattern.*
import Pattern.*
import CoPattern.*
import com.github.tgeng.archon.core.ir.Elimination.EProj

type NameContext = (Int, Map[Name, Int])

given emptyNameContext: NameContext = (1, Map.empty)

private def resolve(astVar: AstVar)(using ctx: NameContext): Either[AstError, Var] =
  ctx._2.get(astVar.name) match
    case None => Left(UnresolvedVar(astVar))
    case Some(dbNumber) => Right(Var(ctx._1 - dbNumber))

private def resolve(astPVar: AstPVar)(using ctx: NameContext): Either[AstError, PVar] =
  ctx._2.get(astPVar.name) match
    case None => Left(UnresolvedPVar(astPVar))
    case Some(dbNumber) => Right(PVar(ctx._1 - dbNumber))

private def bind[T](name: Name)(block: NameContext ?=> T)(using ctx: NameContext): T =
  block(using ctx :+ name)

private def bind[T](names: List[Name])(block: NameContext ?=> T)(using ctx: NameContext): T =
  block(using ctx ++ names)

extension (ctx: NameContext)
  private def :+(name: Name) = (ctx._1 + 1, ctx._2.updated(name, ctx._1))
  private def ++(names: Seq[Name]) = (ctx._1 + names.size, names.zipWithIndex.foldLeft(ctx._2) { (map, tuple) =>
    tuple match
      case (name, offset) => map.updated(name, ctx._1 + offset)
  })

def astToIr(ast: AstCoPattern)
  (using ctx: NameContext)
  (using Σ: Signature): Either[AstError, CoPattern] = ast match
  case AstCPattern(p) =>
    for
      p <- astToIr(p)
    yield CPattern(p)
  case AstCProjection(name) => Right(CProjection(name))

def astToIr(ast: AstPattern)
  (using ctx: NameContext)
  (using Σ: Signature): Either[AstError, Pattern] = ast match
  case v: AstPVar => resolve(v)
  case AstPRefl => Right(PRefl)
  case AstPDataType(qn, args) => transpose(args.map(astToIr)).map(PDataType(qn, _))
  case AstPForcedDataType(qn, args) => transpose(args.map(astToIr)).map(PForcedDataType(qn, _))
  case AstPConstructor(name, args) => transpose(args.map(astToIr)).map(PConstructor(name, _))
  case AstPForcedConstructor(name, args) =>
    transpose(args.map(astToIr)).map(PForcedConstructor(name, _))
  case AstPForced(term) =>
    for
      cTerm <- astToIr(term)
    yield PForced(Collapse(cTerm))
  case AstPAbsurd => Right(PAbsurd)

def astToIr(ast: AstTerm)
  (using ctx: NameContext)
  (using Σ: Signature): Either[AstError, CTerm] = ast match
  case AstDef(qn) => Right(Def(qn))
  case v: AstVar =>
    for v <- resolve(v)
      yield Return(v)
  case AstCollapse(c) =>
    for c <- astToIr(c)
    yield Return(Collapse(c))
  case AstU(cty) =>
    for cty <- astToIr(cty)
      yield Return(U(cty))
  case AstThunk(c) =>
    for c <- astToIr(c)
      yield Return(Thunk(c))
  case AstEffectLiteral(effect) =>
    chainAstWithDefaultName[[X] =>> (QualifiedName, List[X])](gn"eArg", effect) {
      eff => Return(EffectsLiteral(ListSet(eff)))
    }
  case AstLevelLiteral(level) => Right(Return(LevelLiteral(level)))
  case AstCellType(heap, ty, status) => chainAst((gn"heap", heap), (gn"ty", ty)) {
    case heap :: ty :: Nil => Return(CellType(heap, ty, status))
    case _ => throw IllegalStateException()
  }
  case AstEqualityType(ty, left, right) => chainAst(
    (gn"ty", ty),
    (gn"left", left),
    (gn"right", right)
  ) {
    case ty :: left :: right :: Nil => Return(EqualityType(ty, left, right))
    case _ => throw IllegalStateException()
  }
  case AstRefl => Right(Return(Refl))
  case AstForce(v) => chainAst(gn"v", v)(Force(_))
  case AstF(vTy, effects) => chainAst((gn"vTy", vTy), (gn"eff", effects)) {
    case vTy :: effects :: Nil => F(vTy, effects)
    case _ => throw IllegalStateException()
  }
  case AstReturn(v) => astToIr(v)
  case AstLet(boundName, t, ctx) =>
    for t <- astToIr(t)
        ctx <- bind(boundName) {
          astToIr(ctx)
        }
    yield Let(t, ctx)(boundName)
  case AstFunctionType(argName, argTy, bodyTy, effects) =>
    for argTy <- astToIr(argTy)
        effects <- bind(argName) {
          astToIr(effects)
        }
        bodyTy <- bind(argName) {
          astToIr(bodyTy)
        }
        r <- chain((gn"argTy", argTy), (gn"eff", effects)) {
          case (argTy :: effects :: Nil, n) => FunctionType(
            Binding(argTy)(argName),
            bodyTy.weaken(n, 1),
            effects
          )
          case _ => throw IllegalStateException()
        }
    yield r
  case AstRedux(head, elims) =>
    for head <- astToIr(head)
        r <- chainAstWithDefaultName[[X] =>> List[Elimination[X]]](gn"arg", elims) {
          _.foldLeft(head) { (c, e) =>
            e match
              case ETerm(v) => Application(c, v)
              case EProj(n) => Projection(c, n)
          }
        }
    yield r
  case AstOperatorCall((effQn, effArgs), opName, args) =>
    val n = effArgs.size
    chainAstWithDefaultName(gn"arg", effArgs ++ args) { allArgs =>
      val effArgs = allArgs.take(n)
      val args = allArgs.drop(n)
      OperatorCall((effQn, effArgs), opName, args)
    }
  case AstHandler(
  (effQn, effArgs),
  otherEffects,
  outputType,
  transformInputName,
  transform,
  handlers,
  input
  ) =>
    for effArgs <- transpose(effArgs.map(astToIr))
        otherEffects <- astToIr(otherEffects)
        outputType <- astToIr(outputType)
        transform <- bind(transformInputName) {
          astToIr(transform)
        }
        handlers <- transposeValues(
          handlers.view.mapValues { (argNames, resumeName, astTerm) =>
            bind(argNames :+ resumeName) {
              astToIr(astTerm).map((argNames.size + 1, _))
            }
          }.toMap
        )
        input <- astToIr(input)
        r <- chain[[X] =>> List[List[X]]](
          effArgs.map((gn"effArg", _)) :: List((gn"otherEff", otherEffects)) :: List((gn"outputType", outputType)) :: Nil
        ) {
          case (effArgs :: List(otherEffects) :: List(outputType) :: Nil, n) =>
            Handler(
              (effQn, effArgs),
              otherEffects,
              outputType,
              transform.weaken(n, 1),
              handlers.view.mapValues { case (bar, t) => t.weaken(n, bar) }.toMap,
              input.weaken(n, 0)
            )
          case _ => throw IllegalStateException()
        }
    yield r
  case AstHeapHandler(
  otherEffects,
  heapVarName,
  input,
  ) =>
    for otherEffects <- astToIr(otherEffects)
        input <- bind(heapVarName) {
          astToIr(input)
        }
        r <- chain(gn"otherEff", otherEffects) {
          case (otherEffects, n) => HeapHandler(
            otherEffects,
            None,
            IndexedSeq(),
            input.weaken(n, 1)
          )
        }
    yield r
  case AstExSeq(expressions) =>
    if (expressions.isEmpty) then
      Right(Def(Builtins.UnitQn))
    else
      for expressions <- transpose(expressions.map(astToIr))
        yield
          val weakenedExpressions = expressions.zipWithIndex.map { (c, i) => c.weaken(i, 0) }
          weakenedExpressions.dropRight(1).foldRight(weakenedExpressions.last)(Let(_, _)(gn"_"))

private def astToIr(elim: Elimination[AstTerm])
  (using ctx: NameContext)
  (using Σ: Signature): Either[AstError, Elimination[CTerm]] = elim match
  case ETerm(astTerm) => astToIr(astTerm).map(ETerm(_))
  case EProj(name) => Right(EProj(name))

private def chainAst(name: Name, t: AstTerm)
  (block: Signature ?=> VTerm => CTerm)
  (using NameContext)
  (using Signature): Either[AstError, CTerm] = chainAst(List((name, t))) {
  case v :: Nil => block(v)
  case _ => throw IllegalStateException()
}

private def chainAst(ts: (Name, AstTerm)*)
  (block: Signature ?=> List[VTerm] => CTerm)
  (using NameContext)
  (using Signature): Either[AstError, CTerm] = chainAst(ts.toList)(block)

private def chainAst[T[_] : EitherFunctor](ts: T[(Name, AstTerm)])
  (block: Signature ?=> T[VTerm] => CTerm)
  (using NameContext)
  (using Signature): Either[AstError, CTerm] =
  val f = summon[EitherFunctor[T]]
  for ts <- f.map(ts) { case (n, t) => astToIr(t).map((n, _)) }
      r <- chain(ts) { (t, _) => block(t) }
  yield r

private def chainAstWithDefaultName[T[_] : EitherFunctor](defaultName: Name, ts: T[AstTerm])
  (block: Signature ?=> T[VTerm] => CTerm)
  (using NameContext)
  (using Signature): Either[AstError, CTerm] =
  val f = summon[EitherFunctor[T]]
  for ts <- f.map(ts) { t => astToIr(t).map((defaultName, _)) }
      r <- chain(ts) { (t, _) => block(t) }
  yield r

private def chain(name: Name, t: CTerm)
  (block: Signature ?=> (VTerm, Int) => CTerm)
  (using NameContext)
  (using Signature): Either[AstError, CTerm] = chain(List((name, t))) {
  case (v :: Nil, n) => block(v, n)
  case _ => throw IllegalStateException()
}

private def chain(ts: (Name, CTerm)*)
  (block: Signature ?=> (List[VTerm], Int) => CTerm)
  (using NameContext)
  (using Signature): Either[AstError, CTerm] = chain(ts.toList)(block)

private def chain[T[_] : EitherFunctor](ts: T[(Name, CTerm)])
  (block: Signature ?=> (T[VTerm], /* number of non-trivial computations bound */ Int) => CTerm)
  (using NameContext)
  (using Signature): Either[AstError, CTerm] =
  for r <- {
    // Step 1. Count the number of non-trivial computations present in the computation args.
    // This is used to populate DeBruijn index of let bound variables for these non-trivial
    // computations.
    var nonTrivialComputations = 0
    val f = summon[EitherFunctor[T]]
    f.map(ts) {
      case (_, Return(_)) => Right(())
      case _ => Right(nonTrivialComputations += 1)
    }
    val boundComputations = mutable.ArrayBuffer[(Name, CTerm)]()
    var index = 0
    // Step 2. Transform the computations into values and track non-trivial computations that
    // need to appear in let bindings. Weakening is performed where appropriate.
    for vTs <- f.map(ts) {
      case (_, Return(v)) => Right(v.weaken(nonTrivialComputations, 0))
      case (n, c) =>
        boundComputations.addOne((n, c.weaken(index, 0)))
        index += 1
        Right(Var(nonTrivialComputations - index))
    }
    yield boundComputations.foldRight(block(vTs, nonTrivialComputations)) { (elem, ctx) =>
      elem match
        case (n, t) => Let(t, ctx)(n)
    }
  }
  yield r

given listEitherFunctor: EitherFunctor[List[*]] with
  override def map[L, T, S](l: List[T])(g: T => Either[L, S]): Either[L, List[S]] =
    transpose(l.map(g))

given effectsEitherFunctor: EitherFunctor[[X] =>> (QualifiedName, List[X])] with
  override def map[L, T, S](l: (QualifiedName, List[T]))
    (g: T => Either[L, S]): Either[L, (QualifiedName, List[S])] =
    l match
      case (qn, ts) =>
        for ts <- listEitherFunctor.map(ts)(g)
        yield (qn, ts)

given elimsEitherFunctor: EitherFunctor[[X] =>> List[Elimination[X]]] with
  override def map[L, T, S](l: List[Elimination[T]])
    (g: T => Either[L, S]): Either[L, List[Elimination[S]]] =
    listEitherFunctor.map(l) {
      _ match
        case ETerm(t) => g(t).map(ETerm(_))
        case EProj(n) => Right(EProj(n))
    }

given listListEitherFunctor: EitherFunctor[[X] =>> List[List[X]]] with
  override def map[L, T, S](l: List[List[T]])
    (g: T => Either[L, S]): Either[L, List[List[S]]] =
    listEitherFunctor.map(l) {
      listEitherFunctor.map(_)(g)
    }

private trait EitherFunctor[F[_]]:
  def map[L, T, S](f: F[T])(g: T => Either[L, S]): Either[L, F[S]]