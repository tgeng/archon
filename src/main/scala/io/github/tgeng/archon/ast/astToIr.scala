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
import Elimination.*
import io.github.tgeng.archon.ir.Elimination.EProj

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
    chainAstWithDefaultName[[X] =>> List[(QualifiedName, List[X])]](gn"eArg", effects) {
      effs => Return(EffectsLiteral(ListSet(effs: _*)))
    }
  case AstLevelLiteral(level) => Right(Return(LevelLiteral(level)))
  case AstCellType(heap, ty, status) => chainAst((gn"heap", heap), (gn"ty", ty)) {
    case heap :: ty :: Nil => Return(CellType(heap, ty, status))
    case _ => throw IllegalStateException()
  }
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
  (block: Signature ?=> (T[VTerm], Int) => CTerm)
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

given effectsEitherFunctor: EitherFunctor[[X] =>> List[(QualifiedName, List[X])]] with
  override def map[L, T, S](l: List[(QualifiedName, List[T])])
    (g: T => Either[L, S]): Either[L, List[(QualifiedName, List[S])]] =
    l match
      case Nil => Right(Nil)
      case (qn, ts) :: rest =>
        for ts <- listEitherFunctor.map(ts)(g)
            rest <- map(rest)(g)
        yield (qn, ts) :: rest

given EitherFunctor[[X] =>> List[Elimination[X]]] with
  override def map[L, T, S](l: List[Elimination[T]])
    (g: T => Either[L, S]): Either[L, List[Elimination[S]]] =
    listEitherFunctor.map(l) {
      _ match
        case ETerm(t) => g(t).map(ETerm(_))
        case EProj(n) => Right(EProj(n))
    }

private trait EitherFunctor[F[_]]:
  def map[L, T, S](f: F[T])(g: T => Either[L, S]): Either[L, F[S]]