package com.github.tgeng.archon.core.ast

import scala.annotation.targetName
import com.github.tgeng.archon.common.*
import com.github.tgeng.archon.core.common.*
import com.github.tgeng.archon.core.ir.*

import collection.immutable.{Map, Set}
import collection.mutable
import AstTerm.*
import VTerm.*
import CTerm.*
import ULevel.*
import AstError.*
import Elimination.*
import AstPattern.*
import AstCoPattern.*
import Pattern.*
import CoPattern.*
import AstDeclaration.*
import Elimination.*
import PreDeclaration.*
import SourceInfo.*
import Ref.given

type NameContext = (Int, Map[Name, Int])

val emptyNameContext: NameContext = (0, Map.empty)

private def resolve
  (astVar: AstIdentifier)
  (using ctx: NameContext)
  (using Σ: TestSignature)
  : Either[AstError, Either[CTerm, VTerm]] =
  given SourceInfo = astVar.sourceInfo

  ctx._2.get(astVar.name) match
    case Some(dbNumber) => Right(Right(Var(ctx._1 - dbNumber - 1)))
    case None =>
      Σ.resolveOption(astVar.name) match
        case Some(qn) => Right(Left(Def(qn)))
        case None     => Left(UnresolvedIdentifier(astVar))

private def resolve
  (astPVar: AstPVar)
  (using ctx: NameContext)
  (using Σ: TestSignature)
  : Either[AstError, Pattern] =
  given SourceInfo = astPVar.sourceInfo

  ctx._2.get(astPVar.name) match
    case None           => Left(UnresolvedPVar(astPVar))
    case Some(dbNumber) => Right(PVar(ctx._1 - dbNumber - 1))

private def bind[T](name: Name)(block: NameContext ?=> T)(using ctx: NameContext): T =
  block(using ctx :+ name)

private def bind[T](names: List[Name])(block: NameContext ?=> T)(using ctx: NameContext): T =
  block(using ctx ++ names)

extension(ctx: NameContext)
  private def :+(name: Name) = (ctx._1 + 1, ctx._2.updated(name, ctx._1))
  private def ++(names: collection.Seq[Name]) = (
    ctx._1 + names.size,
    names.zipWithIndex.foldLeft(
      ctx._2
    ) { (map, tuple) =>
      tuple match
        case (name, offset) => map.updated(name, ctx._1 + offset)
    }
  )

object NameContext:
  def fromContext(ctx: Context): NameContext =
    emptyNameContext ++ ctx.map(_.name.value)

def astToIr
  (moduleQn: QualifiedName, decl: AstDeclaration)
  (using Σ: TestSignature)
  : Either[AstError, PreDeclaration] =
  given NameContext = emptyNameContext

  decl match
    case AstData(name, tParamTys, ty, isPure, constructors) =>
      astToIr(tParamTys) {
        for
          ty <- astToIr(ty)
          constructors <- transpose(
            constructors.map { constructor =>
              astToIr(constructor.ty)
                .map(PreConstructor(constructor.name, _))
            }
          )
        yield (ty, constructors)
      }.map { case (tParamTys, (ty, constructors)) =>
        PreData(moduleQn / name)(
          tParamTys,
          ty,
          constructors
        )
      }
    case AstRecord(name, tParamTys, ty, fields) =>
      astToIr(tParamTys) {
        for
          ty <- astToIr(ty)
          fields <- bind(n"self") {
            transpose(
              fields.map { field =>
                astToIr(field.ty)
                  .map(Field(field.name, _))
              }
            )
          }
        yield (ty, fields)
      }.map { case (tParamTys, (ty, fields)) =>
        PreRecord(moduleQn / name)(tParamTys, ty, fields)
      }
    case AstDefinition(name, paramTys, ty, clauses) =>
      astToIr(paramTys) {
        for
          ty <- astToIr(ty)
          clauses <- transpose(
            clauses.map { clause =>
              astToIr(clause.bindings) {
                for
                  lhs <- transpose(clause.lhs.map(astToIr))
                  rhs <- clause.rhs match
                    case None    => Right(None)
                    case Some(t) => astToIr(t).map(Some(_))
                  ty <- astToIr(clause.ty)
                yield (lhs, rhs, ty)
              }.map { case (bindings, (lhs, rhs, ty)) =>
                PreClause(???, lhs, rhs)
              }
            }
          )
        yield (ty, clauses)
      }.map { case (paramTys, (ty, clauses)) =>
        PreDefinition(moduleQn / name)(paramTys, ty, clauses)
      }
    case AstEffect(name, tParamTys, operators) =>
      astToIr(tParamTys) {
        transpose(
          operators.map { operator =>
            for ty <- astToIr(operator.ty)
            yield PreOperator(operator.name, ty)
          }
        )
      }.map { case (tParamTys, operators) =>
        PreEffect(moduleQn / name)(tParamTys, operators)
      }

@targetName("astToIrTContext")
private def astToIr[T]
  (tTelescope: AstTContext)
  (action: NameContext ?=> Either[AstError, T])
  (using ctx: NameContext)
  (using Σ: TestSignature)
  : Either[AstError, (PreTContext, T)] =
  astToIr(tTelescope.map(_._1))(action)
    .map { case (telescope, t) =>
      (telescope.zip(tTelescope.map(_._2)), t)
    }

@targetName("astToIrTelescope")
private def astToIr[T]
  (telescope: AstTelescope)
  (action: NameContext ?=> Either[AstError, T])
  (using ctx: NameContext)
  (using
    Σ: TestSignature
  )
  : Either[AstError, (PreContext, T)] = telescope match
  case Nil => action.map((Nil, _))
  case binding :: telescope =>
    for
      ty <- astToIr(binding.ty)
      r <- bind(binding.name.value) {
        astToIr(telescope)(action)
      }
    yield r match
      case (tys, t) => (Binding(ty, ???)(binding.name) :: tys, t)

def astToIr
  (ast: AstCoPattern)
  (using ctx: NameContext)
  (using Σ: TestSignature)
  : Either[AstError, CoPattern] =
  given SourceInfo = ast.sourceInfo

  ast match
    case AstCPattern(p) =>
      for p <- astToIr(p)
      yield CPattern(p)
    case AstCProjection(name) => Right(CProjection(name))

def astToIr
  (ast: AstPattern)
  (using ctx: NameContext)
  (using Σ: TestSignature)
  : Either[AstError, Pattern] =
  given SourceInfo = ast.sourceInfo

  ast match
    case v: AstPVar => resolve(v)
    case AstPConstructor(name, args) =>
      Σ.resolveOption(name) match
        case Some(qn) =>
          Σ.getDataOption(qn) match
            case Some(_) => transpose(args.map(astToIr)).map(PDataType(qn, _))
            case _       => transpose(args.map(astToIr)).map(PConstructor(name, _))
        case None => Left(UnresolvedNameInPattern(name))
    case AstPForcedConstructor(name, args) =>
      Σ.resolveOption(name) match
        case Some(qn) =>
          Σ.getDataOption(qn) match
            case Some(_) =>
              transpose(args.map(astToIr)).map(PForcedDataType(qn, _))
            case _ =>
              transpose(args.map(astToIr)).map(PForcedConstructor(name, _))
        case None => Left(UnresolvedNameInPattern(name))
    case AstPForced(term) =>
      for cTerm <- astToIr(term)
      yield PForced(Collapse(cTerm))
    case AstPAbsurd() => Right(PAbsurd())

def astToIr
  (ast: AstTerm)
  (using ctx: NameContext)
  (using Σ: TestSignature)
  : Either[AstError, CTerm] =
  given SourceInfo = ast.sourceInfo

  ast match
    case AstDef(qn) => Right(Def(qn))
    case v: AstIdentifier =>
      for v <- resolve(v)
      yield v match
        case Right(v) => Return(v)
        case Left(c)  => c
    case AstCollapse(c) =>
      for c <- astToIr(c)
      yield Return(Collapse(c))
    case AstU(cty) =>
      for cty <- astToIr(cty)
      yield Return(U(cty))
    case AstThunk(c) =>
      for c <- astToIr(c)
      yield Return(Thunk(c))
    case AstLevelLiteral(level) => Right(Return(LevelLiteral(level)))
    case AstForce(v)            => chainAst(gn"v", v)(Force(_))
    case AstF(vTy, effects) =>
      chainAst((gn"T", vTy), (gn"e", effects)) {
        case vTy :: effects :: Nil => F(vTy, effects)
        case _                     => throw IllegalStateException()
      }
    case AstFunctionType(argName, argTy, bodyTy, effects) =>
      for
        argTy <- astToIr(argTy)
        effects <- bind(argName) {
          astToIr(effects)
        }
        bodyTy <- bind(argName) {
          astToIr(bodyTy)
        }
        r <- chain((gn"T", argTy), (gn"e", effects)) {
          case (argTy :: effects :: Nil, n) =>
            FunctionType(
              Binding(argTy, ???)(argName),
              bodyTy.weaken(n, 1),
              effects
            )
          case _ => throw IllegalStateException()
        }
      yield r
    case AstRedux(head, elims) =>
      for
        head <- astToIr(head)
        r <- chainAstWithDefaultName[[X] =>> List[Elimination[X]]](
          gn"a",
          elims
        ) { (terms, offset) =>
          terms.foldLeft(head.weaken(offset, 0)) { (c, e) =>
            e match
              case ETerm(v) =>
                Application(c, v)(using siMerge(c.sourceInfo, e.sourceInfo))
              case EProj(n) =>
                Projection(c, n)(using siMerge(c.sourceInfo, e.sourceInfo))
          }
        }
      yield r
    case AstBlock(statements) =>
      import Statement.*
      def foldSequence
        (statements: List[Statement])
        (using ctx: NameContext)
        : Either[AstError, CTerm] =
        statements match
          case Nil                         => Right(Def(Builtins.MkMkUnitQn))
          case STerm(astTerm) :: Nil       => astToIr(astTerm)
          case SBinding(_, astTerm) :: Nil => astToIr(astTerm)
          case STerm(t) :: rest =>
            val name = Name.Unreferenced
            for
              t <- astToIr(t)
              ctx <- bind(name) {
                foldSequence(rest)
              }
            yield Let(t, ctx)(name)
          case SBinding(name, t) :: rest =>
            for
              t <- astToIr(t)
              ctx <- bind(name) {
                foldSequence(rest)
              }
            yield Let(t, ctx)(name)
          case SHandler(
              (effName, effArgs),
              outputEffects,
              outputType,
              transformInputName,
              transform,
              handlers
            ) :: rest =>
            for
              effArgs <- transpose(effArgs.map(astToIr))
              outputEffects <- astToIr(outputEffects)
              outputType <- astToIr(outputType)
              transform <- bind(transformInputName) {
                astToIr(transform)
              }
              handlersBoundNames = handlers.view
                .mapValues(tuple => (tuple._1.map(MutableRef(_)), MutableRef(n"resume")))
                .toMap
              handlers <- transposeValues(
                handlers.view.mapValues { (argNames, astTerm) =>
                  bind(argNames :+ n"resume") {
                    astToIr(astTerm).map((argNames.size + 1, _))
                  }
                }.toMap
              )
              input <- foldSequence(rest)
              r <- chain[[X] =>> List[List[X]]](
                effArgs.map((gn"a", _)) :: List((gn"e", outputEffects)) :: List(
                  (gn"R", outputType)
                ) :: Nil
              ) {
                case (
                    effArgs :: List(outputEffects) :: List(outputType) :: Nil,
                    n
                  ) =>
                  Handler(
                    (Σ.resolve(effName), effArgs),
                    outputEffects,
                    outputType,
                    ???,
                    transform.weaken(n, 1),
                    handlers.view.mapValues { case (bar, t) =>
                      t.weaken(n, bar)
                    }.toMap,
                    input.weaken(n, 0)
                  )(transformInputName, handlersBoundNames)
                case _ => throw IllegalStateException()
              }
            yield r
          case SHeapHandler(
              outputEffects,
              heapVarName
            ) :: rest =>
            for
              outputEffects <- astToIr(outputEffects)
              input <- bind(heapVarName) {
                foldSequence(rest)
              }
              r <- chain(gn"e", outputEffects) { case (outputEffects, n) =>
                HeapHandler(
                  outputEffects,
                  None,
                  IndexedSeq(),
                  input.weaken(n, 1)
                )(heapVarName)
              }
            yield r

      foldSequence(statements)

private def astToIr
  (elim: Elimination[AstTerm])
  (using ctx: NameContext)
  (using Σ: TestSignature)
  : Either[AstError, Elimination[CTerm]] = elim match
  case ETerm(astTerm) =>
    astToIr(astTerm).map(ETerm(_)(using astTerm.sourceInfo))
  case EProj(name) => Right(EProj(name)(using elim.sourceInfo))

private def chainAst
  (name: Name, t: AstTerm)
  (block: TestSignature ?=> VTerm => CTerm)
  (using NameContext)
  (using TestSignature)
  : Either[AstError, CTerm] =
  chainAst(List((name, t))) {
    case v :: Nil => block(v)
    case _        => throw IllegalStateException()
  }

private def chainAst
  (ts: (Name, AstTerm)*)
  (block: TestSignature ?=> List[VTerm] => CTerm)
  (using NameContext)
  (using TestSignature)
  : Either[AstError, CTerm] =
  chainAst(ts.toList)(block)

private def chainAst[T[_]: EitherFunctor]
  (ts: T[(Name, AstTerm)])
  (block: TestSignature ?=> T[VTerm] => CTerm)
  (using NameContext)
  (using TestSignature)
  : Either[AstError, CTerm] =
  val f = summon[EitherFunctor[T]]
  for
    ts <- f.map(ts) { case (n, t) => astToIr(t).map((n, _)) }
    r <- chain(ts) { (t, _) => block(t) }
  yield r

private def chainAstWithDefaultName[T[_]: EitherFunctor]
  (defaultName: Name, ts: T[AstTerm])
  (block: TestSignature ?=> (T[VTerm], Nat) => CTerm)
  (using NameContext)
  (using TestSignature)
  : Either[AstError, CTerm] =
  val f = summon[EitherFunctor[T]]
  for
    ts <- f.map(ts) { t => astToIr(t).map((defaultName, _)) }
    r <- chain(ts) { (t, offset) => block(t, offset) }
  yield r

private def chain
  (name: Name, t: CTerm)
  (block: TestSignature ?=> (VTerm, Int) => CTerm)
  (using NameContext)
  (using TestSignature)
  : Either[AstError, CTerm] =
  chain(List((name, t))) {
    case (v :: Nil, n) => block(v, n)
    case _             => throw IllegalStateException()
  }

private def chain
  (ts: (Name, CTerm)*)
  (block: TestSignature ?=> (List[VTerm], Int) => CTerm)
  (using NameContext)
  (using TestSignature)
  : Either[AstError, CTerm] =
  chain(ts.toList)(block)

private def chain[T[_]: EitherFunctor]
  (ts: T[(Name, CTerm)])
  (
    block: TestSignature ?=> (
      T[VTerm], /* number of non-trivial computations bound */ Int
    ) => CTerm
  )
  (using NameContext)
  (using TestSignature)
  : Either[AstError, CTerm] =
  for r <- {
      // Step 1. Count the number of non-trivial computations present in the computation args.
      // This is used to populate DeBruijn index of let bound variables for these non-trivial
      // computations.
      var nonTrivialComputations = 0
      val f = summon[EitherFunctor[T]]
      f.map(ts) {
        case (_, Return(_, _)) => Right(())
        case _                 => Right(nonTrivialComputations += 1)
      }
      val boundComputations = mutable.ArrayBuffer[(Name, CTerm)]()
      var index = 0
      // Step 2. Transform the computations into values and track non-trivial computations that
      // need to appear in let bindings. Weakening is performed where appropriate.
      for vTs <- f.map(ts) {
          case (_, Return(v, _)) => Right(v.weaken(nonTrivialComputations, 0))
          case (n, c) =>
            boundComputations.addOne((n, c.weaken(index, 0)))
            index += 1
            Right(Var(nonTrivialComputations - index)(using SiEmpty))
        }
      yield boundComputations.foldRight(block(vTs, nonTrivialComputations)) { (elem, ctx) =>
        elem match
          case (n, t) =>
            Let(t, ctx)(n)(using siMerge(elem._2.sourceInfo, ctx.sourceInfo))
      }
    }
  yield r

given listEitherFunctor: EitherFunctor[List[*]] with
  override def map[L, T, S](l: List[T])(g: T => Either[L, S]): Either[L, List[S]] =
    transpose(l.map(g))

given effectsEitherFunctor: EitherFunctor[[X] =>> (QualifiedName, List[X])] with
  override def map[L, T, S]
    (l: (QualifiedName, List[T]))
    (g: T => Either[L, S])
    : Either[L, (QualifiedName, List[S])] =
    l match
      case (qn, ts) =>
        for ts <- listEitherFunctor.map(ts)(g)
        yield (qn, ts)

given elimsEitherFunctor: EitherFunctor[[X] =>> List[Elimination[X]]] with
  override def map[L, T, S]
    (l: List[Elimination[T]])
    (g: T => Either[L, S])
    : Either[L, List[Elimination[S]]] =
    listEitherFunctor.map(l) {
      _ match
        case e @ ETerm(t) => g(t).map(ETerm(_)(using e.sourceInfo))
        case e @ EProj(n) => Right(EProj(n)(using e.sourceInfo))
    }

given listListEitherFunctor: EitherFunctor[[X] =>> List[List[X]]] with
  override def map[L, T, S](l: List[List[T]])(g: T => Either[L, S]): Either[L, List[List[S]]] =
    listEitherFunctor.map(l) {
      listEitherFunctor.map(_)(g)
    }

private trait EitherFunctor[F[_]]:
  def map[L, T, S](f: F[T])(g: T => Either[L, S]): Either[L, F[S]]
