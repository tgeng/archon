package com.github.tgeng.archon.core.ir

import collection.mutable
import com.github.tgeng.archon.common.*
import com.github.tgeng.archon.common.eitherFilter.*
import com.github.tgeng.archon.core.common.*

import SourceInfo.*
import Declaration.*
import CTerm.*
import VTerm.*
import Pattern.*
import IrError.*
import Variance.*
import PreDeclaration.*
import CoPattern.*
import UnificationResult.*
import CaseTree.*
import java.security.Signer

private given Γ0: Context = IndexedSeq()
def elaborateSignature
  (data: PreData)
  (using Σ: Signature)
  (using ctx: TypingContext)
  : Either[IrError, Signature] =
  ctx.trace(s"elaborating data signature ${data.qn}") {
    def elaborateTy
      (ty: CTerm)
      (using Γ: Context)
      (using Signature)
      (using ctx: TypingContext)
      : Either[IrError, (TTelescope, ULevel, VTerm, VTerm)] =
      for
        ty <- reduceCType(ty)
        r <- ty match
          // Here and below we do not care about the declared effect types because data type
          // constructors are always total. Declaring non-total signature is not necessary (nor
          // desirable) but acceptable.
          case F(Type(Top(ul, usage, eqDecidability)), _, _) =>
            Right((Nil, ul, usage, eqDecidability))
          case F(t, _, _) => Left(ExpectVType(t))
          case FunctionType(binding, bodyTy, _) =>
            elaborateTy(bodyTy)(using Γ :+ binding).map {
              case (telescope, ul, usage, eqDecidability) =>
                ((binding, INVARIANT) :: telescope, ul, usage, eqDecidability)
            }
          case _ => Left(NotDataTypeType(ty))
      yield r

    for
      tParamTys <- elaborateTTelescope(data.tParamTys)
      elaboratedTy <- elaborateTy(data.ty)(using Γ0 ++ tParamTys.map(_._1))
    yield elaboratedTy match
      case (tIndices, ul, usage, eqDecidability) =>
        Σ.addDeclaration(
          Data(data.qn)(tParamTys.size, tParamTys ++ tIndices, ul, usage, eqDecidability)
        )
  }

def elaborateBody
  (preData: PreData)
  (using Σ: Signature)
  (using ctx: TypingContext)
  : Either[IrError, Signature] =
  ctx.trace(s"elaborating data body ${preData.qn}") {
    val data = Σ.getData(preData.qn)

    def elaborateTy
      (ty: CTerm)
      (using Γ: Context)
      (using Signature)
      (using ctx: TypingContext)
      : Either[IrError, (Telescope, /* args */ List[VTerm])] =
      for
        ty <- reduceCType(ty)
        r <- ty match
          // Here and below we do not care the declared effect types because data type constructors
          // are always total. Declaring non-total signature is not necessary (nor desirable) but
          // acceptable.
          case F(DataType(qn, args), _, _) if qn == data.qn && args.size == data.tParamTys.size =>
            Right((Nil, args))
          case F(t, _, _) => Left(ExpectDataType(t, Some(data.qn)))
          case FunctionType(binding, bodyTy, _) =>
            elaborateTy(bodyTy)(using Γ :+ binding).map { case (telescope, ul) =>
              (binding :: telescope, ul)
            }
          case _ => Left(NotDataTypeType(ty))
      yield r

    // number of index arguments
    given Context = data.tParamTys.map(_._1).toIndexedSeq

    val indexCount = data.tParamTys.size - preData.tParamTys.size
    preData.constructors.foldLeft[Either[IrError, Signature]](Right(Σ)) {
      case (Right(_Σ), constructor) =>
        given Signature = _Σ
        ctx.trace(s"elaborating constructor ${constructor.name}") {
          // weaken to accommodate data type indices
          val ty = constructor.ty.weaken(indexCount, 0)
          for case (paramTys, args) <- elaborateTy(ty)
          yield _Σ.addConstructor(Constructor(constructor.name, paramTys, args))
        }
      case (Left(e), _) => Left(e)
    }
  }

def elaborateSignature
  (record: PreRecord)
  (using Σ: Signature)
  (using ctx: TypingContext)
  : Either[IrError, Signature] =
  ctx.trace(s"elaborating record signature ${record.qn}") {
    for
      tParamTys <- elaborateTTelescope(record.tParamTys)
      ty <- reduceCType(record.ty)(using tParamTys.map(_._1).toIndexedSeq)
      r <- ty match
        case CType(CTop(ul, _), _) => Right(new Record(record.qn)(tParamTys, ul))
        case t                     => Left(ExpectCType(t))
    yield Σ.addDeclaration(r)
  }

def elaborateBody
  (preRecord: PreRecord)
  (using Σ: Signature)
  (using ctx: TypingContext)
  : Either[IrError, Signature] =
  ctx.trace(s"elaborating record body ${preRecord.qn}") {
    val record = Σ.getRecord(preRecord.qn)

    given SourceInfo = SiEmpty

    given Context = record.tParamTys.map(_._1).toIndexedSeq :+
      Binding(U(RecordType(record.qn, vars(record.tParamTys.size - 1))), ???)(
        record.selfName
      )

    preRecord.fields.foldLeft[Either[IrError, Signature]](Right(Σ)) {
      case (Right(_Σ), field) =>
        ctx.trace(s"elaborating field ${field.name}") {
          for ty <- reduceCType(field.ty)
          yield _Σ.addField(Field(field.name, ty))
        }
      case (Left(e), _) => Left(e)
    }
  }

def elaborateSignature
  (definition: PreDefinition)
  (using Σ: Signature)
  (using ctx: TypingContext)
  : Either[IrError, Signature] =
  given SourceInfo = SiEmpty

  ctx.trace(s"elaborating def signature ${definition.qn}") {
    for
      paramTys <- elaborateTelescope(definition.paramTys)
      ty <- reduceCType(definition.ty)(using paramTys.toIndexedSeq)
    yield Σ.addDeclaration(
      Definition(definition.qn)(
        paramTys.foldRight(ty) { (binding, bodyTy) =>
          FunctionType(binding, bodyTy)
        }
      )
    )
  }

def elaborateBody
  (preDefinition: PreDefinition)
  (using Σ: Signature)
  (using ctx: TypingContext)
  : Either[IrError, Signature] =

  // See [1] for how this part works.
  type Constraint =
    ( /* current split term */ VTerm, /* user pattern */ Pattern, /* type */ VTerm)

  case class ElabClause
    (
      constraints: List[Constraint],
      userPatterns: List[CoPattern],
      rhs: Option[CTerm],
      val source: PreClause
    )

  type Problem = List[ElabClause]

  def weaken(c: Constraint) = c match
    // Note: p is not weakened because p is a user pattern. It does not leave in the Γ being
    // assembled during elaboration.
    case (w, p, _A) => (w.weakened, p, _A.weakened)

  def solve
    (constraints: List[Constraint])
    (using Γ: Context)
    (using Σ: Signature)
    : Either[IrError, Option[PartialSubstitution[VTerm]]] =
    val σ = mutable.Map[Nat, VTerm]()
    matchPattern(constraints.map { case (w, p, _) => (p, w) }, σ) match
      case MatchingStatus.Matched =>
        for _ <- allRight(constraints.map { case (w, p, _A) =>
            p.toTerm match
              case Some(p) =>
                for
                  _ <- checkType(p, _A)
                  _ <- checkType(w, _A)
                  _ <- checkSubsumption(p.subst(σ.get), w, Some(_A))(using
                    CheckSubsumptionMode.CONVERSION
                  )
                yield ()
              case None => Left(UnexpectedAbsurdPattern(p))
          })
        yield Some(σ.get)
      case MatchingStatus.Mismatch | MatchingStatus.Stuck => Right(None)

  /** New var index is `Γ.size`. New var type is `_A`.
    */
  def shift(problem: Problem, _A: VTerm): Either[IrError, Problem] = problem match
    case Nil => Right(Nil)
    case ElabClause(_E, CPattern(p) :: q̅, rhs, source) :: problem =>
      for problem <- shift(problem, _A)
      yield ElabClause((Var(0), p, _A.weakened) :: _E.map(weaken), q̅, rhs, source) :: problem
    case ElabClause(_, q :: _, _, _) :: _   => Left(UnexpectedCProjection(q))
    case ElabClause(_, _, rhs, source) :: _ => Left(MissingUserCoPattern(source))

  def filter(problem: Problem, π: Name): Either[IrError, Problem] = problem match
    case Nil => Right(Nil)
    case ElabClause(_E, CProjection(π2) :: q̅, rhs, source) :: problem =>
      for problem <- filter(problem, π)
      yield
        if π == π2 then ElabClause(_E, q̅, rhs, source) :: problem
        else problem
    case ElabClause(_, q :: _, _, _) :: _       => Left(UnexpectedCPattern(q))
    case c @ ElabClause(_, _, rhs, source) :: _ => Left(MissingUserCoPattern(source))

  def subst
    (problem: Problem, σ: PartialSubstitution[VTerm])
    (using Σ: Signature)
    : Either[IrError, Problem] =
    def simplify
      (v: VTerm, p: Pattern, _A: VTerm)
      (using Σ: Signature)
      : Either[IrError, Option[List[Constraint]]] =
      // It's assumed that v is already normalized. The only place un-normalized term may appear
      // during elaboration is through unification. But unification pre-normalizes terms so in
      // here all terms are already normalized.
      (v, p) match
        case (DataType(qn, args), PDataType(pQn, pArgs)) if qn == pQn =>
          val data = Σ.getData(qn)
          // TODO[P3]: consider changing some of the following runtime error to IrErrors if user input
          // can cause it to happen.
          assert(args.size == pArgs.size && pArgs.size == data.tParamTys.size)
          simplifyAll(args.lazyZip(pArgs).lazyZip(data.tParamTys.map(_._1.ty)).toList)
        case (DataType(_, _), PDataType(_, _))                 => Right(None)
        case (DataType(qn, args), PForcedDataType(pQn, pArgs)) =>
          // TODO[P3]: instead of assert, report a use-friendly error if name doesn't match
          // because such a mismatch means the provided forced pattern is not correct.
          assert(qn == pQn)
          val data = Σ.getData(qn)
          // TODO[P3]: consider changing some of the following runtime error to IrErrors if user input
          // can cause it to happen.
          assert(args.size == pArgs.size && pArgs.size == data.tParamTys.size)
          simplifyAll(args.lazyZip(pArgs).lazyZip(data.tParamTys.map(_._1.ty)).toList)
        case (Con(name, args), PConstructor(pName, pArgs)) if name == pName =>
          // TODO[P3]: consider changing some of the following runtime error to IrErrors if user input
          // can cause it to happen.
          val dataType = _A.asInstanceOf[DataType]
          val constructor = Σ.getConstructor(dataType.qn, name)
          val _As = constructor.paramTys.substLowers(dataType.args: _*)
          assert(args.size == pArgs.size && pArgs.size == _As.size)
          simplifyAll(args.lazyZip(pArgs).lazyZip(_As.map(_.ty)).toList)
        case (Con(_, _), PConstructor(_, _))                     => Right(None)
        case (Con(name, args), PForcedConstructor(pName, pArgs)) =>
          // TODO[P3]: instead of assert, report a use-friendly error if name doesn't match
          // because such a mismatch means the provided forced pattern is not correct.
          assert(name == pName)
          val dataType = _A.asInstanceOf[DataType]
          val constructor = Σ.getConstructor(dataType.qn, name)
          val _As = constructor.paramTys.substLowers(dataType.args: _*)
          assert(args.size == pArgs.size && pArgs.size == _As.size)
          simplifyAll(args.lazyZip(pArgs).lazyZip(_As.map(_.ty)).toList)
        case (Refl(), PRefl()) =>
          // TODO[P3]: consider changing some of the following runtime error to IrErrors if user input
          // can cause it to happen.
          assert(_A.isInstanceOf[EqualityType])
          Right(Some(Nil))
        case _ => Right(Some(List((v, p, _A))))

    def simplifyAll
      (constraints: List[Constraint])
      (using Σ: Signature)
      : Either[IrError, Option[List[Constraint]]] =
      constraints match
        case Nil => Right(Some(Nil))
        case (v, p, _A) :: constraints =>
          for
            _E1 <- simplify(v, p, _A)
            _E2 <- simplifyAll(constraints)
          yield _E1.zip(_E2).map(_ ++ _)
    problem match
      case Nil => Right(Nil)
      case ElabClause(_E, q̅, rhs, source) :: problem =>
        for
          optionE <- simplifyAll(_E)
          r <- optionE match
            case Some(_E) =>
              for problem <- subst(problem, σ)
              yield ElabClause(_E, q̅, rhs, source) :: problem
            case None => subst(problem, σ)
        yield r

  def isEmpty(_A: VTerm)(using Γ: Context)(using Σ: Signature): Either[IrError, Boolean] =
    _A match
      case DataType(qn, _) => Right(Σ.getConstructors(qn).isEmpty)
      case EqualityType(_A, u, v) =>
        for u <- unify(u, v, _A)
        yield u match
          case UNo => true
          case _   => false
      case _ => Right(false)

  def elaborate
    (qn: QualifiedName, q̅ : List[CoPattern], _C: CTerm, problem: Problem)
    (using Γ: Context)
    (using Σ: Signature)
    : Either[IrError, (Signature, CaseTree)] =
    for
      _C <- reduceCType(_C)
      r <- problem match
        // cosplit
        case ElabClause(_E1, CProjection(π) :: q̅1, rhs1, source) :: _ => Right((???, ???))
        // cosplit empty
        // Note: here we don't require an absurd pattern like in [1]. Instead, we require no more 
        // user (projection) pattern. This seems more natural.
        case ElabClause(_E1, Nil, None, source) :: Nil =>
          _C match
            case RecordType(qn, _, _) =>
              Σ.getFields(qn).size match
                case 0 => Right(Σ, CtRecord(Map()))
                case _ => Left(MissingFieldsInCoPattern(source))
            case _ => Left(MissingUserCoPattern(source))
        // intro
        case ElabClause(_E1, (q @ CPattern(p)) :: q̅1, rhs1, source) :: _ =>
          _C match
            case FunctionType(binding, bodyTy, _) =>
              for
                _A <- shift(problem, binding.ty)
                case (_Σ1, _Q) <- elaborate(
                  qn,
                  q̅.map(_.weakened) :+ CPattern(PVar(0)),
                  bodyTy,
                  _A
                )
              yield (_Σ1, CtLambda(_Q)(binding.name))
            case _ => Left(UnexpectedCPattern(q))
        case ElabClause(_E1, Nil, rhs1, source) :: _ => Right((???, ???))
        case Nil                                     => Left(IncompleteClauses(qn))
    yield r

  ctx.trace(s"elaborating def body ${preDefinition.qn}") {
    for
      paramTys <- elaborateTelescope(preDefinition.paramTys)
      r <- {
        given Γ: Context = paramTys.toIndexedSeq
        Right(???)

        // transpose(
        //   preDefinition.clauses.zipWithIndex.flatMap { (clause, index) =>
        //     clause.rhs match
        //       case None => List()
        //       case Some(rhs) =>
        //         List(
        //           ctx.trace(s"elaborating clause $index") {
        //             for
        //               bindings <- elaborateTelescope(clause.bindings)
        //               ty <- reduceCType(clause.ty)(using Γ ++ bindings)
        //             yield
        //               val allBindings = paramTys ++ bindings
        //               Clause(
        //                 allBindings,
        //                 CoPattern.pVars(
        //                   allBindings.size - 1,
        //                   bindings.size
        //                 ) ++ clause.lhs,
        //                 rhs,
        //                 ty
        //               )
        //           }
        //         )
        //   }
        // )
      }
    yield r
  }

def elaborateSignature
  (effect: PreEffect)
  (using Σ: Signature)
  (using ctx: TypingContext)
  : Either[IrError, Signature] =
  ctx.trace(s"elaborating effect signature ${effect.qn}") {
    for tParamTys <- elaborateTelescope(effect.tParamTys)
    yield Σ.addDeclaration(Effect(effect.qn)(tParamTys))
  }

def elaborateBody
  (preEffect: PreEffect)
  (using Σ: Signature)
  (using ctx: TypingContext)
  : Either[IrError, Signature] =
  val effect = Σ.getEffect(preEffect.qn)

  given Context = effect.tParamTys.toIndexedSeq

  ctx.trace(s"elaborating effect body ${effect.qn}") {
    def elaborateTy
      (ty: CTerm)
      (using Γ: Context)
      (using Signature)
      (using ctx: TypingContext)
      : Either[
        IrError,
        (Telescope, /* operator return type */ VTerm, /* operator return usage */ VTerm)
      ] =
      for
        ty <- reduceCType(ty)
        r <- ty match
          // Here and below we do not care the declared effect types because data type constructors
          // are always total. Declaring non-total signature is not necessary (nor desirable) but
          // acceptable.
          case F(ty, effects, usage) =>
            assert(effects == Total)
            Right((Nil, ty, usage))
          case FunctionType(binding, bodyTy, effects) =>
            assert(effects == Total)
            elaborateTy(bodyTy)(using Γ :+ binding).map { case (telescope, ul, usage) =>
              (binding :: telescope, ul, usage)
            }
          case _ => Left(ExpectFType(ty))
      yield r

    preEffect.operators.foldLeft[Either[IrError, Signature]](Right(Σ)) {
      case (Right(_Σ), operator) =>
        given Signature = _Σ
        ctx.trace(s"elaborating operator ${operator.name}") {
          for case (paramTys, resultTy, usage) <- elaborateTy(operator.ty)
          yield _Σ.addOperator(Operator(operator.name, paramTys, resultTy, usage))
        }
      case (Left(e), _) => Left(e)
    }
  }

private def elaborateTTelescope
  (tTelescope: PreTTelescope)
  (using Γ: Context)
  (using Signature)
  (using ctx: TypingContext)
  : Either[IrError, TTelescope] =
  elaborateTelescope(tTelescope.map(_._1)).map(_.zip(tTelescope.map(_._2)))

private def elaborateTelescope
  (telescope: PreTelescope)
  (using Γ: Context)
  (using Signature)
  (using ctx: TypingContext)
  : Either[IrError, Telescope] = telescope match
  case Nil => Right(Nil)
  case binding :: telescope =>
    ctx.trace("elaborating telescope") {
      for
        ty <- reduceVType(binding.ty)
        newBinding = Binding(ty, ???)(binding.name)
        telescope <- elaborateTelescope(telescope)(using Γ :+ newBinding)
      yield newBinding :: telescope
    }

// [1] Jesper Cockx and Andreas Abel. 2018. Elaborating dependent (co)pattern matching. Proc. ACM
// Program. Lang. 2, ICFP, Article 75 (September 2018), 30 pages. https://doi.org/10.1145/3236770
