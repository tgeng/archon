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
import com.github.tgeng.archon.parser.combinators.P
import scala.NonEmptyTuple
import scala.Conversion

def elaborateAll
  (declarations: Seq[PreDeclaration])
  (using Σ: Signature)
  (using ctx: TypingContext)
  : Either[IrError, Signature] =
  for
    decls <- sortPreDeclarations(declarations)
    r <- decls.foldLeft[Either[IrError, Signature]](Right(Σ)) {
      case (Left(e), _)              => Left(e)
      case (Right(_Σ), (part, decl)) => elaborate(part, decl)(using _Σ)
    }
  yield r

def elaborate
  (part: DeclarationPart, decl: PreDeclaration)
  (using Σ: Signature)
  (using ctx: TypingContext)
  : Either[IrError, Signature] = (part, decl) match
  case (DeclarationPart.HEAD, d: PreData)       => elaborateHead(d)
  case (DeclarationPart.HEAD, d: PreRecord)     => elaborateHead(d)
  case (DeclarationPart.HEAD, d: PreDefinition) => elaborateHead(d)
  case (DeclarationPart.HEAD, d: PreEffect)     => elaborateHead(d)
  case (DeclarationPart.BODY, d: PreData)       => elaborateBody(d)
  case (DeclarationPart.BODY, d: PreRecord)     => elaborateBody(d)
  case (DeclarationPart.BODY, d: PreDefinition) => elaborateBody(d)
  case (DeclarationPart.BODY, d: PreEffect)     => elaborateBody(d)

enum DeclarationPart:
  case HEAD, BODY

import DeclarationPart.*
import com.github.tgeng.archon.core.ir.{UnificationResult, unifyAll}

def sortPreDeclarations
  (declarations: Seq[PreDeclaration])
  (using Σ: Signature)
  : Either[IrError, Seq[(DeclarationPart, PreDeclaration)]] =
  given Unit = ()

  val declByQn = declarations.associatedBy(_.qn)
  val sigRefQn = declarations
    .associatedBy(
      _.qn,
      {
        case data: PreData =>
          QualifiedNameVisitor.combine(
            QualifiedNameVisitor.visitPreTContext(data.tParamTys),
            data.ty.visitWith(QualifiedNameVisitor),
          )
        case record: PreRecord =>
          QualifiedNameVisitor.combine(
            QualifiedNameVisitor.visitPreTContext(record.tParamTys),
            record.ty.visitWith(QualifiedNameVisitor),
          )
        case definition: PreDefinition =>
          definition.ty.visitWith(QualifiedNameVisitor)
        case effect: PreEffect =>
          QualifiedNameVisitor.visitPreContext(effect.tParamTys)
      },
    )
    .view
    .mapValues(_ & declByQn.keySet)
    .toMap

  val bodyRefQn = declarations
    .associatedBy(
      _.qn,
      {
        case data: PreData =>
          QualifiedNameVisitor.combine(
            data.constructors.map { constructor =>
              constructor.ty.visitWith(QualifiedNameVisitor)
            }: _*,
          ) + data.qn
        case record: PreRecord =>
          QualifiedNameVisitor.combine(
            record.fields.map { field =>
              field.ty.visitWith(QualifiedNameVisitor)
            }: _*,
          ) + record.qn
        case definition: PreDefinition =>
          QualifiedNameVisitor.combine(
            definition.clauses.flatMap { clause =>
              clause.lhs.map(QualifiedNameVisitor.visitCoPattern(_)) ++
                clause.rhs.map(QualifiedNameVisitor.visitCTerm(_))
            }: _*,
          ) + definition.qn
        case effect: PreEffect =>
          QualifiedNameVisitor.combine(
            effect.operations.map { operation =>
              operation.ty.visitWith(QualifiedNameVisitor)
            }: _*,
          ) + effect.qn
      },
    )
    .view
    .mapValues(_ & declByQn.keySet)
    .toMap

  // rule:
  //   1. any reference of A needs the signature of A, regardless whether it's in the signature or body of some declarations
  //   2. any reference of A in a signature means the accompanied body needs full definition of A
  topologicalSort(
    declarations.flatMap(decl => Seq((HEAD, decl), (BODY, decl))),
  ) {
    case (HEAD, decl) =>
      sigRefQn.get(decl.qn) match
        case Some(qns) => qns.toSeq.sorted.map(qn => (HEAD, declByQn(qn)))
        case None      => Seq()
    case (BODY, decl) =>
      sigRefQn.get(decl.qn) match
        case Some(qns) =>
          qns.toSeq.sorted.map(qn => (BODY, declByQn(qn))) ++
            (bodyRefQn(decl.qn) -- qns).toSeq.sorted.map(qn => (HEAD, declByQn(qn)))
        case None => Seq()
  } match
    case Right(decls) => Right(decls)
    case Left(cycle)  => Left(CyclicDeclarations(cycle))

private object QualifiedNameVisitor extends Visitor[Unit, Set[QualifiedName]]:

  override def combine
    (rs: Set[QualifiedName]*)
    (using ctx: Unit)
    (using
      Σ: Signature,
    )
    : Set[QualifiedName] = rs.flatten.toSet

  override def visitQualifiedName
    (qn: QualifiedName)
    (using ctx: Unit)
    (using Σ: Signature)
    : Set[QualifiedName] = Set(qn)

end QualifiedNameVisitor

private given Γ0: Context = IndexedSeq()
private def elaborateHead
  (preData: PreData)
  (using Σ: Signature)
  (using ctx: TypingContext)
  : Either[IrError, Signature] =
  ctx.trace(s"elaborating data signature ${preData.qn}") {
    def elaborateTy
      (ty: CTerm)
      (using Γ: Context)
      (using Signature)
      (using ctx: TypingContext)
      : Either[IrError, (Telescope, ULevel, VTerm)] =
      for
        ty <- reduceCType(ty)
        r <- ty match
          // Here and below we do not care about the declared effect types because data type
          // constructors are always total. Declaring non-total signature is not necessary (nor
          // desirable) but acceptable.
          case F(Type(Top(ul, eqDecidability)), _, _) =>
            Right((Nil, ul, eqDecidability))
          case F(t, _, _) => Left(ExpectVType(t))
          case FunctionType(binding, bodyTy, _) =>
            elaborateTy(bodyTy)(using Γ :+ binding).map { case (telescope, ul, eqDecidability) =>
              (binding +: telescope, ul, eqDecidability)
            }
          case _ => Left(NotDataTypeType(ty))
      yield r

    for
      tParamTys <- elaborateTContext(preData.tParamTys)
      case (tIndices, ul, eqDecidability) <- elaborateTy(preData.ty)(using
        Γ0 ++ tParamTys.map(_._1),
      )
      data = new Data(preData.qn)(
        tParamTys,
        tIndices,
        ul,
        eqDecidability,
      )
      _ <- checkData(data)
    yield Σ.addDeclaration(data)
  }

private def elaborateBody
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
      : Either[IrError, (Telescope, /* constructor tArgs */ List[VTerm])] =
      for
        ty <- reduceCType(ty)
        r <- ty match
          // Here and below we do not care the declared effect types because data type constructors
          // are always total. Declaring non-total signature is not necessary (nor desirable) but
          // acceptable.
          // TODO: report better error if `qn`, arg count, or param args (not refs to those bound at
          //  data declaration) are unexpected.
          case F(DataType(qn, args), _, _)
            if qn == data.qn && args.size == data.tParamTys.size + data.tIndexTys.size =>
            // Drop parameter args because Constructor.tArgs only track index args
            // TODO: check and report invalid args
            Right((Nil, args.drop(data.tParamTys.size)))
          case F(t, _, _) => Left(ExpectDataType(t, Some(data.qn)))
          case FunctionType(binding, bodyTy, _) =>
            elaborateTy(bodyTy)(using Γ :+ binding).map { case (telescope, ul) =>
              (binding :: telescope, ul)
            }
          case _ => Left(NotDataTypeType(ty))
      yield r

    // number of index arguments
    given Context = data.tParamTys.map(_._1)

    preData.constructors.foldLeft[Either[IrError, Signature]](Right(Σ)) {
      case (Right(_Σ), constructor) =>
        given Signature = _Σ
        ctx.trace(s"elaborating constructor ${constructor.name}") {
          val ty = constructor.ty
          for
            case (paramTys, tArgs) <- elaborateTy(ty)
            con = new Constructor(constructor.name, paramTys, tArgs)
            _ <- checkDataConstructor(preData.qn, con)
          yield _Σ.addConstructor(preData.qn, con)
        }
      case (Left(e), _) => Left(e)
    }
  }

private def elaborateHead
  (record: PreRecord)
  (using Σ: Signature)
  (using ctx: TypingContext)
  : Either[IrError, Signature] =
  ctx.trace(s"elaborating record signature ${record.qn}") {
    for
      tParamTys <- elaborateTContext(record.tParamTys)
      ty <- reduceCType(record.ty)(using tParamTys.map(_._1).toIndexedSeq)
      r <- ty match
        case CType(CTop(ul, _), _) => Right(new Record(record.qn)(tParamTys, ul))
        case t                     => Left(ExpectCType(t))
      _ <- checkRecord(r)
    yield Σ.addDeclaration(r)
  }

private def elaborateBody
  (preRecord: PreRecord)
  (using Σ: Signature)
  (using ctx: TypingContext)
  : Either[IrError, Signature] =
  ctx.trace(s"elaborating record body ${preRecord.qn}") {
    val record = Σ.getRecord(preRecord.qn)

    given SourceInfo = SiEmpty

    given Context = record.tParamTys.map(_._1).toIndexedSeq :+
      Binding(U(RecordType(record.qn, vars(record.tParamTys.size - 1))), Total)(
        record.selfName,
      )

    preRecord.fields.foldLeft[Either[IrError, Signature]](Right(Σ)) {
      case (Right(_Σ), field) =>
        ctx.trace(s"elaborating field ${field.name}") {
          for
            ty <- reduceCType(field.ty)
            f = new Field(field.name, ty)
            _ <- checkRecordField(preRecord.qn, f)
          yield _Σ.addField(preRecord.qn, f)
        }
      case (Left(e), _) => Left(e)
    }
  }

private def elaborateHead
  (definition: PreDefinition)
  (using Σ: Signature)
  (using ctx: TypingContext)
  : Either[IrError, Signature] =
  given SourceInfo = SiEmpty

  ctx.trace(s"elaborating def signature ${definition.qn}") {
    for
      paramTys <- elaborateContext(definition.paramTys)
      ty <- reduceCType(definition.ty)(using paramTys.toIndexedSeq)
      d = new Definition(definition.qn)(
        paramTys.foldRight(ty) { (binding, bodyTy) =>
          FunctionType(binding, bodyTy)
        },
      )
      d <- checkDef(d)
      // TODO: use rewritten term here
    yield Σ.addDeclaration(d)
  }

private def elaborateBody
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
      val source: PreClause,
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
        for _ <- allRight(constraints.map { case (w, pattern, _A) =>
            pattern.toTerm match
              case Some(p) =>
                for
                  (p, _) <- checkType(p, _A)
                  (w, _) <- checkType(w, _A)
                  constraint <- checkSubsumption(p.subst(σ.get), w, Some(_A))(using
                    CheckSubsumptionMode.CONVERSION,
                  )
                  _ <- if constraint.isEmpty then Right(()) else Left(UnmatchedPattern(pattern, w, constraint))
                yield ()
              case None => Left(UnexpectedAbsurdPattern(pattern))
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
          assert(
            args.size == pArgs.size && pArgs.size == data.tParamTys.size + data.tIndexTys.size,
          )
          simplifyAll(
            args
              .lazyZip(pArgs)
              .lazyZip(data.tParamTys.map(_._1.ty) ++ data.tIndexTys.map(_.ty))
              .toList,
          )
        case (DataType(_, _), PDataType(_, _))                 => Right(None)
        case (DataType(qn, args), PForcedDataType(pQn, pArgs)) =>
          // TODO[P3]: instead of assert, report a use-friendly error if name doesn't match
          // because such a mismatch means the provided forced pattern is not correct.
          assert(qn == pQn)
          val data = Σ.getData(qn)
          // TODO[P3]: consider changing some of the following runtime error to IrErrors if user input
          // can cause it to happen.
          assert(
            args.size == pArgs.size && pArgs.size == data.tParamTys.size + data.tIndexTys.size,
          )
          simplifyAll(
            args
              .lazyZip(pArgs)
              .lazyZip(data.tParamTys.map(_._1.ty) ++ data.tIndexTys.map(_.ty))
              .toList,
          )
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
          optionE <- simplifyAll(_E.map { case (v, p, _A) => (v.subst(σ), p, _A) })
          r <- optionE match
            case Some(_E) =>
              for problem <- subst(problem, σ)
              yield ElabClause(_E, q̅, rhs, source) :: problem
            case None => subst(problem, σ)
        yield r

  def apply(qn: QualifiedName, q̅ : List[CoPattern]): CTerm = Redux(Def(qn), q̅.map(_.toElimination.get))

  def elaborate
    (q̅ : List[CoPattern], _C: CTerm, problem: Problem)
    (using Γ: Context)
    (using Σ: Signature)
    : Either[IrError, (Signature, CaseTree)] =
    for
      _C <- reduceCType(_C)
      r <- (problem, _C) match
        // [cosplit]
        case (
            ElabClause(_E1, (p @ CProjection(_)) :: q̅1, rhs1, source) :: _,
            RecordType(qn, args, _),
          ) =>
          Σ.getFields(qn)
            .foldLeft[Either[IrError, (Signature, Map[Name, CaseTree])]](Right((Σ, Map()))) {
              case (Right((_Σ, fields)), field) =>
                for
                  problem <- filter(problem, field.name)
                  case (_Σ, ct) <- elaborate(
                    q̅ :+ CProjection(field.name),
                    field.ty.substLowers(args :+ Thunk(apply(qn, q̅)): _*),
                    problem,
                  )(using Γ)(using _Σ)
                yield (_Σ, fields + (field.name -> ct))
              case (Left(e), _) => Left(e)
            }
            .map { case (_Σ, fields) => (_Σ, CtRecord(fields)) }
        // [cosplit empty]
        // Note: here we don't require an absurd pattern like in [1]. Instead, we require no more
        // user (projection) pattern. This seems more natural.
        case (ElabClause(_E1, Nil, None, source) :: _, RecordType(qn, _, _)) =>
          Σ.getFields(qn).size match
            // There is no need to modify Σ because empty record does not have any clause
            case 0 => Right(Σ, CtRecord(Map()))
            case _ => Left(MissingFieldsInCoPattern(source))
        // [intro]
        case (
            ElabClause(_E1, (q @ CPattern(p)) :: q̅1, rhs1, source) :: _,
            FunctionType(binding, bodyTy, _),
          ) =>
          for
            _A <- shift(problem, binding.ty)
            case (_Σ1, _Q) <- elaborate(
              q̅.map(_.weakened) :+ CPattern(PVar(0)),
              bodyTy,
              _A,
            )
          yield (_Σ1, CtLambda(_Q)(binding.name))
        // mismatch between copattern and _C
        case (ElabClause(_, q :: _, _, source) :: _, _) =>
          Left(UnexpectedUserCoPattern(source, q))
        // All copatterns are introduced. Now start doing split
        case (ElabClause(_E1, Nil, _, _) :: _, _) =>
          def split
            (q̅ : List[CoPattern], _C: CTerm, problem: Problem)
            (using Γ: Context)
            (using Σ: Signature)
            : Either[IrError, (Signature, CaseTree)] =
            val ElabClause(_E1, _, rhs1, source1) = problem(0)

            def providedAtLeastU1Usage(x: Var): Boolean =
              checkUsageSubsumption(UsageLiteral(Usage.U1), Γ.resolve(x).usage)(using
                CheckSubsumptionMode.SUBSUMPTION,
              ) match
                case Right(constraint) if constraint.isEmpty => true
                case _        => false

            // Find something to split.
            _E1.foldLeft[Either[IrError, (Signature, CaseTree)]](
              // Start with a very generic error in case no split actions can be taken at all.
              Left(UnsolvedElaboration(source1)),
            ) {
              // If a split action was successful, skip any further actions on the remaining
              // constraints.
              case (Right(r), _) => Right(r)

              // split data type
              case (_, (x: Var, PDataType(qn, args), _A)) =>
                if !providedAtLeastU1Usage(x) then
                  Left(InsufficientResourceForSplit(x, Γ.resolve(x)))
                else
                  val (_Γ1, binding, _Γ2) = Γ.split(x)
                  assert(
                    binding.ty.weaken(_Γ2.size + 1, 0) == _A,
                    "these types should be identical because they are created by [intro]",
                  )
                  // 1. collect used types among clauses as {Qn_1, Qn_2, .. Qn_k}. Here the first
                  //    `None` is the default catch-all case.
                  val qns: List[Option[QualifiedName]] = None ::
                    (for
                      case ElabClause(constraints, _, _, _) <- problem
                      case (y: Var, PDataType(qn, _), _) <- constraints
                      if x == y
                    yield Some(qn))

                  //  2. do case split with {Qn_1, Qn_2, ..., Qn_k, x}, where x is simply a Var
                  //     for "catch all" case. Note that matching "Var" would cause `solve` to
                  //     fail unless there is a PVar pattern.
                  qns
                    .foldLeft[
                      Either[
                        IrError,
                        (Signature, Map[QualifiedName, CaseTree], Option[CaseTree]),
                      ],
                    ](
                      Right(Σ, Map(), None),
                    ) {
                      // Normal type case
                      case (Right(_Σ, branches, defaultCase), Some(qn)) =>
                        val data = Σ.getData(qn)
                        // in context _Γ1
                        val Δ = data.tParamTys.map(_._1)

                        // in context _Γ1 ⊎ Δ
                        val ρ1 = Substitutor.id[Pattern](_Γ1.size) ⊎ Substitutor.of(
                          Δ.size,
                          PDataType(qn, pVars(Δ.size - 1)),
                        )
                        val ρ1t = ρ1.toTermSubstitutor

                        // in context _Γ1 ⊎ Δ ⊎ _Γ2
                        val ρ2 = ρ1 ⊎ Substitutor.id[Pattern](_Γ2.size)

                        val ρ2t = ρ2.toTermSubstitutor
                        given Context = _Γ1 ++ Δ ++ _Γ2.subst(ρ1t)

                        for
                          problem <- subst(problem, ρ2t)
                          _ <- problem match
                            case Nil =>
                              throw IllegalStateException(
                                "impossible because the type qualified names are collected from clauses in the problem",
                              )
                            case _ => Right(())
                          case (_Σ, branch) <- split(
                            q̅.map(_.subst(ρ2)),
                            _C.subst(ρ2t),
                            problem,
                          )
                        yield (_Σ, branches + (qn -> branch), defaultCase)
                      // Default `x` catch-all case
                      case (Right(_Σ, branches, _), None) =>
                        for
                          problem <- subst(problem, Substitutor.id(Γ.size))
                          _ <- problem match
                            case Nil => Left(MissingDefaultTypeCase())
                            case _   => Right(())
                          case (_Σ, branch) <- split(q̅, _C, problem)
                        yield (_Σ, branches, Some(branch))
                      case (Left(e), _) => Left(e)
                    }
                    .map {
                      //  3. generate cases, where the branch corresponding to `x` goes to the default
                      //     case
                      case (_Σ, branches, Some(defaultCase)) =>
                        (_Σ, CtTypeCase(x, branches, defaultCase))
                      case _ =>
                        throw IllegalStateException(
                          "impossible because missing default case should have caused missing default type error",
                        )
                    }

              // split constructor
              case (_, (x: Var, PConstructor(name, args), _A @ DataType(qn, tArgs))) =>
                if providedAtLeastU1Usage(x) then
                  Left(InsufficientResourceForSplit(x, Γ.resolve(x)))
                else
                  val (_Γ1, binding, _Γ2) = Γ.split(x)
                  assert(
                    binding.ty.weaken(_Γ2.size + 1, 0) == _A,
                    "these types should be identical because they are created by [intro]",
                  )
                  val data = Σ.getData(qn)
                  Σ.getConstructors(qn)
                    .foldLeft[Either[IrError, (Signature, Map[Name, CaseTree])]](
                      Right(Σ, Map()),
                    ) {
                      case (Right(_Σ, branches), constructor) =>
                        given Signature = _Σ
                        // in context _Γ1
                        val tArgs = binding.ty.asInstanceOf[DataType].args
                        val Δ = constructor.paramTys.substLowers(tArgs: _*)

                        // in context _Γ1 ⊎ Δ
                        val cTArgs = constructor.tArgs.map(
                          _.substLowers(tArgs ++ vars(constructor.paramTys.size - 1): _*),
                        )
                        for
                          unificationResult <- unifyAll(
                            tArgs.drop(data.tParamTys.size).map(_.weaken(Δ.size, 0)),
                            cTArgs,
                            data.tIndexTys,
                          )(using _Γ1 ++ Δ)
                          r <- unificationResult match
                            case UnificationResult.UYes(_Γ1, ρ, τ) =>
                              // in context _Γ1 ⊎ Δ
                              val ρ1 = ρ ⊎ Substitutor.of(
                                Δ.size,
                                PConstructor(constructor.name, pVars(Δ.size - 1)),
                              )

                              val ρ1t = ρ1.toTermSubstitutor

                              // in context _Γ1 ⊎ Δ ⊎ _Γ2
                              val ρ2 = ρ1 ⊎ Substitutor.id[Pattern](_Γ2.size)

                              val ρ2t = ρ2.toTermSubstitutor
                              given Context =
                                _Γ1 ++ Δ.subst(ρ.toTermSubstitutor) ++ _Γ2.subst(ρ1t)

                              for
                                problem <- subst(problem, ρ2t)
                                _ <- problem match
                                  case Nil =>
                                    Left(MissingConstructorCase(qn, constructor.name))
                                  case _ => Right(())
                                case (_Σ, branch) <- split(
                                  q̅.map(_.subst(ρ2)),
                                  _C.subst(ρ2t),
                                  problem,
                                )
                              yield (
                                _Σ,
                                branches + (constructor.name -> branch.subst(
                                  τ.toTermSubstitutor ⊎ Substitutor.id(Δ.size + _Γ2.size),
                                )),
                              )
                            case _: UnificationResult.UNo | _: UnificationResult.UUndecided =>
                              Left(UnificationFailure(unificationResult))
                        yield r
                      case (Left(e), _) => Left(e)
                    }
                    .map { case (_Σ, branches) => (_Σ, CtDataCase(x, qn, branches)) }


              // split empty
              case (_, (x: Var, PAbsurd(), _A)) =>
                _A match
                  case DataType(qn, args) =>
                    val data = Σ.getData(qn)
                    val isEmpty = Σ
                      .getConstructors(qn)
                      .forall(constructor => {
                        // all constructor arg unification fails
                        val tParamArgs = args.take(data.tParamTys.size)
                        val tIndexArgs = args.drop(data.tParamTys.size)
                        val conTArgs = constructor.tArgs.map(_.substLowers(tParamArgs: _*))
                        val newΓ = Γ ++ constructor.paramTys.substLowers(tParamArgs: _*)
                        // All unification should be successful or inconclusive. That is, no failure is found.
                        unifyAll(
                          tIndexArgs.map(_.weaken(constructor.paramTys.size, 0)),
                          conTArgs,
                          data.tIndexTys
                            .substLowers(tParamArgs: _*)
                            .weaken(constructor.paramTys.size, 0),
                        )(using newΓ) match
                          case Right(_: UNo) => true
                          case _             => false
                      })
                    if isEmpty then Right(Σ, CtDataCase(x, qn, Map()))
                    else Left(NonEmptyType(_A, source1))
                  case _ => Left(NonEmptyType(_A, source1))
              // No action to do, just forward the previous error
              case (l, _) => l
            } match
              case Right(r) => Right(r)

              // [done]: no action can be taken, try [done] or fail with error of last action, which
              // could be missing constructor case, non-empty type, etc.
              case Left(e) =>
                for
                  rhs1 <- rhs1 match
                    case Some(rhs1) => Right(rhs1)
                    case None       => Left(e)
                  σOption <- solve(_E1)
                  (rhs1, usages) <- σOption match
                    case Some(σ) => checkType(rhs1.subst(σ), _C)
                    case None    => Left(e)
                  constraint <- checkUsagesSubsumption(usages)
                  _ <- if constraint.isEmpty then Right(()) else Left(UnsatifisfiedUsageRequirements(constraint))
                yield (Σ.addClause(preDefinition.qn, Clause(Γ, q̅, rhs1, _C)), CtTerm(rhs1))
          split(q̅, _C, problem)
        case (Nil, _) => Left(IncompleteClauses(preDefinition.qn))
    yield r

  ctx.trace(s"elaborating def body ${preDefinition.qn}") {
    for
      paramTys <- elaborateContext(preDefinition.paramTys)
      (_Σ, _Q) <- elaborate(
        Nil,
        preDefinition.ty,
        preDefinition.clauses.map { case source @ PreClause(_, lhs, rhs) =>
          ElabClause(Nil, lhs, rhs, source)
        },
      )(using paramTys.toIndexedSeq)
    yield _Σ.addCaseTree(preDefinition.qn, _Q)
  }

private def elaborateHead
  (effect: PreEffect)
  (using Σ: Signature)
  (using ctx: TypingContext)
  : Either[IrError, Signature] =
  ctx.trace(s"elaborating effect signature ${effect.qn}") {
    for
      tParamTys <- elaborateContext(effect.tParamTys)
      e = new Effect(effect.qn)(
        tParamTys,
        effect.operations.map(_.continuationUsage).foldLeft[Option[Usage]](None) {
          case (None, None) => None
          // None continuation usage is approximated as U1.
          case (Some(u), None)      => Some(Usage.U1 | u)
          case (None, Some(u))      => Some(Usage.U1 | u)
          case (Some(u1), Some(u2)) => Some(u1 | u2)
        },
      )
      _ <- checkEffect(e)
    yield Σ.addDeclaration(e)
  }

private def elaborateBody
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
        (Telescope, /* operation return type */ VTerm, /* operation return usage */ VTerm),
      ] =
      for
        ty <- reduceCType(ty)
        r <- ty match
          // Here and below we do not care the declared effect types because data type constructors
          // are always total. Declaring non-total signature is not necessary (nor desirable) but
          // acceptable.
          case F(ty, effects, usage) =>
            Right((Nil, ty, usage))
          case FunctionType(binding, bodyTy, effects) =>
            elaborateTy(bodyTy)(using Γ :+ binding).map { case (telescope, ul, usage) =>
              (binding :: telescope, ul, usage)
            }
          case _ => Left(ExpectFType(ty))
      yield r

    preEffect.operations.foldLeft[Either[IrError, Signature]](Right(Σ)) {
      case (Right(_Σ), operation) =>
        given Signature = _Σ
        ctx.trace(s"elaborating operation ${operation.name}") {
          for
            case (paramTys, resultTy, usage) <- elaborateTy(operation.ty)
            o = Operation(operation.name, operation.continuationUsage, paramTys, resultTy, usage)
            _ <- checkOperation(effect.qn, o)
          yield _Σ.addOperation(effect.qn, o)
        }
      case (Left(e), _) => Left(e)
    }
  }

private def elaborateTContext
  (tTelescope: PreTContext)
  (using Γ: Context)
  (using Signature)
  (using ctx: TypingContext)
  : Either[IrError, TContext] =
  elaborateContext(tTelescope.map(_._1)).map(_.zip(tTelescope.map(_._2)))

private def elaborateContext
  (telescope: PreContext)
  (using Γ: Context)
  (using Signature)
  (using ctx: TypingContext)
  : Either[IrError, Context] = telescope match
  case Nil => Right(IndexedSeq())
  case binding :: context =>
    ctx.trace("elaborating context") {
      for
        ty <- reduceVType(binding.ty)
        usage <- reduceUsage(binding.usage)
        newBinding = Binding(ty, usage)(binding.name)
        context <- elaborateContext(context)(using Γ :+ newBinding)
      yield newBinding +: context
    }

// [1] Jesper Cockx and Andreas Abel. 2018. Elaborating dependent (co)pattern matching. Proc. ACM
// Program. Lang. 2, ICFP, Article 75 (September 2018), 30 pages. https://doi.org/10.1145/3236770
