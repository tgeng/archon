package com.github.tgeng.archon.core.ir

import com.github.tgeng.archon.common.*
import com.github.tgeng.archon.common.eitherFilter.*
import com.github.tgeng.archon.core.common.*
import com.github.tgeng.archon.core.ir.CTerm.*
import com.github.tgeng.archon.core.ir.CaseTree.*
import com.github.tgeng.archon.core.ir.CoPattern.*
import com.github.tgeng.archon.core.ir.Declaration.*
import com.github.tgeng.archon.core.ir.IrError.*
import com.github.tgeng.archon.core.ir.Pattern.*
import com.github.tgeng.archon.core.ir.PreDeclaration.*
import com.github.tgeng.archon.core.ir.SourceInfo.*
import com.github.tgeng.archon.core.ir.UnificationResult.*
import com.github.tgeng.archon.core.ir.VTerm.*

import scala.collection.mutable

@throws(classOf[IrError])
def elaborateAll
  (declarations: Seq[PreDeclaration])
  (using Σ: Signature)
  (using ctx: TypingContext)
  : Signature =
  val decls = sortPreDeclarations(declarations)
  decls.foldLeft[Signature](Σ) { case (_Σ, (part, decl)) =>
    elaborate(part, decl)(using _Σ)
  }

@throws(classOf[IrError])
def elaborate
  (part: DeclarationPart, decl: PreDeclaration)
  (using Σ: Signature)
  (using ctx: TypingContext)
  : Signature =
  (part, decl) match
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

import com.github.tgeng.archon.core.ir.DeclarationPart.*
import com.github.tgeng.archon.core.ir.unifyAll

@throws(classOf[IrError])
def sortPreDeclarations
  (declarations: Seq[PreDeclaration])
  (using Σ: Signature)
  : Seq[(DeclarationPart, PreDeclaration)] =
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
              clause.lhs.map(QualifiedNameVisitor.visitCoPattern) ++
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
    case Right(decls) => decls
    case Left(cycle)  => throw CyclicDeclarations(cycle)

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
@throws(classOf[IrError])
private def elaborateHead
  (preData: PreData)
  (using Σ: Signature)
  (using ctx: TypingContext)
  : Signature =
  ctx.trace(s"elaborating data signature ${preData.qn}") {
    @throws(classOf[IrError])
    def elaborateTy
      (ty: CTerm)
      (using Γ: Context)
      (using Signature)
      (using ctx: TypingContext)
      : (Telescope, VTerm, VTerm) =
      checkIsCType(ty)._1.normalized(None) match
        // Here and below we do not care about the declared effect types because data type
        // constructors are always total. Declaring non-total signature is not necessary (nor
        // desirable) but acceptable.
        case F(Type(Top(level, eqDecidability)), _, _) => (Nil, level, eqDecidability)
        case F(t, _, _)                                => throw ExpectVType(t)
        case FunctionType(binding, bodyTy, _) =>
          val (telescope, level, eqDecidability) = elaborateTy(bodyTy)(using Γ :+ binding)
          (binding +: telescope, level, eqDecidability)
        case _ => throw NotDataTypeType(ty)

    val tParamTys = elaborateTContext(preData.tParamTys)
    val (tIndices, level, eqDecidability) = elaborateTy(preData.ty)(using
      Γ0 ++ tParamTys.map(_._1),
    )
    val data = checkData(
      new Data(preData.qn)(
        tParamTys,
        tIndices,
        level,
        eqDecidability,
      ),
    )
    Σ.addDeclaration(data)
  }

@throws(classOf[IrError])
private def elaborateBody
  (preData: PreData)
  (using Σ: Signature)
  (using ctx: TypingContext)
  : Signature =
  ctx.trace(s"elaborating data body ${preData.qn}") {
    val data = Σ.getData(preData.qn)

    @throws(classOf[IrError])
    def elaborateTy
      (ty: CTerm)
      (using Γ: Context)
      (using Signature)
      (using ctx: TypingContext)
      : (Telescope, /* constructor tArgs */ List[VTerm]) =
      checkIsCType(ty)._1.normalized(None) match
        // Here and below we do not care the declared effect types because data type constructors
        // are always total. Declaring non-total signature is not necessary (nor desirable) but
        // acceptable.
        // TODO: report better error if `qn`, arg count, or param args (not refs to those bound at
        //  data declaration) are unexpected.
        case F(DataType(qn, args), _, _)
          if qn == data.qn && args.size == data.tParamTys.size + data.tIndexTys.size =>
          // Drop parameter args because Constructor.tArgs only track index args
          // TODO: check and report invalid args
          (Nil, args.drop(data.tParamTys.size))
        case F(t, _, _) => throw ExpectDataType(t, Some(data.qn))
        case FunctionType(binding, bodyTy, _) =>
          val (telescope, level) = elaborateTy(bodyTy)(using Γ :+ binding)
          (binding :: telescope, level)
        case _ => throw NotDataTypeType(ty)

    // number of index arguments
    given Context = data.tParamTys.map(_._1)

    preData.constructors.foldLeft[Signature](Σ) { case (_Σ, constructor) =>
      given Signature = _Σ
      ctx.trace(s"elaborating constructor ${constructor.name}") {
        val ty = constructor.ty
        val (paramTys, tArgs) = elaborateTy(ty)
        val con =
          checkDataConstructor(preData.qn, new Constructor(constructor.name, paramTys, tArgs))
        _Σ.addConstructor(preData.qn, con)
      }
    }
  }

@throws(classOf[IrError])
private def elaborateHead
  (record: PreRecord)
  (using Σ: Signature)
  (using ctx: TypingContext)
  : Signature =
  ctx.trace(s"elaborating record signature ${record.qn}") {
    val tParamTys = elaborateTContext(record.tParamTys)(using Γ0)
    given Context = tParamTys.map(_._1).toIndexedSeq
    val selfUsage = Collapse(checkType(record.selfUsage, F(UsageType(), Total()))._1).normalized
    val r = checkIsCType(record.ty)._1.normalized(None) match
      case CType(CTop(level, _), _) =>
        new Record(record.qn)(
          tParamTys,
          level,
          Binding(Thunk(RecordType(record.qn, vars(tParamTys.size - 1))), selfUsage)(
            record.selfName,
          ),
        )
      case t => throw ExpectCType(t)
    Σ.addDeclaration(checkRecord(r))
  }

@throws(classOf[IrError])
private def elaborateBody
  (preRecord: PreRecord)
  (using Σ: Signature)
  (using ctx: TypingContext)
  : Signature =
  ctx.trace(s"elaborating record body ${preRecord.qn}") {
    val record = Σ.getRecord(preRecord.qn)

    given SourceInfo = SiEmpty

    given Context = record.tParamTys.map(_._1).toIndexedSeq :+
      Binding(U(RecordType(record.qn, vars(record.tParamTys.size - 1))), Total())(
        record.selfBinding.name,
      )

    preRecord.fields.foldLeft[Signature](Σ) { case (_Σ, field) =>
      ctx.trace(s"elaborating field ${field.name}") {
        val ty = checkIsCType(field.ty)._1.normalized(None)
        val f = checkRecordField(preRecord.qn, new Field(field.name, ty))
        _Σ.addField(preRecord.qn, f)
      }
    }
  }

@throws(classOf[IrError])
private def elaborateHead
  (definition: PreDefinition)
  (using Σ: Signature)
  (using ctx: TypingContext)
  : Signature =
  given SourceInfo = SiEmpty

  ctx.trace(s"elaborating def signature ${definition.qn}") {
    val paramTys = elaborateContext(definition.paramTys)
    val ty = checkIsCType(definition.ty)(using paramTys.toIndexedSeq)._1
      .normalized(None)(using paramTys.toIndexedSeq)
    val d = new Definition(definition.qn)(
      paramTys.foldRight(ty) { (binding, bodyTy) =>
        FunctionType(binding, bodyTy)
      },
    )
    Σ.addDeclaration(checkDef(d))
  }

@throws(classOf[IrError])
private def elaborateBody
  (preDefinition: PreDefinition)
  (using Σ: Signature)
  (using ctx: TypingContext)
  : Signature =

  // See [1] for how this part works.
  type Constraint =
    ( /* current split term */ VTerm, /* user pattern */ Pattern, /* type */ VTerm)

  case class ElabClause
    (
      constraints: List[Constraint],
      userPatterns: List[CoPattern],
      rhs: Option[CTerm],
      source: PreClause,
    )

  type Problem = List[ElabClause]

  def weaken(c: Constraint) = c match
    // Note: p is not weakened because p is a user pattern. It does not leave in the Γ being
    // assembled during elaboration.
    case (w, p, _A) => (w.weakened, p, _A.weakened)

  @throws(classOf[IrError])
  def solve
    (constraints: List[Constraint])
    (using Γ: Context)
    (using Σ: Signature)
    : Option[PartialSubstitution[VTerm]] =
    val σ = mutable.Map[Nat, VTerm]()
    matchPattern(constraints.map { case (w, p, _) => (p, w) }, σ) match
      case MatchingStatus.Matched =>
        constraints.foreach { case (w, pattern, _A) =>
          pattern.toTerm match
            case Some(p) =>
              val constraint =
                checkIsConvertible(checkType(p, _A)._1.subst(σ.get), checkType(w, _A)._1, Some(_A))
              if !constraint.isEmpty then throw UnmatchedPattern(pattern, w, constraint)
            case None => throw UnexpectedAbsurdPattern(pattern)
        }
        Some(σ.get)
      case MatchingStatus.Mismatch | MatchingStatus.Stuck => None

  /** New var index is `Γ.size`. New var type is `_A`.
    */
  @throws(classOf[IrError])
  def shift(problem: Problem, _A: VTerm): Problem = problem match
    case Nil => Nil
    case ElabClause(_E, CPattern(p) :: q̅, rhs, source) :: problem =>
      ElabClause((Var(0), p, _A.weakened) :: _E.map(weaken), q̅, rhs, source) :: shift(problem, _A)
    case ElabClause(_, q :: _, _, _) :: _   => throw UnexpectedCProjection(q)
    case ElabClause(_, _, rhs, source) :: _ => throw MissingUserCoPattern(source)

  @throws(classOf[IrError])
  def filter(problem: Problem, π: Name): Problem = problem match
    case Nil => Nil
    case ElabClause(_E, CProjection(π2) :: q̅, rhs, source) :: problem =>
      if π == π2 then ElabClause(_E, q̅, rhs, source) :: filter(problem, π)
      else problem
    case ElabClause(_, q :: _, _, _) :: _       => throw UnexpectedCPattern(q)
    case c @ ElabClause(_, _, rhs, source) :: _ => throw MissingUserCoPattern(source)

  @throws(classOf[IrError])
  def subst(problem: Problem, σ: PartialSubstitution[VTerm])(using Σ: Signature): Problem =
    def simplify(v: VTerm, p: Pattern, _A: VTerm)(using Σ: Signature): Option[List[Constraint]] =
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
        case (DataType(_, _), PDataType(_, _))                 => None
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
        case (Con(_, _), PConstructor(_, _))                     => None
        case (Con(name, args), PForcedConstructor(pName, pArgs)) =>
          // TODO[P3]: instead of assert, report a use-friendly error if name doesn't match
          // because such a mismatch means the provided forced pattern is not correct.
          assert(name == pName)
          val dataType = _A.asInstanceOf[DataType]
          val constructor = Σ.getConstructor(dataType.qn, name)
          val _As = constructor.paramTys.substLowers(dataType.args: _*)
          assert(args.size == pArgs.size && pArgs.size == _As.size)
          simplifyAll(args.lazyZip(pArgs).lazyZip(_As.map(_.ty)).toList)
        case _ => Some(List((v, p, _A)))

    @throws(classOf[IrError])
    def simplifyAll(constraints: List[Constraint])(using Σ: Signature): Option[List[Constraint]] =
      constraints match
        case Nil => Some(Nil)
        case (v, p, _A) :: constraints =>
          val _E1 = simplify(v, p, _A)
          val _E2 = simplifyAll(constraints)
          _E1.zip(_E2).map(_ ++ _)
    problem match
      case Nil => Nil
      case ElabClause(_E, q̅, rhs, source) :: problem =>
        val optionE = simplifyAll(_E.map { case (v, p, _A) => (v.subst(σ), p, _A) })
        optionE match
          case Some(_E) =>
            ElabClause(_E, q̅, rhs, source) :: subst(problem, σ)
          case None => subst(problem, σ)

  def apply(qn: QualifiedName, q̅ : List[CoPattern]): CTerm =
    Redex(Def(qn), q̅.map(_.toElimination.get))

  @throws(classOf[IrError])
  def elaborate
    (q̅ : List[CoPattern], _C: CTerm, problem: Problem)
    (using Γ: Context)
    (using Σ: Signature)
    : (Signature, CaseTree) =
    (problem, checkIsCType(_C)._1.normalized(None)) match
      // [cosplit]
      case (
          ElabClause(_E1, (p @ CProjection(_)) :: q̅1, rhs1, source) :: _,
          RecordType(qn, args, _),
        ) =>
        val (_Σ, fields) = Σ
          .getFields(qn)
          .foldLeft[(Signature, Map[Name, CaseTree])]((Σ, Map())) { case ((_Σ, fields), field) =>
            val (_Σmod, ct) = elaborate(
              q̅ :+ CProjection(field.name),
              field.ty.substLowers(args :+ Thunk(apply(qn, q̅)): _*),
              filter(problem, field.name),
            )(using Γ)(using _Σ)
            (_Σmod, fields + (field.name -> ct))
          }
        (_Σ, CtRecord(fields))
      // [cosplit empty]
      // Note: here we don't require an absurd pattern like in [1]. Instead, we require no more
      // user (projection) pattern. This seems more natural.
      case (ElabClause(_E1, Nil, None, source) :: _, RecordType(qn, _, _)) =>
        Σ.getFields(qn).size match
          // There is no need to modify Σ because empty record does not have any clause
          case 0 => (Σ, CtRecord(Map()))
          case _ => throw MissingFieldsInCoPattern(source)
      // [intro]
      case (
          ElabClause(_E1, (q @ CPattern(p)) :: q̅1, rhs1, source) :: _,
          FunctionType(binding, bodyTy, _),
        ) =>
        val _A = shift(problem, binding.ty)
        val (_Σ1, _Q) = elaborate(
          q̅.map(_.weakened) :+ CPattern(PVar(0)),
          bodyTy,
          _A,
        )
        (_Σ1, CtLambda(_Q)(binding.name))
      // mismatch between copattern and _C
      case (ElabClause(_, q :: _, _, source) :: _, _) =>
        throw UnexpectedUserCoPattern(source, q)
      // All copatterns are introduced. Now start doing split
      case (ElabClause(_E1, Nil, _, _) :: _, _) =>
        def split
          (q̅ : List[CoPattern], _C: CTerm, problem: Problem)
          (using Γ: Context)
          (using Σ: Signature)
          : Either[IrError, (Signature, CaseTree)] =
          val ElabClause(_E1, _, rhs1, source1) = problem.head

          // We cannot use `checkUsageSubsumption` here because that implies the usage must subsume U1, which
          // may not be true because here we are only *attempting* to find a place to split.
          def providedAtLeastU1Usage(x: Var): Boolean =
            Γ.resolve(x).usage.normalized match
              case UsageLiteral(Usage.U0) => false
              case UsageLiteral(_)        => true
              case _                      => true

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
              if !providedAtLeastU1Usage(x) then Left(InsufficientResourceForSplit(x, Γ.resolve(x)))
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

                      if subst(problem, ρ2t).isEmpty then
                        throw IllegalStateException(
                          "impossible because the type qualified names are collected from clauses in the problem",
                        )
                      for case (_Σ, branch) <- split(
                          q̅.map(_.subst(ρ2)),
                          _C.subst(ρ2t),
                          problem,
                        )
                      yield (_Σ, branches + (qn -> branch), defaultCase)
                    // Default `x` catch-all case
                    case (Right(_Σ, branches, _), None) =>
                      if subst(problem, Substitutor.id(Γ.size)).isEmpty then
                        throw MissingDefaultTypeCase()
                      for case (_Σ, branch) <- split(q̅, _C, problem)
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
              if !providedAtLeastU1Usage(x) then Left(InsufficientResourceForSplit(x, Γ.resolve(x)))
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
                      val unificationResult = unifyAll(
                        tArgs.drop(data.tParamTys.size).map(_.weaken(Δ.size, 0)),
                        cTArgs,
                        data.tIndexTys,
                      )(using _Γ1 ++ Δ)
                      unificationResult match
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

                          if subst(problem, ρ2t).isEmpty then
                            throw MissingConstructorCase(qn, constructor.name)
                          for case (_Σ, branch) <- split(
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
                        case _: UNo => true
                        case _      => false
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
                σOption = solve(_E1)
                (rhs1, usages) <- σOption match
                  case Some(σ) => Right(checkType(rhs1.subst(σ), _C))
                  case None    => Left(e)
                _ <-
                  val constraints = checkUsagesSubsumption(usages)
                  if constraints.isEmpty then Right(())
                  else Left(UnsatifisfiedUsageRequirements(constraints))
              yield (Σ.addClause(preDefinition.qn, Clause(Γ, q̅, rhs1, _C)), CtTerm(rhs1))
        split(q̅, _C, problem) match
          case Right(r) => r
          case Left(e)  => throw e
      case (Nil, _) => throw IncompleteClauses(preDefinition.qn)

  ctx.trace(s"elaborating def body ${preDefinition.qn}") {
    val paramTys = elaborateContext(preDefinition.paramTys)
    val (_Σ, _Q) = elaborate(
      Nil,
      preDefinition.ty,
      preDefinition.clauses.map { case source @ PreClause(_, lhs, rhs) =>
        ElabClause(Nil, lhs, rhs, source)
      },
    )(using paramTys.toIndexedSeq)
    _Σ.addCaseTree(preDefinition.qn, _Q)
  }

@throws(classOf[IrError])
private def elaborateHead
  (effect: PreEffect)
  (using Σ: Signature)
  (using ctx: TypingContext)
  : Signature =
  ctx.trace(s"elaborating effect signature ${effect.qn}") {
    val tParamTys = elaborateContext(effect.tParamTys)
    val e = new Effect(effect.qn)(
      tParamTys,
      effect.operations.map(_.continuationUsage).foldLeft(ContinuationUsage.CuLinear)(_ | _),
    )
    Σ.addDeclaration(checkEffect(e))
  }

@throws(classOf[IrError])
private def elaborateBody
  (preEffect: PreEffect)
  (using Σ: Signature)
  (using ctx: TypingContext)
  : Signature =
  val effect = Σ.getEffect(preEffect.qn)

  given Context = effect.tParamTys.toIndexedSeq

  ctx.trace(s"elaborating effect body ${effect.qn}") {
    def elaborateTy
      (ty: CTerm)
      (using Γ: Context)
      (using Signature)
      (using ctx: TypingContext)
      : (Telescope, /* operation return type */ VTerm, /* operation return usage */ VTerm) =
      checkIsCType(ty)._1.normalized(None) match
        // Here and below we do not care the declared effect types because data type constructors
        // are always total. Declaring non-total signature is not necessary (nor desirable) but
        // acceptable.
        case F(ty, effects, usage) =>
          (Nil, ty, usage)
        case FunctionType(binding, bodyTy, effects) =>
          val (telescope, level, usage) = elaborateTy(bodyTy)(using Γ :+ binding)
          (binding :: telescope, level, usage)
        case _ => throw ExpectFType(ty)

    preEffect.operations.foldLeft[Signature](Σ) { case (_Σ, operation) =>
      given Signature = _Σ
      ctx.trace(s"elaborating operation ${operation.name}") {
        val (paramTys, resultTy, usage) = elaborateTy(operation.ty)
        val o = Operation(operation.name, operation.continuationUsage, paramTys, resultTy, usage)
        _Σ.addOperation(effect.qn, checkOperation(effect.qn, o))
      }
    }
  }

@throws(classOf[IrError])
private def elaborateTContext
  (tTelescope: PreTContext)
  (using Γ: Context)
  (using Signature)
  (using ctx: TypingContext)
  : TContext =
  elaborateContext(tTelescope.map(_._1)).zip(tTelescope.map(_._2))

@throws(classOf[IrError])
private def elaborateContext
  (telescope: PreContext)
  (using Γ: Context)
  (using Signature)
  (using ctx: TypingContext)
  : Context = telescope match
  case Nil => IndexedSeq()
  case binding :: context =>
    ctx.trace("elaborating context") {
      val ty = reduceVType(binding.ty)
      val usage = reduceUsage(binding.usage)
      val newBinding = Binding(ty, usage)(binding.name)
      newBinding +: elaborateContext(context)(using Γ :+ newBinding)
    }

// [1] Jesper Cockx and Andreas Abel. 2018. Elaborating dependent (co)pattern matching. Proc. ACM
// Program. Lang. 2, ICFP, Article 75 (September 2018), 30 pages. https://doi.org/10.1145/3236770
