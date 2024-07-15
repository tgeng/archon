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

import scala.collection.immutable.SeqMap
import scala.collection.mutable

@throws(classOf[IrError])
def elaborateAll
  (declarations: Seq[PreDeclaration])
  (using Γ: Context)
  (using Σ: Signature)
  (using ctx: TypingContext)
  : Signature =
  val decls = sortPreDeclarations(declarations)
  decls.foldLeft[Signature](Σ) { case (_Σ, (part, decl)) =>
    try elaborate(part, decl)(using Γ)(using _Σ)
    catch
      case e: IrError =>
        ctx.enableDebugging = true
        elaborate(part, decl)(using Γ)(using _Σ)
  }

@throws(classOf[IrError])
def elaborate
  (part: DeclarationPart, decl: PreDeclaration)
  (using Γ: Context)
  (using Σ: Signature)
  (using ctx: TypingContext)
  : Signature =
  try
    (part, decl) match
      case (DeclarationPart.HEAD, d: PreData)       => elaborateDataHead(d)
      case (DeclarationPart.HEAD, d: PreRecord)     => elaborateRecordHead(d)
      case (DeclarationPart.HEAD, d: PreDefinition) => elaborateDefHead(d)
      case (DeclarationPart.HEAD, d: PreEffect)     => elaborateEffectHead(d)
      case (DeclarationPart.BODY, d: PreData)       => elaborateDataBody(d)
      case (DeclarationPart.BODY, d: PreRecord)     => elaborateRecordBody(d)
      case (DeclarationPart.BODY, d: PreDefinition) => elaborateDefBody(d)
      case (DeclarationPart.BODY, d: PreEffect)     => elaborateEffectBody(d)
  catch case e: IrError => throw ElaborationFailure(part, decl, e)

enum DeclarationPart:
  case HEAD, BODY

import com.github.tgeng.archon.core.ir.DeclarationPart.*
import com.github.tgeng.archon.core.ir.unifyAll

@throws(classOf[IrError])
def sortPreDeclarations
  (declarations: Seq[PreDeclaration])
  (using Signature)
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
            }*,
          ) + data.qn
        case record: PreRecord =>
          QualifiedNameVisitor.combine(
            record.fields.map { field =>
              field.ty.visitWith(QualifiedNameVisitor)
            }*,
          ) + record.qn
        case definition: PreDefinition =>
          QualifiedNameVisitor.combine(
            definition.clauses.flatMap { clause =>
              clause.lhs.map(QualifiedNameVisitor.visitCoPattern) ++
                clause.rhs.map(QualifiedNameVisitor.visitCTerm)
            }*,
          ) + definition.qn
        case effect: PreEffect =>
          QualifiedNameVisitor.combine(
            effect.operations.map { operation =>
              operation.ty.visitWith(QualifiedNameVisitor)
            }*,
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
  ):
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
  match
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

@throws(classOf[IrError])
private def elaborateDataHead
  (preData: PreData)
  (using Γ: Context)
  (using Σ: Signature)
  (using ctx: TypingContext)
  : Signature =
  if Σ.getDataOption(preData.qn).isDefined then throw DuplicatedDeclaration(preData.qn)
  ctx.trace(s"elaborating data signature ${preData.qn}"):
    val tParamTys = elaborateTTelescope(preData.tParamTys)(using Γ)
    given Context = Γ ++ tParamTys.map(_._1)

    def elaborateTy
      (ty: CTerm)
      (using Γ: Context)
      (using Signature)
      (using TypingContext)
      : (Telescope, VTerm, VTerm) =
      checkIsCType(ty).normalized(None) match
        // Here and below we do not care about the declared effect types because data type
        // constructors are always total. Declaring non-total signature is not necessary (nor
        // desirable) but acceptable.
        case F(Type(Top(level, eqDecidability)), _, _) => (Nil, level, eqDecidability)
        case F(t, _, _)                                => throw ExpectVType(t)
        case FunctionType(binding, bodyTy, _) =>
          val (telescope, level, eqDecidability) = elaborateTy(bodyTy)(using Γ :+ binding)
          (binding +: telescope, level, eqDecidability)
        case _ => throw NotDataTypeType(ty)

    val (tIndices, level, eqDecidability) = elaborateTy(preData.ty)
    // level and eqDecidability should not depend on index arguments
    val strengthenedLevel =
      try level.strengthen(tIndices.size, 0)
      catch case e: StrengthenException => throw DataLevelCannotDependOnIndexArgument(preData)
    val strengthenedEqDecidability =
      try eqDecidability.strengthen(tIndices.size, 0)
      catch
        case e: StrengthenException => throw DataEqDecidabilityCannotDependOnIndexArgument(preData)
    val data = checkData(
      Data(
        preData.qn,
        Γ.zip(Iterator.continually(Variance.INVARIANT)) ++ tParamTys,
        tIndices,
        strengthenedLevel,
        strengthenedEqDecidability,
      ),
    )
    Σ.addDeclaration(data)

@throws(classOf[IrError])
private def elaborateDataBody
  (preData: PreData)
  (using Σ: Signature)
  (using ctx: TypingContext)
  : Signature =
  val data = Σ.getData(preData.qn)

  @throws(classOf[IrError])
  def elaborateTy
    (ty: CTerm)
    (using Γ: Context)
    (using Signature)
    (using TypingContext)
    : (Telescope, /* constructor tArgs */ List[VTerm]) =
    checkIsCType(ty).normalized(None) match
      // Here and below we do not care the declared effect types because data type constructors
      // are always total. Declaring non-total signature is not necessary (nor desirable) but
      // acceptable.
      // TODO: report better error if `qn`, arg count, or param args (not refs to those bound at
      //  data declaration) are unexpected.
      case F(DataType(qn, args), _, _)
        if qn == data.qn && args.size == data.context.size + data.tIndexTys.size =>
        // Drop parameter args because Constructor.tArgs only track index args
        // TODO: check and report invalid args
        (Nil, args.drop(data.context.size))
      case F(t, _, _) => throw ExpectDataType(t, Some(data.qn))
      case FunctionType(binding, bodyTy, _) =>
        val (telescope, level) = elaborateTy(bodyTy)(using Γ :+ binding)
        (binding :: telescope, level)
      case _ => throw NotDataTypeType(ty)

  // number of index arguments
  given Context = data.context.map(_._1)

  ctx.trace(s"elaborating data body ${preData.qn}"):
    preData.constructors.foldLeft[Signature](Σ) { case (_Σ, constructor) =>
      given Signature = _Σ
      ctx.trace(s"elaborating constructor ${constructor.name}"):
        val ty = constructor.ty
        val (paramTys, tArgs) = elaborateTy(ty)
        val con =
          checkDataConstructor(preData.qn, Constructor(constructor.name, paramTys, tArgs))
        _Σ.addConstructor(preData.qn, con)
    }

@throws(classOf[IrError])
private def elaborateRecordHead
  (record: PreRecord)
  (using Γ: Context)
  (using Σ: Signature)
  (using ctx: TypingContext)
  : Signature =
  if Σ.getRecordOption(record.qn).isDefined then throw DuplicatedDeclaration(record.qn)
  ctx.trace(s"elaborating record signature ${record.qn}"):
    val tParamTys = elaborateTTelescope(record.tParamTys)(using Γ)
    given Context = Γ ++ tParamTys.map(_._1)
    val r: Record =
      checkIsCType(record.ty).normalized(None) match
        case CType(CTop(level, _), _) =>
          Record(
            record.qn,
            Γ.zip(Iterator.continually(Variance.INVARIANT)) ++ tParamTys,
            level,
            // Self usage is always `uAny` because
            // 1. it's only used in field type declarations so `uAny` is handy
            // 2. having `uAny` here does not put any restrictions because any references of `self`
            //    are always in field types and all such usages will multiple by `u0` when type
            //    checking field implementations.
            Binding(U(RecordType(record.qn, vars(tParamTys.size - 1))), uAny)(
              record.selfName,
            ),
          )
        case t => throw ExpectCType(t)
    Σ.addDeclaration(checkRecord(r))

@throws(classOf[IrError])
private def elaborateRecordBody
  (preRecord: PreRecord)
  (using Σ: Signature)
  (using ctx: TypingContext)
  : Signature =
  val record = Σ.getRecord(preRecord.qn)

  given SourceInfo = SiEmpty

  given Context = record.context.map(_._1).toIndexedSeq :+
    Binding(U(RecordType(record.qn, vars(record.context.size - 1))), Total())(
      record.selfBinding.name,
    )

  ctx.trace(s"elaborating record body ${preRecord.qn}"):
    preRecord.fields.foldLeft[Signature](Σ) { case (_Σ, field) =>
      ctx.trace(s"elaborating field ${field.name}"):
        val ty = checkIsCType(field.ty).normalized(None)
        val f = checkRecordField(preRecord.qn, Field(field.name, ty))
        _Σ.addField(preRecord.qn, f)
    }

@throws(classOf[IrError])
private def elaborateDefHead
  (definition: PreDefinition)
  (using Γ: Context)
  (using Σ: Signature)
  (using ctx: TypingContext)
  : Signature =
  if Σ.getDefinitionOption(definition.qn).isDefined then throw DuplicatedDeclaration(definition.qn)
  given SourceInfo = SiEmpty

  ctx.trace(s"elaborating def signature ${definition.qn}"):
    val paramTys = elaborateTelescope(definition.paramTys)(using Γ)
    given newΓ: Context = Γ ++ paramTys
    val ty = checkIsCType(definition.ty).normalized(None)
    val d: Definition = Definition(definition.qn, newΓ, ty)
    Σ.addDeclaration(checkDef(d))

@throws(classOf[IrError])
private def elaborateDefBody
  (preDefinition: PreDefinition)
  (using Σ: Signature)
  (using ctx: TypingContext)
  : Signature =

  // See [1] for how this part works.
  case class ElabConstraint(currentSplitTerm: VTerm, userPattern: Pattern, currentType: VTerm)

  case class ElabClause
    (
      constraints: List[ElabConstraint],
      userPatterns: List[CoPattern],
      rhs: Option[CTerm],
      source: PreClause,
    )

  type Problem = List[ElabClause]

  def weaken(c: ElabConstraint): ElabConstraint = c match
    // Note: p is not weakened because p is a user pattern. It does not live in the Γ being
    // assembled during elaboration.
    case ElabConstraint(w, p, _A) => ElabConstraint(w.weakened, p, _A.weakened)

  @throws(classOf[IrError])
  def solve
    (constraints: List[ElabConstraint])
    (using Γ: Context)
    (using Signature)
    : Option[PartialSubstitution[VTerm]] =
    val σ = mutable.SeqMap[Nat, VTerm]()
    matchPattern(constraints.map { case ElabConstraint(w, p, _) => (p, w) }, σ) match
      case MatchingStatus.Matched =>
        constraints.foreach { case ElabConstraint(w, pattern, _A) =>
          pattern.toTerm match
            case Some(p) =>
              val constraint =
                checkIsConvertible(checkType(p, _A).subst(σ.get), checkType(w, _A), Some(_A))
              if !constraint.isEmpty then throw UnmatchedPattern(pattern, w, constraint)
            case None => throw UnexpectedAbsurdPattern(pattern)
        }
        Some(σ.get)
      case MatchingStatus.Mismatch | MatchingStatus.Stuck => None

  /** New var index is `Γ.size`. New var type is `_A`.
    */
  @throws(classOf[IrError])
  def shift(problem: Problem, _A: VTerm)(using Γ: Context): Problem = problem match
    case Nil => Nil
    case ElabClause(_E, CPattern(p) :: q̅, rhs, source) :: problem =>
      ElabClause(
        ElabConstraint(Var(0), p, _A.weakened) :: _E.map(weaken),
        q̅,
        rhs,
        source,
      ) :: shift(problem, _A)
    case ElabClause(_, q :: _, _, _) :: _ => throw UnexpectedCProjection(q)
    case ElabClause(_, _, _, source) :: _ => throw MissingUserCoPattern(source)

  @throws(classOf[IrError])
  def filter(problem: Problem, π: Name)(using Γ: Context): Problem = problem match
    case Nil => Nil
    case ElabClause(_E, CProjection(π2) :: q̅, rhs, source) :: problem =>
      if π == π2 then ElabClause(_E, q̅, rhs, source) :: filter(problem, π)
      else problem
    case ElabClause(_, q :: _, _, _) :: _ => throw UnexpectedCPattern(q)
    case ElabClause(_, _, _, source) :: _ => throw MissingUserCoPattern(source)

  @throws(classOf[IrError])
  def subst
    (problem: Problem, σ: PartialSubstitution[VTerm])
    (using Γ: Context)
    (using Σ: Signature)
    : Problem =
    def simplify
      (v: VTerm, p: Pattern, ty: VTerm)
      (using Σ: Signature)
      : Option[List[ElabConstraint]] =
      // It's assumed that v is already normalized. The only place un-normalized term may appear
      // during elaboration is through unification. But unification pre-normalizes terms so in
      // here all terms are already normalized.
      (v, p) match
        case (DataType(qn, args), PDataType(pQn, pArgs)) if qn == pQn =>
          val data = Σ.getData(qn)
          // TODO[P3]: consider changing some of the following runtime error to IrErrors if user input
          // can cause it to happen.
          assert(
            args.size == pArgs.size && pArgs.size == data.context.size + data.tIndexTys.size,
          )
          simplifyAll(
            args
              .lazyZip(pArgs)
              .lazyZip(data.context.map(_._1.ty) ++ data.tIndexTys.map(_.ty))
              .map(ElabConstraint.apply)
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
            args.size == pArgs.size && pArgs.size == data.context.size + data.tIndexTys.size,
          )
          simplifyAll(
            args
              .lazyZip(pArgs)
              .lazyZip(data.context.map(_._1.ty) ++ data.tIndexTys.map(_.ty))
              .map(ElabConstraint.apply)
              .toList,
          )
        case (Con(name, args), PConstructor(pName, pArgs)) if name == pName =>
          // TODO[P3]: consider changing some of the following runtime error to IrErrors if user input
          // can cause it to happen.
          val dataType = ty.asInstanceOf[DataType]
          val constructor = Σ.getConstructor(dataType.qn, name)
          val _As = constructor.paramTys.substLowers(dataType.args*)
          assert(args.size == pArgs.size && pArgs.size == _As.size)
          simplifyAll(args.lazyZip(pArgs).lazyZip(_As.map(_.ty)).map(ElabConstraint.apply).toList)
        case (Con(_, _), PConstructor(_, _))                     => None
        case (Con(name, args), PForcedConstructor(pName, pArgs)) =>
          // TODO[P3]: instead of assert, report a use-friendly error if name doesn't match
          // because such a mismatch means the provided forced pattern is not correct.
          assert(name == pName)
          val dataType = ty.asInstanceOf[DataType]
          val constructor = Σ.getConstructor(dataType.qn, name)
          val _As = constructor.paramTys.substLowers(dataType.args*)
          assert(args.size == pArgs.size && pArgs.size == _As.size)
          simplifyAll(args.lazyZip(pArgs).lazyZip(_As.map(_.ty)).map(ElabConstraint.apply).toList)
        case (v, p) => Some(List(ElabConstraint(v, p, ty)))

    @throws(classOf[IrError])
    def simplifyAll
      (constraints: List[ElabConstraint])
      (using Σ: Signature)
      : Option[List[ElabConstraint]] =
      constraints match
        case Nil => Some(Nil)
        case ElabConstraint(v, p, _A) :: constraints =>
          val _E1 = simplify(v, p, _A)
          val _E2 = simplifyAll(constraints)
          _E1.zip(_E2).map(_ ++ _)
    problem match
      case Nil => Nil
      case ElabClause(_E, q̅, rhs, source) :: problem =>
        val optionE = simplifyAll(_E.map { case ElabConstraint(v, p, _A) =>
          ElabConstraint(v.subst(σ), p, _A)
        })
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
    (problem, checkIsCType(_C).normalized(None)) match
      // [cosplit]
      case (
          ElabClause(_, CProjection(_) :: _, _, _) :: _,
          RecordType(qn, args, _),
        ) =>
        val (_Σ, fields) = Σ
          .getFields(qn)
          .foldLeft[(Signature, SeqMap[Name, CaseTree])]((Σ, SeqMap())):
            case ((_Σ, fields), field) =>
              val (_Σmod, ct) = elaborate(
                q̅ :+ CProjection(field.name),
                field.ty.substLowers(args :+ Thunk(apply(qn, q̅))*),
                filter(problem, field.name),
              )(using Γ)(using _Σ)

              (_Σmod, fields + (field.name -> ct))
        (_Σ, CtRecord(fields))
      // [cosplit empty]
      // Note: here we don't require an absurd pattern like in [1]. Instead, we require no more
      // user (projection) pattern. This seems more natural.
      case (ElabClause(_, Nil, None, source) :: _, RecordType(qn, _, _)) =>
        Σ.getFields(qn).size match
          // There is no need to modify Σ because empty record does not have any clause
          case 0 => (Σ, CtRecord(SeqMap()))
          case _ => throw MissingFieldsInCoPattern(source)
      // [intro]
      case (
          ElabClause(_, CPattern(_) :: _, _, _) :: _,
          FunctionType(unsolvedBinding, bodyTy, _),
        ) =>
        val binding = unsolvedBinding.map(ctx.solveTerm)
        val _A = shift(problem, binding.ty)
        val (_Σ1, _Q) = elaborate(
          q̅.map(_.weakened) :+ CPattern(PVar(0)),
          bodyTy,
          _A,
        )(using Γ :+ binding)
        (_Σ1, CtLambda(_Q)(binding.name))
      // mismatch between copattern and _C
      case (ElabClause(_, q :: _, _, source) :: _, _) =>
        throw UnexpectedUserCoPattern(source, q)
      // All copatterns are introduced. Now start doing split
      case (ElabClause(_, Nil, _, _) :: _, _) =>
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
            // Start with a very generic error in case no split actions cannot be taken at all.
            Left(UnsolvedElaboration(source1)),
          ):
            // If a split action was successful, skip any further actions on the remaining
            // constraints.
            case (Right(r), _) => Right(r)

            // split data type
            case (_, ElabConstraint(x: Var, PDataType(_, _), _A)) =>
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
                    case ElabConstraint(y: Var, PDataType(qn, _), _) <- constraints
                    if x == y
                  yield Some(qn))

                //  2. do case split with {Qn_1, Qn_2, ..., Qn_k, x}, where x is simply a Var
                //     for "catch all" case. Note that matching "Var" would cause `solve` to
                //     fail unless there is a PVar pattern.
                qns
                  .foldLeft[
                    Either[
                      IrError,
                      (Signature, SeqMap[QualifiedName, CaseTree], Option[CaseTree]),
                    ],
                  ](
                    Right(Σ, SeqMap(), None),
                  ):
                    // Normal type case
                    case (Right(_, branches, defaultCase), Some(qn)) =>
                      val data = Σ.getData(qn)
                      // in context _Γ1
                      val Δ = data.context.map(_._1)

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

                      val newProblem = subst(problem, ρ2t)
                      if newProblem.isEmpty then
                        throw IllegalStateException(
                          "impossible because the type qualified names are collected from clauses in the problem",
                        )
                      for case (_Σ, branch) <- split(
                          q̅.map(_.subst(ρ2)),
                          _C.subst(ρ2t),
                          newProblem,
                        )
                      yield (_Σ, branches + (qn -> branch), defaultCase)
                    // Default `x` catch-all case
                    case (Right(_, branches, _), None) =>
                      val newProblem = subst(problem, Substitutor.id(Γ.size))
                      if newProblem.isEmpty then throw MissingDefaultTypeCase()
                      for case (_Σ, branch) <- split(q̅, _C, newProblem)
                      yield (_Σ, branches, Some(branch))
                    case (Left(e), _) => Left(e)
                  .map:
                    //  3. generate cases, where the branch corresponding to `x` goes to the default
                    //     case
                    case (_Σ, branches, Some(defaultCase)) =>
                      (_Σ, CtTypeCase(x, branches, defaultCase))
                    case _ =>
                      throw IllegalStateException(
                        "impossible because missing default case should have caused missing default type error",
                      )

            // split constructor
            case (_, ElabConstraint(x: Var, PConstructor(_, _), _A @ DataType(qn, _))) =>
              if !providedAtLeastU1Usage(x) then Left(InsufficientResourceForSplit(x, Γ.resolve(x)))
              else
                val (_Γ1, binding, _Γ2) = Γ.split(x)
                assert(
                  binding.ty.weaken(_Γ2.size + 1, 0) == _A,
                  "these types should be identical because they are created by [intro]",
                )
                val data = Σ.getData(qn)
                Σ.getConstructors(qn)
                  .foldLeft[Either[IrError, (Signature, SeqMap[Name, CaseTree])]](
                    Right(Σ, SeqMap()),
                  ):
                    case (Right(_Σ, branches), constructor) =>
                      given Signature = _Σ
                      // in context _Γ1
                      val tArgs = binding.ty.asInstanceOf[DataType].args
                      val Δ = constructor.paramTys.substLowers(tArgs*)

                      // in context _Γ1 ⊎ Δ
                      val cTArgs = constructor.tArgs.map(
                        _.substLowers(tArgs ++ vars(constructor.paramTys.size - 1)*),
                      )
                      val unificationResult = unifyAll(
                        tArgs.drop(data.context.size).map(_.weaken(Δ.size, 0)),
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
                          given ΓSplit: Context =
                            _Γ1 ++ Δ.subst(ρ.toTermSubstitutor) ++ _Γ2.subst(ρ1t)
                          ctx.debug(ΓSplit)

                          val newProblem = subst(problem, ρ2t)
                          if newProblem.isEmpty then
                            throw MissingConstructorCase(qn, constructor.name)
                          for case (_Σ, branch) <- split(
                              q̅.map(_.subst(ρ2)),
                              _C.subst(ρ2t),
                              newProblem,
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
                  .map { case (_Σ, branches) => (_Σ, CtDataCase(x, qn, branches)) }

            // split empty
            case (_, ElabConstraint(x: Var, PAbsurd(), _A)) =>
              _A match
                case DataType(qn, args) =>
                  val data = Σ.getData(qn)
                  val isEmpty = Σ
                    .getConstructors(qn)
                    .forall(constructor => {
                      // all constructor arg unification fails
                      val tParamArgs = args.take(data.context.size)
                      val tIndexArgs = args.drop(data.context.size)
                      val conTArgs = constructor.tArgs.map(_.substLowers(tParamArgs*))
                      val newΓ = Γ ++ constructor.paramTys.substLowers(tParamArgs*)
                      // All unification should be successful or inconclusive. That is, no failure is found.
                      unifyAll(
                        tIndexArgs.map(_.weaken(constructor.paramTys.size, 0)),
                        conTArgs,
                        data.tIndexTys
                          .substLowers(tParamArgs*)
                          .weaken(constructor.paramTys.size, 0),
                      )(using newΓ) match
                        case _: UNo => true
                        case _      => false
                    })
                  if isEmpty then Right(Σ, CtDataCase(x, qn, SeqMap()))
                  else Left(NonEmptyType(_A, source1))
                case _ => Left(NonEmptyType(_A, source1))
            // No action to do, just forward the previous error
            case (l, _) => l
          match
            case Right(r) => Right(r)

            // [done]: no action can be taken, try [done] or fail with error of last action, which
            // could be missing constructor case, non-empty type, etc.
            case Left(e) =>
              for
                rhs1 <- rhs1 match
                  case Some(rhs1) => Right(rhs1)
                  case None       => Left(e)
                σOption = solve(_E1)
                rhs1 <- σOption match
                  case Some(σ) => Right(checkType(rhs1.subst(σ), _C))
                  case None    => Left(e)
                _ <-
                  val rhs1Usages = collectUsages(rhs1, Some(_C))
                  val constraints = checkUsagesSubsumption(rhs1Usages)
                  if constraints.isEmpty then Right(())
                  else Left(UnsatisfiedUsageRequirements(constraints))
              yield
                val solvedRhs = ctx.solveTerm(rhs1)
                (
                  Σ.addClause(
                    preDefinition.qn,
                    Clause(ctx.solveTerm(Γ), q̅, solvedRhs, ctx.solveTerm(_C)),
                  ),
                  CtTerm(solvedRhs),
                )
        split(q̅, _C, problem) match
          case Right(r) => r
          case Left(e)  => throw e
      case (Nil, _) => throw IncompleteClauses(preDefinition.qn)

  val definition = Σ.getDefinition(preDefinition.qn)
  given Context = definition.context

  ctx.trace(s"elaborating def body ${preDefinition.qn}"):
    val (_Σ, _Q) = elaborate(
      Nil,
      definition.ty,
      preDefinition.clauses.map { case source @ PreClause(_, lhs, rhs) =>
        ElabClause(Nil, lhs, rhs, source)
      },
    )
    _Σ.addCaseTree(preDefinition.qn, _Q)

@throws(classOf[IrError])
private def elaborateEffectHead
  (effect: PreEffect)
  (using Γ: Context)
  (using Σ: Signature)
  (using ctx: TypingContext)
  : Signature =
  if Σ.getEffectOption(effect.qn).isDefined then throw DuplicatedDeclaration(effect.qn)
  ctx.trace(s"elaborating effect signature ${effect.qn}"):
    val tParamTys = elaborateTelescope(effect.tParamTys)(using Γ)
    given Γ2: Context = Γ ++ tParamTys
    val continuationUsage = checkType(effect.continuationUsage, F(UsageType()))
      .normalized(Some(F(UsageType()))) match
      case Return(continuationUsage, _) => continuationUsage
      case c                            => throw ExpectReturnAValue(c)
    val handlerType = checkType(effect.handlerType, F(HandlerTypeType()))
      .normalized(Some(F(HandlerTypeType()))) match
      case Return(handlerType, _) => handlerType
      case c                      => throw ExpectReturnAValue(c)

    val e: Effect = Effect(effect.qn, Γ2, continuationUsage, handlerType)
    Σ.addDeclaration(checkEffect(e))

@throws(classOf[IrError])
private def elaborateEffectBody
  (preEffect: PreEffect)
  (using Σ: Signature)
  (using ctx: TypingContext)
  : Signature =
  val effect = Σ.getEffect(preEffect.qn)

  given Context = effect.context

  ctx.trace(s"elaborating effect body ${effect.qn}"):
    def elaborateTy
      (ty: CTerm)
      (using Γ: Context)
      (using Signature)
      (using TypingContext)
      : (Telescope, /* operation return type */ VTerm, /* operation return usage */ VTerm) =
      checkIsCType(ty).normalized(None) match
        // Here and below we do not care the declared effect types because data type constructors
        // are always total. Declaring non-total signature is not necessary (nor desirable) but
        // acceptable.
        case F(ty, _, usage) =>
          (Nil, ty, usage)
        case FunctionType(binding, bodyTy, _) =>
          val (telescope, level, usage) = elaborateTy(bodyTy)(using Γ :+ binding)
          (binding :: telescope, level, usage)
        case _ => throw ExpectFType(ty)

    preEffect.operations.foldLeft[Signature](Σ) { case (_Σ, operation) =>
      given Signature = _Σ
      ctx.trace(s"elaborating operation ${operation.name}"):
        val (paramTys, resultTy, usage) = elaborateTy(operation.ty)
        val o = Operation(operation.name, paramTys, resultTy, usage)
        _Σ.addOperation(effect.qn, checkOperation(effect.qn, o))
    }

@throws(classOf[IrError])
private def elaborateTTelescope
  (tTelescope: PreTTelescope)
  (using Context)
  (using Signature)
  (using TypingContext)
  : TTelescope =
  elaborateTelescope(tTelescope.map(_._1)).zip(tTelescope.map(_._2))

@throws(classOf[IrError])
private def elaborateTelescope
  (telescope: PreTelescope)
  (using Γ: Context)
  (using Signature)
  (using ctx: TypingContext)
  : Telescope = telescope match
  case Nil => Nil
  case binding :: context =>
    ctx.trace("elaborating context"):
      val ty = reduceVType(binding.ty)
      val usage = reduceUsage(binding.usage)
      val newBinding = Binding(ty, usage)(binding.name)
      newBinding :: elaborateTelescope(context)(using Γ :+ newBinding)

// [1] Jesper Cockx and Andreas Abel. 2018. Elaborating dependent (co)pattern matching. Proc. ACM
// Program. Lang. 2, ICFP, Article 75 (September 2018), 30 pages. https://doi.org/10.1145/3236770
