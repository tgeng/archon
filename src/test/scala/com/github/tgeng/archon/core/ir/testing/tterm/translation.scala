package com.github.tgeng.archon.core.ir.testing.tterm

import com.github.tgeng.archon.common.{MutableRef, Nat}
import com.github.tgeng.archon.core.common.Name.Normal
import com.github.tgeng.archon.core.common.{Name, QualifiedName, gn}
import com.github.tgeng.archon.core.ir.*
import com.github.tgeng.archon.core.ir.CTerm.*
import com.github.tgeng.archon.core.ir.PreDeclaration.*
import com.github.tgeng.archon.core.ir.SourceInfo.SiEmpty
import com.github.tgeng.archon.core.ir.VTerm.*
import com.github.tgeng.archon.core.ir.testing.tterm.ConstructorInfo.*
import com.github.tgeng.archon.core.ir.testing.tterm.TCoPattern.*
import com.github.tgeng.archon.core.ir.testing.tterm.TDeclaration.*
import com.github.tgeng.archon.core.ir.testing.tterm.TPattern.*
import com.github.tgeng.archon.core.ir.testing.tterm.TTerm.*
import com.github.tgeng.archon.core.ir.testing.tterm.TranslationError.UnresolvedSymbol

import scala.collection.immutable.SeqMap
import scala.collection.mutable

enum TranslationError(msg: String) extends Exception(msg):
  case UnresolvedSymbol(name: String) extends TranslationError(s"Unresolved symbol: $name")

enum ConstructorInfo:
  case CiData(qn: QualifiedName)
  case CiDataValue(n: Name)
  case CiRecord(qn: QualifiedName)
  case CiEffect(qn: QualifiedName)

case class TranslationContext
  (
    moduleQn: QualifiedName,
    localVarCount: Int = 0,
    localVars: Map[String, Int] = Map.empty,
    globalDefs: Map[String, QualifiedName] = Map.empty,
    constructorDecls: Map[String, ConstructorInfo] = Map.empty,
    ignoreUnresolvableGlobalName: Boolean = false,
    isTypeLevel: Boolean = false,
  ):
  def bindLocal(names: String*): TranslationContext =
    this.copy(
      localVarCount = localVarCount + names.size,
      localVars = localVars ++ names.zipWithIndex.map((n, i) => n -> (localVarCount + i)),
    )

  def bindDef(name: String, qn: QualifiedName): TranslationContext =
    this.copy(globalDefs = globalDefs + (name -> qn))

  def bindDef(name: String): TranslationContext =
    bindDef(name, moduleQn / name)

  def bindDataDecl(data: TData): TranslationContext =
    this.copy(
      constructorDecls = constructorDecls +
        (data.name -> CiData(moduleQn / data.name)) ++
        data.constructors.map(c => c.name -> CiDataValue(Name.Normal(c.name))),
    )

  def bindRecordDecl(record: TRecord): TranslationContext =
    this.copy(
      constructorDecls = constructorDecls + (record.name -> CiRecord(moduleQn / record.name)),
    )

  def bindDecls(decls: Seq[TDeclaration]): TranslationContext =
    decls.foldLeft(this) { (ctx, decl) =>
      decl match
        case data: TData     => ctx.bindDataDecl(data)
        case record: TRecord => ctx.bindRecordDecl(record)
        case d: TDefinition  => ctx.bindDef(d.name)
    }

  def bindPreDecls(decls: Seq[PreDeclaration]): TranslationContext =
    decls.foldLeft(this) { (ctx, decl) =>
      decl match
        case data: PreData =>
          ctx.copy(
            constructorDecls = constructorDecls +
              (data.qn.shortName.toString -> CiData(data.qn)) ++
              data.constructors.map(c => c.name.toString -> CiDataValue(c.name)),
          )
        case record: PreRecord =>
          ctx.copy(
            constructorDecls = constructorDecls +
              (record.qn.shortName.toString -> CiRecord(record.qn)),
          )
        case _ => ctx.bindDef(decl.qn.shortName.toString, decl.qn)
    }

  def lookup(name: String): Either[Nat, QualifiedName] =
    localVars.get(name) match
      case Some(index) => Left(localVarCount - 1 - index)
      case None        => Right(lookupGlobal(name))

  def lookupLocal(name: String): Nat = localVars.get(name) match
    case Some(index) => localVarCount - 1 - index
    case None        => throw UnresolvedSymbol(name)

  def lookupGlobal(name: String): QualifiedName = globalDefs.get(name) match
    case Some(qn)                             => qn
    case None if ignoreUnresolvableGlobalName => QualifiedName.Root / "__unresolved__" / name
    case None                                 => throw UnresolvedSymbol(name)

extension (tTerm: TTerm)
  def toCTerm(using ctx: TranslationContext): CTerm =
    given SourceInfo = tTerm.sourceInfo
    tTerm match
      case TAuto() => Return(Auto())
      case TCon(name, args) =>
        translate(args*) { case args =>
          Return(VTerm.Con(Name.Normal(name), args.toList)(using tTerm.sourceInfo))
        }
      case TU(t)                => Return(U(t.toCTerm(using ctx.copy(isTypeLevel = true))))
      case TThunk(t)            => Return(Thunk(t.toCTerm))
      case TLevelLiteral(level) => Return(LevelLiteral(level))
      case TId(id) =>
        ctx.lookup(id) match
          case Left(index) => Return(Var(index))
          case Right(qn)   => Def(qn)
      case TDef(qn) => Def(qn)
      case TForce(t) =>
        translate(t) { case Seq(t) =>
          Force(t)
        }
      case TF(ty, effects, usage) =>
        given TranslationContext = ctx.copy(isTypeLevel = true)
        translate(ty, effects, usage) { case Seq(ty, effects, usage) =>
          F(ty, effects, usage)
        }
      case TLet(name, t, ty, effects, usage, body) =>
        given TranslationContext = ctx.copy(isTypeLevel = true)
        translate(ty, effects, usage) { case Seq(ty, effects, usage) =>
          Let(
            t.toCTerm(using ctx),
            Binding(ty, usage)(Name.Normal(name)),
            effects,
            body.toCTerm(using ctx.bindLocal(name)),
          )
        }
      case TRedex(c, elims) =>
        translate(elims.flatMap {
          case Elimination.ETerm(t) => Seq(t)
          case _                    => Seq.empty
        }*):
          case argsSeq =>
            val args = argsSeq.toIndexedSeq
            var index = 0
            val translatedElims = elims.map:
              case Elimination.ETerm(_) =>
                val arg = args(index)
                index = index + 1
                Elimination.ETerm[VTerm](arg)
              case Elimination.EProj(name) => Elimination.EProj[VTerm](name)
            redex(c.toCTerm, translatedElims)
      case TFunctionType(arg, bodyType, effects) =>
        given TranslationContext = ctx.copy(isTypeLevel = true)
        translate(arg.ty, arg.usage, effects) { case Seq(ty, usage, effects) =>
          FunctionType(
            Binding(ty, usage)(Name.Normal(arg.name)),
            bodyType.toCTerm(using summon[TranslationContext].bindLocal(arg.name)),
            effects,
          )
        }
      case THandler(
          eff,
          otherEffects,
          outputEffects,
          outputUsage,
          outputTy,
          parameter,
          parameterBinding,
          parameterDisposer,
          parameterReplicator,
          transform,
          handlers,
          input,
          inputBinding,
        ) =>
        translate(
          eff,
          otherEffects,
          outputEffects,
          outputUsage,
          outputTy,
          parameter,
          parameterBinding.ty,
          parameterBinding.usage,
          inputBinding.ty,
          inputBinding.usage,
        ) {
          case Seq(
              eff,
              otherEffects,
              outputEffects,
              outputUsage,
              outputTy,
              parameter,
              parameterTy,
              parameterUsage,
              inputTy,
              inputUsage,
            ) =>
            Handler(
              eff,
              otherEffects,
              outputEffects,
              outputUsage,
              outputTy,
              parameter,
              Binding(parameterTy, parameterUsage)(Name.Normal(parameterBinding.name)),
              parameterDisposer.map(_.toCTerm),
              parameterReplicator.map(_.toCTerm),
              transform.toCTerm,
              handlers
                .map:
                  case (qn, THandlerImpl(h, body, boundNames)) =>
                    qn -> HandlerImpl(
                      h,
                      body.toCTerm(using
                        summon[TranslationContext].bindLocal(parameterBinding.name +: boundNames*),
                      ),
                      F(Auto(), Auto(), u1),
                      h.handlerType match
                        case HandlerType.Simple  => None
                        case HandlerType.Complex => Some(Auto()),
                    )(boundNames.map(n => Name.Normal(n)))
                .to(SeqMap),
              input.toCTerm,
              Binding(inputTy, inputUsage)(Name.Normal(inputBinding.name)),
            )
        }

def translate
  (tTerms: TTerm*)
  (f: PartialFunction[Seq[VTerm], CTerm])
  (using ctx: TranslationContext)
  : CTerm =
  var index = 0
  val (vterms, cterms) = tTerms
    .map(_.toCTerm)
    .reverse
    .map:
      case Return(v, _)         => (v, None)
      case c if ctx.isTypeLevel => (Collapse(c)(using c.sourceInfo), None)
      case c =>
        val v = Var(index)(using c.sourceInfo)
        index = index + 1
        (v, Some(c))
    .reverse
    .unzip
  given SourceInfo = SiEmpty
  cterms.flatten.foldRight(f(vterms))(Let(_, Binding(Auto(), Auto())(gn"v"), Auto(), _))

extension (tp: TCoPattern)
  def toCoPattern(using TranslationContext): CoPattern =
    given SourceInfo = tp.sourceInfo
    tp match
      case TcProjection(name) => CoPattern.CProjection(Name.Normal(name))
      case TcPattern(pattern) => CoPattern.CPattern(pattern.toPattern)

extension (tp: TPattern)
  def toPattern(using ctx: TranslationContext): Pattern =
    given SourceInfo = tp.sourceInfo
    tp match
      case TpVar(name) => Pattern.PVar(ctx.lookupLocal(name))
      case TpXConstructor(forced, name, args) =>
        val argPatterns = args.map(_.toPattern).toList
        ctx.constructorDecls.get(name) match
          case Some(CiData(qn)) =>
            if forced then Pattern.PForcedDataType(qn, argPatterns)
            else Pattern.PDataType(qn, argPatterns)
          case Some(CiDataValue(n)) =>
            if forced then Pattern.PForcedConstructor(n, argPatterns)
            else Pattern.PConstructor(n, argPatterns)
          case _ =>
            if ctx.ignoreUnresolvableGlobalName then
              val qn = QualifiedName.Root / "__unresolved__" / name
              if forced then Pattern.PForcedDataType(qn, argPatterns)
              else Pattern.PDataType(qn, argPatterns)
            else throw UnresolvedSymbol(name)
      case TpForced(tTerm) => Pattern.PForced(Collapse(tTerm.toCTerm))
      case TPAbsurd()      => Pattern.PAbsurd()

extension (tps: Seq[TCoPattern])
  def collectPatternNames: List[String] =
    val names = mutable.ListBuffer.empty[String]
    def processPattern(pattern: TPattern): Unit = pattern match
      case TpVar(name) =>
        names += name
      case TpXConstructor(_, _, args) =>
        args.foreach(processPattern)
      case _ =>
    def processCoPattern(coPattern: TCoPattern): Unit = coPattern match
      case TcProjection(name) =>
      case TcPattern(pattern) => processPattern(pattern)
    tps.foreach(processCoPattern)
    names.distinct.toList

extension (td: TDeclaration)
  def toPreDeclaration(using ctx: TranslationContext): PreDeclaration =
    td match
      case TData(name, tParamTys, ty, constructors) =>
        val tParamTysCTerm = tParamTys.map:
          case (TBinding(name, ty, usage), variance) =>
            (Binding(ty.toCTerm, usage.toCTerm)(Name.Normal(name)), variance)
        val tyCTerm = ty.toCTerm
        val constructorCTerms = constructors.map(_.toPreConstructor)
        PreDeclaration.PreData(
          ctx.moduleQn / name,
          tParamTysCTerm.toList,
          tyCTerm,
          constructorCTerms.toList,
        )
      case TRecord(selfName, name, tParamTys, ty, fields) =>
        val tParamTysCTerm = tParamTys.map:
          case (TBinding(name, ty, usage), variance) =>
            (Binding(ty.toCTerm, usage.toCTerm)(Name.Normal(name)), variance)
        val tyCTerm = ty.toCTerm
        val fieldCTerms = fields.map(_.toPreField)
        PreDeclaration.PreRecord(
          ctx.moduleQn / name,
          tParamTysCTerm.toList,
          tyCTerm,
          fieldCTerms.toList,
        )
      case TDefinition(name, tParamTys, ty, clauses) =>
        val tParamTysCTerm = tParamTys.map:
          case TBinding(name, ty, usage) =>
            Binding(ty.toCTerm, usage.toCTerm)(Name.Normal(name))
        val tyCTerm = ty.toCTerm
        val clauseCTerms = clauses.map(_.toPreClause)
        PreDeclaration.PreDefinition(
          ctx.moduleQn / name,
          tParamTysCTerm.toList,
          tyCTerm,
          clauseCTerms.toList,
        )

extension (tc: TConstructor)
  def toPreConstructor(using ctx: TranslationContext): PreConstructor =
    PreConstructor(Name.Normal(tc.name), tc.ty.toCTerm)

extension (tf: TField)
  def toPreField(using ctx: TranslationContext): Field =
    Field(Name.Normal(tf.name), tf.ty.toCTerm)

extension (tc: TClause)
  def toPreClause(using ctx: TranslationContext): PreClause =
    val boundNames = tc.patterns.collectPatternNames
    given TranslationContext = ctx.bindLocal(boundNames*)
    val lhs = tc.patterns.map(_.toCoPattern)
    val rhs = tc.body.map(_.toCTerm)
    PreClause(boundNames.map(n => MutableRef(Name.Normal(n))), lhs.toList, rhs)
