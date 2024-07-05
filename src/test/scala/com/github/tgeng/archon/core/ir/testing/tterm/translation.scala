package com.github.tgeng.archon.core.ir.testing.tterm

import com.github.tgeng.archon.common.{MutableRef, Nat}
import com.github.tgeng.archon.core.common.Name.Normal
import com.github.tgeng.archon.core.common.{Name, QualifiedName, gn}
import com.github.tgeng.archon.core.ir.*
import com.github.tgeng.archon.core.ir.CTerm.*
import com.github.tgeng.archon.core.ir.PreDeclaration.*
import com.github.tgeng.archon.core.ir.SourceInfo.SiEmpty
import com.github.tgeng.archon.core.ir.VTerm.*
import com.github.tgeng.archon.core.ir.testing.tterm.GlobalNameInfo.*
import com.github.tgeng.archon.core.ir.testing.tterm.TCoPattern.*
import com.github.tgeng.archon.core.ir.testing.tterm.TDeclaration.*
import com.github.tgeng.archon.core.ir.testing.tterm.TPattern.*
import com.github.tgeng.archon.core.ir.testing.tterm.TTerm.*
import com.github.tgeng.archon.core.ir.testing.tterm.TranslationError.UnresolvedSymbol

import scala.collection.immutable.SeqMap
import scala.collection.mutable

enum TranslationError(msg: String) extends Exception(msg):
  case UnresolvedSymbol(name: String) extends TranslationError(s"Unresolved symbol: $name")

enum GlobalNameInfo:
  case GDef(qn: QualifiedName)
  case GData(qn: QualifiedName)
  case GDataValue(n: Name)
  case GRecord(qn: QualifiedName)
  case GEffect(qn: QualifiedName)

case class TranslationContext
  (
    moduleQn: QualifiedName,
    localVarCount: Int = 0,
    localVars: Map[String, Int] = Map.empty,
    globalDefs: Map[String, GlobalNameInfo] = Map.empty,
    ignoreUnresolvableGlobalName: Boolean = false,
    isTypeLevel: Boolean = false,
  ):
  def bindLocal(names: String*): TranslationContext =
    this.copy(
      localVarCount = localVarCount + names.size,
      localVars = localVars ++ names.zipWithIndex.map((n, i) => n -> (localVarCount + i)),
    )

  def bindDef(name: String, qn: QualifiedName): TranslationContext =
    this.copy(globalDefs = globalDefs + (name -> GDef(qn)))

  def bindDef(name: String): TranslationContext =
    bindDef(name, moduleQn / name)

  def bindDataDecl(data: TData): TranslationContext =
    this.copy(
      globalDefs = globalDefs +
        (data.name -> GData(moduleQn / data.name)) ++
        data.constructors.map(c => c.name -> GDataValue(Name.Normal(c.name))),
    )

  def bindRecordDecl(record: TRecord): TranslationContext =
    this.copy(
      globalDefs = globalDefs + (record.name -> GRecord(moduleQn / record.name)),
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
            globalDefs = globalDefs +
              (data.qn.shortName.toString -> GData(data.qn)) ++
              data.constructors.map(c => c.name.toString -> GDataValue(c.name)),
          )
        case record: PreRecord =>
          ctx.copy(
            globalDefs = globalDefs +
              (record.qn.shortName.toString -> GRecord(record.qn)),
          )
        case _ => ctx.bindDef(decl.qn.shortName.toString, decl.qn)
    }

  def lookup(name: String): Either[Nat, GlobalNameInfo] =
    localVars.get(name) match
      case Some(index) => Left(localVarCount - 1 - index)
      case None        => Right(lookupGlobal(name))

  def lookupLocal(name: String): Nat = localVars.get(name) match
    case Some(index) => localVarCount - 1 - index
    case None        => throw UnresolvedSymbol(name)

  def lookupGlobal(name: String): GlobalNameInfo = globalDefs.get(name) match
    case Some(g)                              => g
    case None if ignoreUnresolvableGlobalName => GDef(QualifiedName.Root / "__unresolved__" / name)
    case None                                 => throw UnresolvedSymbol(name)

extension (tTerm: TTerm)
  def toCTerm(using ctx: TranslationContext): CTerm =
    given SourceInfo = tTerm.sourceInfo
    tTerm match
      case TAuto() => Return(Auto())
      case TCon(name, args) =>
        translate(args*) { case args =>
          given SourceInfo = tTerm.sourceInfo
          ctx.globalDefs.get(name) match
            case Some(GData(qn))     => Return(DataType(qn, args.toList))
            case Some(GDataValue(n)) => Return(Con(n, args.toList))
            case Some(GEffect(qn))   => Return(EffectsLiteral(Set((qn, args.toList))))
            case Some(GRecord(qn))   => RecordType(qn, args.toList)
            case _                   => throw UnresolvedSymbol(name)
        }
      case TU(t)                => Return(U(t.toCTerm(using ctx.copy(isTypeLevel = true))))
      case TThunk(t)            => Return(Thunk(t.toCTerm))
      case TLevelLiteral(level) => Return(LevelLiteral(level))
      case TId(id) =>
        ctx.lookup(id) match
          case Left(index)          => Return(Var(index))
          case Right(GDef(qn))      => Def(qn)
          case Right(GData(qn))     => Return(DataType(qn, Nil))
          case Right(GDataValue(n)) => Return(Con(n, Nil))
          case Right(GRecord(qn))   => RecordType(qn, Nil)
          case Right(GEffect(qn))   => Return(EffectsLiteral(Set((qn, Nil))))
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
      case TpId(name) =>
        ctx.lookup(name) match
          case Left(index)          => Pattern.PVar(index)
          case Right(GData(qn))     => Pattern.PDataType(qn, Nil)
          case Right(GDataValue(n)) => Pattern.PConstructor(n, Nil)
          case Right(GRecord(_)) | Right(GEffect(_)) | Right(GDef(_)) =>
            throw UnresolvedSymbol(name)
      case TpXConstructor(forced, name, args) =>
        val argPatterns = args.map(_.toPattern).toList
        ctx.globalDefs.get(name) match
          case Some(GData(qn)) =>
            if forced then Pattern.PForcedDataType(qn, argPatterns)
            else Pattern.PDataType(qn, argPatterns)
          case Some(GDataValue(n)) =>
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
  def collectPatternNames(using ctx: TranslationContext): List[String] =
    val names = mutable.ArrayBuffer.empty[String]
    def processPattern(pattern: TPattern): Unit = pattern match
      case TpId(name) =>
        ctx.globalDefs.get(name) match
          // skip existing data type and value constructors
          case Some(_: (GData | GDataValue)) =>
          case _                             => names.addOne(name)
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
        val tParamTysCTerm = translateTParamTysWithVariance(tParamTys.toList)
        {
          given TranslationContext = ctx.bindLocal(tParamTys.map(_._1.name)*)
          val tyCTerm = ty.toCTerm
          val constructorCTerms = constructors.map(_.toPreConstructor)
          PreDeclaration.PreData(
            ctx.moduleQn / name,
            tParamTysCTerm,
            tyCTerm,
            constructorCTerms.toList,
          )
        }
      case TRecord(selfName, name, tParamTys, ty, fields) =>
        val tParamTysCTerm = translateTParamTysWithVariance(tParamTys.toList)
        {
          given TranslationContext = ctx.bindLocal(tParamTys.map(_._1.name)*)
          val tyCTerm = ty.toCTerm
          val fieldCTerms = fields.map(_.toPreField)
          PreDeclaration.PreRecord(
            ctx.moduleQn / name,
            tParamTysCTerm,
            tyCTerm,
            fieldCTerms.toList,
          )
        }
      case TDefinition(name, tParamTys, ty, clauses) =>
        val tParamTysCTerm = translateTParamTys(tParamTys.toList)
        {
          given TranslationContext = ctx.bindLocal(tParamTys.map(_.name)*)
          val tyCTerm = ty.toCTerm
          val clauseCTerms = clauses.map(_.toPreClause)
          PreDeclaration.PreDefinition(
            ctx.moduleQn / name,
            tParamTysCTerm,
            tyCTerm,
            clauseCTerms.toList,
          )
        }

private def translateTParamTys
  (bindings: List[TBinding])
  (using ctx: TranslationContext)
  : List[Binding[CTerm]] =
  bindings match
    case Nil => Nil
    case TBinding(name, ty, usage) :: rest =>
      Binding(ty.toCTerm, usage.toCTerm)(Name.Normal(name)) :: translateTParamTys(rest)(using
        ctx.bindLocal(name),
      )

private def translateTParamTysWithVariance
  (bindings: List[(TBinding, Variance)])
  (using ctx: TranslationContext)
  : List[(Binding[CTerm], Variance)] =
  bindings match
    case Nil => Nil
    case (TBinding(name, ty, usage), variance) :: rest =>
      (
        Binding(ty.toCTerm, usage.toCTerm)(Name.Normal(name)),
        variance,
      ) :: translateTParamTysWithVariance(rest)(using
        ctx.bindLocal(name),
      )

extension (tc: TConstructor)
  def toPreConstructor(using ctx: TranslationContext): PreConstructor =
    PreConstructor(Name.Normal(tc.name), tc.ty.toCTerm)

extension (tf: TField)
  def toPreField(using ctx: TranslationContext): Field =
    Field(Name.Normal(tf.name), tf.ty.toCTerm)

extension (tc: TClause)
  def toPreClause(using ctx: TranslationContext): PreClause =
    val boundNames = tc.patterns.collectPatternNames(using ctx)
    given TranslationContext = ctx.bindLocal(boundNames*)
    val lhs = tc.patterns.map(_.toCoPattern)
    val rhs = tc.body.map(_.toCTerm)
    PreClause(boundNames.map(n => MutableRef(Name.Normal(n))), lhs.toList, rhs)
