package com.github.tgeng.archon.core.ir.testing.tterm

import com.github.tgeng.archon.common.{MutableRef, Nat}
import com.github.tgeng.archon.core.common.{Name, QualifiedName, gn}
import com.github.tgeng.archon.core.ir.*
import com.github.tgeng.archon.core.ir.CTerm.*
import com.github.tgeng.archon.core.ir.VTerm.*
import com.github.tgeng.archon.core.ir.testing.tterm.TCoPattern.*
import com.github.tgeng.archon.core.ir.testing.tterm.TDeclaration.*
import com.github.tgeng.archon.core.ir.testing.tterm.TPattern.*
import com.github.tgeng.archon.core.ir.testing.tterm.TTerm.*
import com.github.tgeng.archon.core.ir.testing.tterm.TranslationError.UnresolvedSymbol

import scala.collection.immutable.SeqMap
import scala.collection.mutable

enum TranslationError extends Exception:
  case UnresolvedSymbol(name: String)

case class TranslationContext
  (
    moduleQn: QualifiedName,
    localVarCount: Int = 0,
    localVars: Map[String, Int] = Map.empty,
    globalDefs: Map[String, QualifiedName] = Map.empty,
    dataDecls: Map[String, QualifiedName] = Map.empty,
    constructorDecls: Set[String] = Set.empty,
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
      dataDecls = dataDecls + (data.name -> (moduleQn / data.name)),
      constructorDecls = constructorDecls ++ data.constructors.map(_.name),
      globalDefs = (globalDefs + (data.name -> moduleQn / data.name)) ++ data.constructors.map(c =>
        c.name -> (moduleQn / data.name / c.name),
      ),
    )

  def lookup(name: String): Either[Nat, QualifiedName] =
    localVars.get(name) match
      case Some(index) => Left(localVarCount - 1 - index)
      case None =>
        globalDefs.get(name) match
          case Some(qualifiedName) => Right(qualifiedName)
          case None                => throw UnresolvedSymbol(name)
  def lookupLocal(name: String): Nat = localVars.get(name) match
    case Some(index) => localVarCount - 1 - index
    case None        => throw UnresolvedSymbol(name)

  def lookupGlobal(name: String): QualifiedName = globalDefs.get(name) match
    case Some(qn) => qn
    case None     => throw UnresolvedSymbol(name)

extension (tTerm: TTerm)
  def toCTerm(using context: TranslationContext): CTerm =
    given SourceInfo = tTerm.sourceInfo
    tTerm match
      case TAuto()              => Return(Auto())
      case TU(t)                => Return(U(t.toCTerm))
      case TThunk(t)            => Return(Thunk(t.toCTerm))
      case TLevelLiteral(level) => Return(LevelLiteral(level))
      case TId(id) =>
        context.lookup(id) match
          case Left(index) => Return(Var(index))
          case Right(qn)   => Def(qn)
      case TDef(qn)  => Def(qn)
      case TForce(t) => t.toCTerm.flatMap(Force(_))
      case TF(ty, effects, usage) =>
        for
          ty <- ty.toCTerm
          effects <- effects.toCTerm
          usage <- usage.toCTerm
          r <- F(ty, effects, usage)
        yield r
      case TLet(name, t, ty, effects, usage, body) =>
        for
          ty <- ty.toCTerm
          effects <- effects.toCTerm
          usage <- usage.toCTerm
          r <- Let(
            t.toCTerm,
            ty,
            effects,
            usage,
            body.toCTerm(using summon[TranslationContext].bindLocal(name)),
          )(Name.Normal(name))
        yield r
      case TApp(f, arg) =>
        for
          arg <- arg.toCTerm
          r <- redex(f.toCTerm, arg)
        yield r
      case TFunctionType(arg, bodyType, effects) =>
        for
          effects <- effects.toCTerm
          argTy <- arg.ty.toCTerm
          argUsage <- arg.usage.toCTerm
          r <- FunctionType(
            Binding(argTy, argUsage)(Name.Normal(arg.name)),
            bodyType.toCTerm(using summon[TranslationContext].bindLocal(arg.name)),
            effects,
          )
        yield r
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
        for
          eff <- eff.toCTerm
          otherEffects <- otherEffects.toCTerm
          outputEffects <- outputEffects.toCTerm
          outputUsage <- outputUsage.toCTerm
          outputTy <- outputTy.toCTerm
          parameter <- parameter.toCTerm
          parameterTy <- parameterBinding.ty.toCTerm
          parameterUsage <- parameterBinding.usage.toCTerm
          inputTy <- inputBinding.ty.toCTerm
          inputUsage <- inputBinding.usage.toCTerm
          r <- Handler(
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
              .map { case (qn, THandlerImpl(h, body, boundNames)) =>
                qn -> HandlerImpl(
                  h,
                  body.toCTerm(using
                    summon[TranslationContext].bindLocal(parameterBinding.name +: boundNames*),
                  ),
                )(boundNames.map(n => Name.Normal(n)))
              }
              .to(SeqMap),
            input.toCTerm,
            Binding(inputTy, inputUsage)(Name.Normal(inputBinding.name)),
          )
        yield r

extension (self: CTerm)
  def map(f: TranslationContext ?=> VTerm => VTerm)(using ctx: TranslationContext): CTerm =
    val newCtx = ctx.bindLocal("")
    given SourceInfo = SourceInfo.SiEmpty
    Let(
      self,
      Auto(),
      Auto(),
      Auto(),
      Return(f(using newCtx)(Var(0))),
    )(gn"v")

  def flatMap(f: TranslationContext ?=> VTerm => CTerm)(using ctx: TranslationContext): CTerm =
    val newCtx = ctx.bindLocal("")
    given SourceInfo = SourceInfo.SiEmpty
    Let(
      self,
      Auto(),
      Auto(),
      Auto(),
      f(using newCtx)(Var(0)),
    )(gn"v")

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
        ctx.dataDecls.get(name) match
          case Some(qn) =>
            if forced then Pattern.PForcedDataType(qn, argPatterns)
            else Pattern.PDataType(qn, argPatterns)
          case None =>
            if ctx.constructorDecls(name) then
              if forced then Pattern.PForcedConstructor(Name.Normal(name), argPatterns)
              else Pattern.PConstructor(Name.Normal(name), argPatterns)
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
        PreDeclaration.PreData(ctx.moduleQn / name)(
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
        PreDeclaration.PreRecord(ctx.moduleQn / name)(
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
        PreDeclaration.PreDefinition(ctx.moduleQn / name)(
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
