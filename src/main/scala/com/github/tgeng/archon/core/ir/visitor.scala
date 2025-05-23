package com.github.tgeng.archon.core.ir

import com.github.tgeng.archon.common.*
import com.github.tgeng.archon.common.eitherUtil.*
import com.github.tgeng.archon.core.common.*
import com.github.tgeng.archon.core.ir.CTerm.*
import com.github.tgeng.archon.core.ir.CaseTree.*
import com.github.tgeng.archon.core.ir.CoPattern.*
import com.github.tgeng.archon.core.ir.Pattern.*
import com.github.tgeng.archon.core.ir.VTerm.*

trait TermVisitor[C, R]:
  def combine(rs: R*)(using ctx: C)(using Σ: Signature)(using TypingContext): R

  def withTelescope
    (telescope: => Telescope)
    (action: C ?=> R)
    (using ctx: C)
    (using Σ: Signature)
    (using TypingContext)
    : R

  def visitBinding
    (binding: Binding[VTerm])
    (using ctx: C)
    (using Σ: Signature)
    (using TypingContext)
    : R =
    combine(visitVTerm(binding.ty), visitVTerm(binding.usage))

  def visitTelescope
    (telescope: List[Binding[VTerm]])
    (using ctx: C)
    (using Σ: Signature)
    (using TypingContext)
    : R =
    telescope match
      case Nil => combine()
      case binding :: rest =>
        combine(
          visitBinding(binding),
          withTelescope(List(binding)) {
            visitTelescope(rest)
          },
        )

  def visitVTerm(tm: VTerm)(using ctx: C)(using Σ: Signature)(using TypingContext): R = tm match
    case ty: Type                               => visitType(ty)
    case top: Top                               => visitTop(top)
    case v: Var                                 => visitVar(v)
    case collapse: Collapse                     => visitCollapse(collapse)
    case u: U                                   => visitU(u)
    case thunk: Thunk                           => visitThunk(thunk)
    case dataType: DataType                     => visitDataType(dataType)
    case con: Con                               => visitCon(con)
    case usageType: UsageType                   => visitUsageType(usageType)
    case usageLiteral: UsageLiteral             => visitUsageLiteral(usageLiteral)
    case usageProd: UsageProd                   => visitUsageProd(usageProd)
    case usageSum: UsageSum                     => visitUsageSum(usageSum)
    case usageJoin: UsageJoin                   => visitUsageJoin(usageJoin)
    case effectsType: EffectsType               => visitEffectsType(effectsType)
    case effects: Effects                       => visitEffects(effects)
    case levelType: LevelType                   => visitLevelType(levelType)
    case level: Level                           => visitLevel(level)
    case effectInstanceType: EffectInstanceType => visitEffectInstanceType(effectInstanceType)
    case effectInstance: EffectInstance         => visitEffectInstance(effectInstance)
    case auto: Auto                             => visitAuto(auto)

  def visitType(ty: Type)(using ctx: C)(using Σ: Signature)(using TypingContext): R =
    visitVTerm(ty.upperBound)

  def visitTop(top: Top)(using ctx: C)(using Σ: Signature)(using TypingContext): R = combine(
    visitVTerm(top.level),
  )

  def visitVar(v: Var)(using ctx: C)(using Σ: Signature)(using TypingContext): R = combine()

  def visitCollapse(collapse: Collapse)(using ctx: C)(using Σ: Signature)(using TypingContext): R =
    visitCTerm(collapse.cTm)

  def visitU(u: U)(using ctx: C)(using Σ: Signature)(using TypingContext): R = visitCTerm(u.cTy)

  def visitThunk(thunk: Thunk)(using ctx: C)(using Σ: Signature)(using TypingContext): R =
    visitCTerm(thunk.c)

  def visitDataType(dataType: DataType)(using ctx: C)(using Σ: Signature)(using TypingContext): R =
    combine(
      visitQualifiedName(dataType.qn) +:
        dataType.args.map(visitVTerm)*,
    )

  def visitCon(con: Con)(using ctx: C)(using Σ: Signature)(using TypingContext): R =
    combine(
      visitName(con.name) +:
        con.args.map(visitVTerm)*,
    )

  def visitUsageType
    (usageType: UsageType)
    (using ctx: C)
    (using Σ: Signature)
    (using TypingContext)
    : R =
    combine(
      (visitQualifiedName(Builtins.UsageQn) +: usageType.upperBound.map(visitVTerm).toSeq)*,
    )

  def visitUsageLiteral
    (usageLiteral: UsageLiteral)
    (using ctx: C)
    (using Σ: Signature)
    (using TypingContext)
    : R =
    combine()

  def visitUsageProd
    (usageProd: UsageProd)
    (using ctx: C)
    (using Σ: Signature)
    (using TypingContext)
    : R =
    combine(usageProd.operands.map(visitVTerm).toSeq*)

  def visitUsageSum(usageSum: UsageSum)(using ctx: C)(using Σ: Signature)(using TypingContext): R =
    combine(usageSum.operands.map(visitVTerm).toSeq*)

  def visitUsageJoin
    (usageJoin: UsageJoin)
    (using ctx: C)
    (using Σ: Signature)
    (using TypingContext)
    : R =
    combine(usageJoin.operands.map(visitVTerm).toSeq*)

  def visitEffectsType
    (effectsType: EffectsType)
    (using ctx: C)
    (using Σ: Signature)
    (using TypingContext)
    : R =
    visitQualifiedName(Builtins.EffectsQn)

  def visitEffects(effects: Effects)(using ctx: C)(using Σ: Signature)(using TypingContext): R =
    combine(
      (effects.handlerKeys.map(visitVTerm) ++ effects.unionOperands.keys.map(
        visitVTerm,
      )).toSeq*,
    )

  def visitLevelType
    (levelType: LevelType)
    (using ctx: C)
    (using Σ: Signature)
    (using TypingContext)
    : R =
    visitQualifiedName(Builtins.LevelQn)

  def visitLevel(level: Level)(using ctx: C)(using Σ: Signature)(using TypingContext): R =
    combine(
      level.maxOperands.map { case (v, _) =>
        visitVTerm(v)
      }.toSeq*,
    )

  def visitEffectInstanceType
    (instanceType: EffectInstanceType)
    (using ctx: C)
    (using Σ: Signature)
    (using TypingContext)
    : R =
    visitEff(instanceType.eff)

  def visitEffectInstance
    (instance: VTerm.EffectInstance)
    (using ctx: C)
    (using Σ: Signature)
    (using TypingContext)
    : R =
    visitEff(instance.eff)

  def visitAuto(auto: Auto)(using ctx: C)(using Σ: Signature)(using TypingContext): R = combine()

  def visitHole(using ctx: C)(using Σ: Signature)(using TypingContext): R = combine()

  def visitCapturedContinuationTip
    (cct: CapturedContinuationTip)
    (using ctx: C)
    (using Σ: Signature)
    (using TypingContext)
    : R =
    visitF(cct.ty)

  def visitCType(cType: CType)(using ctx: C)(using Σ: Signature)(using TypingContext): R =
    combine(
      visitCTerm(cType.upperBound),
      visitVTerm(cType.effects),
    )

  def visitCTop(cTop: CTop)(using ctx: C)(using Σ: Signature)(using TypingContext): R =
    combine(
      visitVTerm(cTop.level),
      visitVTerm(cTop.effects),
    )

  def visitMeta(m: Meta)(using ctx: C)(using Σ: Signature)(using TypingContext): R = combine()

  def visitDef(d: Def)(using ctx: C)(using Σ: Signature)(using TypingContext): R =
    visitQualifiedName(d.qn)

  def visitForce(force: Force)(using ctx: C)(using Σ: Signature)(using TypingContext): R =
    visitVTerm(force.v)

  def visitF(f: F)(using ctx: C)(using Σ: Signature)(using TypingContext) =
    combine(
      visitVTerm(f.vTy),
      visitVTerm(f.effects),
      visitVTerm(f.usage),
    )

  def visitReturn(r: Return)(using ctx: C)(using Σ: Signature)(using TypingContext): R =
    combine(
      visitVTerm(r.v),
      visitVTerm(r.usage),
    )

  def visitLet(let: Let)(using ctx: C)(using Σ: Signature)(using TypingContext): R = combine(
    visitCTerm(let.t),
    visitBinding(let.tBinding),
    visitVTerm(let.eff),
    withTelescope(List(let.tBinding)) {
      visitCTerm(let.body)
    },
  )

  def visitRedex(redex: Redex)(using ctx: C)(using Σ: Signature)(using TypingContext): R = combine(
    visitCTerm(redex.t) +: redex.elims.map(visitElim)*,
  )

  def visitElim
    (elim: Elimination[VTerm])
    (using ctx: C)
    (using Σ: Signature)
    (using TypingContext)
    : R = elim match
    case Elimination.EProj(n) => visitName(n)
    case Elimination.ETerm(v) => visitVTerm(v)

  def visitFunctionType
    (functionType: FunctionType)
    (using ctx: C)
    (using Σ: Signature)
    (using TypingContext)
    : R =
    combine(
      visitVTerm(functionType.binding.ty),
      withTelescope(List(functionType.binding)) {
        visitCTerm(functionType.bodyTy)
      },
      visitVTerm(functionType.effects),
    )

  def visitCorecordType
    (corecordType: CorecordType)
    (using ctx: C)
    (using Σ: Signature)
    (using TypingContext)
    : R =
    combine(
      visitQualifiedName(corecordType.qn) +:
        corecordType.args.map(visitVTerm) :+
        visitVTerm(corecordType.effects)*,
    )

  def visitOperationCall
    (operationCall: OperationCall)
    (using ctx: C)
    (using Σ: Signature)
    (using TypingContext)
    : R =
    combine(
      visitVTerm(operationCall.effInstance) +:
        visitName(operationCall.name) +:
        operationCall.args.map(visitVTerm)*,
    )

  def visitContinuation
    (continuation: Continuation)
    (using ctx: C)
    (using Σ: Signature)
    (using TypingContext)
    : R =
    visitCTerm(continuation.continuationTerm)

  def visitHandler(handler: Handler)(using ctx: C)(using Σ: Signature)(using TypingContext): R =
    combine(
      Seq(
        visitEff(handler.eff),
        visitVTerm(handler.parameter),
        visitBinding(handler.parameterBinding),
      ) ++ handler.parameterDisposer.map(t =>
        withTelescope(List(handler.parameterBinding)) {
          visitCTerm(t)
        },
      ) ++ handler.parameterReplicator.map(t =>
        withTelescope(List(handler.parameterBinding)) {
          visitCTerm(t)
        },
      ) ++ Seq(
        withTelescope(List(handler.parameterBinding, handler.inputBinding)) {
          visitCTerm(handler.transform)
        },
      ) ++ handler.handlers.map { (qn, handlerImpl) =>
        visitHandlerImpl(handler.eff, handler.parameterBinding, qn, handlerImpl)
      } ++ Seq(
        visitCTerm(handler.input),
        visitBinding(handler.inputBinding),
      )*,
    )

  def visitHandlerImpl
    (eff: Eff, parameterBinding: Binding[VTerm], qn: QualifiedName, handlerImpl: HandlerImpl)
    (using ctx: C)
    (using Σ: Signature)
    (using TypingContext)
    : R =
    val operation = Σ.getOperation(qn).asRight
    assert(operation.paramTys.size == handlerImpl.boundNames.size)
    val handlerParams = operation.paramTys
      .substLowers(eff._2*)
      .zip(handlerImpl.boundNames)
      .map((binding, name) => binding.copy()(name, binding.isImplicitlyAvailable))
    withTelescope(parameterBinding +: handlerParams) {
      combine(
        (Seq(visitCTerm(handlerImpl.body), visitCTerm(handlerImpl.bodyTy)) ++
          handlerImpl.continuationType.map(visitVTerm).toSeq)*,
      )
    }

  def visitEff
    (eff: (QualifiedName, Arguments))
    (using ctx: C)
    (using Σ: Signature)
    (using TypingContext)
    : R =
    combine(
      visitQualifiedName(eff._1) +:
        eff._2.map(visitVTerm)*,
    )

  def visitBigLevel(layer: Nat)(using ctx: C)(using Σ: Signature)(using TypingContext): R =
    combine()

  def visitQualifiedName
    (qn: QualifiedName)
    (using ctx: C)
    (using Σ: Signature)
    (using TypingContext)
    : R = combine()

  def visitName(name: Name)(using ctx: C)(using Σ: Signature)(using TypingContext): R = combine()

  def visitCTerm(tm: CTerm)(using ctx: C)(using Σ: Signature)(using TypingContext): R = tm match
    case Hole                         => visitHole
    case cct: CapturedContinuationTip => visitCapturedContinuationTip(cct)
    case cType: CType                 => visitCType(cType)
    case cTop: CTop                   => visitCTop(cTop)
    case m: Meta                      => visitMeta(m)
    case d: Def                       => visitDef(d)
    case force: Force                 => visitForce(force)
    case f: F                         => visitF(f)
    case r: Return                    => visitReturn(r)
    case let: Let                     => visitLet(let)
    case redex: Redex                 => visitRedex(redex)
    case functionType: FunctionType   => visitFunctionType(functionType)
    case corecordType: CorecordType   => visitCorecordType(corecordType)
    case operationCall: OperationCall => visitOperationCall(operationCall)
    case continuation: Continuation   => visitContinuation(continuation)
    case handler: Handler             => visitHandler(handler)

trait Visitor[C, R] extends TermVisitor[C, R]:

  override def withTelescope
    (telescope: => Telescope)
    (action: C ?=> R)
    (using ctx: C)
    (using Σ: Signature)
    (using TypingContext)
    : R =
    withBoundNames(telescope.map(_.name))(action)

  def withBoundNames
    (bindingNames: => Seq[Ref[Name]])
    (action: C ?=> R)
    (using ctx: C)
    (using Σ: Signature)
    (using TypingContext)
    : R

  def visitPreTContext
    (tTelescope: List[(Binding[CTerm], Variance)])
    (using ctx: C)
    (using Σ: Signature)
    (using TypingContext)
    : R =
    tTelescope match
      case Nil => combine()
      case (binding, _) :: rest =>
        combine(
          visitPreBinding(binding),
          withBoundNames(Seq(binding.name)) {
            visitPreTContext(rest)
          },
        )

  def visitTContext
    (tTelescope: List[(Binding[VTerm], Variance)])
    (using ctx: C)
    (using Σ: Signature)
    (using TypingContext)
    : R =
    tTelescope match
      case Nil => combine()
      case (binding, _) :: rest =>
        combine(
          visitBinding(binding),
          withBoundNames(Seq(binding.name)) {
            visitTContext(rest)
          },
        )

  def visitPreContext
    (telescope: List[Binding[CTerm]])
    (using ctx: C)
    (using Σ: Signature)
    (using TypingContext)
    : R =
    telescope match
      case Nil => combine()
      case binding :: rest =>
        combine(
          visitPreBinding(binding),
          withBoundNames(Seq(binding.name)) {
            visitPreContext(rest)
          },
        )

  def visitPreBinding
    (binding: Binding[CTerm])
    (using ctx: C)
    (using Σ: Signature)
    (using TypingContext)
    : R =
    combine(visitCTerm(binding.ty), visitCTerm(binding.usage))

  def visitPattern(pattern: Pattern)(using ctx: C)(using Σ: Signature)(using TypingContext): R =
    pattern match
      case pVar: PVar           => visitPVar(pVar)
      case pDataType: PDataType => visitPDataType(pDataType)
      case pForcedDataType: PForcedDataType =>
        visitPForcedDataType(pForcedDataType)
      case pConstructor: PConstructor => visitPConstructor(pConstructor)
      case pForcedConstructor: PForcedConstructor =>
        visitPForcedConstructor(pForcedConstructor)
      case pForced: PForced => visitPForced(pForced)
      case pAbsurd: PAbsurd => visitPAbsurd(pAbsurd)

  def visitPVar(pVar: PVar)(using ctx: C)(using Σ: Signature)(using TypingContext): R = combine()

  def visitPDataType
    (pDataType: PDataType)
    (using ctx: C)
    (using Σ: Signature)
    (using TypingContext)
    : R =
    combine(
      visitQualifiedName(pDataType.qn) +:
        pDataType.args.map(visitPattern)*,
    )

  def visitPForcedDataType
    (pForcedDataType: PForcedDataType)
    (using ctx: C)
    (using Σ: Signature)
    (using TypingContext)
    : R =
    combine(
      visitQualifiedName(pForcedDataType.qn) +:
        pForcedDataType.args.map(visitPattern)*,
    )

  def visitPConstructor
    (pConstructor: PConstructor)
    (using ctx: C)
    (using Σ: Signature)
    (using TypingContext)
    : R =
    combine(
      visitName(pConstructor.name) +:
        pConstructor.args.map(visitPattern)*,
    )

  def visitPForcedConstructor
    (pForcedConstructor: PForcedConstructor)
    (using ctx: C)
    (using Σ: Signature)
    (using TypingContext)
    : R =
    combine(
      visitName(pForcedConstructor.name) +:
        pForcedConstructor.args.map(visitPattern)*,
    )

  def visitPForced(pForced: PForced)(using ctx: C)(using Σ: Signature)(using TypingContext): R =
    visitVTerm(pForced.term)

  def visitPAbsurd(pAbsurd: PAbsurd)(using ctx: C)(using Σ: Signature)(using TypingContext): R =
    combine()

  def visitCoPattern
    (coPattern: CoPattern)
    (using ctx: C)
    (using Σ: Signature)
    (using TypingContext)
    : R = coPattern match
    case p: CPattern    => visitCPattern(p)
    case p: CProjection => visitCProjection(p)

  def visitCPattern(p: CPattern)(using ctx: C)(using Σ: Signature)(using TypingContext): R =
    visitPattern(p.pattern)

  def visitCProjection(p: CProjection)(using ctx: C)(using Σ: Signature)(using TypingContext): R =
    visitName(p.name)

  def visitCaseTree(ct: CaseTree)(using ctx: C)(using Σ: Signature)(using TypingContext): R =
    ct match
      case t: CtTerm      => visitCtTerm(t)
      case l: CtLambda    => visitCtLambda(l)
      case r: CtCorecord  => visitCtCorecord(r)
      case tc: CtTypeCase => visitCtTypeCase(tc)
      case dc: CtDataCase => visitCtDataCase(dc)

  def visitCtTerm(t: CtTerm)(using ctx: C)(using Σ: Signature)(using TypingContext): R = visitCTerm(
    t.term,
  )

  def visitCtLambda(l: CtLambda)(using ctx: C)(using Σ: Signature)(using TypingContext): R =
    withBoundNames(Seq(l.boundName)):
      visitCaseTree(l.body)

  def visitCtCorecord(r: CtCorecord)(using ctx: C)(using Σ: Signature)(using TypingContext): R =
    combine(
      r.cofields.flatMap { (name, body) =>
        Seq(visitName(name), visitCaseTree(body))
      }.toSeq*,
    )

  def visitCtTypeCase(ct: CtTypeCase)(using ctx: C)(using Σ: Signature)(using TypingContext): R =
    combine(
      visitVTerm(ct.operand) +:
        ct.cases.flatMap { (qn, body) =>
          Seq(
            visitQualifiedName(qn),
            withBoundNames(Σ.getData(qn).asRight.context.map(_._1.name).toList) {
              visitCaseTree(body)
            },
          )
        }.toSeq :+ visitCaseTree(ct.default)*,
    )

  def visitCtDataCase(dt: CtDataCase)(using ctx: C)(using Σ: Signature)(using TypingContext): R =
    val constructors = Σ.getConstructors(dt.qn).asRight
    combine(
      visitVTerm(dt.operand) +:
        visitQualifiedName(dt.qn) +: dt.cases.flatMap { (name, body) =>
          val constructor = constructors
            .collectFirst {
              case con if con.name == name => con
            }
            .getOrElse(throw IllegalStateException(s"missing constructor $name for ${dt.qn}"))
          Seq(
            visitName(name),
            withBoundNames(constructor.paramTys.map(_.name)) {
              visitCaseTree(body)
            },
          )
        }.toSeq*,
    )

trait TermTransformer[C]:

  def withTelescope[T]
    (telescope: => Telescope)
    (action: C ?=> T)
    (using ctx: C)
    (using Σ: Signature)
    (using TypingContext)
    : T

  def transformVTerm(tm: VTerm)(using ctx: C)(using Σ: Signature)(using TypingContext): VTerm =
    tm match
      case ty: Type                   => transformType(ty)
      case top: Top                   => transformTop(top)
      case v: Var                     => transformVar(v)
      case collapse: Collapse         => transformCollapse(collapse)
      case u: U                       => transformU(u)
      case thunk: Thunk               => transformThunk(thunk)
      case dataType: DataType         => transformDataType(dataType)
      case con: Con                   => transformCon(con)
      case usageLiteral: UsageLiteral => transformUsageLiteral(usageLiteral)
      case usageProd: UsageProd       => transformUsageProd(usageProd)
      case usageSum: UsageSum         => transformUsageSum(usageSum)
      case usageJoin: UsageJoin       => transformUsageJoin(usageJoin)
      case usageType: UsageType       => transformUsageType(usageType)
      case effectsType: EffectsType   => transformEffectsType(effectsType)
      case effects: Effects           => transformEffects(effects)
      case levelType: LevelType       => transformLevelType(levelType)
      case level: Level               => transformLevel(level)
      case auto: Auto                 => transformAuto(auto)
      case effectInstanceType: VTerm.EffectInstanceType =>
        transformEffectInstanceType(effectInstanceType)
      case effectInstance: VTerm.EffectInstance => transformEffectInstance(effectInstance)

  def transformType(ty: Type)(using ctx: C)(using Σ: Signature)(using TypingContext): VTerm =
    Type(transformVTerm(ty.upperBound))(using ty.sourceInfo)

  def transformTop(top: Top)(using ctx: C)(using Σ: Signature)(using TypingContext): VTerm = Top(
    transformVTerm(top.level),
  )(using top.sourceInfo)

  def transformVar(v: Var)(using ctx: C)(using Σ: Signature)(using TypingContext): VTerm = v

  def transformCollapse
    (collapse: Collapse)
    (using ctx: C)
    (using Σ: Signature)
    (using TypingContext)
    : VTerm = Collapse(
    transformCTerm(collapse.cTm),
  )(using collapse.sourceInfo)

  def transformU(u: U)(using ctx: C)(using Σ: Signature)(using TypingContext): VTerm = U(
    transformCTerm(u.cTy),
  )(using u.sourceInfo)

  def transformThunk(thunk: Thunk)(using ctx: C)(using Σ: Signature)(using TypingContext): VTerm =
    Thunk(transformCTerm(thunk.c))(using thunk.sourceInfo)

  def transformDataType
    (dataType: DataType)
    (using ctx: C)
    (using Σ: Signature)
    (using TypingContext)
    : VTerm =
    DataType(
      transformQualifiedName(dataType.qn),
      dataType.args.map(transformVTerm),
    )(using dataType.sourceInfo)

  def transformCon(con: Con)(using ctx: C)(using Σ: Signature)(using TypingContext): VTerm =
    Con(transformName(con.name), con.args.map(transformVTerm))(using con.sourceInfo)

  def transformUsageType
    (usageType: UsageType)
    (using ctx: C)
    (using Σ: Signature)
    (using TypingContext)
    : VTerm =
    usageType

  def transformUsageLiteral
    (usageLiteral: UsageLiteral)
    (using ctx: C)
    (using Σ: Signature)
    (using TypingContext)
    : VTerm =
    usageLiteral

  def transformUsageProd
    (usageProd: UsageProd)
    (using ctx: C)
    (using Σ: Signature)
    (using TypingContext)
    : VTerm = UsageProd(
    usageProd.operands.map(transformVTerm),
  )

  def transformUsageSum
    (usageSum: UsageSum)
    (using ctx: C)
    (using Σ: Signature)
    (using TypingContext)
    : VTerm = UsageSum(
    usageSum.operands.map(transformVTerm),
  )

  def transformUsageJoin
    (usageJoin: UsageJoin)
    (using ctx: C)
    (using Σ: Signature)
    (using TypingContext)
    : VTerm = UsageJoin(
    usageJoin.operands.map(transformVTerm),
  )

  def transformEffectsType
    (effectsType: EffectsType)
    (using ctx: C)
    (using Σ: Signature)
    (using TypingContext)
    : VTerm =
    effectsType

  def transformEffects
    (effects: Effects)
    (using ctx: C)
    (using Σ: Signature)
    (using TypingContext)
    : VTerm = Effects(
    effects.handlerKeys.map(transformVTerm),
    effects.unionOperands.map((k, v) => (transformVTerm(k), v)),
  )(using effects.sourceInfo)

  def transformLevelType
    (levelType: LevelType)
    (using ctx: C)
    (using Σ: Signature)
    (using TypingContext)
    : VTerm =
    levelType

  def transformLevel(level: Level)(using ctx: C)(using Σ: Signature)(using TypingContext): VTerm =
    Level(
      level.literal,
      level.maxOperands.map((k, v) => (transformVTerm(k), v)),
    )(using level.sourceInfo)

  def transformEffectInstanceType
    (instanceType: EffectInstanceType)
    (using ctx: C)
    (using Σ: Signature)
    (using TypingContext)
    : VTerm =
    EffectInstanceType(
      transformEff(instanceType.eff),
      instanceType.handlerConstraint,
    )

  def transformEffectInstance
    (instance: EffectInstance)
    (using ctx: C)
    (using Σ: Signature)
    (using TypingContext)
    : VTerm =
    EffectInstance(
      transformEff(instance.eff),
      instance.handlerConstraint,
      instance.handlerKey,
    )

  def transformAuto(auto: Auto)(using ctx: C)(using Σ: Signature)(using TypingContext): VTerm = auto

  def transformHole(using ctx: C)(using Σ: Signature)(using TypingContext): CTerm = Hole

  def transformCapturedContinuationTip
    (cct: CapturedContinuationTip)
    (using ctx: C)
    (using Σ: Signature)
    (using TypingContext)
    : CTerm =
    CapturedContinuationTip(transformF(cct.ty))

  def transformCType(cType: CType)(using ctx: C)(using Σ: Signature)(using TypingContext): CTerm =
    CType(transformCTerm(cType.upperBound), transformVTerm(cType.effects))(using cType.sourceInfo)

  def transformCTop(cTop: CTop)(using ctx: C)(using Σ: Signature)(using TypingContext): CTerm =
    CTop(
      transformVTerm(cTop.level),
      transformVTerm(cTop.effects),
    )(using cTop.sourceInfo)

  def transformMeta(m: Meta)(using ctx: C)(using Σ: Signature)(using TypingContext): CTerm =
    Meta(m.index)(using m.sourceInfo)

  def transformDef(d: Def)(using ctx: C)(using Σ: Signature)(using TypingContext): CTerm = Def(
    transformQualifiedName(d.qn),
  )(using d.sourceInfo)

  def transformForce(force: Force)(using ctx: C)(using Σ: Signature)(using TypingContext): CTerm =
    Force(transformVTerm(force.v))(using force.sourceInfo)

  def transformF(f: F)(using ctx: C)(using Σ: Signature)(using TypingContext): F =
    F(
      transformVTerm(f.vTy),
      transformVTerm(f.effects),
      transformVTerm(f.usage),
    )(using f.sourceInfo)

  def transformReturn(r: Return)(using ctx: C)(using Σ: Signature)(using TypingContext): CTerm =
    Return(transformVTerm(r.v), transformVTerm(r.usage))(using r.sourceInfo)

  def transformLet(let: Let)(using ctx: C)(using Σ: Signature)(using TypingContext): CTerm =
    Let(
      transformCTerm(let.t),
      Binding(transformVTerm(let.tBinding.ty), transformVTerm(let.tBinding.usage))(
        let.tBinding.name,
      ),
      transformVTerm(let.eff),
      withTelescope(List(let.tBinding)) {
        transformCTerm(let.body)
      },
    )(using let.sourceInfo)

  def transformRedex(redex: Redex)(using ctx: C)(using Σ: Signature)(using TypingContext): CTerm =
    Redex(
      transformCTerm(redex.t),
      redex.elims.map(transformElim),
    )(using redex.sourceInfo)

  def transformElim
    (elim: Elimination[VTerm])
    (using ctx: C)
    (using Σ: Signature)
    (using TypingContext)
    : Elimination[VTerm] = elim match
    case Elimination.EProj(n) => Elimination.EProj(transformName(n))(using elim.sourceInfo)
    case Elimination.ETerm(v) => Elimination.ETerm(transformVTerm(v))(using elim.sourceInfo)

  def transformFunctionType
    (functionType: FunctionType)
    (using ctx: C)
    (using Σ: Signature)
    (using TypingContext)
    : CTerm =
    FunctionType(
      Binding(
        transformVTerm(functionType.binding.ty),
        transformVTerm(functionType.binding.usage),
      )(functionType.binding.name),
      withTelescope(List(functionType.binding)) {
        transformCTerm(functionType.bodyTy)
      },
      transformVTerm(functionType.effects),
    )(using functionType.sourceInfo)

  def transformCorecordType
    (corecordType: CorecordType)
    (using ctx: C)
    (using Σ: Signature)
    (using TypingContext)
    : CTerm =
    CorecordType(
      transformQualifiedName(corecordType.qn),
      corecordType.args.map(transformVTerm),
      transformVTerm(corecordType.effects),
    )(using corecordType.sourceInfo)

  def transformOperationCall
    (operationCall: OperationCall)
    (using ctx: C)
    (using Σ: Signature)
    (using TypingContext)
    : CTerm =
    OperationCall(
      transformVTerm(operationCall.effInstance),
      transformName(operationCall.name),
      operationCall.args.map(transformVTerm),
    )(using operationCall.sourceInfo)

  def transformContinuation
    (continuation: Continuation)
    (using ctx: C)
    (using Σ: Signature)
    (using TypingContext)
    : CTerm =
    Continuation(transformHandler(continuation.continuationTerm), continuation.continuationUsage)

  def transformHandler
    (handler: Handler)
    (using ctx: C)
    (using Σ: Signature)
    (using TypingContext)
    : Handler =
    Handler(
      transformEff(handler.eff),
      transformVTerm(handler.otherEffects),
      transformVTerm(handler.handlerEffects),
      transformVTerm(handler.outputUsage),
      transformVTerm(handler.outputTy),
      transformVTerm(handler.parameter),
      handler.parameterBinding.map(transformVTerm),
      handler.parameterDisposer.map(t =>
        withTelescope(List(handler.parameterBinding)) {
          transformCTerm(t)
        },
      ),
      handler.parameterReplicator.map(t =>
        withTelescope(List(handler.parameterBinding)) {
          transformCTerm(t)
        },
      ),
      withTelescope(List(handler.parameterBinding, handler.inputBinding)) {
        transformCTerm(handler.transform)
      },
      handler.handlers.map { (qn, handlerImpl) =>
        (
          qn,
          withTelescope(List(handler.parameterBinding)) {
            transformHandlerImpl(handler.eff, qn, handlerImpl)
          },
        )
      },
      transformCTerm(handler.input),
      handler.inputBinding.map(transformVTerm),
    )(using handler.sourceInfo)

  def transformHandlerImpl
    (eff: Eff, qn: QualifiedName, handlerImpl: HandlerImpl)
    (using ctx: C)
    (using Σ: Signature)
    (using TypingContext)
    : HandlerImpl =
    val operation = Σ.getOperation(qn).asRight
    assert(operation.paramTys.size == handlerImpl.boundNames.size)
    val handlerParams = operation.paramTys
      .substLowers(eff._2*)
      .zip(handlerImpl.boundNames)
      .map((binding, name) => binding.copy()(name, binding.isImplicitlyAvailable))
    withTelescope(handlerParams) {
      handlerImpl.copy(body = transformCTerm(handlerImpl.body))(handlerImpl.boundNames)
    }

  def transformEff
    (eff: (QualifiedName, Arguments))
    (using ctx: C)
    (using Σ: Signature)
    (using TypingContext)
    : Eff =
    (transformQualifiedName(eff._1), eff._2.map(transformVTerm))

  def transformQualifiedName
    (qn: QualifiedName)
    (using ctx: C)
    (using Σ: Signature)
    (using TypingContext)
    : QualifiedName =
    qn

  def transformName(name: Name)(using ctx: C)(using Σ: Signature)(using TypingContext): Name = name

  def transformCTerm(tm: CTerm)(using ctx: C)(using Σ: Signature)(using TypingContext): CTerm =
    tm match
      case Hole                         => transformHole
      case cct: CapturedContinuationTip => transformCapturedContinuationTip(cct)
      case cType: CType                 => transformCType(cType)
      case cTop: CTop                   => transformCTop(cTop)
      case m: Meta                      => transformMeta(m)
      case d: Def                       => transformDef(d)
      case force: Force                 => transformForce(force)
      case f: F                         => transformF(f)
      case r: Return                    => transformReturn(r)
      case let: Let                     => transformLet(let)
      case redex: Redex                 => transformRedex(redex)
      case functionType: FunctionType   => transformFunctionType(functionType)
      case corecordType: CorecordType   => transformCorecordType(corecordType)
      case operationCall: OperationCall => transformOperationCall(operationCall)
      case continuation: Continuation   => transformContinuation(continuation)
      case handler: Handler             => transformHandler(handler)

trait Transformer[C] extends TermTransformer[C]:

  override def withTelescope[T]
    (telescope: => Telescope)
    (action: C ?=> T)
    (using ctx: C)
    (using Σ: Signature)
    (using TypingContext)
    : T = withBoundNames(telescope.map(_.name))(action)

  def withBoundNames[T]
    (bindingNames: => Seq[Ref[Name]])
    (action: C ?=> T)
    (using ctx: C)
    (using Σ: Signature)
    (using TypingContext)
    : T

  def transformCaseTree
    (ct: CaseTree)
    (using ctx: C)
    (using Σ: Signature)
    (using TypingContext)
    : CaseTree =
    ct match
      case t: CtTerm      => transformCtTerm(t)
      case l: CtLambda    => transformCtLambda(l)
      case r: CtCorecord  => transformCtCorecord(r)
      case tc: CtTypeCase => transformCtTypeCase(tc)
      case dc: CtDataCase => transformCtDataCase(dc)

  def transformCtTerm(ct: CtTerm)(using ctx: C)(using Σ: Signature)(using TypingContext): CaseTree =
    CtTerm(transformCTerm(ct.term))

  def transformCtLambda
    (l: CtLambda)
    (using ctx: C)
    (using Σ: Signature)
    (using TypingContext)
    : CaseTree =
    CtLambda(
      withBoundNames(Seq(l.boundName)) {
        transformCaseTree(l.body)
      },
    )(l.boundName)

  def transformCtCorecord
    (r: CtCorecord)
    (using ctx: C)
    (using Σ: Signature)
    (using TypingContext)
    : CaseTree =
    CtCorecord(
      r.cofields.map { (name, cofield) =>
        (name, transformCaseTree(cofield))
      },
    )

  def transformCtTypeCase
    (tc: CtTypeCase)
    (using ctx: C)
    (using Σ: Signature)
    (using TypingContext)
    : CaseTree =
    CtTypeCase(
      transformVTerm(tc.operand),
      tc.cases.map { (qn, body) =>
        val data = Σ.getData(qn).asRight
        (
          qn,
          withBoundNames((data.context.map(_._1.name) ++ data.tIndexTys.map(_.name)).toList) {
            body
          },
        )
      },
      transformCaseTree(tc.default),
    )

  def transformCtDataCase
    (dc: CtDataCase)
    (using ctx: C)
    (using Σ: Signature)
    (using TypingContext)
    : CaseTree =
    val constructors = Σ.getConstructors(dc.qn).asRight
    CtDataCase(
      transformVTerm(dc.operand),
      dc.qn,
      dc.cases.map { (name, body) =>
        val constructor = constructors
          .collectFirst { case con if con.name == name => con }
          .getOrElse(throw IllegalStateException(s"missing constructor $name for ${dc.qn}"))
        (name, withBoundNames(constructor.paramTys.map(_.name)) { body })
      },
    )

  def transformCoPattern
    (q: CoPattern)
    (using ctx: C)
    (using Σ: Signature)
    (using TypingContext)
    : CoPattern =
    q match
      case p: CPattern    => transformCPattern(p)
      case p: CProjection => transformCProjection(p)

  def transformCPattern
    (p: CPattern)
    (using ctx: C)
    (using Σ: Signature)
    (using TypingContext)
    : CoPattern =
    CPattern(transformPattern(p.pattern))

  def transformCProjection
    (p: CProjection)
    (using ctx: C)
    (using Σ: Signature)
    (using TypingContext)
    : CoPattern =
    CProjection(transformName(p.name))(using p.sourceInfo)

  def transformPattern(p: Pattern)(using ctx: C)(using Σ: Signature)(using TypingContext): Pattern =
    p match
      case v: PVar               => transformPVar(v)
      case d: PDataType          => transformPDataType(d)
      case d: PForcedDataType    => transformPForcedDataType(d)
      case c: PConstructor       => transformPConstructor(c)
      case c: PForcedConstructor => transformPForcedConstructor(c)
      case f: PForced            => transformPForced(f)
      case a: PAbsurd            => transformPAbsurd(a)

  def transformPVar(v: PVar)(using ctx: C)(using Σ: Signature)(using TypingContext): Pattern = v

  def transformPDataType
    (d: PDataType)
    (using ctx: C)
    (using Σ: Signature)
    (using TypingContext)
    : Pattern =
    PDataType(transformQualifiedName(d.qn), d.args.map(transformPattern))(using d.sourceInfo)

  def transformPForcedDataType
    (d: PForcedDataType)
    (using ctx: C)
    (using Σ: Signature)
    (using TypingContext)
    : Pattern =
    PForcedDataType(transformQualifiedName(d.qn), d.args.map(transformPattern))(using d.sourceInfo)

  def transformPConstructor
    (d: PConstructor)
    (using ctx: C)
    (using Σ: Signature)
    (using TypingContext)
    : Pattern =
    PConstructor(transformName(d.name), d.args.map(transformPattern))(using d.sourceInfo)

  def transformPForcedConstructor
    (d: PForcedConstructor)
    (using ctx: C)
    (using Σ: Signature)
    (using TypingContext)
    : Pattern =
    PForcedConstructor(transformName(d.name), d.args.map(transformPattern))(using d.sourceInfo)

  def transformPForced(f: PForced)(using ctx: C)(using Σ: Signature)(using TypingContext): Pattern =
    PForced(transformVTerm(f.term))(using f.sourceInfo)

  def transformPAbsurd(a: PAbsurd)(using ctx: C)(using Σ: Signature)(using TypingContext): Pattern =
    a
