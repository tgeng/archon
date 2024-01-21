package com.github.tgeng.archon.core.ir

import com.github.tgeng.archon.common.*
import com.github.tgeng.archon.core.common.*
import com.github.tgeng.archon.core.ir.CTerm.*
import com.github.tgeng.archon.core.ir.CaseTree.*
import com.github.tgeng.archon.core.ir.CoPattern.*
import com.github.tgeng.archon.core.ir.Pattern.*
import com.github.tgeng.archon.core.ir.VTerm.*

trait Visitor[C, R]:

  def combine(rs: R*)(using ctx: C)(using Σ: Signature): R

  def withBindings
    (bindingNames: => Seq[Ref[Name]])
    (action: C ?=> R)
    (using ctx: C)
    (using Σ: Signature)
    : R =
    action(using ctx)

  def visitPreTContext
    (tTelescope: List[(Binding[CTerm], Variance)])
    (using ctx: C)
    (using Σ: Signature)
    : R =
    tTelescope match
      case Nil => combine()
      case (binding, _) :: rest =>
        combine(
          visitPreBinding(binding),
          withBindings(Seq(binding.name)) {
            visitPreTContext(rest)
          },
        )

  def visitTContext
    (tTelescope: List[(Binding[VTerm], Variance)])
    (using ctx: C)
    (using Σ: Signature)
    : R =
    tTelescope match
      case Nil => combine()
      case (binding, _) :: rest =>
        combine(
          visitBinding(binding),
          withBindings(Seq(binding.name)) {
            visitTContext(rest)
          },
        )

  def visitPreContext(telescope: List[Binding[CTerm]])(using ctx: C)(using Σ: Signature): R =
    telescope match
      case Nil => combine()
      case binding :: rest =>
        combine(
          visitPreBinding(binding),
          withBindings(Seq(binding.name)) {
            visitPreContext(rest)
          },
        )

  def visitTelescope(telescope: List[Binding[VTerm]])(using ctx: C)(using Σ: Signature): R =
    telescope match
      case Nil => combine()
      case binding :: rest =>
        combine(
          visitBinding(binding),
          withBindings(Seq(binding.name)) {
            visitTelescope(rest)
          },
        )

  def visitPreBinding(binding: Binding[CTerm])(using ctx: C)(using Σ: Signature): R =
    combine(visitCTerm(binding.ty), visitCTerm(binding.usage))

  def visitBinding(binding: Binding[VTerm])(using ctx: C)(using Σ: Signature): R =
    combine(visitVTerm(binding.ty), visitVTerm(binding.usage))

  def visitPattern(pattern: Pattern)(using ctx: C)(using Σ: Signature): R =
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

  def visitPVar(pVar: PVar)(using ctx: C)(using Σ: Signature): R = combine()

  def visitPDataType(pDataType: PDataType)(using ctx: C)(using Σ: Signature): R =
    combine(
      visitQualifiedName(pDataType.qn) +:
        pDataType.args.map(visitPattern): _*,
    )

  def visitPForcedDataType(pForcedDataType: PForcedDataType)(using ctx: C)(using Σ: Signature): R =
    combine(
      visitQualifiedName(pForcedDataType.qn) +:
        pForcedDataType.args.map(visitPattern): _*,
    )

  def visitPConstructor(pConstructor: PConstructor)(using ctx: C)(using Σ: Signature): R =
    combine(
      visitName(pConstructor.name) +:
        pConstructor.args.map(visitPattern): _*,
    )

  def visitPForcedConstructor
    (pForcedConstructor: PForcedConstructor)
    (using ctx: C)
    (using Σ: Signature)
    : R =
    combine(
      visitName(pForcedConstructor.name) +:
        pForcedConstructor.args.map(visitPattern): _*,
    )

  def visitPForced(pForced: PForced)(using ctx: C)(using Σ: Signature): R =
    visitVTerm(pForced.term)

  def visitPAbsurd(pAbsurd: PAbsurd)(using ctx: C)(using Σ: Signature): R =
    combine()

  def visitCoPattern(coPattern: CoPattern)(using ctx: C)(using Σ: Signature): R = coPattern match
    case p: CPattern    => visitCPattern(p)
    case p: CProjection => visitCProjection(p)

  def visitCPattern(p: CPattern)(using ctx: C)(using Σ: Signature): R =
    visitPattern(p.pattern)

  def visitCProjection(p: CProjection)(using ctx: C)(using Σ: Signature): R =
    visitName(p.name)

  def visitCaseTree(ct: CaseTree)(using ctx: C)(using Σ: Signature): R = ct match
    case t: CtTerm      => visitCtTerm(t)
    case l: CtLambda    => visitCtLambda(l)
    case r: CtRecord    => visitCtRecord(r)
    case tc: CtTypeCase => visitCtTypeCase(tc)
    case dc: CtDataCase => visitCtDataCase(dc)

  def visitCtTerm(t: CtTerm)(using ctx: C)(using Σ: Signature): R = visitCTerm(t.term)

  def visitCtLambda(l: CtLambda)(using ctx: C)(using Σ: Signature): R =
    withBindings(Seq(l.boundName)) {
      visitCaseTree(l.body)
    }

  def visitCtRecord(r: CtRecord)(using ctx: C)(using Σ: Signature): R =
    combine(
      r.fields.flatMap { (name, body) =>
        Seq(visitName(name), visitCaseTree(body))
      }.toSeq: _*,
    )

  def visitCtTypeCase(ct: CtTypeCase)(using ctx: C)(using Σ: Signature): R =
    combine(
      visitVTerm(ct.operand) +:
        ct.cases.flatMap { (qn, body) =>
          Seq(
            visitQualifiedName(qn),
            withBindings(Σ.getData(qn).tParamTys.map(_._1.name).toList) {
              visitCaseTree(body)
            },
          )
        }.toSeq :+ visitCaseTree(ct.default): _*,
    )

  def visitCtDataCase(dt: CtDataCase)(using ctx: C)(using Σ: Signature): R =
    val constructors = Σ.getConstructors(dt.qn)
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
            withBindings(constructor.paramTys.map(_.name)) {
              visitCaseTree(body)
            },
          )
        }.toSeq: _*,
    )

  def visitVTerm(tm: VTerm)(using ctx: C)(using Σ: Signature): R = tm match
    case ty: Type                   => visitType(ty)
    case top: Top                   => visitTop(top)
    case v: Var                     => visitVar(v)
    case collapse: Collapse         => visitCollapse(collapse)
    case u: U                       => visitU(u)
    case thunk: Thunk               => visitThunk(thunk)
    case dataType: DataType         => visitDataType(dataType)
    case con: Con                   => visitCon(con)
    case usageType: UsageType       => visitUsageType(usageType)
    case usageLiteral: UsageLiteral => visitUsageLiteral(usageLiteral)
    case usageProd: UsageProd       => visitUsageProd(usageProd)
    case usageSum: UsageSum         => visitUsageSum(usageSum)
    case usageJoin: UsageJoin       => visitUsageJoin(usageJoin)
    case eqDecidabilityType: EqDecidabilityType =>
      visitEqDecidabilityType(eqDecidabilityType)
    case eqDecidabilityLiteral: EqDecidabilityLiteral =>
      visitEqDecidabilityLiteral(
        eqDecidabilityLiteral,
      )
    case effectsType: EffectsType => visitEffectsType(effectsType)
    case effects: Effects         => visitEffects(effects)
    case levelType: LevelType     => visitLevelType(levelType)
    case level: Level             => visitLevel(level)
    case auto: Auto               => visitAuto(auto)

  def visitType(ty: Type)(using ctx: C)(using Σ: Signature): R =
    visitVTerm(ty.upperBound)

  def visitTop(top: Top)(using ctx: C)(using Σ: Signature): R = combine(
    visitVTerm(top.level),
    visitVTerm(top.eqDecidability),
  )

  def visitVar(v: Var)(using ctx: C)(using Σ: Signature): R = combine()

  def visitCollapse(collapse: Collapse)(using ctx: C)(using Σ: Signature): R =
    visitCTerm(collapse.cTm)

  def visitU(u: U)(using ctx: C)(using Σ: Signature): R = visitCTerm(u.cTy)

  def visitThunk(thunk: Thunk)(using ctx: C)(using Σ: Signature): R =
    visitCTerm(thunk.c)

  def visitDataType(dataType: DataType)(using ctx: C)(using Σ: Signature): R =
    combine(
      visitQualifiedName(dataType.qn) +:
        dataType.args.map(visitVTerm): _*,
    )

  def visitCon(con: Con)(using ctx: C)(using Σ: Signature): R =
    combine(
      visitName(con.name) +:
        con.args.map(visitVTerm): _*,
    )

  def visitUsageType(usageType: UsageType)(using ctx: C)(using Σ: Signature): R =
    visitQualifiedName(Builtins.UsageQn)

  def visitUsageLiteral(usageLiteral: UsageLiteral)(using ctx: C)(using Σ: Signature): R =
    combine()

  def visitUsageProd(usageProd: UsageProd)(using ctx: C)(using Σ: Signature): R =
    combine(usageProd.operands.toSeq.map(visitVTerm): _*)

  def visitUsageSum(usageSum: UsageSum)(using ctx: C)(using Σ: Signature): R =
    combine(usageSum.operands.multiMap(visitVTerm).multiToSeq: _*)

  def visitUsageJoin(usageJoin: UsageJoin)(using ctx: C)(using Σ: Signature): R =
    combine(usageJoin.operands.toSeq.map(visitVTerm): _*)

  def visitEqDecidabilityType
    (eqDecidabilityType: EqDecidabilityType)
    (using ctx: C)
    (using Σ: Signature)
    : R =
    visitQualifiedName(Builtins.EqDecidabilityQn)

  def visitEqDecidabilityLiteral
    (eqDecidabilityLiteral: EqDecidabilityLiteral)
    (using ctx: C)
    (using Σ: Signature)
    : R =
    eqDecidabilityLiteral.eqDecidability match
      case EqDecidability.EqDecidable => visitQualifiedName(Builtins.EqDecidableQn)
      case EqDecidability.EqUnknown   => visitQualifiedName(Builtins.EqUnknownQn)

  def visitEffectsType(effectsType: EffectsType)(using ctx: C)(using Σ: Signature): R =
    visitQualifiedName(Builtins.EffectsQn)

  def visitEffects(effects: Effects)(using ctx: C)(using Σ: Signature): R =
    combine(
      (effects.literal.map(visitEff) ++ effects.unionOperands.keys.map(
        visitVTerm,
      )).toSeq: _*,
    )

  def visitLevelType(levelType: LevelType)(using ctx: C)(using Σ: Signature): R =
    visitQualifiedName(Builtins.LevelQn)

  def visitLevel(level: Level)(using ctx: C)(using Σ: Signature): R =
    combine(
      level.maxOperands.map { case (v, _) =>
        visitVTerm(v)
      }.toSeq: _*,
    )

  def visitAuto(auto: Auto)(using ctx: C)(using Σ: Signature): R = combine()

  def visitHole(using ctx: C)(using Σ: Signature): R = combine()

  def visitCapturedContinuationTip
    (cct: CapturedContinuationTip)
    (using ctx: C)
    (using Σ: Signature)
    : R =
    visitF(cct.ty)

  def visitCType(cType: CType)(using ctx: C)(using Σ: Signature): R =
    combine(
      visitCTerm(cType.upperBound),
      visitVTerm(cType.effects),
    )

  def visitCTop(cTop: CTop)(using ctx: C)(using Σ: Signature): R =
    combine(
      visitVTerm(cTop.level),
      visitVTerm(cTop.effects),
    )

  def visitMeta(m: Meta)(using ctx: C)(using Σ: Signature): R = combine()

  def visitDef(d: Def)(using ctx: C)(using Σ: Signature): R =
    visitQualifiedName(d.qn)

  def visitForce(force: Force)(using ctx: C)(using Σ: Signature): R =
    visitVTerm(force.v)

  def visitF(f: F)(using ctx: C)(using Σ: Signature) =
    combine(
      visitVTerm(f.vTy),
      visitVTerm(f.effects),
      visitVTerm(f.usage),
    )

  def visitReturn(r: Return)(using ctx: C)(using Σ: Signature): R =
    combine(visitVTerm(r.v))

  def visitLet(let: Let)(using ctx: C)(using Σ: Signature): R = combine(
    visitCTerm(let.t),
    visitVTerm(let.ty),
    visitVTerm(let.eff),
    visitVTerm(let.usage),
    withBindings(Seq(let.boundName)) {
      visitCTerm(let.ctx)
    },
  )

  def visitRedex(redex: Redex)(using ctx: C)(using Σ: Signature): R = combine(
    visitCTerm(redex.t) +: redex.elims.map(visitElim): _*,
  )

  def visitElim(elim: Elimination[VTerm])(using ctx: C)(using Σ: Signature): R = elim match
    case Elimination.EProj(n) => visitName(n)
    case Elimination.ETerm(v) => visitVTerm(v)

  def visitFunctionType(functionType: FunctionType)(using ctx: C)(using Σ: Signature): R =
    combine(
      visitVTerm(functionType.binding.ty),
      withBindings(Seq(functionType.binding.name)) {
        visitCTerm(functionType.bodyTy)
      },
      visitVTerm(functionType.effects),
    )

  def visitRecordType(recordType: RecordType)(using ctx: C)(using Σ: Signature): R =
    combine(
      visitQualifiedName(recordType.qn) +:
        recordType.args.map(visitVTerm) :+
        visitVTerm(recordType.effects): _*,
    )

  def visitOperationCall(operationCall: OperationCall)(using ctx: C)(using Σ: Signature): R =
    combine(
      visitEff(operationCall.eff) +:
        visitName(operationCall.name) +:
        operationCall.args.map(visitVTerm): _*,
    )

  def visitContinuation(continuation: Continuation)(using ctx: C)(using Σ: Signature): R =
    visitCTerm(continuation.continuationTerm)

  def visitHandler(handler: Handler)(using ctx: C)(using Σ: Signature): R =
    combine(
      Seq(
        visitVTerm(handler.eff),
        visitVTerm(handler.parameter),
        visitBinding(handler.parameterBinding),
      ) ++ handler.parameterDisposer.map(t =>
        withBindings(Seq(handler.parameterBinding.name)) {
          visitCTerm(t)
        },
      ) ++ handler.parameterReplicator.map(t =>
        withBindings(Seq(handler.parameterBinding.name)) {
          visitCTerm(t)
        },
      ) ++ Seq(
        withBindings(Seq(handler.parameterBinding.name, handler.inputBinding.name)) {
          visitCTerm(handler.transform)
        },
      ) ++ handler.handlers.map { (name, handlerImpl) =>
        val (argNames, resumeName) = handler.handlersBoundNames(name)
        withBindings((handler.parameterBinding.name +: argNames) ++ resumeName) {
          visitHandlerImpl(handlerImpl)
        }
      } ++ Seq(
        visitCTerm(handler.input),
        visitBinding(handler.inputBinding),
      ): _*,
    )

  def visitHandlerImpl(handlerImpl: HandlerImpl)(using ctx: C)(using Σ: Signature): R =
    visitCTerm(handlerImpl.body)

  def visitEff(eff: (QualifiedName, Arguments))(using ctx: C)(using Σ: Signature): R =
    combine(
      visitQualifiedName(eff._1) +:
        eff._2.map(visitVTerm): _*,
    )

  def visitBigLevel(layer: Nat)(using ctx: C)(using Σ: Signature): R = combine()

  def visitQualifiedName(qn: QualifiedName)(using ctx: C)(using Σ: Signature): R = combine()

  def visitName(name: Name)(using ctx: C)(using Σ: Signature): R = combine()

  def visitCTerm(tm: CTerm)(using ctx: C)(using Σ: Signature): R = tm match
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
    case recordType: RecordType       => visitRecordType(recordType)
    case operationCall: OperationCall => visitOperationCall(operationCall)
    case continuation: Continuation   => visitContinuation(continuation)
    case handler: Handler             => visitHandler(handler)

trait Transformer[C]:

  def withBindings[T]
    (bindingNames: => Seq[Ref[Name]])
    (action: C ?=> T)
    (using ctx: C)
    (using Σ: Signature)
    : T =
    action(using ctx)

  def transformCaseTree(ct: CaseTree)(using ctx: C)(using Σ: Signature): CaseTree =
    ct match
      case t: CtTerm      => transformCtTerm(t)
      case l: CtLambda    => transformCtLambda(l)
      case r: CtRecord    => transformCtRecord(r)
      case tc: CtTypeCase => transformCtTypeCase(tc)
      case dc: CtDataCase => transformCtDataCase(dc)

  def transformCtTerm(ct: CtTerm)(using ctx: C)(using Σ: Signature): CaseTree =
    CtTerm(transformCTerm(ct.term))

  def transformCtLambda(l: CtLambda)(using ctx: C)(using Σ: Signature): CaseTree =
    CtLambda(
      withBindings(Seq(l.boundName)) {
        transformCaseTree(l.body)
      },
    )(l.boundName)

  def transformCtRecord(r: CtRecord)(using ctx: C)(using Σ: Signature): CaseTree =
    CtRecord(
      r.fields.map { (name, field) =>
        (name, transformCaseTree(field))
      },
    )

  def transformCtTypeCase(tc: CtTypeCase)(using ctx: C)(using Σ: Signature): CaseTree =
    CtTypeCase(
      transformVTerm(tc.operand),
      tc.cases.map { (qn, body) =>
        val data = Σ.getData(qn)
        (
          qn,
          withBindings((data.tParamTys.map(_._1.name) ++ data.tIndexTys.map(_.name)).toList) {
            body
          },
        )
      },
      transformCaseTree(tc.default),
    )

  def transformCtDataCase(dc: CtDataCase)(using ctx: C)(using Σ: Signature): CaseTree =
    val constructors = Σ.getConstructors(dc.qn)
    CtDataCase(
      transformVTerm(dc.operand),
      dc.qn,
      dc.cases.map { (name, body) =>
        val constructor = constructors
          .collectFirst { case con if con.name == name => con }
          .getOrElse(throw IllegalStateException(s"missing constructor $name for ${dc.qn}"))
        (name, withBindings(constructor.paramTys.map(_.name)) { body })
      },
    )

  def transformCoPattern(q: CoPattern)(using ctx: C)(using Σ: Signature): CoPattern =
    q match
      case p: CPattern    => transformCPattern(p)
      case p: CProjection => transformCProjection(p)

  def transformCPattern(p: CPattern)(using ctx: C)(using Σ: Signature): CoPattern =
    CPattern(transformPattern(p.pattern))

  def transformCProjection(p: CProjection)(using ctx: C)(using Σ: Signature): CoPattern =
    CProjection(transformName(p.name))(using p.sourceInfo)

  def transformPattern(p: Pattern)(using ctx: C)(using Σ: Signature): Pattern =
    p match
      case v: PVar               => transformPVar(v)
      case d: PDataType          => transformPDataType(d)
      case d: PForcedDataType    => transformPForcedDataType(d)
      case c: PConstructor       => transformPConstructor(c)
      case c: PForcedConstructor => transformPForcedConstructor(c)
      case f: PForced            => transformPForced(f)
      case a: PAbsurd            => transformPAbsurd(a)

  def transformPVar(v: PVar)(using ctx: C)(using Σ: Signature): Pattern = v

  def transformPDataType(d: PDataType)(using ctx: C)(using Σ: Signature): Pattern =
    PDataType(transformQualifiedName(d.qn), d.args.map(transformPattern))(using d.sourceInfo)

  def transformPForcedDataType(d: PForcedDataType)(using ctx: C)(using Σ: Signature): Pattern =
    PForcedDataType(transformQualifiedName(d.qn), d.args.map(transformPattern))(using d.sourceInfo)

  def transformPConstructor(d: PConstructor)(using ctx: C)(using Σ: Signature): Pattern =
    PConstructor(transformName(d.name), d.args.map(transformPattern))(using d.sourceInfo)

  def transformPForcedConstructor
    (d: PForcedConstructor)
    (using ctx: C)
    (using Σ: Signature)
    : Pattern =
    PForcedConstructor(transformName(d.name), d.args.map(transformPattern))(using d.sourceInfo)

  def transformPForced(f: PForced)(using ctx: C)(using Σ: Signature): Pattern =
    PForced(transformVTerm(f.term))(using f.sourceInfo)

  def transformPAbsurd(a: PAbsurd)(using ctx: C)(using Σ: Signature): Pattern = a

  def transformVTerm(tm: VTerm)(using ctx: C)(using Σ: Signature): VTerm =
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
      case eqDecidabilityType: EqDecidabilityType =>
        transformEqDecidabilityType(eqDecidabilityType)
      case eqDecidabilityLiteral: EqDecidabilityLiteral =>
        transformEqDecidabilityLiteral(
          eqDecidabilityLiteral,
        )
      case effectsType: EffectsType => transformEffectsType(effectsType)
      case effects: Effects         => transformEffects(effects)
      case levelType: LevelType     => transformLevelType(levelType)
      case level: Level             => transformLevel(level)
      case auto: Auto               => transformAuto(auto)

  def transformType(ty: Type)(using ctx: C)(using Σ: Signature): VTerm =
    Type(transformVTerm(ty.upperBound))(using ty.sourceInfo)

  def transformTop(top: Top)(using ctx: C)(using Σ: Signature): VTerm = Top(
    transformVTerm(top.level),
    transformVTerm(top.eqDecidability),
  )(using top.sourceInfo)

  def transformVar(v: Var)(using ctx: C)(using Σ: Signature): VTerm = v

  def transformCollapse(collapse: Collapse)(using ctx: C)(using Σ: Signature): VTerm = Collapse(
    transformCTerm(collapse.cTm),
  )(using collapse.sourceInfo)

  def transformU(u: U)(using ctx: C)(using Σ: Signature): VTerm = U(
    transformCTerm(u.cTy),
  )(using u.sourceInfo)

  def transformThunk(thunk: Thunk)(using ctx: C)(using Σ: Signature): VTerm =
    Thunk(transformCTerm(thunk.c))(using thunk.sourceInfo)

  def transformDataType(dataType: DataType)(using ctx: C)(using Σ: Signature): VTerm =
    DataType(
      transformQualifiedName(dataType.qn),
      dataType.args.map(transformVTerm),
    )(using dataType.sourceInfo)

  def transformCon(con: Con)(using ctx: C)(using Σ: Signature): VTerm =
    Con(transformName(con.name), con.args.map(transformVTerm))(using con.sourceInfo)

  def transformUsageType(usageType: UsageType)(using ctx: C)(using Σ: Signature): VTerm =
    usageType

  def transformUsageLiteral(usageLiteral: UsageLiteral)(using ctx: C)(using Σ: Signature): VTerm =
    usageLiteral

  def transformUsageProd(usageProd: UsageProd)(using ctx: C)(using Σ: Signature): VTerm = UsageProd(
    usageProd.operands.map(transformVTerm),
  )

  def transformUsageSum(usageSum: UsageSum)(using ctx: C)(using Σ: Signature): VTerm = UsageSum(
    usageSum.operands.multiMap(transformVTerm),
  )

  def transformUsageJoin(usageJoin: UsageJoin)(using ctx: C)(using Σ: Signature): VTerm = UsageJoin(
    usageJoin.operands.map(transformVTerm),
  )

  def transformEqDecidabilityType
    (eqDecidabilityType: EqDecidabilityType)
    (using ctx: C)
    (using Σ: Signature)
    : VTerm =
    eqDecidabilityType

  def transformEqDecidabilityLiteral
    (eqDecidabilityLiteral: EqDecidabilityLiteral)
    (using ctx: C)
    (using Σ: Signature)
    : VTerm = eqDecidabilityLiteral

  def transformEffectsType(effectsType: EffectsType)(using ctx: C)(using Σ: Signature): VTerm =
    effectsType

  def transformEffects(effects: Effects)(using ctx: C)(using Σ: Signature): VTerm = Effects(
    effects.literal.map { (qn, args) => (qn, args.map(transformVTerm)) },
    effects.unionOperands.map((k, v) => (transformVTerm(k), v)),
  )(using effects.sourceInfo)

  def transformLevelType(levelType: LevelType)(using ctx: C)(using Σ: Signature): VTerm =
    levelType

  def transformLevel(level: Level)(using ctx: C)(using Σ: Signature): VTerm =
    Level(
      level.literal,
      level.maxOperands.map((k, v) => (transformVTerm(k), v)),
    )(using level.sourceInfo)

  def transformAuto(auto: Auto)(using ctx: C)(using Σ: Signature): VTerm = auto

  def transformHole(using ctx: C)(using Σ: Signature): CTerm = Hole

  def transformCapturedContinuationTip
    (cct: CapturedContinuationTip)
    (using ctx: C)
    (using Σ: Signature)
    : CTerm =
    CapturedContinuationTip(transformF(cct.ty))

  def transformCType(cType: CType)(using ctx: C)(using Σ: Signature): CTerm =
    CType(transformCTerm(cType.upperBound), transformVTerm(cType.effects))(using cType.sourceInfo)

  def transformCTop(cTop: CTop)(using ctx: C)(using Σ: Signature): CTerm =
    CTop(
      transformVTerm(cTop.level),
      transformVTerm(cTop.effects),
    )(using cTop.sourceInfo)

  def transformMeta(m: Meta)(using ctx: C)(using Σ: Signature): CTerm =
    Meta(m.index)(using m.sourceInfo)

  def transformDef(d: Def)(using ctx: C)(using Σ: Signature): CTerm = Def(
    transformQualifiedName(d.qn),
  )(using d.sourceInfo)

  def transformForce(force: Force)(using ctx: C)(using Σ: Signature): CTerm =
    Force(transformVTerm(force.v))(using force.sourceInfo)

  def transformF(f: F)(using ctx: C)(using Σ: Signature): F =
    F(
      transformVTerm(f.vTy),
      transformVTerm(f.effects),
      transformVTerm(f.usage),
    )(using f.sourceInfo)

  def transformReturn(r: Return)(using ctx: C)(using Σ: Signature): CTerm =
    Return(transformVTerm(r.v), transformVTerm(r.usage))(using r.sourceInfo)

  def transformLet(let: Let)(using ctx: C)(using Σ: Signature): CTerm =
    Let(
      transformCTerm(let.t),
      transformVTerm(let.ty),
      transformVTerm(let.eff),
      transformVTerm(let.usage),
      withBindings(Seq(let.boundName)) {
        transformCTerm(let.ctx)
      },
    )(let.boundName)(using let.sourceInfo)

  def transformRedex(redex: Redex)(using ctx: C)(using Σ: Signature): CTerm =
    Redex(
      transformCTerm(redex.t),
      redex.elims.map(transformElim),
    )(using redex.sourceInfo)

  def transformElim
    (elim: Elimination[VTerm])
    (using ctx: C)
    (using Σ: Signature)
    : Elimination[VTerm] = elim match
    case Elimination.EProj(n) => Elimination.EProj(transformName(n))(using elim.sourceInfo)
    case Elimination.ETerm(v) => Elimination.ETerm(transformVTerm(v))(using elim.sourceInfo)

  def transformFunctionType(functionType: FunctionType)(using ctx: C)(using Σ: Signature): CTerm =
    FunctionType(
      Binding(
        transformVTerm(functionType.binding.ty),
        transformVTerm(functionType.binding.usage),
      )(functionType.binding.name),
      withBindings(List(functionType.binding.name)) {
        transformCTerm(functionType.bodyTy)
      },
      transformVTerm(functionType.effects),
    )(using functionType.sourceInfo)

  def transformRecordType(recordType: RecordType)(using ctx: C)(using Σ: Signature): CTerm =
    RecordType(
      transformQualifiedName(recordType.qn),
      recordType.args.map(transformVTerm),
      transformVTerm(recordType.effects),
    )(using recordType.sourceInfo)

  def transformOperationCall
    (operationCall: OperationCall)
    (using ctx: C)
    (using Σ: Signature)
    : CTerm =
    OperationCall(
      transformEff(operationCall.eff),
      transformName(operationCall.name),
      operationCall.args.map(transformVTerm),
    )(using operationCall.sourceInfo)

  def transformContinuation(continuation: Continuation)(using ctx: C)(using Σ: Signature): CTerm =
    Continuation(transformHandler(continuation.continuationTerm), continuation.continuationUsage)

  def transformHandler(handler: Handler)(using ctx: C)(using Σ: Signature): Handler =
    Handler(
      transformVTerm(handler.eff),
      transformVTerm(handler.otherEffects),
      transformVTerm(handler.outputEffects),
      transformVTerm(handler.outputUsage),
      transformVTerm(handler.outputTy),
      transformVTerm(handler.parameter),
      handler.parameterBinding.map(transformVTerm),
      handler.parameterDisposer.map(t =>
        withBindings(Seq(handler.parameterBinding.name)) {
          transformCTerm(t)
        },
      ),
      handler.parameterReplicator.map(t =>
        withBindings(Seq(handler.parameterBinding.name)) {
          transformCTerm(t)
        },
      ),
      withBindings(Seq(handler.parameterBinding.name, handler.inputBinding.name)) {
        transformCTerm(handler.transform)
      },
      handler.handlers.map { (name, handlerImpl) =>
        val (argNames, resumeName) = handler.handlersBoundNames(name)
        (
          name,
          withBindings((handler.parameterBinding.name +: argNames) ++ resumeName) {
            transformHandlerImpl(handlerImpl)
          },
        )
      },
      transformCTerm(handler.input),
      handler.inputBinding.map(transformVTerm),
    )(
      handler.handlersBoundNames,
    )(using handler.sourceInfo)

  def transformHandlerImpl
    (handlerImpl: HandlerImpl)
    (using ctx: C)
    (using Σ: Signature)
    : HandlerImpl =
    handlerImpl.copy(body = transformCTerm(handlerImpl.body))

  def transformEff(eff: (QualifiedName, Arguments))(using ctx: C)(using Σ: Signature): Eff =
    (transformQualifiedName(eff._1), eff._2.map(transformVTerm))

  def transformBigLevel(layer: Nat)(using ctx: C)(using Σ: Signature): Nat =
    layer

  def transformQualifiedName(qn: QualifiedName)(using ctx: C)(using Σ: Signature): QualifiedName =
    qn

  def transformName(name: Name)(using ctx: C)(using Σ: Signature): Name = name

  def transformCTerm(tm: CTerm)(using ctx: C)(using Σ: Signature): CTerm =
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
      case recordType: RecordType       => transformRecordType(recordType)
      case operationCall: OperationCall => transformOperationCall(operationCall)
      case continuation: Continuation   => transformContinuation(continuation)
      case handler: Handler             => transformHandler(handler)
