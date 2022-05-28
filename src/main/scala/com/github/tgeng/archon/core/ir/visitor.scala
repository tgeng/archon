package com.github.tgeng.archon.core.ir

import com.github.tgeng.archon.common.*
import com.github.tgeng.archon.core.common.*
import CTerm.*
import VTerm.*
import ULevel.*

trait Visitor[C, R]:

  def visitPreTTelescope(tTelescope: Seq[(Binding[CTerm], Variance)])(using ctx: C)(using Σ: Signature): R =
    combine(tTelescope.map(e => visitCTerm(e._1.ty)): _*)

  def visitTTelescope(tTelescope: Seq[(Binding[VTerm], Variance)])(using ctx: C)(using Σ: Signature): R =
    combine(tTelescope.map(e => visitBinding(e._1)): _*)

  def visitPreTelescope(telescope: Seq[Binding[CTerm]])(using ctx: C)(using Σ: Signature): R =
    combine(telescope.map(b => visitCTerm(b.ty)): _*)

  def visitTelescope(telescope: Seq[Binding[VTerm]])(using ctx: C)(using Σ: Signature): R =
    combine(telescope.map(visitBinding): _*)

  def visitBinding(binding: Binding[VTerm])(using ctx: C)(using Σ: Signature): R =
    visitVTerm(binding.ty)

  def visitVTerms(tms: Seq[VTerm])(using ctx: C)(using Σ: Signature): R =
    combine(tms.map(visitVTerm): _*)

  def visitCTerms(tms: Seq[CTerm])(using ctx: C)(using Σ: Signature): R =
    combine(tms.map(visitCTerm): _*)

  def combine(rs: R*)(using ctx: C)(using Σ: Signature): R

  def offsetContext(ctx: C, bindingNames: =>List[Name]): C = ctx

  def visitVTerm(tm: VTerm)(using ctx: C)(using Σ: Signature): R = tm match
    case ty: Type => visitType(ty)
    case top: Top => visitTop(top)
    case pure: Pure => visitPure(pure)
    case v: Var => visitVar(v)
    case collapse: Collapse => visitCollapse(collapse)
    case u: U => visitU(u)
    case thunk: Thunk => visitThunk(thunk)
    case dataType: DataType => visitDataType(dataType)
    case con: Con => visitCon(con)
    case equalityType: EqualityType => visitEqualityType(equalityType)
    case Refl => visitRefl
    case EffectsType => visitEffectsType
    case effects: Effects => visitEffects(effects)
    case LevelType => visitLevelType
    case level: Level => visitLevel(level)
    case HeapType => visitHeapType
    case heap: Heap => visitHeap(heap)
    case cellType: CellType => visitCellType(cellType)
    case cell: Cell => visitCell(cell)

  def visitType(ty: Type)(using ctx: C)(using Σ: Signature): R =
    combine(
      visitULevel(ty.ul),
      visitVTerm(ty.upperBound)
    )

  def visitTop(top: Top)(using ctx: C)(using Σ: Signature): R = visitULevel(top.ul)

  def visitPure(pure: Pure)(using ctx: C)(using Σ: Signature): R = visitULevel(pure.ul)

  def visitVar(v: Var)(using ctx: C)(using Σ: Signature): R = combine()

  def visitCollapse(collapse: Collapse)
    (using ctx: C)
    (using Σ: Signature): R = visitCTerm(collapse.cTm)

  def visitU(u: U)(using ctx: C)(using Σ: Signature): R = visitCTerm(u.cTy)

  def visitThunk(thunk: Thunk)(using ctx: C)(using Σ: Signature): R = visitCTerm(thunk.c)

  def visitDataType(dataType: DataType)(using ctx: C)(using Σ: Signature): R =
    combine(
      visitQualifiedName(dataType.qn) +:
        dataType.args.map(visitVTerm): _*
    )

  def visitCon(con: Con)(using ctx: C)(using Σ: Signature): R =
    combine(
      visitName(con.name) +:
        con.args.map(visitVTerm): _*
    )

  def visitEqualityType(equalityType: EqualityType)(using ctx: C)(using Σ: Signature): R =
    combine(
      visitVTerm(equalityType.ty),
      visitVTerm(equalityType.left),
      visitVTerm(equalityType.right)
    )

  def visitRefl(using ctx: C)(using Σ: Signature): R = combine()

  def visitEffectsType(using ctx: C)(using Σ: Signature): R = visitQualifiedName(Builtins.EffectsQn)

  def visitEffects(effects: Effects)(using ctx: C)(using Σ: Signature): R =
    combine(
      (effects.literal.map(visitEff) ++ effects.unionOperands.map(visitVar)).toSeq: _*
    )

  def visitLevelType(using ctx: C)(using Σ: Signature): R = visitQualifiedName(Builtins.LevelQn)

  def visitLevel(level: Level)(using ctx: C)(using Σ: Signature): R =
    combine(
      level.maxOperands.map {
        case (v, _) => visitVTerm(v)
      }.toSeq: _*
    )

  def visitHeapType(using ctx: C)(using Σ: Signature): R = visitQualifiedName(Builtins.HeapQn)

  def visitHeap(heap: Heap)(using ctx: C)(using Σ: Signature): R = combine()

  def visitCellType(cellType: CellType)(using ctx: C)(using Σ: Signature): R =
    combine(
      visitVTerm(cellType.heap),
      visitVTerm(cellType.ty),
    )

  def visitCell(cell: Cell)(using ctx: C)(using Σ: Signature): R = combine()

  def visitHole(using ctx: C)(using Σ: Signature): R = combine()

  def visitCType(cType: CType)(using ctx: C)(using Σ: Signature): R =
    combine(
      visitULevel(cType.ul),
      visitCTerm(cType.upperBound),
      visitVTerm(cType.effects)
    )

  def visitCTop(cTop: CTop)(using ctx: C)(using Σ: Signature): R =
    combine(
      visitULevel(cTop.ul),
      visitVTerm(cTop.effects)
    )

  def visitDef(d: Def)(using ctx: C)(using Σ: Signature): R = visitQualifiedName(d.qn)

  def visitForce(force: Force)(using ctx: C)(using Σ: Signature): R = visitVTerm(force.v)

  def visitF(f: F)(using ctx: C)(using Σ: Signature) =
    combine(
      visitVTerm(f.vTy),
      visitVTerm(f.effects)
    )

  def visitReturn(r: Return)(using ctx: C)(using Σ: Signature): R = visitVTerm(r.v)

  def visitLet(let: Let)(using ctx: C)(using Σ: Signature): R =
    combine(
      visitCTerm(let.t),
      visitCTerm(let.ctx)(using offsetContext(ctx, List(let.boundName)))
    )

  def visitFunctionType(functionType: FunctionType)(using ctx: C)(using Σ: Signature): R =
    combine(
      visitVTerm(functionType.binding.ty),
      visitCTerm(functionType.bodyTy)(using offsetContext(ctx, List(functionType.binding.name))),
      visitVTerm(functionType.effects)
    )

  def visitApplication(application: Application)(using ctx: C)(using Σ: Signature): R =
    combine(
      visitCTerm(application.fun),
      visitVTerm(application.arg),
    )

  def visitRecordType(recordType: RecordType)(using ctx: C)(using Σ: Signature): R =
    combine(
      visitQualifiedName(recordType.qn) +:
        recordType.args.map(visitVTerm) :+
        visitVTerm(recordType.effects): _*
    )

  def visitProjection(projection: Projection)(using ctx: C)(using Σ: Signature): R =
    combine(
      visitCTerm(projection.rec),
      visitName(projection.name)
    )

  def visitOperatorCall(operatorCall: OperatorCall)(using ctx: C)(using Σ: Signature): R =
    combine(
      visitEff(operatorCall.eff) +:
        visitName(operatorCall.name) +:
        operatorCall.args.map(visitVTerm): _*
    )

  def visitContinuation(continuation: Continuation)(using ctx: C)(using Σ: Signature): R =
    combine(continuation.capturedStack.map(visitCTerm): _*)

  def visitHandler(handler: Handler)(using ctx: C)(using Σ: Signature): R =
    lazy val operatorsByName = Σ.getOperators(handler.eff._1).associatedBy(_.name)
    combine(
      visitEff(handler.eff) +:
        visitVTerm(handler.otherEffects) +:
        visitVTerm(handler.outputType) +:
        visitCTerm(handler.transform)(using offsetContext(ctx, List(gn"x"))) +:
        handler.handlers.map { (name, body) =>
          visitCTerm(body)(
            using offsetContext(
              ctx,
              (gn"resume" +: operatorsByName(name).paramTys.map(_.name)).reverse
            )
          )
        }.toSeq :+
        visitCTerm(handler.input): _*
    )

  def visitAllocOp(allocOp: AllocOp)(using ctx: C)(using Σ: Signature): R =
    combine(
      visitVTerm(allocOp.heap),
      visitVTerm(allocOp.ty),
    )

  def visitSetOp(setOp: SetOp)(using ctx: C)(using Σ: Signature): R =
    combine(
      visitVTerm(setOp.cell),
      visitVTerm(setOp.value),
    )

  def visitGetOp(getOp: GetOp)(using ctx: C)(using Σ: Signature): R =
    combine(visitVTerm(getOp.cell))

  def visitHeapHandler(heapHandler: HeapHandler)(using ctx: C)(using Σ: Signature): R =
    combine(
      visitVTerm(heapHandler.otherEffects),
      visitCTerm(heapHandler.input)(using offsetContext(ctx, List(gn"h")))
    )

  def visitEff(eff: (QualifiedName, Arguments))(using ctx: C)(using Σ: Signature): R =
    combine(
      visitQualifiedName(eff._1) +:
        eff._2.map(visitVTerm): _*
    )

  def visitULevel(ul: ULevel)(using ctx: C)(using Σ: Signature): R = ul match
    case USimpleLevel(level) => visitVTerm(level)
    case UωLevel(layer) => visitBigLevel(layer)

  def visitBigLevel(layer: Nat)(using ctx: C)(using Σ: Signature): R = combine()

  def visitQualifiedName(qn: QualifiedName)(using ctx: C)(using Σ: Signature): R = combine()

  def visitName(name: Name)(using ctx: C)(using Σ: Signature): R = combine()

  def visitCTerm(tm: CTerm)(using ctx: C)(using Σ: Signature): R = tm match
    case Hole => visitHole
    case cType: CType => visitCType(cType)
    case cTop: CTop => visitCTop(cTop)
    case d: Def => visitDef(d)
    case force: Force => visitForce(force)
    case f: F => visitF(f)
    case r: Return => visitReturn(r)
    case let: Let => visitLet(let)
    case functionType: FunctionType => visitFunctionType(functionType)
    case application: Application => visitApplication(application)
    case recordType: RecordType => visitRecordType(recordType)
    case projection: Projection => visitProjection(projection)
    case operatorCall: OperatorCall => visitOperatorCall(operatorCall)
    case continuation: Continuation => visitContinuation(continuation)
    case handler: Handler => visitHandler(handler)
    case allocOp: AllocOp => visitAllocOp(allocOp)
    case setOp: SetOp => visitSetOp(setOp)
    case getOp: GetOp => visitGetOp(getOp)
    case heapHandler: HeapHandler => visitHeapHandler(heapHandler)

trait Transformer[C]:
  def offsetContext(ctx: C, bindingNames: List[Name]): C = ctx

  def transformVTerm(tm: VTerm)(using ctx: C)(using Σ: Signature): VTerm = tm match
    case ty: Type => transformType(ty)
    case top: Top => transformTop(top)
    case pure: Pure => transformPure(pure)
    case v: Var => transformVar(v)
    case collapse: Collapse => transformCollapse(collapse)
    case u: U => transformU(u)
    case thunk: Thunk => transformThunk(thunk)
    case dataType: DataType => transformDataType(dataType)
    case con: Con => transformCon(con)
    case equalityType: EqualityType => transformEqualityType(equalityType)
    case Refl => transformRefl
    case EffectsType => transformEffectsType
    case effects: Effects => transformEffects(effects)
    case LevelType => transformLevelType
    case level: Level => transformLevel(level)
    case HeapType => transformHeapType
    case heap: Heap => transformHeap(heap)
    case cellType: CellType => transformCellType(cellType)
    case cell: Cell => transformCell(cell)

  def transformType(ty: Type)(using ctx: C)(using Σ: Signature): VTerm =
    Type(
      transformULevel(ty.ul),
      transformVTerm(ty.upperBound)
    )

  def transformTop(top: Top)(using ctx: C)(using Σ: Signature): VTerm = Top(transformULevel(top.ul))

  def transformPure(pure: Pure)
    (using ctx: C)
    (using Σ: Signature): VTerm = Pure(transformULevel(pure.ul))

  def transformVar(v: Var)(using ctx: C)(using Σ: Signature): VTerm = v

  def transformCollapse(collapse: Collapse)
    (using ctx: C)
    (using Σ: Signature): VTerm = Collapse(transformCTerm(collapse.cTm))

  def transformU(u: U)(using ctx: C)(using Σ: Signature): VTerm = U(transformCTerm(u.cTy))

  def transformThunk(thunk: Thunk)(using ctx: C)(using Σ: Signature): VTerm = Thunk(
    transformCTerm(
      thunk.c
    )
  )

  def transformDataType(dataType: DataType)(using ctx: C)(using Σ: Signature): VTerm =
    DataType(
      transformQualifiedName(dataType.qn),
      dataType.args.map(transformVTerm)
    )

  def transformCon(con: Con)(using ctx: C)(using Σ: Signature): VTerm =
    Con(
      transformName(con.name),
      con.args.map(transformVTerm),
    )

  def transformEqualityType(equalityType: EqualityType)(using ctx: C)(using Σ: Signature): VTerm =
    EqualityType(
      transformVTerm(equalityType.ty),
      transformVTerm(equalityType.left),
      transformVTerm(equalityType.right)
    )

  def transformRefl(using ctx: C)(using Σ: Signature): VTerm = Refl

  def transformEffectsType(using ctx: C)(using Σ: Signature): VTerm = EffectsType

  def transformEffects(effects: Effects)(using ctx: C)(using Σ: Signature): VTerm

  def transformLevelType(using ctx: C)(using Σ: Signature): VTerm = LevelType

  def transformLevel(level: Level)(using ctx: C)(using Σ: Signature): VTerm

  def transformHeapType(using ctx: C)(using Σ: Signature): VTerm = HeapType

  def transformHeap(heap: Heap)(using ctx: C)(using Σ: Signature): VTerm = heap

  def transformCellType(cellType: CellType)(using ctx: C)(using Σ: Signature): VTerm =
    CellType(
      transformVTerm(cellType.heap),
      transformVTerm(cellType.ty),
      cellType.status,
    )

  def transformCell(cell: Cell)(using ctx: C)(using Σ: Signature): VTerm = cell

  def transformHole(using ctx: C)(using Σ: Signature): CTerm = Hole

  def transformCType(cType: CType)(using ctx: C)(using Σ: Signature): CTerm =
    CType(
      transformULevel(cType.ul),
      transformCTerm(cType.upperBound),
      transformVTerm(cType.effects)
    )

  def transformCTop(cTop: CTop)(using ctx: C)(using Σ: Signature): CTerm =
    CTop(
      transformULevel(cTop.ul),
      transformVTerm(cTop.effects),
    )

  def transformDef(d: Def)
    (using ctx: C)
    (using Σ: Signature): CTerm = Def(transformQualifiedName(d.qn))

  def transformForce(force: Force)(using ctx: C)(using Σ: Signature): CTerm =
    Force(transformVTerm(force.v))

  def transformF(f: F)(using ctx: C)(using Σ: Signature) =
    F(
      transformVTerm(f.vTy),
      transformVTerm(f.effects)
    )

  def transformReturn(r: Return)(using ctx: C)(using Σ: Signature): CTerm =
    Return(transformVTerm(r.v))

  def transformLet(let: Let)(using ctx: C)(using Σ: Signature): CTerm =
    Let(
      transformCTerm(let.t),
      transformCTerm(let.ctx)(using offsetContext(ctx, List(let.boundName)))
    )(let.boundName)

  def transformFunctionType(functionType: FunctionType)(using ctx: C)(using Σ: Signature): CTerm =
    FunctionType(
      Binding(transformVTerm(functionType.binding.ty))(functionType.binding.name),
      transformCTerm(functionType.bodyTy)(
        using offsetContext(
          ctx,
          List(functionType.binding.name)
        )
      ),
      transformVTerm(functionType.effects)
    )

  def transformApplication(application: Application)(using ctx: C)(using Σ: Signature): CTerm =
    Application(
      transformCTerm(application.fun),
      transformVTerm(application.arg),
    )

  def transformRecordType(recordType: RecordType)(using ctx: C)(using Σ: Signature): CTerm =
    RecordType(
      transformQualifiedName(recordType.qn),
      recordType.args.map(transformVTerm),
      transformVTerm(recordType.effects),
    )

  def transformProjection(projection: Projection)(using ctx: C)(using Σ: Signature): CTerm =
    Projection(
      transformCTerm(projection.rec),
      transformName(projection.name),
    )

  def transformOperatorCall(operatorCall: OperatorCall)(using ctx: C)(using Σ: Signature): CTerm =
    OperatorCall(
      transformEff(operatorCall.eff),
      transformName(operatorCall.name),
      operatorCall.args.map(transformVTerm),
    )

  def transformContinuation(continuation: Continuation)(using ctx: C)(using Σ: Signature): CTerm =
    Continuation(continuation.capturedStack.map(transformCTerm))

  def transformHandler(handler: Handler)(using ctx: C)(using Σ: Signature): CTerm =
    val operatorsByName = Σ.getOperators(handler.eff._1).associatedBy(_.name)
    Handler(
      transformEff(handler.eff),
      transformVTerm(handler.otherEffects),
      transformVTerm(handler.outputType),
      transformCTerm(handler.transform)(using offsetContext(ctx, List(gn"x"))),
      handler.handlers.map { (name, body) =>
        (name, transformCTerm(body)(
          using offsetContext(
            ctx,
            (gn"resume" +: operatorsByName(name).paramTys.map(_.name)).reverse
          )
        ))
      },
      transformCTerm(handler.input),
    )

  def transformAllocOp(allocOp: AllocOp)(using ctx: C)(using Σ: Signature): CTerm =
    AllocOp(
      transformVTerm(allocOp.heap),
      transformVTerm(allocOp.ty),
    )

  def transformSetOp(setOp: SetOp)(using ctx: C)(using Σ: Signature): CTerm =
    SetOp(
      transformVTerm(setOp.cell),
      transformVTerm(setOp.value),
    )

  def transformGetOp(getOp: GetOp)(using ctx: C)(using Σ: Signature): CTerm =
    GetOp(transformVTerm(getOp.cell))

  def transformHeapHandler(heapHandler: HeapHandler)(using ctx: C)(using Σ: Signature): CTerm =
    HeapHandler(
      transformVTerm(heapHandler.otherEffects),
      heapHandler.key,
      heapHandler.heapContent,
      transformCTerm(heapHandler.input)(using offsetContext(ctx, List(gn"h")))
    )

  def transformEff(eff: (QualifiedName, Arguments))(using ctx: C)(using Σ: Signature): Eff =
    (transformQualifiedName(eff._1), eff._2.map(transformVTerm))

  def transformULevel(ul: ULevel)(using ctx: C)(using Σ: Signature): ULevel = ul match
    case USimpleLevel(level) => USimpleLevel(transformVTerm(level))
    case UωLevel(layer) => UωLevel(transformBigLevel(layer))

  def transformBigLevel(layer: Nat)(using ctx: C)(using Σ: Signature): Nat = layer

  def transformQualifiedName(qn: QualifiedName)
    (using ctx: C)
    (using Σ: Signature): QualifiedName = qn

  def transformName(name: Name)(using ctx: C)(using Σ: Signature): Name = name

  def transformCTerm(tm: CTerm)(using ctx: C)(using Σ: Signature): CTerm = tm match
    case Hole => transformHole
    case cType: CType => transformCType(cType)
    case cTop: CTop => transformCTop(cTop)
    case d: Def => transformDef(d)
    case force: Force => transformForce(force)
    case f: F => transformF(f)
    case r: Return => transformReturn(r)
    case let: Let => transformLet(let)
    case functionType: FunctionType => transformFunctionType(functionType)
    case application: Application => transformApplication(application)
    case recordType: RecordType => transformRecordType(recordType)
    case projection: Projection => transformProjection(projection)
    case operatorCall: OperatorCall => transformOperatorCall(operatorCall)
    case continuation: Continuation => transformContinuation(continuation)
    case handler: Handler => transformHandler(handler)
    case allocOp: AllocOp => transformAllocOp(allocOp)
    case setOp: SetOp => transformSetOp(setOp)
    case getOp: GetOp => transformGetOp(getOp)
    case heapHandler: HeapHandler => transformHeapHandler(heapHandler)
