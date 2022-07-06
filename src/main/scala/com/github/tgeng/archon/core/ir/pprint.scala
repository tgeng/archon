package com.github.tgeng.archon.core.ir

import collection.mutable
import com.github.tgeng.archon.common.*
import com.github.tgeng.archon.core.common.*
import collection.immutable.{ListMap, ListSet}

import WrapPolicy.*
import IndentPolicy.*
import DelimitPolicy.*
import Name.*
import Variance.*
import CoPattern.*
import Pattern.*
import VTerm.*
import CTerm.*
import ULevel.*


private class RenamerContext:
  val nameStack = mutable.ArrayBuffer[Ref[Name]]()

  val allNames = mutable.LinkedHashSet[Ref[Name]]()
  val allReferencedNames = mutable.Set[Ref[Name]]()

  val potentiallyConflictingNames = mutable.Map[Ref[Name], mutable.ArrayBuffer[Ref[Name]]]()

object Renamer extends Visitor[RenamerContext, Unit] :

  def rename(tm: VTerm)(using Γ: Context)(using Σ: Signature): Unit =
    doRename(visitVTerm(tm))

  def rename(tm: CTerm)(using Γ: Context)(using Σ: Signature): Unit =
    doRename(visitCTerm(tm))

  private def createRenamerContext(using Γ: Context) =
    val ctx = RenamerContext()
    val initialNames = Γ.map(_.name)
    ctx.nameStack.addAll(initialNames)
    ctx.allNames.addAll(initialNames)
    ctx

  private def doRename(action: RenamerContext ?=> Unit)(using Γ: Context): Unit =
    val ctx: RenamerContext = createRenamerContext
    action(using ctx)
    import Name.*
    ctx.allNames.foreach { ref =>
      ref.value match
        case _: Generated if !ctx.allReferencedNames(ref) => ref.value = Unreferenced
        case _ =>
    }
    ctx.allNames.foreach { ref =>
      ref.value match
        case Unreferenced =>
        case n =>
          ref.value = n.deriveNameWithoutConflicts(
            ctx.potentiallyConflictingNames.lift(n)
              .getOrElse(Nil)
              .map(_.value).toSet
          )
    }

  override def combine(rs: Unit*)(using ctx: RenamerContext)(using Σ: Signature) = ()

  override def withBindings(bindingNames: => Seq[Ref[Name]])
    (action: RenamerContext ?=> Unit)
    (using ctx: RenamerContext)
    (using Σ: Signature): Unit =
    val names = bindingNames
    ctx.nameStack.appendAll(names)
    ctx.allNames.addAll(names)
    action(using ctx)
    ctx.nameStack.remove(ctx.nameStack.size - names.size, names.size)

  override def visitVar(v: VTerm.Var)
    (using ctx: RenamerContext)
    (using Σ: Signature): Unit =
    val stackIndex = ctx.nameStack.size - v.idx - 1
    val refName = try {
      ctx.nameStack(stackIndex)
    } catch {
      case e => throw e
    }
    ctx.allReferencedNames.add(refName)
    for name <- ctx.nameStack.view.slice(stackIndex + 1, ctx.nameStack.size) do
      ctx.potentiallyConflictingNames.getOrElseUpdate(name, mutable.ArrayBuffer()).addOne(refName)

enum PPrintPrecedence extends Ordered[PPrintPrecedence] :
  case PPManualEncapsulation, PPApp, PPLevelOp, PPEffOp, PPFun, PPComma, PPBase

  override def compare(that: PPrintPrecedence): Int = this.ordinal.compareTo(that.ordinal)

import PPrintPrecedence.*

class PPrintContext(
  val names: mutable.ArrayBuffer[Ref[Name]],
  var currentPrecedence: PPrintPrecedence = PPBase,
):
  def resolve(dbIndex: Nat): Ref[Name] = names(names.size - 1 - dbIndex)

  def withPrecedence(precedence: PPrintPrecedence)(action: PPrintContext ?=> Block): Block =
    val oldPrecedence = currentPrecedence
    currentPrecedence = precedence
    try {
      val b = action(using this)
      if oldPrecedence == PPManualEncapsulation || oldPrecedence > precedence then
        b
      else
        Block(Concat, Wrap, FixedIncrement(2), "(", b, ")")
    } finally {
      currentPrecedence = oldPrecedence
    }

  def withBindings[T](bindings: Seq[Ref[Name]])(action: PPrintContext ?=> T): T =
    names.appendAll(bindings)
    try {
      action(using this)
    } finally {
      names.remove(names.size - bindings.size, bindings.size)
    }

object PPrintContext:
  def apply(ctx: Context) = new PPrintContext(ctx.map(_.name).to(mutable.ArrayBuffer))

object PrettyPrinter extends Visitor[PPrintContext, Block] :
  def pprint(tm: VTerm | CTerm)(using Γ: Context)(using Σ: Signature): Block = tm match
    case tm: VTerm =>
      Renamer.rename(tm)
      visitVTerm(tm)(using PPrintContext(Γ))
    case tm: CTerm =>
      Renamer.rename(tm)
      visitCTerm(tm)(using PPrintContext(Γ))

  given(using PPrintContext)(using Signature): Conversion[VTerm, Block] = visitVTerm(_)

  given(using PPrintContext)(using Signature): Conversion[CTerm, Block] = visitCTerm(_)

  given(using PPrintContext)
    (using Signature): Conversion[Binding[VTerm], Block] = visitBinding(_)

  given(using PPrintContext)
    (using Signature): Conversion[Ref[Name], Block] = n => Block(n.value.toString)

  given(using PPrintContext)
    (using Signature): Conversion[Name, Block] = n => Block(n.toString)

  given(using PPrintContext)(using Signature): Conversion[ULevel, Block] = visitULevel(_)

  given(using PPrintContext)
    (using Signature): Conversion[QualifiedName, Block] = visitQualifiedName(_)

  override def combine(blocks: Block*)
    (using ctx: PPrintContext)
    (using Σ: Signature): Block =
    if blocks.isEmpty then throw IllegalStateException()
    else Block(Whitespace, Aligned, Wrap, blocks)

  override def withBindings(bindingNames: => Seq[Ref[Name]])
    (action: PPrintContext ?=> Block)
    (using ctx: PPrintContext)
    (using Σ: Signature): Block = ctx.withBindings(bindingNames) {
    action
  }

  override def visitPreTTelescope(tTelescope: Seq[(Binding[CTerm], Variance)])
    (using ctx: PPrintContext)
    (using Σ: Signature): Block =
    given(using PPrintContext)
      (using Signature): Conversion[Binding[CTerm], Block] = visitPreBinding(_)

    bracketAndComma(
      tTelescope.map {
        case (binding, INVARIANT) => binding
        case (binding, COVARIANT) => Block("+", binding)
        case (binding, CONTRAVARIANT) => Block("-", binding)
      }
    )

  override def visitTTelescope(tTelescope: Seq[(Binding[VTerm], Variance)])
    (using PPrintContext)
    (using Signature): Block = bracketAndComma(
    tTelescope.map {
      case (binding, INVARIANT) => binding
      case (binding, COVARIANT) => Block("+", binding)
      case (binding, CONTRAVARIANT) => Block("-", binding)
    }
  )

  override def visitPreTelescope(telescope: Seq[Binding[CTerm]])
    (using ctx: PPrintContext)
    (using Σ: Signature): Block = bracketAndComma(telescope.map(visitPreBinding))

  override def visitTelescope(telescope: Seq[Binding[VTerm]])
    (using ctx: PPrintContext)
    (using Σ: Signature): Block = bracketAndComma(telescope.map(visitBinding))

  override def visitPreBinding(binding: Binding[CTerm])
    (using PPrintContext)
    (using Signature): Block = binding.name.value match
    case Unreferenced => Block(binding.ty)
    case n => Block(n, ":", binding.ty)

  override def visitBinding(binding: Binding[VTerm])
    (using PPrintContext)
    (using Signature): Block = binding.name.value match
    case Unreferenced => Block(binding.ty)
    case n => Block(n, ":", binding.ty)

  override def visitPVar(pVar: PVar)
    (using ctx: PPrintContext)
    (using Σ: Signature): Block = Block(ctx.resolve(pVar.idx).value.toString)

  override def visitPRefl(PRefl: PRefl)
    (using gctx: PPrintContext)
    (using Σ: Signature): Block = Block("Refl{}")

  override def visitPDataType(pDataType: PDataType)
    (using ctx: PPrintContext)
    (using Σ: Signature): Block = bracketAndSpace(
    pDataType.qn,
    pDataType.args.map(visitPattern)
  )

  override def visitPForcedDataType(pDataType: PForcedDataType)
    (using ctx: PPrintContext)
    (using Σ: Signature): Block = bracketAndSpace(
    Block("." + pDataType.qn.shortName),
    pDataType.args.map(visitPattern)
  )

  override def visitPForced(pForced: PForced)
    (using ctx: PPrintContext)
    (using Σ: Signature): Block = Block(Concat, ".(", pForced.term, ")")

  override def visitPAbsurd(pAbsurd: PAbsurd)
    (using ctx: PPrintContext)
    (using Σ: Signature): Block = Block("()")

  override def visitCProjection(p: CProjection)
    (using ctx: PPrintContext)
    (using Σ: Signature): Block = Block(Concat, "#", p.name)

  override def visitType(ty: Type)
    (using ctx: PPrintContext)
    (using Σ: Signature): Block = ty match
    case Type(USimpleLevel(Level(l, operands)), Top(_)) if operands.isEmpty => Block("Type" + l.sub)
    case Type(USimpleLevel(l), Top(_)) => app("Type", l)
    case Type(UωLevel(layer), Top(_)) => Block("TYPE" + layer.sub)
    case Type(USimpleLevel(l), upperbound) => app("SubtypeOf", l, upperbound)
    case Type(UωLevel(layer), upperbound) => Block("SUBTYPEOF", layer.toString, upperbound)

  override def visitTop(top: Top)
    (using ctx: PPrintContext)
    (using Σ: Signature): Block = top.ul match
    case USimpleLevel(Level(l, operands)) if operands.isEmpty => Block("Top" + l.sub)
    case USimpleLevel(l) => app("Top", l)
    case UωLevel(layer) => Block("TOP" + layer.sub)

  override def visitPure(pure: Pure)
    (using ctx: PPrintContext)
    (using Σ: Signature): Block = pure.ul match
    case USimpleLevel(Level(l, operands)) if operands.isEmpty => Block("Pure" + l.sub)
    case USimpleLevel(l) => app("Pure", l)
    case UωLevel(layer) => Block("PURE" + layer.sub)

  override def visitVar(v: Var)(using ctx: PPrintContext)(using Σ: Signature): Block =
    Block(ctx.resolve(v.idx).value.toString)

  override def visitCollapse(collapse: Collapse)
    (using ctx: PPrintContext)
    (using Σ: Signature): Block = app("clp", collapse.cTm)

  override def visitU(u: U)(using ctx: PPrintContext)(using Σ: Signature): Block = app("U", u.cTy)

  override def visitThunk(thunk: Thunk)
    (using ctx: PPrintContext)
    (using Σ: Signature): Block = app("thk", thunk.c)

  override def visitDataType(dataType: DataType)
    (using ctx: PPrintContext)
    (using Σ: Signature): Block = bracketAndSpace(dataType.qn, dataType.args.map(visitVTerm))

  override def visitCon(con: Con)(using ctx: PPrintContext)(using Σ: Signature): Block =
    bracketAndSpace(con.name, con.args.map(visitVTerm))

  override def visitEqualityType(equalityType: EqualityType)
    (using ctx: PPrintContext)
    (using Σ: Signature): Block = app(
    "Equality",
    equalityType.ty,
    equalityType.left,
    equalityType.right,
  )

  override def visitRefl(refl: Refl)
    (using ctx: PPrintContext)
    (using Σ: Signature): Block = Block("Refl{}")

  override def visitEffects(effects: Effects)(using ctx: PPrintContext)(using Σ: Signature): Block =
    ctx.withPrecedence(PPEffOp) {
      (effects.literal.map(visitEff) ++ effects.unionOperands.map(visitVar)) sepBy "|"
    }

  override def visitLevel(level: Level)(using ctx: PPrintContext)(using Σ: Signature): Block =
    val operands = mutable.ArrayBuffer[Block]()
    if level.maxOperands.values.forall(_ < level.literal) then
      operands.append(Block("L" + level.literal.sub))
    level.maxOperands.foreach { (v, offset) =>
      offset match
        case 0 => operands.append(v)
        case _ => operands.append(Block(Whitespace, NoWrap, v, "+", offset.toString))
    }
    if operands.size == 1 then
      operands.head
    else ctx.withPrecedence(PPLevelOp) {
      operands sepBy "∨"
    }

  override def visitHeap(heap: Heap)
    (using ctx: PPrintContext)
    (using Σ: Signature): Block = Block(heap.key.toString)

  override def visitCellType(cellType: CellType)
    (using ctx: PPrintContext)
    (using Σ: Signature): Block = cellType.status match
    case CellStatus.Initialized => app("Cell", cellType.heap, cellType.ty)
    case CellStatus.Uninitialized => app("UCell", cellType.heap, cellType.ty)

  override def visitCell(cell: Cell)
    (using ctx: PPrintContext)
    (using Σ: Signature): Block =
    Block("cell" + cell.index + "@" + cell.heapKey)

  override def visitHole(using ctx: PPrintContext)(using Σ: Signature): Block = Block("<hole>")

  override def visitCType(cType: CType)
    (using ctx: PPrintContext)
    (using Σ: Signature): Block = cType match
    case CType(USimpleLevel(Level(l, operands)), CTop(_, _), eff) if operands.isEmpty =>
      Block("CType" + l.sub)
    case CType(USimpleLevel(l), CTop(_, tEff), eff) if tEff == Total => ctype(eff, "CType", l)
    case CType(UωLevel(layer), CTop(_, tEff), eff) if tEff == Total =>
      ctype(eff, "CTYPE" + layer.sub)
    case CType(USimpleLevel(l), upperbound, eff) => ctype(eff, "CSubtypeOf", l, upperbound)
    case CType(UωLevel(layer), upperbound, eff) =>
      ctype(eff, "CSUBTYPEOF", layer.toString, upperbound)


  override def visitCTop(cTop: CTop)(using ctx: PPrintContext)(using Σ: Signature): Block =
    cTop.ul match
      case USimpleLevel(Level(l, operands)) if operands.isEmpty =>
        ctype(cTop.effects, "CTop" + l.sub)
      case USimpleLevel(l) => ctype(cTop.effects, "CTop", l)
      case UωLevel(layer) => ctype(cTop.effects, "CTOP" + layer.sub)

  override def visitForce(force: Force)
    (using ctx: PPrintContext)
    (using Σ: Signature): Block = app("frc", force.v)

  override def visitF(f: F)(using ctx: PPrintContext)(using Σ: Signature) =
    ctype(f.effects, "F", f.vTy)

  override def visitReturn(r: Return)
    (using ctx: PPrintContext)
    (using Σ: Signature): Block = app("rtn", r.v)

  override def visitLet(let: Let)(using ctx: PPrintContext)(using Σ: Signature): Block =
    val (bindings, body) = unroll[(Name, Block), CTerm](let) {
      case l@Let(t, body) => Left(((l.boundName, visitCTerm(t)), body, Seq(l.boundName)))
      case c => Right(visitCTerm(c))
    }

    ctx.withPrecedence(PPBase) {
      Block(
        AlwaysNewline,
        Aligned,
        bindings.map {
          case (boundName, t) => Block("let", boundName, "=", t)
        },
        body
      )
    }

  override def visitFunctionType(functionType: FunctionType)
    (using ctx: PPrintContext)
    (using Σ: Signature): Block = ctx.withPrecedence(PPFun) {
    val (bindings, body) = unroll[(Block, Block), CTerm](functionType) {
      case FunctionType(
      binding,
      bodyTy,
      effects
      ) => Left(((visitBinding(binding), visitVTerm(effects)), bodyTy, Seq(binding.name)))
      case c => Right(visitCTerm(c))
    }

    ctx.withPrecedence(PPFun) {
      Block(
        Whitespace,
        ChopDown,
        Aligned,
        bindings.map {
          case (binding, effects) => ctype(effects, binding, "->")
        },
        body
      )
    }
  }

  override def visitApplication(application: Application)
    (using ctx: PPrintContext)
    (using Σ: Signature): Block =
    val (args, f) = unroll[Elimination[VTerm], CTerm](application) {
      case Application(fun, arg) => Left((Elimination.ETerm(arg), fun, Nil))
      case Projection(fun, name) => Left((Elimination.EProj(name), fun, Nil))
      case t => Right(visitCTerm(t))
    }
    app(f, args.map(visitElim))

  private def visitElim(elim: Elimination[VTerm])
    (using ctx: PPrintContext)
    (using Σ: Signature): Block = elim match
    case Elimination.ETerm(t) => t
    case Elimination.EProj(n) => Block("#" + n)


  override def visitRecordType(recordType: RecordType)
    (using ctx: PPrintContext)
    (using Σ: Signature): Block = ctype(
    recordType.effects,
    bracketAndSpace(recordType.qn, recordType.args.map(visitVTerm))
  )

  override def visitProjection(projection: Projection)
    (using ctx: PPrintContext)
    (using Σ: Signature): Block =

    val (args, f) = unroll[Elimination[VTerm], CTerm](projection) {
      case Application(fun, arg) => Left((Elimination.ETerm(arg), fun, Nil))
      case Projection(fun, name) => Left((Elimination.EProj(name), fun, Nil))
      case c => Right(visitCTerm(c))
    }
    app(f, args.map(visitElim))

  override def visitOperatorCall(operatorCall: OperatorCall)
    (using ctx: PPrintContext)
    (using Σ: Signature): Block = app(
    Block(operatorCall.name, "@", visitEff(operatorCall.eff)),
    operatorCall.args.map(visitVTerm)
  )

  override def visitContinuation(continuation: Continuation)
    (using ctx: PPrintContext)
    (using Σ: Signature): Block = Block(s"<continuation#${continuation.systemId} ${continuation.capturedStack.size}>")

  override def visitHandler(handler: Handler)
    (using ctx: PPrintContext)
    (using Σ: Signature): Block = visitHandlers(handler)

  override def visitAllocOp(allocOp: AllocOp)(using ctx: PPrintContext)(using Σ: Signature): Block =
    app("alloc", allocOp.heap, allocOp.ty)

  override def visitSetOp(setOp: SetOp)(using ctx: PPrintContext)(using Σ: Signature): Block =
    app("set", setOp.cell, setOp.value)

  override def visitGetOp(getOp: GetOp)(using ctx: PPrintContext)(using Σ: Signature): Block =
    app("get", getOp.cell)

  override def visitHeapHandler(heapHandler: HeapHandler)
    (using ctx: PPrintContext)
    (using Σ: Signature): Block = visitHandlers(heapHandler)

  private def visitHandlers(handler: HeapHandler | Handler)
    (using ctx: PPrintContext)
    (using Σ: Signature): Block =
    val (handlers, input) = unroll[Block, CTerm](handler) {
      case h@Handler(effTm, otherEffects, outputType, transform, handlers, input) => Left(
        (
          Block(
            Whitespace, NoWrap,
            "hdl",
            visitEff(effTm),
            eff(otherEffects),
            outputType,
            bracketAndNewline(
              Block(
                Whitespace, Wrap, FixedIncrement(2),
                Block(Whitespace, NoWrap, "rtn", h.transformBoundName, "->"),
                transform
              ) +: handlers.keys.toSeq.map { name =>
                val (paramNames, resumeName) = h.handlersBoundNames(name)
                val body = handlers(name)
                Block(
                  Whitespace, Wrap, FixedIncrement(2),
                  Block(
                    Whitespace, NoWrap,
                    name, paramNames.map(r => visitName(r.value)), resumeName, "->",
                  ),
                  body
                )
              }
            )
          ),
          input,
          Nil)
      )
      case h@HeapHandler(otherEffects, _, _, input) => Left(
        (
          Block(
            Whitespace, NoWrap,
            "heap",
            h.boundName,
            eff(otherEffects),
          ),
          input,
          Seq(h.boundName))
      )
      case c => Right(visitCTerm(c))
    }

    ctx.withPrecedence(PPBase) {
      Block(
        AlwaysNewline,
        Aligned,
        handlers,
        input
      )
    }

  override def visitEff(eff: (QualifiedName, Arguments))
    (using ctx: PPrintContext)
    (using Σ: Signature): Block = bracketAndSpace(eff._1, eff._2.map(visitVTerm))

  override def visitBigLevel(layer: Nat)
    (using ctx: PPrintContext)
    (using Σ: Signature): Block = Block("ω" + layer)

  override def visitQualifiedName(qn: QualifiedName)
    (using ctx: PPrintContext)
    (using Σ: Signature): Block = Block(qn.shortName.toString)

  override def visitName(name: Name)
    (using ctx: PPrintContext)
    (using Σ: Signature): Block = Block(name.toString)

  private def ctype(
    effTm: PPrintContext ?=> Block,
    blocks: (PPrintContext ?=> String | Block | Iterable[Block])*
  )
    (using ctx: PPrintContext): Block = ctx.withPrecedence(PPEffOp) {
    if effTm == Total then
      app(blocks: _*)
    else
      Block(
        Whitespace, Wrap, FixedIncrement(2),
        Block(
          Concat, NoWrap, "<", ctx.withPrecedence(PPManualEncapsulation) {
            effTm
          }, ">"
        ),
        app(blocks: _*),

      )
  }

  private def eff(tm: VTerm)
    (using ctx: PPrintContext)
    (using Σ: Signature): Block = ctx.withPrecedence(PPEffOp) {
    Block(Concat, NoWrap, "<", tm, ">")
  }

  private def app(blocks: (PPrintContext ?=> String | Block | Iterable[Block])*)
    (using ctx: PPrintContext): Block = ctx.withPrecedence(PPApp) {
    Block(
      Whitespace +:
        FixedIncrement(2) +:
        Wrap +:
        blocks.map[(WrapPolicy | IndentPolicy | DelimitPolicy | Block | String | Iterable[Block])](
          _ (using summon[PPrintContext])
        ): _*
    )
  }

  private def bracketAndSpace(head: Block, blocks: PPrintContext ?=> Seq[Block])
    (using ctx: PPrintContext): Block = ctx.withPrecedence(PPManualEncapsulation) {
    Block(
      Concat, FixedIncrement(2),
      head,
      "{",
      ctx.withPrecedence(PPComma) {
        Block(
          Whitespace, ChopDown, Aligned,
          blocks(using ctx)
        )
      },
      "}"
    )
  }

  private def bracketAndComma(blocks: PPrintContext ?=> Seq[Block])
    (using ctx: PPrintContext): Block = ctx.withPrecedence(PPManualEncapsulation) {
    Block(
      Concat, FixedIncrement(2),
      "{",
      ctx.withPrecedence(PPComma) {
        Block(
          Whitespace, ChopDown, Aligned,
          blocks(using ctx).map(b => Block(NoWrap, Concat, b, ","))
        )
      },
      "}"
    )
  }

  private def bracketAndNewline(blocks: PPrintContext ?=> Seq[Block])
    (using ctx: PPrintContext): Block = ctx.withPrecedence(PPManualEncapsulation) {
    Block(
      Concat, FixedIncrement(2),
      "{",
      ctx.withPrecedence(PPComma) {
        Block(
          Whitespace, AlwaysNewline, Aligned,
          blocks(using ctx)
        )
      },
      "}"
    )
  }

  extension (blocks: Iterable[String | Block])
    def sepBy(delimiter: String | Block): Block =
      if blocks.isEmpty then Block()
      else Block(
        Whitespace,
        Wrap,
        FixedIncrement(2),
        blocks.init.map(Block(Whitespace, NoWrap, _, delimiter)),
        blocks.last
      )

private def unroll[E, T](t: T)
  (destruct: PPrintContext ?=> T => Either[(E, T, Seq[Ref[Name]]), Block])
  (using ctx: PPrintContext): (List[E], Block) = destruct(t) match
  case Left((e, t, bindings)) => ctx.withBindings(bindings) {
    unroll(t)(destruct) match
      case (es, t) => (e :: es, t)
  }
  case Right(b) => (Nil, b)

