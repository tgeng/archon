package com.github.tgeng.archon.core.ir

import collection.mutable
import com.github.tgeng.archon.common.*
import com.github.tgeng.archon.core.common.*
import collection.immutable.{Map, Set}

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

  def rename(t: List[Binding[VTerm]])(using Γ: Context)(using Σ: Signature): Unit =
    doRename(visitTelescope(t))

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
        case Unreferenced if ctx.allReferencedNames(ref) => ref.value = gn"v"
        case _ =>
    }
    ctx.allNames.foreach { ref =>
      ref.value match
        case Unreferenced =>
        case n =>
          ref.value = n.deriveNameWithoutConflicts(
            ctx.potentiallyConflictingNames.getOrElse(ref, Nil)
              .map(_.value)
              .toSet
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
    val refName = ctx.nameStack(stackIndex)
    ctx.allReferencedNames.add(refName)
    for name <- ctx.nameStack.view.slice(stackIndex + 1, ctx.nameStack.size) do
      ctx.potentiallyConflictingNames.getOrElseUpdate(name, mutable.ArrayBuffer()).addOne(refName)

enum PPrintPrecedence extends Ordered[PPrintPrecedence] :
  case PPManualEncapsulation, PPApp, PPLevelOp, PPEffOp, PPFun, PPComma, PPStatement, PPBase

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
  def pprint(tm: VTerm | CTerm | List[Binding[VTerm]])
    (using Γ: Context)
    (using Σ: Signature): Block = tm match
    case tm: VTerm =>
      Renamer.rename(tm)
      visitVTerm(tm)(using PPrintContext(Γ))
    case tm: CTerm =>
      Renamer.rename(tm)
      visitCTerm(tm)(using PPrintContext(Γ))
    case _: List[?] =>
      val t = tm.asInstanceOf[List[Binding[VTerm]]]
      Renamer.rename(t)
      visitTelescope(t)(using PPrintContext(Γ))


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

  override def visitPreTTelescope(tTelescope: List[(Binding[CTerm], Variance)])
    (using ctx: PPrintContext)
    (using Σ: Signature): Block =
    given(using PPrintContext)
      (using Signature): Conversion[Binding[CTerm], Block] = visitPreBinding(_)

    bracketAndComma(
      telescopeToBlock(tTelescope, _._1.name) {
        case (binding, INVARIANT) => binding
        case (binding, COVARIANT) => Block("+", binding)
        case (binding, CONTRAVARIANT) => Block("-", binding)
      }
    )

  override def visitTTelescope(tTelescope: List[(Binding[VTerm], Variance)])
    (using PPrintContext)
    (using Signature): Block = bracketAndComma(
    telescopeToBlock(tTelescope, _._1.name) {
      case (binding, INVARIANT) => binding
      case (binding, COVARIANT) => Block("+", binding)
      case (binding, CONTRAVARIANT) => Block("-", binding)
    }
  )

  override def visitPreTelescope(telescope: List[Binding[CTerm]])
    (using ctx: PPrintContext)
    (using Σ: Signature): Block = bracketAndComma(
    telescopeToBlock(telescope, _.name)(visitPreBinding)
  )

  override def visitTelescope(telescope: List[Binding[VTerm]])
    (using ctx: PPrintContext)
    (using Σ: Signature): Block = bracketAndComma(
    telescopeToBlock(telescope, _.name)(visitBinding)
  )

  private def telescopeToBlock[T](telescope: List[T], nameExtractor: T => Ref[Name])
    (toBlock: PPrintContext ?=> T => Block)
    (using ctx: PPrintContext)
    (using Σ: Signature): List[Block] = telescope match
    case Nil => Nil
    case t :: rest => toBlock(t) :: ctx.withBindings(Seq(nameExtractor(t))) {
      telescopeToBlock(rest, nameExtractor)(toBlock)
    }

  override def visitPreBinding(binding: Binding[CTerm])
    (using PPrintContext)
    (using Signature): Block = binding.name.value match
    case Unreferenced => Block(binding.ty)
    case n => Block(n, ":", binding.ty)

  override def visitBinding(binding: Binding[VTerm])
    (using PPrintContext)
    (using Signature): Block = binding.name.value match
    case Unreferenced => Block(binding.ty)
    case n => Block(n.toString + ":", binding.ty)

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
    case Type(USimpleLevel(Level(l, operands)), Top(_, _, _)) if operands.isEmpty => Block("Type" + l.sub)
    case Type(USimpleLevel(l), Top(_, _, _)) => app("Type", l)
    case Type(UωLevel(layer), Top(_, _, _)) => Block("TYPE" + layer.sub)
    case Type(USimpleLevel(l), upperbound) => app("SubtypeOf", l, upperbound)
    case Type(UωLevel(layer), upperbound) => Block("SUBTYPEOF", layer.toString, upperbound)

  override def visitTop(top: Top)
    (using ctx: PPrintContext)
    (using Σ: Signature): Block = top.ul match
    case USimpleLevel(Level(l, operands)) if operands.isEmpty => Block("Top" + l.sub)
    case USimpleLevel(l) => app("Top", l)
    case UωLevel(layer) => Block("TOP" + layer.sub)

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
    if effects.literal.isEmpty && effects.unionOperands.isEmpty then
      Block("total")
    else
      ctx.withPrecedence(PPEffOp) {
        (effects.literal.map(visitEff) ++ effects.unionOperands.map(visitVTerm)) sepBy "|"
      }

  override def visitLevel(level: Level)(using ctx: PPrintContext)(using Σ: Signature): Block =
    def toBlock(varAndOffset: (VTerm, Nat)): Block = varAndOffset match
      case (v, 0) => v
      case (v, offset) =>
        ctx.withPrecedence(PPLevelOp)(Block(Whitespace, NoWrap, v, "+", offset.toString))

    val operands = mutable.ArrayBuffer[Block]()
    if level.maxOperands.values.forall(_ < level.literal) then
      operands.append(Block("L" + level.literal.sub))

    if operands.isEmpty && level.maxOperands.size == 1 then
      toBlock(level.maxOperands.head)
    else if operands.nonEmpty && level.maxOperands.isEmpty then
      operands.head
    else
      ctx.withPrecedence(PPLevelOp) {
        level.maxOperands.foreach { (v, offset) =>
          operands.append(toBlock((v, offset)))
        }
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

  override def visitDef(d: Def)(using ctx: PPrintContext)(using Σ: Signature): Block =
    Block(Concat, NoWrap, "𝑓 ", d.qn.shortName)

  override def visitForce(force: Force)
    (using ctx: PPrintContext)
    (using Σ: Signature): Block = app("frc", force.v)

  override def visitF(f: F)(using ctx: PPrintContext)(using Σ: Signature) =
    ctype(f.effects, "F", f.vTy)

  override def visitReturn(r: Return)
    (using ctx: PPrintContext)
    (using Σ: Signature): Block = app("rtn", r.v)

  override def visitLet(let: Let)(using ctx: PPrintContext)(using Σ: Signature): Block =
    visitStatements(let)

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

  override def visitApplication(application: Application)
    (using ctx: PPrintContext)
    (using Σ: Signature): Block =
    ctx.withPrecedence(PPApp) {
      val (args, f) = unroll[Elimination[VTerm], CTerm](application) {
        case Application(fun, arg) => Left((Elimination.ETerm(arg), fun, Nil))
        case Projection(fun, name) => Left((Elimination.EProj(name), fun, Nil))
        case t => Right(visitCTerm(t))
      }
      juxtapose(f, args.reverse.map(visitElim))
    }

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
    juxtapose(f, args.reverse.map(visitElim))

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
    (using Σ: Signature): Block = visitStatements(handler)

  override def visitAllocOp(allocOp: AllocOp)(using ctx: PPrintContext)(using Σ: Signature): Block =
    app("alloc", allocOp.heap, allocOp.ty)

  override def visitSetOp(setOp: SetOp)(using ctx: PPrintContext)(using Σ: Signature): Block =
    app("set", setOp.cell, setOp.value)

  override def visitGetOp(getOp: GetOp)(using ctx: PPrintContext)(using Σ: Signature): Block =
    app("get", getOp.cell)

  override def visitHeapHandler(heapHandler: HeapHandler)
    (using ctx: PPrintContext)
    (using Σ: Signature): Block = visitStatements(heapHandler)

  private def visitStatements(handler: HeapHandler | Handler | Let)
    (using ctx: PPrintContext)
    (using Σ: Signature): Block =
    val (statements, input) = unroll[Block, CTerm](handler) {
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
                withBindings(Seq(h.transformBoundName)) {
                  transform
                }
              ) +: handlers.keys.toSeq.map { name =>
                val (paramNames, resumeName) = h.handlersBoundNames(name)
                val body = handlers(name)
                Block(
                  Whitespace, Wrap, FixedIncrement(2),
                  Block(
                    Whitespace, NoWrap,
                    name, paramNames.map(r => visitName(r.value)), resumeName, "->",
                  ),
                  withBindings(paramNames :+ resumeName) {
                    body
                  }
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
      case l@Let(t, body) => Left(
        Block("let", l.boundName, "=", visitCTerm(t)),
        body,
        Seq(l.boundName)
      )
      case c => Right(visitCTerm(c))
    }

    ctx.withPrecedence(PPStatement) {
      Block(
        AlwaysNewline,
        Aligned,
        statements,
        input
      )
    }

  override def visitEff(eff: (QualifiedName, Arguments))
    (using ctx: PPrintContext)
    (using Σ: Signature): Block = bracketAndSpace(Block(NoWrap, Concat, "𝑒 " + eff._1.shortName), eff._2.map(visitVTerm))

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
    if effTm.toString == "total" then // This is a hack, but it's so handy...
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
    juxtapose(blocks: _*)
  }

  private def juxtapose(blocks: (PPrintContext ?=> String | Block | Iterable[Block])*)
    (using ctx: PPrintContext): Block =
    Block(
      Whitespace +:
        FixedIncrement(2) +:
        Wrap +:
        blocks.map[(WrapPolicy | IndentPolicy | DelimitPolicy | Block | String | Iterable[Block])](
          _ (using summon[PPrintContext])
        ): _*
    )

  private def bracketAndSpace(head: Block, blocks: PPrintContext ?=> Seq[Block])
    (using ctx: PPrintContext): Block = ctx.withPrecedence(PPManualEncapsulation) {
    Block(
      NoWrap, Concat, FixedIncrement(2),
      head,
      "{",
      ctx.withPrecedence(PPComma) {
        Block(
          Whitespace, NoWrap, Aligned,
          blocks(using ctx)
        )
      },
      "}"
    )
  }

  private def bracketAndComma(blocks: PPrintContext ?=> Seq[Block])
    (using ctx: PPrintContext): Block = ctx.withPrecedence(PPManualEncapsulation) {
    Block(
      Concat, NoWrap,
      "{",
      ctx.withPrecedence(PPComma) {
        val bs = blocks(using ctx)
        if bs.isEmpty then
          Block()
        else
          Block(
            Whitespace, ChopDown, FixedIncrement(2),
            bs.init.map(b => Block(NoWrap, Concat, b, ",")),
            bs.last
          )
      },
      "}"
    )
  }

  private def bracketAndNewline(blocks: PPrintContext ?=> Seq[Block])
    (using ctx: PPrintContext): Block = ctx.withPrecedence(PPManualEncapsulation) {
    Block(
      Concat,
      "{",
      ctx.withPrecedence(PPComma) {
        Block(
          Concat, AlwaysNewline, FixedIncrement(2),
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

