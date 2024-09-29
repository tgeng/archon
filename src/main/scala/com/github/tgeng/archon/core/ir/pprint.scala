package com.github.tgeng.archon.core.ir

import com.github.tgeng.archon.common.*
import com.github.tgeng.archon.common.DelimitPolicy.*
import com.github.tgeng.archon.common.IndentPolicy.*
import com.github.tgeng.archon.common.WrapPolicy.*
import com.github.tgeng.archon.core.common.*
import com.github.tgeng.archon.core.common.Name.*
import com.github.tgeng.archon.core.ir.CTerm.*
import com.github.tgeng.archon.core.ir.CoPattern.*
import com.github.tgeng.archon.core.ir.Pattern.*
import com.github.tgeng.archon.core.ir.VTerm.*
import com.github.tgeng.archon.core.ir.Variance.*

import scala.collection.decorators.*
import scala.collection.mutable
import scala.collection.mutable.ArrayBuffer

private class RenamerContext:
  val nameStack: mutable.ArrayBuffer[Ref[Name]] = mutable.ArrayBuffer[Ref[Name]]()

  val allNames: mutable.LinkedHashSet[Ref[Name]] = mutable.LinkedHashSet[Ref[Name]]()
  val allReferencedNames: mutable.Set[Ref[Name]] = mutable.Set[Ref[Name]]()

  val potentiallyConflictingNames: mutable.Map[Ref[Name], ArrayBuffer[Ref[Name]]] =
    mutable.Map[Ref[Name], mutable.ArrayBuffer[Ref[Name]]]()

object Renamer extends Visitor[RenamerContext, Unit]:

  def rename(tm: VTerm)(using Γ: Context)(using Signature): Unit =
    doRename(visitVTerm(tm))

  def rename(tm: CTerm)(using Γ: Context)(using Signature): Unit =
    doRename(visitCTerm(tm))

  def rename(t: List[Binding[VTerm]])(using Γ: Context)(using Signature): Unit =
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
        case _                                           =>
    }
    ctx.allNames.foreach { ref =>
      ref.value match
        case Unreferenced =>
        case n =>
          ref.value = n.deriveNameWithoutConflicts(
            ctx.potentiallyConflictingNames
              .getOrElse(ref, Nil)
              .map(_.value)
              .toSet,
          )
    }

  override def combine(rs: Unit*)(using ctx: RenamerContext)(using Σ: Signature): Unit = ()

  override def withBoundNames
    (bindingNames: => Seq[Ref[Name]])
    (action: RenamerContext ?=> Unit)
    (using ctx: RenamerContext)
    (using Σ: Signature)
    : Unit =
    val names = bindingNames
    ctx.nameStack.appendAll(names)
    ctx.allNames.addAll(names)
    action(using ctx)
    ctx.nameStack.remove(ctx.nameStack.size - names.size, names.size)

  override def visitVar(v: VTerm.Var)(using ctx: RenamerContext)(using Σ: Signature): Unit =
    val stackIndex = ctx.nameStack.size - v.idx - 1
    if stackIndex < 0 then throw IndexOutOfBoundsException(s"Variable index out of bound: ${v.idx}")
    val refName = ctx.nameStack(stackIndex)
    ctx.allReferencedNames.add(refName)
    for name <- ctx.nameStack.view.slice(stackIndex + 1, ctx.nameStack.size) do
      ctx.potentiallyConflictingNames
        .getOrElseUpdate(name, mutable.ArrayBuffer())
        .addOne(refName)

enum PPrintPrecedence extends Ordered[PPrintPrecedence]:
  case PPManualEncapsulation, PPApp, PPLevelOp, PPEffOp, PPFun, PPComma,
    PPStatement, PPBase

  override def compare(that: PPrintPrecedence): Int =
    this.ordinal.compareTo(that.ordinal)

import com.github.tgeng.archon.core.ir.PPrintPrecedence.*

class PPrintContext
  (
    val names: mutable.ArrayBuffer[Ref[Name]],
    var currentPrecedence: PPrintPrecedence = PPBase,
  ):
  def resolve(dbIndex: Nat): Ref[Name] = names(names.size - 1 - dbIndex)

  def withPrecedence(precedence: PPrintPrecedence)(action: PPrintContext ?=> Block): Block =
    val oldPrecedence = currentPrecedence
    currentPrecedence = precedence
    try
      val b = action(using this)
      if oldPrecedence == PPManualEncapsulation || oldPrecedence > precedence
      then b
      else Block(Concat, Wrap, FixedIncrement(2), "(", b, ")")
    finally currentPrecedence = oldPrecedence

  def withBindings[T](bindings: Seq[Ref[Name]])(action: PPrintContext ?=> T): T =
    names.appendAll(bindings)
    try
      action(using this)
    finally
      names.remove(names.size - bindings.size, bindings.size)

object PPrintContext:
  def apply(ctx: Context) = new PPrintContext(
    ctx.map(_.name).to(mutable.ArrayBuffer),
  )

import pprint as genericPprint

object PrettyPrinter extends Visitor[PPrintContext, Block]:
  def pprint(telescope: Telescope)(using Γ: Context)(using Σ: Signature): Block =
    Renamer.rename(telescope)
    visitTelescope(telescope)(using PPrintContext(Γ))

  def pprint(tm: VTerm | CTerm)(using Γ: Context)(using Σ: Signature): Block =
    try
      tm match
        case tm: VTerm =>
          Renamer.rename(tm)
          visitVTerm(tm)(using PPrintContext(Γ))
        case tm: CTerm =>
          Renamer.rename(tm)
          visitCTerm(tm)(using PPrintContext(Γ))
    catch
      case _: IndexOutOfBoundsException =>
        throw IllegalArgumentException(
          s"Failed to pretty print:\n${genericPprint.apply(tm)}\nwith context:\n${genericPprint(Γ)}",
        )

  def pprint(any: Any)(using Γ: Context)(using Σ: Signature): Block =
    Block(
      genericPprint
        .copy(
          additionalHandlers = { case value: (VTerm | CTerm) =>
            genericPprint.Tree.Literal(pprint(value).toString())
          },
        )
        .apply(any)
        .toString,
    )

  given (using PPrintContext)(using Signature): Conversion[VTerm, Block] =
    visitVTerm(_)

  given (using PPrintContext)(using Signature): Conversion[CTerm, Block] =
    visitCTerm(_)

  given (using PPrintContext)(using Signature): Conversion[Binding[VTerm], Block] = visitBinding(
    _,
  )

  given (using PPrintContext)(using Signature): Conversion[Ref[Name], Block] =
    n => Block(n.value.toString)

  given (using PPrintContext)(using Signature): Conversion[Name, Block] = n => Block(n.toString)

  given (using PPrintContext)(using Signature): Conversion[QualifiedName, Block] =
    visitQualifiedName(_)

  override def visitAuto(auto: Auto)(using ctx: PPrintContext)(using Σ: Signature): Block =
    Block("<auto>")

  override def visitMeta(m: CTerm.Meta)(using ctx: PPrintContext)(using Σ: Signature): Block =
    Block(s"<${m.toString}>")

  override def combine(blocks: Block*)(using ctx: PPrintContext)(using Σ: Signature): Block =
    if blocks.isEmpty then throw IllegalStateException()
    else Block(Whitespace, Aligned, Wrap, blocks)

  override def withBoundNames
    (bindingNames: => Seq[Ref[Name]])
    (action: PPrintContext ?=> Block)
    (using ctx: PPrintContext)
    (using Σ: Signature)
    : Block =
    ctx.withBindings(bindingNames):
      action

  override def visitPreTContext
    (tTelescope: List[(Binding[CTerm], Variance)])
    (using ctx: PPrintContext)
    (using Σ: Signature)
    : Block =
    given (using PPrintContext)(using Signature): Conversion[Binding[CTerm], Block] =
      visitPreBinding(_)

    bracketAndComma(
      telescopeToBlock(tTelescope, _._1.name) {
        case (binding, INVARIANT)     => binding
        case (binding, COVARIANT)     => Block("+", binding)
        case (binding, CONTRAVARIANT) => Block("-", binding)
      },
    )

  override def visitUsageLiteral
    (usageLiteral: VTerm.UsageLiteral)
    (using ctx: PPrintContext)
    (using Σ: Signature)
    : Block =
    Block(usageLiteral.usage.toString)

  override def visitUsageProd
    (usageProd: VTerm.UsageProd)
    (using ctx: PPrintContext)
    (using Σ: Signature)
    : Block =
    Block(usageProd.operands.toSeq.map(visitVTerm).intersperse("*"), Whitespace, Aligned, Wrap)

  override def visitUsageSum
    (usageSum: VTerm.UsageSum)
    (using ctx: PPrintContext)
    (using Σ: Signature)
    : Block =
    Block(usageSum.operands.toSeq.map(visitVTerm).intersperse("+"), Whitespace, Aligned, Wrap)

  override def visitUsageJoin
    (usageJoin: VTerm.UsageJoin)
    (using ctx: PPrintContext)
    (using Σ: Signature)
    : Block =
    Block(usageJoin.operands.toSeq.map(visitVTerm).intersperse("|"), Whitespace, Aligned, Wrap)

  override def visitTContext
    (tTelescope: List[(Binding[VTerm], Variance)])
    (using PPrintContext)
    (using Signature)
    : Block = bracketAndComma(
    telescopeToBlock(tTelescope, _._1.name) {
      case (binding, INVARIANT)     => binding
      case (binding, COVARIANT)     => Block("+", binding)
      case (binding, CONTRAVARIANT) => Block("-", binding)
    },
  )

  override def visitPreContext
    (telescope: List[Binding[CTerm]])
    (using ctx: PPrintContext)
    (using Σ: Signature)
    : Block =
    bracketAndComma(
      telescopeToBlock(telescope, _.name)(visitPreBinding),
    )

  override def visitTelescope
    (telescope: List[Binding[VTerm]])
    (using ctx: PPrintContext)
    (using Σ: Signature)
    : Block =
    bracketAndComma(
      telescopeToBlock(telescope, _.name)(visitBinding),
    )

  private def telescopeToBlock[T]
    (telescope: List[T], nameExtractor: T => Ref[Name])
    (toBlock: PPrintContext ?=> T => Block)
    (using ctx: PPrintContext)
    (using Signature)
    : List[Block] = telescope match
    case Nil => Nil
    case t :: rest =>
      toBlock(t) :: ctx.withBindings(Seq(nameExtractor(t))):
        telescopeToBlock(rest, nameExtractor)(toBlock)

  override def visitPreBinding
    (binding: Binding[CTerm])
    (using PPrintContext)
    (using Signature)
    : Block =
    binding.name.value match
      case Unreferenced => Block(binding.ty)
      case n            => Block(n, ":", binding.ty)

  override def visitBinding(binding: Binding[VTerm])(using PPrintContext)(using Signature): Block =
    binding.name.value match
      case Unreferenced => Block(binding.ty)
      case n            => Block(n.toString + ":", binding.ty)

  override def visitPVar(pVar: PVar)(using ctx: PPrintContext)(using Σ: Signature): Block = Block(
    ctx.resolve(pVar.idx).value.toString,
  )

  override def visitPDataType
    (pDataType: PDataType)
    (using ctx: PPrintContext)
    (using Σ: Signature)
    : Block =
    bracketAndSpace(
      pDataType.qn,
      pDataType.args.map(visitPattern),
    )

  override def visitPForcedDataType
    (pDataType: PForcedDataType)
    (using ctx: PPrintContext)
    (using Σ: Signature)
    : Block =
    bracketAndSpace(
      Block("." + pDataType.qn.shortName),
      pDataType.args.map(visitPattern),
    )

  override def visitPForced(pForced: PForced)(using ctx: PPrintContext)(using Σ: Signature): Block =
    Block(Concat, ".(", pForced.term, ")")

  override def visitPAbsurd(pAbsurd: PAbsurd)(using ctx: PPrintContext)(using Σ: Signature): Block =
    Block("()")

  override def visitCProjection
    (p: CProjection)
    (using ctx: PPrintContext)
    (using Σ: Signature)
    : Block =
    Block(Concat, "#", p.name)

  override def visitType(ty: Type)(using ctx: PPrintContext)(using Σ: Signature): Block = ty match
    case Type(Top(Level(l, operands))) if operands.isEmpty =>
      Block("Type" + l.sub)
    case Type(upperBound) => app("TypeOf", upperBound)

  override def visitTop(top: Top)(using ctx: PPrintContext)(using Σ: Signature): Block =
    top.level match
      case Level(l, operands) if operands.isEmpty =>
        Block("Top" + l.sub)
      case l => app("Top", l)

  override def visitVar(v: Var)(using ctx: PPrintContext)(using Σ: Signature): Block =
    Block(ctx.resolve(v.idx).value.toString)

  override def visitCollapse
    (collapse: Collapse)
    (using ctx: PPrintContext)
    (using Σ: Signature)
    : Block =
    app(".collapse", collapse.cTm)

  override def visitU(u: U)(using ctx: PPrintContext)(using Σ: Signature): Block = app("U", u.cTy)

  override def visitThunk(thunk: Thunk)(using ctx: PPrintContext)(using Σ: Signature): Block =
    app(".thunk", thunk.c)

  override def visitDataType
    (dataType: DataType)
    (using ctx: PPrintContext)
    (using Σ: Signature)
    : Block =
    Block(Concat, NoWrap, dataType.qn, bracketAndComma(dataType.args.map(visitVTerm)))

  override def visitCon(con: Con)(using ctx: PPrintContext)(using Σ: Signature): Block =
    Block(Concat, NoWrap, con.name, bracketAndComma(con.args.map(visitVTerm)))

  override def visitEffects(effects: Effects)(using ctx: PPrintContext)(using Σ: Signature): Block =
    if effects.handlerKeys.isEmpty && effects.unionOperands.isEmpty then Block("total")
    else
      ctx.withPrecedence(PPEffOp):
        (effects.handlerKeys.map(visitVTerm) ++ effects.unionOperands.map((k, v) =>
          (if v then "$" else "") + visitVTerm(k),
        )) sepBy "|"

  override def visitLevel(level: Level)(using ctx: PPrintContext)(using Σ: Signature): Block =
    def toBlock(varAndOffset: (VTerm, Nat)): Block = varAndOffset match
      case (v, 0) => v
      case (v, offset) =>
        ctx.withPrecedence(PPLevelOp)(
          Block(Whitespace, NoWrap, v, "+", offset.toString),
        )

    val operands = mutable.ArrayBuffer[Block]()
    operands.append(Block("L" + level.literal.sub))
    if operands.isEmpty && level.maxOperands.size == 1 then toBlock(level.maxOperands.head)
    else if operands.nonEmpty && level.maxOperands.isEmpty then operands.head
    else
      ctx.withPrecedence(PPLevelOp):
        level.maxOperands.foreach { (v, offset) =>
          operands.append(toBlock((v, offset)))
        }
        operands sepBy "∨"

  override def visitHole(using ctx: PPrintContext)(using Σ: Signature): Block =
    Block("<hole>")

  override def visitCType
    (cType: CType)
    (using ctx: PPrintContext)
    (using
      Σ: Signature,
    )
    : Block = cType match
    case CType(CTop(Level(l, operands), tEff), eff) if operands.isEmpty && tEff == Total() =>
      ctype(eff, "CType", l.sub)
    case CType(CTop(l, tEff), eff) if tEff == Total() =>
      ctype(eff, "CType", l)
    case CType(upperBound, eff) =>
      ctype(eff, "CTypeOf", upperBound)

  override def visitCTop
    (cTop: CTop)
    (using ctx: PPrintContext)
    (using
      Σ: Signature,
    )
    : Block =
    cTop.level match
      case Level(l, operands) if operands.isEmpty =>
        ctype(cTop.effects, "CTop" + l.sub)
      case l => ctype(cTop.effects, "CTop", l)

  override def visitDef
    (d: Def)
    (using ctx: PPrintContext)
    (using
      Σ: Signature,
    )
    : Block =
    Block(Concat, NoWrap, ".", d.qn.toString)

  override def visitForce
    (force: Force)
    (using ctx: PPrintContext)
    (using
      Σ: Signature,
    )
    : Block = app(".force", force.v)

  override def visitF(f: F)(using ctx: PPrintContext)(using Σ: Signature): Block =
    ctype(f.effects, "[", f.usage, "]", f.vTy)

  override def visitReturn
    (r: Return)
    (using ctx: PPrintContext)
    (using
      Σ: Signature,
    )
    : Block = app(".return", "[", r.usage, "]", r.v)

  override def visitLet
    (let: Let)
    (using ctx: PPrintContext)
    (using
      Σ: Signature,
    )
    : Block =
    visitStatements(let)

  override def visitFunctionType
    (functionType: FunctionType)
    (using
      ctx: PPrintContext,
    )
    (using Σ: Signature)
    : Block = ctx.withPrecedence(PPFun):
    val (bindings, body) = unroll[(Block, Block), CTerm](functionType):
      case FunctionType(
          binding,
          bodyTy,
          effects,
        ) =>
        Left(
          (
            (visitBinding(binding), visitVTerm(effects)),
            bodyTy,
            Seq(binding.name),
          ),
        )
      case c => Right(visitCTerm(c))

    Block(
      Whitespace,
      ChopDown,
      Aligned,
      bindings.map { case (binding, effects) =>
        ctype(effects, binding, "->")
      },
      body,
    )

  override def visitRedex(redex: Redex)(using ctx: PPrintContext)(using Σ: Signature): Block =
    ctx.withPrecedence(PPApp):
      juxtapose(redex.t, redex.elims.map(visitElim))

  override def visitElim
    (elim: Elimination[VTerm])
    (using ctx: PPrintContext)
    (using
      Σ: Signature,
    )
    : Block = elim match
    case Elimination.ETerm(t) => t
    case Elimination.EProj(n) => Block("#" + n)

  override def visitRecordType
    (
      recordType: RecordType,
    )
    (using ctx: PPrintContext)
    (using Σ: Signature)
    : Block = ctype(
    recordType.effects,
    Block(Concat, NoWrap, recordType.qn, bracketAndComma(recordType.args.map(visitVTerm))),
  )

  override def visitOperationCall
    (
      operationCall: OperationCall,
    )
    (using ctx: PPrintContext)
    (using Σ: Signature)
    : Block = app(
    Block(operationCall.name, "@", visitVTerm(operationCall.effInstance)),
    operationCall.args.map(visitVTerm),
  )

  override def visitContinuation
    (
      continuation: Continuation,
    )
    (using ctx: PPrintContext)
    (using Σ: Signature)
    : Block = Block(
    s"<continuation#${continuation.systemId}>",
  )

  override def visitHandler
    (handler: Handler)
    (using ctx: PPrintContext)
    (using
      Σ: Signature,
    )
    : Block = visitStatements(handler)

  private def visitStatements
    (
      handler: Handler | Let,
    )
    (using ctx: PPrintContext)
    (using Signature)
    : Block =
    val (statements, input) = unroll[Block, CTerm](handler):
      // TODO[P2]: print the extra effect and output type annotations
      case h @ Handler(
          eff,
          otherEffects,
          outputEffects,
          outputUsage,
          outputType,
          parameterBinding,
          parameter,
          parameterDisposer,
          parameterReplicator,
          transform,
          handlers,
          input,
          inputBinding,
          handlerKey,
        ) =>
        Left(
          (
            Block(
              Whitespace,
              NoWrap,
              ".handler",
              visitEff(eff),
              handlerDefinition(
                h.parameterBinding.name,
                Block(
                  Whitespace,
                  Wrap,
                  FixedIncrement(2),
                  Block(Whitespace, NoWrap, ".return", h.inputBinding.name, "->"),
                  withBoundNames(Seq(h.inputBinding.name)) {
                    transform
                  },
                ) +: (parameterDisposer
                  .map(disposer =>
                    Block(
                      Whitespace,
                      Wrap,
                      FixedIncrement(2),
                      Block(Whitespace, NoWrap, ".dispose", "->"),
                      withBoundNames(Seq(h.parameterBinding.name)) {
                        disposer
                      },
                    ),
                  )
                  .toSeq ++ parameterReplicator
                  .map(replicator =>
                    Block(
                      Whitespace,
                      Wrap,
                      FixedIncrement(2),
                      Block(Whitespace, NoWrap, ".replicate", "->"),
                      withBoundNames(Seq(h.parameterBinding.name)) {
                        replicator
                      },
                    ),
                  )
                  .toSeq ++ handlers.keys.toSeq.map { name =>
                  val handlerImpl = handlers(name)
                  val allParamNames = handlerImpl.boundNames
                  val paramBlock = Block(
                    Whitespace,
                    NoWrap,
                    name,
                    allParamNames.map(r => visitName(r.value)),
                    "->",
                  )

                  Block(
                    Whitespace,
                    Wrap,
                    FixedIncrement(2),
                    paramBlock,
                    withBoundNames(allParamNames) {
                      handlerImpl.body
                    },
                  )
                }),
              ),
            ),
            input,
            Nil,
          ),
        )
      case l @ Let(t, tBinding, eff, body) =>
        Left(
          Block(
            ".let",
            l.tBinding.name,
            ":",
            "[",
            tBinding.usage,
            "]",
            "<",
            eff,
            ">",
            tBinding.ty,
            "=",
            visitCTerm(t),
          ),
          body,
          Seq(tBinding.name),
        )
      case c => Right(visitCTerm(c))

    ctx.withPrecedence(PPStatement):
      Block(
        AlwaysNewline,
        Aligned,
        statements,
        input,
      )

  override def visitEff
    (
      eff: (QualifiedName, Arguments),
    )
    (using ctx: PPrintContext)
    (using Σ: Signature)
    : Block = bracketAndSpace(
    Block(NoWrap, Concat, "𝑒 " + eff._1.shortName),
    eff._2.map(visitVTerm),
  )

  override def visitBigLevel
    (layer: Nat)
    (using ctx: PPrintContext)
    (using
      Σ: Signature,
    )
    : Block = Block("ω" + layer)

  override def visitQualifiedName
    (qn: QualifiedName)
    (using ctx: PPrintContext)
    (using
      Σ: Signature,
    )
    : Block = Block(qn.toString)

  override def visitName
    (name: Name)
    (using ctx: PPrintContext)
    (using
      Σ: Signature,
    )
    : Block = Block(name.toString)

  private def ctype
    (
      effTm: PPrintContext ?=> Block,
      blocks: (PPrintContext ?=> String | Block | Iterable[Block])*,
    )
    (using ctx: PPrintContext)
    : Block = ctx.withPrecedence(PPEffOp):
    if effTm.toString == "total" then // This is a hack, but it's so handy...
      app(blocks*)
    else
      Block(
        Whitespace,
        Wrap,
        FixedIncrement(2),
        Block(
          Concat,
          NoWrap,
          "<",
          ctx.withPrecedence(PPManualEncapsulation) {
            effTm
          },
          ">",
        ),
        app(blocks*),
      )

  private def eff(tm: VTerm)(using ctx: PPrintContext)(using Σ: Signature): Block =
    ctx.withPrecedence(PPEffOp):
      Block(Concat, NoWrap, "<", tm, ">")

  private def app
    (
      blocks: (PPrintContext ?=> String | Block | Iterable[Block])*,
    )
    (using ctx: PPrintContext)
    : Block = ctx.withPrecedence(PPApp):
    juxtapose(blocks*)

  private def juxtapose
    (
      blocks: (PPrintContext ?=> String | Block | Iterable[Block])*,
    )
    (using ctx: PPrintContext)
    : Block =
    Block(
      Whitespace +:
        FixedIncrement(2) +:
        Wrap +:
        blocks.map[
          WrapPolicy | IndentPolicy | DelimitPolicy | Block | String | Iterable[Block],
        ](
          _(using summon[PPrintContext]),
        )*,
    )

  private def bracketAndSpace
    (
      head: Block,
      blocks: PPrintContext ?=> Seq[Block],
    )
    (using ctx: PPrintContext)
    : Block =
    ctx.withPrecedence(PPManualEncapsulation):
      Block(
        NoWrap,
        Concat,
        FixedIncrement(2),
        head,
        "{",
        ctx.withPrecedence(PPComma) {
          Block(
            Whitespace,
            NoWrap,
            Aligned,
            blocks(using ctx),
          )
        },
        "}",
      )

  private def bracketAndComma
    (blocks: PPrintContext ?=> Seq[Block])
    (using
      ctx: PPrintContext,
    )
    : Block = ctx.withPrecedence(PPManualEncapsulation):
    Block(
      Concat,
      NoWrap,
      "{",
      ctx.withPrecedence(PPComma) {
        val bs = blocks(using ctx)
        if bs.isEmpty then Block()
        else
          Block(
            Whitespace,
            ChopDown,
            FixedIncrement(2),
            bs.init.map(b => Block(NoWrap, Concat, b, ",")),
            bs.last,
          )
      },
      "}",
    )

  private def handlerDefinition
    (paramName: Ref[Name], blocks: PPrintContext ?=> Seq[Block])
    (using
      ctx: PPrintContext,
    )
    : Block = ctx.withPrecedence(PPManualEncapsulation):
    Block(
      Concat,
      "{",
      ctx.withPrecedence(PPComma) {
        Block(
          Concat,
          AlwaysNewline,
          FixedIncrement(2),
          blocks(using ctx),
        )
      },
      "}",
    )

  extension (blocks: Iterable[String | Block])
    infix def sepBy(delimiter: String | Block): Block =
      if blocks.isEmpty then Block()
      else
        Block(
          Whitespace,
          Wrap,
          FixedIncrement(2),
          blocks.init.map(Block(Whitespace, NoWrap, _, delimiter)),
          blocks.last,
        )

private def unroll[E, T]
  (t: T)
  (
    destruct: PPrintContext ?=> T => Either[(E, T, Seq[Ref[Name]]), Block],
  )
  (using ctx: PPrintContext)
  : (List[E], Block) = destruct(t) match
  case Left((e, t, bindings)) =>
    ctx.withBindings(bindings):
      unroll(t)(destruct) match
        case (es, t) => (e :: es, t)
  case Right(b) => (Nil, b)

extension (o: LevelOrder)
  def sub: String =
    val mString = o.m match
      case 0 => ""
      case m =>
        subNat(m) + "ω₊" // Unfortunately there doesn't seem to be a subscript character for ω
    val nString = subNat(o.n)
    mString + nString

private def subNat(i: Nat): String = i.toString.map(i => (i - '0' + '₀').toChar)

def verbosePPrinter: pprint.PPrinter =
  val visited = mutable.Set.empty[Any]

  def p: pprint.PPrinter = pprint.copy(
    additionalHandlers = {
      case qn: QualifiedName => pprint.Tree.Literal(s"qn\"${qn.toString}\"")
      case n: Name           => pprint.Tree.Literal(s"n\"${n.toString}\"")
      case r: Ref[?]         => pprint.Tree.Literal(s"\"${r.value.toString}\"")
      case b: Binding[?] if !visited.contains((b, b.name)) =>
        visited.add((b, b.name))
        pprint.Tree
          .Infix(
            p.treeify(b, false, true),
            "@",
            pprint.Tree.Literal(pprint.apply(b.name.value.toString).toString),
          )
      case t: VTerm if !visited.contains((t, t.sourceInfo)) =>
        visited.add((t, t.sourceInfo))
        pprint.Tree
          .Infix(
            p.treeify(t, false, true),
            "@",
            pprint.Tree.Literal(pprint.apply(t.sourceInfo.toString).toString),
          )
      case t: CTerm if !visited.contains((t, t.sourceInfo)) =>
        visited.add((t, t.sourceInfo))
        pprint.Tree
          .Infix(
            p.treeify(t, false, true),
            "@",
            pprint.Tree.Literal(pprint.apply(t.sourceInfo.toString).toString),
          )
    },
  )

  p
