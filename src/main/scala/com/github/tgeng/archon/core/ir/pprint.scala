package com.github.tgeng.archon.core.ir

import collection.mutable
import com.github.tgeng.archon.common.*
import com.github.tgeng.archon.core.common.*

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

  private def doRename(action: RenamerContext ?=> Unit): Unit =
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
            ctx.potentiallyConflictingNames(n)
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
    val stackIndex = ctx.nameStack.size - v.index - 1
    val refName = ctx.nameStack(stackIndex)
    ctx.allReferencedNames.add(refName)
    for name <- ctx.nameStack.view.slice(stackIndex + 1, ctx.nameStack.size) do
      ctx.potentiallyConflictingNames.getOrElseUpdate(name, mutable.ArrayBuffer()).addOne(refName)

type PrettyPrintContext = collection.IndexedSeq[Ref[Name]]

object TermPrettyPrinter extends Visitor[PrettyPrintContext, Block] :
  def pprint(tm: VTerm)(using Γ: Context)(using Σ: Signature): Block =
    Renamer.rename(tm)
    visitVTerm(tm)(using Γ.map(_.name))

  def pprint(tm: CTerm)(using Γ: Context)(using Σ: Signature): Block =
    Renamer.rename(tm)
    visitCTerm(tm)(using Γ.map(_.name))

  given(using PrettyPrintContext)(using Signature): Conversion[VTerm, Block] = visitVTerm(_)

  given(using PrettyPrintContext)(using Signature): Conversion[CTerm, Block] = visitCTerm(_)

  given(using PrettyPrintContext)
    (using Signature): Conversion[Binding[VTerm], Block] = visitBinding(_)

  given(using PrettyPrintContext)
    (using Signature): Conversion[Ref[Name], Block] = n => Block(n.value.toString)

  given(using PrettyPrintContext)
    (using Signature): Conversion[Name, Block] = n => Block(n.toString)

  import WrapPolicy.*
  import IndentPolicy.*
  import DelimitPolicy.*
  import Name.*
  import Variance.*

  override def combine(blocks: Block*)
    (using ctx: PrettyPrintContext)
    (using Σ: Signature): Block =
    if blocks.isEmpty then throw IllegalStateException()
    else Block(Whitespace, Aligned, Wrap, blocks)

  override def withBindings(bindingNames: => Seq[Ref[Name]])
    (action: PrettyPrintContext ?=> Block)
    (using ctx: PrettyPrintContext)
    (using Σ: Signature): Block =
    action(using ctx ++ bindingNames)

  override def visitPreTTelescope(tTelescope: Seq[(Binding[CTerm], Variance)])
    (using ctx: PrettyPrintContext)
    (using Σ: Signature): Block =
    given(using PrettyPrintContext)
      (using Signature): Conversion[Binding[CTerm], Block] = visitPreBinding(_)

    bracketAndComma(
      tTelescope.map {
        case (binding, INVARIANT) => binding
        case (binding, COVARIANT) => Block("+", binding)
        case (binding, CONTRAVARIANT) => Block("-", binding)
      }
    )

  override def visitTTelescope(tTelescope: Seq[(Binding[VTerm], Variance)])
    (using PrettyPrintContext)
    (using Signature): Block = bracketAndComma(
    tTelescope.map {
      case (binding, INVARIANT) => binding
      case (binding, COVARIANT) => Block("+", binding)
      case (binding, CONTRAVARIANT) => Block("-", binding)
    }
  )

  override def visitPreTelescope(telescope: Seq[Binding[CTerm]])
    (using ctx: PrettyPrintContext)
    (using Σ: Signature): Block = bracketAndComma(telescope.map(visitPreBinding))

  override def visitTelescope(telescope: Seq[Binding[VTerm]])
    (using ctx: PrettyPrintContext)
    (using Σ: Signature): Block = bracketAndComma(telescope.map(visitBinding))

  override def visitPreBinding(binding: Binding[CTerm])
    (using PrettyPrintContext)
    (using Signature): Block = binding.name.value match
    case Unreferenced => Block(binding.ty)
    case n => Block(n, ":", binding.ty)

  override def visitBinding(binding: Binding[VTerm])
    (using PrettyPrintContext)
    (using Signature): Block = binding.name.value match
    case Unreferenced => Block(binding.ty)
    case n => Block(n, ":", binding.ty)

  private def bracketAndComma(blocks: Seq[Block]): Block = Block(
    Concat, FixedIncrement(2),
    "{",
    Block(
      Whitespace, ChopDown, Aligned,
      blocks.map(b => Block(NoWrap, Concat, b, ","))
    ),
    "}"
  )
