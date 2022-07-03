package com.github.tgeng.archon.core.ir

import collection.mutable
import com.github.tgeng.archon.common.*
import com.github.tgeng.archon.core.common.*

private class RenamerContext:
  val nameStack = mutable.ArrayBuffer[Ref[Name]]()

  val allNames = mutable.LinkedHashSet[Ref[Name]]()
  val allReferencedNames = mutable.Set[Ref[Name]]()

  val potentiallyConflictingNames = mutable.Map[Ref[Name], mutable.ArrayBuffer[Ref[Name]]]()

object RenamerDetector extends Visitor[RenamerContext, Unit] :

  def rename(tm: VTerm)(using Γ: Context)(using Σ: Signature): Unit =
    doRename(visitVTerm(tm))

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
        case _ => ???
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

object TermPrettyPrinter extends Visitor[IndexedSeq[Name], Block] :
  override def combine(blocks: Block*)(using ctx: IndexedSeq[Name])(using Σ: Signature) =
    Block(blocks: _*)
