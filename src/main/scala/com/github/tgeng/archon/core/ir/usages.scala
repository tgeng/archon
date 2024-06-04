package com.github.tgeng.archon.core.ir

import com.github.tgeng.archon.common.Block

def collectUsages
  (tm: VTerm)
  (using Γ: Context)
  (using Σ: Signature)
  (using ctx: TypingContext)
  : Usages =
  ctx.trace("collectUsages", PrettyPrinter.pprint(tm)):
    UsagesCollector.visitVTerm(tm)(using (Γ, ctx))

def collectUsages
  (tm: CTerm)
  (using Γ: Context)
  (using Σ: Signature)
  (using ctx: TypingContext)
  : Usages =
  ctx.trace("collectUsages", PrettyPrinter.pprint(tm)):
    UsagesCollector.visitCTerm(tm)(using (Γ, ctx))

private object UsagesCollector extends TermVisitor[(Context, TypingContext), Usages]:
  // TODO: do not count usages in type!! Also take continuation usage into account. Also do use
  // usage multiplication when handling function args.

  override def combine
    (rs: Usages*)
    (using ctx: (Context, TypingContext))
    (using Σ: Signature)
    : Usages =
    rs.fold(Usages.zero(using ctx._1))(_ + _)

  override def withTelescope
    (telescope: => Telescope)
    (action: ((Context, TypingContext)) ?=> Usages)
    (using ctx: (Context, TypingContext))
    (using Σ: Signature)
    : Usages =
    // TODO: verify usages beyond the current context
    action(using (ctx._1 ++ telescope, ctx._2))

  override def visitVar
    (v: VTerm.Var)
    (using ctx: (Context, TypingContext))
    (using Σ: Signature)
    : Usages = Usages.single(v)(using ctx._1)
