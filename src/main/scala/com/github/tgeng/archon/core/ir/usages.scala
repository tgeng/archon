package com.github.tgeng.archon.core.ir

def collectUsages
  (tm: VTerm)
  (using Γ: Context)
  (using Σ: Signature)
  (using ctx: TypingContext)
  : Usages =
  UsagesCollector.visitVTerm(tm)(using (Γ, ctx))

def collectUsages
  (tm: CTerm)
  (using Γ: Context)
  (using Σ: Signature)
  (using ctx: TypingContext)
  : Usages =
  UsagesCollector.visitCTerm(tm)(using (Γ, ctx))

private object UsagesCollector extends TermVisitor[(Context, TypingContext), Usages]:

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
    action(using (ctx._1 ++ telescope, ctx._2))

  override def visitVar
    (v: VTerm.Var)
    (using ctx: (Context, TypingContext))
    (using Σ: Signature)
    : Usages = Usages.single(v)(using ctx._1)
