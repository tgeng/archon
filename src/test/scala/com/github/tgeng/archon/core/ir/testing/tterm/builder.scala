package com.github.tgeng.archon.core.ir.testing.tterm

import com.github.tgeng.archon.core.ir.*

extension (ctx: StringContext)
  def ct(args: Any*)(using TranslationContext): CTerm =
    val tTerm = Parser.parseTTerm(ctx.s(args*))
    tTerm.toCTerm

  def vt(args: Any*)(using TranslationContext): VTerm =
    val tTerm = Parser.parseTTerm(ctx.s(args*))
    tTerm.toCTerm match
      case CTerm.Return(v, VTerm.Auto()) => v
      case ct                            => VTerm.Collapse(ct)(using ct.sourceInfo)

  def decls
    (args: Any*)
    (using tCtx: TranslationContext)
    (using Context)
    (using Signature)
    (using TypingContext)
    : (TranslationContext, Signature) =
    val decls = Parser.parseDeclarations(ctx.s(args*))
    given newTranslationCtx: TranslationContext = tCtx.bindDecls(decls)
    val preDecls = decls.map(_.toPreDeclaration)
    val newSignature = elaborateAll(preDecls)
    (newTranslationCtx, newSignature)

extension (newContexts: (TranslationContext, Signature))
  def apply[T](f: (TranslationContext, Signature) ?=> T): T =
    f(using newContexts._1, newContexts._2)
