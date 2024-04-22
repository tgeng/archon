package com.github.tgeng.archon.core.ir.testing.tterm

import com.github.tgeng.archon.core.ir.*

import scala.jdk.CollectionConverters.*
import scala.language.unsafeNulls

extension (ctx: StringContext)
  def ct(args: Any*)(using TranslationContext): CTerm =
    val tTerm = Parser.parseTTerm(ctx.s(args*))
    tTerm.toCTerm

  def vt(args: Any*)(using TranslationContext): VTerm =
    val tTerm = Parser.parseTTerm(ctx.s(args*))
    tTerm.toCTerm match
      case CTerm.Return(v, VTerm.Auto()) => v
      case ct                            => VTerm.Collapse(ct)(using ct.sourceInfo)

  def decls[T]
    (args: Any*)
    (using tCtx: TranslationContext)
    (using Context)
    (using Signature)
    (using TypingContext)
    (f: (TranslationContext, Signature) ?=> T)
    : T =
    val str = ctx.s(args*)
    val lastLine = str.lines().iterator().asScala.toSeq.last
    val indent = lastLine.size
    val newStr = str.lines().map(_.drop(indent)).toList.asScala.drop(1).dropRight(1).mkString("\n")
    val decls = Parser.parseDeclarations(newStr)
    given newTranslationCtx: TranslationContext = tCtx.bindDecls(decls)
    val preDecls = decls.map(_.toPreDeclaration)
    val newSignature = elaborateAll(preDecls)
    f(using newTranslationCtx, newSignature)
