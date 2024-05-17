package com.github.tgeng.archon.core.ir.testing

import com.github.tgeng.archon.core.ir.*
import com.github.tgeng.archon.core.ir.CTerm.*
import com.github.tgeng.archon.core.ir.VTerm.*
import org.scalatest.Assertions.*

def assertVType
  (t: VTerm, ty: VTerm, expectedNormalizedT: Option[VTerm] = None)
  (using Γ: Context)
  (using Σ: Signature)
  (using ctx: TypingContext)
  : Unit =
  try
    val (actualNormalizedT, usages) = checkType(t, ty)
    expectedNormalizedT match
      case Some(expected) if expected != actualNormalizedT =>
        fail(
          s"Actual: ${PrettyPrinter.pprint(actualNormalizedT)}\nExpected: ${PrettyPrinter.pprint(expected)}",
        )
      case _ =>
    verifyUsages(usages, Γ.toTelescope)(using Context.empty)
  catch
    case e: IrError => {
      enableDebugging
      checkType(t, ty)
    }

def assertNotVType
  (t: VTerm, ty: VTerm)
  (using Γ: Context)
  (using Σ: Signature)
  (using ctx: TypingContext)
  : Unit =
  try
    checkType(t, ty)
    enableDebugging
    checkType(t, ty)
    fail(s"Expected type mismatch.")
  catch case _: IrError => ()

def assertCType
  (t: CTerm, ty: CTerm, expectedNormalizedT: Option[CTerm] = None)
  (using Γ: Context)
  (using Σ: Signature)
  (using ctx: TypingContext)
  : Unit =
  try
    val (actualNormalizedT, usages) = checkType(t, ty)
    expectedNormalizedT match
      case Some(expected) if expected != actualNormalizedT =>
        fail(
          s"Actual: ${PrettyPrinter.pprint(actualNormalizedT)}\nExpected: ${PrettyPrinter.pprint(expected)}",
        )
      case _ =>
    verifyUsages(usages, Γ.toTelescope)(using Context.empty)
  catch
    case e: IrError => {
      enableDebugging
      checkType(t, ty)
    }

def assertNotCType
  (t: CTerm, ty: CTerm)
  (using Γ: Context)
  (using Σ: Signature)
  (using ctx: TypingContext)
  : Unit =
  try
    checkType(t, ty)
    enableDebugging
    checkType(t, ty)
    fail(s"Expected type mismatch.")
  catch case _: IrError => ()

def assertSubtype
  (sub: VTerm, sup: VTerm)
  (using Γ: Context)
  (using Σ: Signature)
  (using ctx: TypingContext)
  : Unit =
  if ctx.solve(checkIsSubtype(sub, sup)).nonEmpty then
    fail(s"Expect\n${PrettyPrinter.pprint(sub)}\n⊆\n${PrettyPrinter.pprint(sup)}")

def assertConvertible
  (a: VTerm, b: VTerm, ty: Option[VTerm] = None)
  (using Γ: Context)
  (using Σ: Signature)
  (using ctx: TypingContext)
  : Unit =
  val replacedA = replaceAuto(a, ty)
  val replacedB = replaceAuto(b, ty)
  try
    if ctx.solve(checkIsConvertible(replacedA, replacedB, ty)).nonEmpty then
      fail(s"Expect\n${PrettyPrinter.pprint(a)}\n≡\n${PrettyPrinter.pprint(b)}")
  catch
    case e: IrError =>
      enableDebugging
      ctx.solve(checkIsConvertible(replacedA, replacedB, ty))

private def replaceAuto
  (t: VTerm, ty: Option[VTerm])
  (using Γ: Context)
  (using Σ: Signature)
  (using ctx: TypingContext)
  : VTerm =
  given SourceInfo = SourceInfo.SiEmpty
  t match
    case Auto() => Collapse(ctx.addUnsolved(F(ty.get)))
    case _      => t

inline def enableDebugging(using ctx: TypingContext): Unit =
  val stacktrace = Thread.currentThread().nn.getStackTrace.nn
  println(s"Debugging ${stacktrace(2)}")
  ctx.enableDebugging = true
