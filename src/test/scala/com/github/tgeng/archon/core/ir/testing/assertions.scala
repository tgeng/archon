package com.github.tgeng.archon.core.ir.testing

import com.github.tgeng.archon.common.*
import com.github.tgeng.archon.core.ir.*
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

private inline def enableDebugging(using ctx: TypingContext): Unit =
  val stacktrace = Thread.currentThread().nn.getStackTrace.nn
  println(s"Debugging ${stacktrace(2)}")
  ctx.enableDebugging = true
