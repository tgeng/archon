package com.github.tgeng.archon.core.ir.testing

import com.github.tgeng.archon.core.ir.*
import com.github.tgeng.archon.core.ir.CTerm.*
import org.scalatest.Assertions.*

def assertVType
  (t: VTerm, ty: VTerm, expectedNormalizedT: Option[VTerm] = None)
  (using Γ: Context)
  (using Σ: Signature)
  (using ctx: TypingContext)
  : Unit =
  try
    val (actualNormalizedT) = checkType(t, ty)
    expectedNormalizedT match
      case Some(expected) if expected != actualNormalizedT =>
        fail(
          s"Actual: ${PrettyPrinter.pprint(actualNormalizedT)}\nExpected: ${PrettyPrinter.pprint(expected)}",
        )
      case _ =>
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
    val checkedTy = checkIsCType(ty)
    val actualNormalizedT = checkType(t, checkedTy)
    expectedNormalizedT match
      case Some(expected) if expected != actualNormalizedT =>
        fail(
          s"Actual: ${PrettyPrinter.pprint(actualNormalizedT)}\nExpected: ${PrettyPrinter.pprint(expected)}",
        )
      case _ =>
  catch
    case e: IrError => {
      enableDebugging
      val checkedTy = checkIsCType(ty)
      checkType(t, checkedTy)
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

def assertVSubtype
  (sub: VTerm, sup: VTerm)
  (using Γ: Context)
  (using Σ: Signature)
  (using ctx: TypingContext)
  : Unit =
  if ctx.solve(checkIsSubtype(sub, sup)).nonEmpty then
    fail(s"Expect\n${PrettyPrinter.pprint(sub)}\n⊆\n${PrettyPrinter.pprint(sup)}")

def assertVConvertible
  (a: VTerm, b: VTerm, ty: Option[VTerm] = None)
  (using Γ: Context)
  (using Σ: Signature)
  (using ctx: TypingContext)
  : Unit =
  val (checkedA, checkedB, checkedTy) = ty match
    case None =>
      val (checkedA, checkedTy) = inferTypeWithDebugging(a)
      val (checkedB, _) = inferTypeWithDebugging(b)
      (checkedA, checkedB, checkedTy)
    case Some(ty) =>
      val checkedTy = checkIsType(ty)
      val checkedA = checkTypeWithDebugging(a, checkedTy)
      val checkedB = checkTypeWithDebugging(b, checkedTy)
      (checkedA, checkedB, checkedTy)
  try
    if ctx.solve(checkIsConvertible(checkedA, checkedB, ty)).nonEmpty then
      fail(s"Expect\n${PrettyPrinter.pprint(a)}\n≡\n${PrettyPrinter.pprint(b)}")
  catch
    case e: IrError =>
      enableDebugging
      ctx.solve(checkIsConvertible(checkedA, checkedB, Some(checkedTy)))

def assertCSubtype
  (sub: CTerm, sup: CTerm)
  (using Γ: Context)
  (using Σ: Signature)
  (using ctx: TypingContext)
  : Unit =
  if ctx.solve(checkIsSubtype(sub, sup)).nonEmpty then
    fail(s"Expect\n${PrettyPrinter.pprint(sub)}\n⊆\n${PrettyPrinter.pprint(sup)}")

def assertCConvertible
  (a: CTerm, b: CTerm, ty: Option[CTerm] = None)
  (using Γ: Context)
  (using Σ: Signature)
  (using ctx: TypingContext)
  : Unit =
  val (checkedA, checkedB, checkedTy) = ty match
    case None =>
      val (checkedA, checkedTy) = inferTypeWithDebugging(a)
      val (checkedB, _) = inferTypeWithDebugging(b)
      (checkedA, checkedB, checkedTy)
    case Some(ty) =>
      val checkedTy = checkIsCType(ty)
      val checkedA = checkTypeWithDebugging(a, checkedTy)
      val checkedB = checkTypeWithDebugging(b, checkedTy)
      (checkedA, checkedB, checkedTy)
  try
    if ctx.solve(checkIsConvertible(checkedA, checkedB, ty)).nonEmpty then
      fail(s"Expect\n${PrettyPrinter.pprint(a)}\n≡\n${PrettyPrinter.pprint(b)}")
  catch
    case e: IrError =>
      enableDebugging
      ctx.solve(checkIsConvertible(checkedA, checkedB, Some(checkedTy)))

def checkTypeWithDebugging
  (tm: CTerm, ty: CTerm)
  (using Γ: Context)
  (using Σ: Signature)
  (using ctx: TypingContext)
  : CTerm =
  try checkType(tm, ty)
  catch
    case e: IrError =>
      enableDebugging
      checkType(tm, ty)

def checkTypeWithDebugging
  (tm: VTerm, ty: VTerm)
  (using Γ: Context)
  (using Σ: Signature)
  (using ctx: TypingContext)
  : VTerm =
  try checkType(tm, ty)
  catch
    case e: IrError =>
      enableDebugging
      checkType(tm, ty)

def inferTypeWithDebugging
  (tm: CTerm)
  (using Γ: Context)
  (using Σ: Signature)
  (using ctx: TypingContext)
  : (CTerm, CTerm) =
  try inferType(tm)
  catch
    case e: IrError =>
      enableDebugging
      inferType(tm)

def inferTypeWithDebugging
  (tm: VTerm)
  (using Γ: Context)
  (using Σ: Signature)
  (using ctx: TypingContext)
  : (VTerm, VTerm) =
  try inferType(tm)
  catch
    case e: IrError =>
      enableDebugging
      inferType(tm)

inline def enableDebugging(using ctx: TypingContext): Unit =
  val stacktrace = Thread.currentThread().nn.getStackTrace.nn
  println(s"Debugging ${stacktrace(2)}")
  ctx.enableDebugging = true
