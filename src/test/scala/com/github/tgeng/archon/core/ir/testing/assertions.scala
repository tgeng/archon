package com.github.tgeng.archon.core.ir.testing

import com.github.tgeng.archon.core.ir.*
import org.scalatest.Assertions.*

def assertType
  (t: VTerm, ty: VTerm)
  (using Γ: Context)
  (using Σ: Signature)
  (using ctx: TypingContext)
  : Unit = {
  try {
    checkType(t, ty)
  } catch {
    case e: IrError => {
      enableDebugging
      checkType(t, ty)
    }
  }
}

def assertNotType
  (t: VTerm, ty: VTerm)
  (using Γ: Context)
  (using Σ: Signature)
  (using ctx: TypingContext)
  : Unit = {
  try {
    checkType(t, ty)
    enableDebugging
    checkType(t, ty)
    fail(s"Expected type mismatch.")
  } catch {
    case _: IrError => ()
  }
}

def enableDebugging(using ctx: TypingContext): Unit = {
  ctx.enableDebugging = true
}
