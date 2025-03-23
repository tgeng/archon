package com.github.tgeng.archon.core.ir

import com.github.tgeng.archon.common.*
import com.github.tgeng.archon.core.common.*
import com.github.tgeng.archon.core.ir.VTerm.*

trait FreeVarsVisitorTrait extends Visitor[Nat, Seq[Var]]:
  override def withBoundNames
    (bindingNames: => Seq[Ref[Name]])
    (action: Nat ?=> Seq[VTerm.Var])
    (using bar: Nat)
    (using Σ: Signature)
    (using TypingContext)
    : Seq[Var] =
    action(using bar + bindingNames.size)

  override def combine
    (rs: Seq[Var]*)
    (using ctx: Nat)
    (using Σ: Signature)
    (using TypingContext)
    : Seq[Var] = rs.flatten

  override def visitVar(v: Var)(using bar: Nat)(using Σ: Signature)(using TypingContext): Seq[Var] =
    if v.idx < bar then Nil else Seq(v.strengthen(bar, 0).asInstanceOf[Var])

object FreeVarsVisitor extends FreeVarsVisitorTrait
