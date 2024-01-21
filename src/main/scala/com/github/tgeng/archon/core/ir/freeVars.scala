package com.github.tgeng.archon.core.ir

import com.github.tgeng.archon.common.*
import com.github.tgeng.archon.core.common.*
import com.github.tgeng.archon.core.ir.VTerm.*

trait FreeVarsVisitorTrait extends Visitor[Nat, Seq[Var]]:

  override def withBindings
    (bindingNames: => List[Name])
    (action: Nat ?=> Seq[Var])
    (using bar: Nat)
    (using Σ: Signature)
    : Seq[Var] =
    action(using bar + bindingNames.size)

  override def combine(rs: Seq[Var]*)(using ctx: Nat)(using Σ: Signature): Seq[Var] = rs.flatten

  override def visitVar(v: Var)(using bar: Nat)(using Σ: Signature): Seq[Var] =
    if v.idx < bar then Nil else Seq(v.strengthen(bar, 0).asInstanceOf[Var])

object FreeVarsVisitor extends FreeVarsVisitorTrait
