package com.github.tgeng.archon.core.ir

import com.github.tgeng.archon.common.*
import com.github.tgeng.archon.common.IndentPolicy.*
import com.github.tgeng.archon.common.WrapPolicy.*
import com.github.tgeng.archon.core.ir.PrettyPrinter.pprint
import com.github.tgeng.archon.core.ir.VTerm.*

/** Checks if a term is total through types and some heuristics.
  *
  * Precondition: `tm` has been type checked and has type `ty`
  * @param tm
  *   the term to check
  * @param ty
  *   the type of the term. If `None`, the term is assumed to be a type and is total. If the type is
  *   present it must be normalized.
  * @return
  */
def isTotal
  (tm: CTerm, ty: Option[CTerm])
  (using Γ: Context)
  (using Σ: Signature)
  (using ctx: TypingContext)
  : Boolean =
  ctx.trace[Boolean](
    "isTotal",
    Block(ChopDown, Aligned, yellow(tm.sourceInfo), pprint(tm)),
    successMsg = r => r.toString,
  ):
    ty match
      case None => true
      case Some(ty) =>
        val effects = ty.asInstanceOf[IType].effects.normalized
        if effects == Total()(using SourceInfo.SiEmpty) then true
        // TODO: use heuristics to determine if a term is total
        else if effects == MaybeDiv()(using SourceInfo.SiEmpty) then true
        else false
