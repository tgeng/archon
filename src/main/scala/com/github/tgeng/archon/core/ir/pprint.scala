package com.github.tgeng.archon.core.ir

import collection.mutable
import com.github.tgeng.archon.common.*
import com.github.tgeng.archon.core.common.*

private class NameBinding(
  var nameRef: Ref[Name],
  var refCount: Nat = 0,
)

object Renamer extends Visitor[IndexedSeq[Nat], Unit]:
  override def combine(rs: Unit*)(using ctx: IndexedSeq[Nat])(using Σ: Signature) = ()

object TermPrettyPrinter extends Visitor[IndexedSeq[Name], Block] :
  override def combine(blocks: Block*)(using ctx: IndexedSeq[Name])(using Σ: Signature) =
    Block(blocks: _*)

extension[T] (v: mutable.IndexedSeq[T])
  private def apply(ref: VTerm.Var): T =
    val offset = ref.index + 1
    v(v.length - offset)

  private def update(ref: VTerm.Var, t: T) =
    val offset = ref.index + 1
    v(v.length - offset) = t

