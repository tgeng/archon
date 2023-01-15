package com.github.tgeng.archon.core.ir

import com.github.tgeng.archon.common.Nat

/** Head is on the left, e.g. [x: Nat, y: Vector String x] is represented as `x: Nat :: y: Vector
  * String x :: []`
  */
type Telescope = List[Binding[VTerm]]

/** Head is the last element. Hence, resolving DeBruijn index is done from the end.
  */
type Context = collection.IndexedSeq[Binding[VTerm]]

extension(ctx: collection.IndexedSeq[Binding[VTerm]])
  def resolve(ref: VTerm.Var)(using Signature): Binding[VTerm] = resolve(ref.idx)

  def resolve(idx: Nat)(using Signature): Binding[VTerm] =
    val offset = idx + 1
    ctx(ctx.size - offset).map(RaisableVTerm.raise(_, offset))

  def split(ref: VTerm.Var): (Context, Binding[VTerm], Telescope) =
    val index = ctx.size - (ref.idx + 1)
    (ctx.take(index), ctx(index), ctx.drop(index + 1).toList)
