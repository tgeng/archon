package com.github.tgeng.archon.core.ir

import com.github.tgeng.archon.common.Nat
import com.github.tgeng.archon.core.ir.IrError.*

import scala.annotation.targetName

/** First element is the outermost binding, e.g. [x: Nat, y: Vector String x] is represented as `x:
  * Nat :: y: Vector String x :: []`
  */
type Telescope = List[Binding[VTerm]]
type TTelescope = List[(Binding[VTerm], Variance)]

/** First element is the outermost binding.
  */
type Context = collection.IndexedSeq[Binding[VTerm]]

extension (ctx: collection.IndexedSeq[Binding[VTerm]])
  def resolve(ref: VTerm.Var)(using Signature): Binding[VTerm] = resolve(ref.idx)

  def resolve(idx: Nat)(using Signature): Binding[VTerm] =
    val offset = idx + 1
    if idx < 0 || idx >= ctx.size then
      throw InternalIrError(s"Bad index $idx for context ${pprint(ctx).plainText}")(using ctx)
    ctx(ctx.size - offset).map(RaisableVTerm.raise(_, offset))

  def split(ref: VTerm.Var): (Context, Binding[VTerm], Telescope) =
    val index = ctx.size - (ref.idx + 1)
    (ctx.take(index), ctx(index), ctx.drop(index + 1).toList)

  def toTelescope = ctx.toList

type TContext = collection.IndexedSeq[(Binding[VTerm], Variance)]

/** Null escape status means it's not declared and hence type checking can derive it instead.
  */
type EContext = collection.IndexedSeq[(Binding[VTerm], EscapeStatus | Null)]

extension (ctx: collection.IndexedSeq[(Binding[VTerm], Variance)])
  @targetName("resolveT")
  def resolve(ref: VTerm.Var)(using Signature): (Binding[VTerm], Variance) = resolve(ref.idx)

  @targetName("resolveT")
  def resolve(idx: Nat)(using Signature): (Binding[VTerm], Variance) =
    val offset = idx + 1
    val (b, v) = ctx(ctx.size - offset)
    (b.map(RaisableVTerm.raise(_, offset)), v)

object Context:
  def fromTelescope(telescope: Telescope) = telescope.toIndexedSeq
  def empty = IndexedSeq.empty
