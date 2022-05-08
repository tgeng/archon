package io.github.tgeng.archon.core.ir

/**
 * Head is on the left, e.g. [x: Nat, y: Vector String x] is represented as `x: Nat :: y: Vector String x :: []`
 */
type Telescope = List[Binding[VTerm]]

/**
 * Head is the last element. Hence, resolving DeBruijn index is done from the end.
 */
type Context = collection.IndexedSeq[Binding[VTerm]]

extension (v: collection.IndexedSeq[Binding[VTerm]])
  def apply(ref: VTerm.Var)(using Signature) : Binding[VTerm] =
    val offset = ref.index + 1
    v(v.length - offset).map(RaisableVTerm.raise(_, offset))
