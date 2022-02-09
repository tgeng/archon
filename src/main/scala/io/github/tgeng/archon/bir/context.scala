package io.github.tgeng.archon.bir

/**
 * Head is on the left, e.g. [x: Nat, y: Vector String x] is represented as `x: Nat :: y: Vector String x :: []`
 */
type Telescope = List[Binding[VTerm]]

/**
 * Head is the last element. Hence, resolving DeBruijn index is done from the end.
 */
type Context = Vector[Binding[VTerm]]

extension [T] (v: Vector[T])
  def apply(ref: VTerm.LocalRef) : T = v(v.length - ref.idx - 1)
