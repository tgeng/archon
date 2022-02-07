package io.github.tgeng.archon.bir

import io.github.tgeng.archon.common.*

case class Substitutor()

trait Raisable[T]:
  def raise(t: T, bar: Int, amount: Int): T

trait Substitutable[S: Raisable]:
  def substitute[T](s: S, substitutor: Substitutor[T]): S
