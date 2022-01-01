package io.github.tgeng.archon.tt.substitution

import io.github.tgeng.archon.common.*

enum LocalVariableReference:
  case DeBrujin(index: Int, nameHint: Name)
  case Named(name: Name)

trait LocalVariable[R <: LocalVariableReference]:
  def ref: R

trait Raisable[T]:
  def raise(t: T, bar: Int, amount: Int): T

trait Substitutable[S] extends Raisable[S]:
  def substitute[T](s: S, substitutor: Substitutor[T]): S

object Substitutable:
  def foo = ???

case class Substitutor[T]()