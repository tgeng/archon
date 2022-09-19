package com.github.tgeng.archon.core.ir

import scala.collection.mutable
import com.github.tgeng.archon.common.*
import com.github.tgeng.archon.core.common.*
import com.github.tgeng.archon.core.ir.VTerm.Type

import scala.collection.immutable.{Map, Set}

type PartialSubstitution[T] = Int => Option[T]

trait Raisable[T]:
  def raise(t: T, amount: Int, bar: Int = 0)(using Σ: Signature): T

trait Substitutable[S: Raisable, T]:
  def substitute(s: S, substitution: PartialSubstitution[T], offset: Int = 0)(
    using Σ: Signature
  ): S

import VTerm.*
import CTerm.*

private object RaiseTransformer
  extends Transformer[( /* amount */ Int, /* bar */ Int)]:
  override def withBindings[T](bindingNames: => Seq[Ref[Name]])(
    action: ((Int, Int)) ?=> T
  )(using ctx: (Int, Int))(using Σ: Signature): T =
    action(using (ctx._1, ctx._2 + bindingNames.size))

  override def transformVar(v: Var)(using ctx: (Int, Int))(using Σ: Signature) =
    if v.idx >= ctx._2 then Var(v.idx + ctx._1)(using v.sourceInfo) else v

end RaiseTransformer

given RaisableVTerm: Raisable[VTerm] with
  override def raise(v: VTerm, amount: Int, bar: Int)(using
    Σ: Signature
  ): VTerm =
    RaiseTransformer.transformVTerm(v)(using (amount, bar))

given RaisableCTerm: Raisable[CTerm] with
  override def raise(c: CTerm, amount: Int, bar: Int)(using
    Σ: Signature
  ): CTerm =
    RaiseTransformer.transformCTerm(c)(using (amount, bar))

given RaisableTelescope: Raisable[Telescope] with
  override def raise(telescope: Telescope, amount: Int, bar: Int)(using
    Σ: Signature
  ): Telescope = telescope match
    case Nil => Nil
    case binding :: telescope =>
      binding.map(RaisableVTerm.raise(_, amount, bar)) :: raise(
        telescope,
        amount,
        bar + 1
      )

private object SubstituteTransformer
  extends Transformer[(PartialSubstitution[VTerm], /* offset */ Int)]:
  override def withBindings[T](bindingNames: => Seq[Ref[Name]])(
    action: ((PartialSubstitution[VTerm], Int)) ?=> T
  )(using ctx: (PartialSubstitution[VTerm], Int))(using Σ: Signature): T =
    action(using (ctx._1, ctx._2 + bindingNames.size))

  override def transformVar(v: Var)(using
    ctx: (PartialSubstitution[VTerm], /* offset */ Int)
  )(using Σ: Signature) =
    ctx._1(v.idx - ctx._2) match
      case Some(t) => RaisableVTerm.raise(t, ctx._2)
      case _       => v

end SubstituteTransformer

given SubstitutableVTerm: Substitutable[VTerm, VTerm] with
  override def substitute(
    v: VTerm,
    substitution: PartialSubstitution[VTerm],
    offset: Int
  )(using Σ: Signature): VTerm =
    SubstituteTransformer.transformVTerm(v)(using (substitution, offset))

given SubstitutableCTerm: Substitutable[CTerm, VTerm] with
  override def substitute(
    c: CTerm,
    substitution: PartialSubstitution[VTerm],
    offset: Int
  )(using Σ: Signature): CTerm =
    SubstituteTransformer.transformCTerm(c)(using (substitution, offset))

given SubstitutableTelescope: Substitutable[Telescope, VTerm] with
  override def substitute(
    telescope: Telescope,
    substitution: PartialSubstitution[VTerm],
    offset: Int
  )(using Σ: Signature): Telescope = telescope match
    case Nil => Nil
    case binding :: telescope =>
      binding.map(
        SubstitutableVTerm.substitute(_, substitution, offset)
      ) :: substitute(
        telescope,
        substitution,
        offset + 1
      )

extension (c: CTerm)
  def subst(substitution: PartialSubstitution[VTerm])(using Σ: Signature) =
    SubstitutableCTerm.substitute(c, substitution)
  def weakened(using Σ: Signature) = c.weaken(1, 0)
  def weaken(amount: Nat, at: Nat)(using Σ: Signature) =
    RaisableCTerm.raise(c, amount, at)
  def strengthened(using Σ: Signature) = c.strengthen(1, 0)
  def strengthen(amount: Nat, at: Nat)(using Σ: Signature) =
    RaisableCTerm.raise(c, -amount, at)

  /** Substitutes lower DeBruijn indices with the given terms. The first term
    * substitutes the highest index with the last substitutes 0. Then the result
    * is raised so that the substituted indices are taken by other (deeper)
    * indices.
    */
  def substLowers(vTerms: VTerm*)(using Σ: Signature) =
    val count = vTerms.length
    c
      // for example, consider substitution happened when applying (4, 5) to the body of function \a,
      // b => a + b. In DeBruijn index the lambda body is `$1 + $0` and `vTerms` is `[4, 5]`. The
      // first argument `4` at index `0` should replace `$1`.
      .subst(i => vTerms.lift(count - 1 - i).map(_.weaken(count, 0)))
      // strengthen the resulted term so that even higher indices are correct.
      .strengthen(count, 0)

extension (v: VTerm)
  def subst(substitution: PartialSubstitution[VTerm])(using Σ: Signature) =
    SubstitutableVTerm.substitute(v, substitution)
  def weaken(amount: Nat, at: Nat)(using Σ: Signature) =
    RaisableVTerm.raise(v, amount, at)
  def weakened(using Σ: Signature) = v.weaken(1, 0)
  def strengthened(using Σ: Signature) = v.strengthen(1, 0)
  def strengthen(amount: Nat, at: Nat)(using Σ: Signature) =
    RaisableVTerm.raise(v, -amount, at)

  /** Substitutes lower DeBruijn indices with the given terms. The first term
    * substitutes the highest index with the last substitutes 0. Then the result
    * is raised so that the substituted indices are taken by other (deeper)
    * indices.
    */
  def substLowers(vTerms: VTerm*)(using Σ: Signature) =
    val count = vTerms.length
    v
      // for example, consider substitution happened when applying (4, 5) to the body of function \a,
      // b => a + b. In DeBruijn index the lambda body is `$1 + $0` and `vTerms` is `[4, 5]`. The
      // first argument `4` at index `0` should replace `$1`.
      .subst(i => vTerms.lift(count - 1 - i).map(_.weaken(count, 0)))
      // strengthen the resulted term so that even higher indices are correct.
      .strengthen(count, 0)

extension (ul: ULevel)
  def subst(substitution: PartialSubstitution[VTerm])(using Σ: Signature) =
    ul.map(
      SubstitutableVTerm.substitute(_, substitution)
    )
  def weaken(amount: Nat, at: Nat)(using Σ: Signature) =
    ul.map(RaisableVTerm.raise(_, amount, at))
  def weakened(using Σ: Signature) = ul.weaken(1, 0)
  def strengthened(using Σ: Signature) = ul.strengthen(1, 0)
  def strengthen(amount: Nat, at: Nat)(using Σ: Signature) = ul.map(
    RaisableVTerm.raise(
      _,
      -amount,
      at
    )
  )

  /** Substitutes lower DeBruijn indices with the given terms. The first term
    * substitutes the highest index with the last substitutes 0. Then the result
    * is raised so that the substituted indices are taken by other (deeper)
    * indices.
    */
  def substLowers(vTerms: VTerm*)(using Σ: Signature) =
    val count = vTerms.length
    ul
      // for example, consider substitution happened when applying (4, 5) to the body of function \a,
      // b => a + b. In DeBruijn index the lambda body is `$1 + $0` and `vTerms` is `[4, 5]`. The
      // first argument `4` at index `0` should replace `$1`.
      .subst(i => vTerms.lift(count - 1 - i).map(_.weaken(count, 0)))
      // strengthen the resulted term so that even higher indices are correct.
      .strengthen(count, 0)

extension (telescope: Telescope)
  def subst(substitution: PartialSubstitution[VTerm])(using Σ: Signature) =
    SubstitutableTelescope.substitute(telescope, substitution)
  def weaken(amount: Nat, at: Nat)(using Σ: Signature) =
    RaisableTelescope.raise(
      telescope,
      amount,
      at
    )
  def weakened(using Σ: Signature) = telescope.weaken(1, 0)
  def strengthened(using Σ: Signature) = telescope.strengthen(1, 0)
  def strengthen(amount: Nat, at: Nat)(using Σ: Signature) =
    RaisableTelescope.raise(
      telescope,
      -amount,
      at
    )

  /** Substitutes lower DeBruijn indices with the given terms. The first term
    * substitutes the highest index with the last substitutes 0. Then the result
    * is raised so that the substituted indices are taken by other (deeper)
    * indices.
    */
  def substLowers(vTerms: VTerm*)(using Σ: Signature) =
    val count = vTerms.length
    telescope
      // for example, consider substitution happened when applying (4, 5) to the body of function \a,
      // b => a + b. In DeBruijn index the lambda body is `$1 + $0` and `vTerms` is `[4, 5]`. The
      // first argument `4` at index `0` should replace `$1`.
      .subst(i => vTerms.lift(count - 1 - i).map(_.weaken(count, 0)))
      // strengthen the resulted term so that even higher indices are correct.
      .strengthen(count, 0)
