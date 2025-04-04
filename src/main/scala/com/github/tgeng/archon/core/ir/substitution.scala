package com.github.tgeng.archon.core.ir

import com.github.tgeng.archon.common.*
import com.github.tgeng.archon.core.common.*

type PartialSubstitution[T] = Int => Option[T]

trait Raisable[T]:
  def raise(t: T, amount: Int, bar: Int = 0)(using Σ: Signature)(using TypingContext): T

trait Substitutable[S: Raisable, T]:
  def substitute
    (s: S, substitution: PartialSubstitution[T], offset: Int = 0)
    (using Σ: Signature)
    (using TypingContext)
    : S

import com.github.tgeng.archon.core.ir.CTerm.*
import com.github.tgeng.archon.core.ir.Pattern.*
import com.github.tgeng.archon.core.ir.VTerm.*

case class StrengthenException(v: Var | PVar, amount: Int) extends Exception

private object RaiseTransformer extends Transformer[( /* amount */ Int, /* bar */ Int)]:
  override def withBoundNames[T]
    (bindingNames: => Seq[Ref[Name]])
    (action: ((Int, Int)) ?=> T)
    (using ctx: (Int, Int))
    (using Σ: Signature)
    (using TypingContext)
    : T =
    action(using (ctx._1, ctx._2 + bindingNames.size))

  override def transformVar
    (v: Var)
    (using ctx: (Int, Int))
    (using Σ: Signature)
    (using TypingContext)
    : VTerm =
    if v.idx >= ctx._2 then
      val newIndex = v.idx + ctx._1
      if newIndex < 0 then throw StrengthenException(v, ctx._1)
      Var(newIndex)(using v.sourceInfo)
    else v

  override def transformPVar
    (v: PVar)
    (using ctx: (Int, Int))
    (using Σ: Signature)
    (using TypingContext)
    : Pattern =
    if v.idx >= ctx._2 then
      val newIndex = v.idx + ctx._1
      if newIndex < 0 then throw StrengthenException(v, ctx._1)
      PVar(newIndex)(using v.sourceInfo)
    else v

end RaiseTransformer

given RaisablePattern: Raisable[Pattern] with
  override def raise
    (v: Pattern, amount: Int, bar: Int)
    (using Σ: Signature)
    (using TypingContext)
    : Pattern =
    RaiseTransformer.transformPattern(v)(using (amount, bar))

given RaisableCoPattern: Raisable[CoPattern] with
  override def raise
    (v: CoPattern, amount: Int, bar: Int)
    (using Σ: Signature)
    (using TypingContext)
    : CoPattern =
    RaiseTransformer.transformCoPattern(v)(using (amount, bar))

given RaisableVTerm: Raisable[VTerm] with
  override def raise
    (v: VTerm, amount: Int, bar: Int)
    (using Σ: Signature)
    (using TypingContext)
    : VTerm =
    RaiseTransformer.transformVTerm(v)(using (amount, bar))

given RaisableCTerm: Raisable[CTerm] with
  override def raise
    (c: CTerm, amount: Int, bar: Int)
    (using Σ: Signature)
    (using TypingContext)
    : CTerm =
    RaiseTransformer.transformCTerm(c)(using (amount, bar))

given RaisableTelescope: Raisable[Telescope] with
  override def raise
    (telescope: Telescope, amount: Int, bar: Int)
    (using Σ: Signature)
    (using TypingContext)
    : Telescope =
    telescope match
      case Nil => Nil
      case binding :: telescope =>
        binding.map(RaisableVTerm.raise(_, amount, bar)) :: raise(
          telescope,
          amount,
          bar + 1,
        )

private object PatternSubstituteTransformer
  extends Transformer[(PartialSubstitution[Pattern], /* offset */ Int)]:
  override def withBoundNames[T]
    (bindingNames: => Seq[Ref[Name]])
    (action: ((PartialSubstitution[Pattern], Int)) ?=> T)
    (using ctx: (PartialSubstitution[Pattern], Int))
    (using Σ: Signature)
    (using TypingContext)
    : T =
    action(using (ctx._1, ctx._2 + bindingNames.size))

  override def transformVar
    (v: Var)
    (using ctx: (PartialSubstitution[Pattern], /* offset */ Int))
    (using Σ: Signature)
    (using TypingContext)
    : VTerm =
    ctx._1(v.idx - ctx._2) match
      case Some(t) =>
        RaisableVTerm.raise(
          t.toTerm.getOrElse(
            throw IllegalArgumentException(
              "substitutor using patterns should not contain PAbsurd",
            ),
          ),
          ctx._2,
        )
      case _ => v

  override def transformPVar
    (v: PVar)
    (using ctx: (PartialSubstitution[Pattern], /* offset */ Int))
    (using Σ: Signature)
    (using TypingContext)
    : Pattern =
    ctx._1(v.idx - ctx._2) match
      case Some(t) => RaisablePattern.raise(t, ctx._2)
      case _       => v

end PatternSubstituteTransformer

given SubstitutablePattern: Substitutable[Pattern, Pattern] with
  override def substitute
    (
      p: Pattern,
      substitution: PartialSubstitution[Pattern],
      offset: Int,
    )
    (using Σ: Signature)
    (using TypingContext)
    : Pattern =
    PatternSubstituteTransformer.transformPattern(p)(using (substitution, offset))

given SubstitutableCoPattern: Substitutable[CoPattern, Pattern] with
  override def substitute
    (
      p: CoPattern,
      substitution: PartialSubstitution[Pattern],
      offset: Int,
    )
    (using Σ: Signature)
    (using TypingContext)
    : CoPattern =
    PatternSubstituteTransformer.transformCoPattern(p)(using (substitution, offset))

private object VTermSubstituteTransformer
  extends Transformer[(PartialSubstitution[VTerm], /* offset */ Int)]:
  override def withBoundNames[T]
    (bindingNames: => Seq[Ref[Name]])
    (action: ((PartialSubstitution[VTerm], Int)) ?=> T)
    (using ctx: (PartialSubstitution[VTerm], Int))
    (using Σ: Signature)
    (using TypingContext)
    : T =
    action(using (ctx._1, ctx._2 + bindingNames.size))

  override def transformVar
    (v: Var)
    (using ctx: (PartialSubstitution[VTerm], /* offset */ Int))
    (using Σ: Signature)
    (using TypingContext)
    : VTerm =
    ctx._1(v.idx - ctx._2) match
      case Some(t) => RaisableVTerm.raise(t, ctx._2)
      case _       => v

  override def transformPVar
    (v: PVar)
    (using ctx: (PartialSubstitution[VTerm], /* offset */ Int))
    (using Σ: Signature)
    (using TypingContext)
    : Pattern =
    ctx._1(v.idx - ctx._2) match
      case Some(t) => PForced(RaisableVTerm.raise(t, ctx._2))
      case _       => v

end VTermSubstituteTransformer

given SubstitutableVTerm: Substitutable[VTerm, VTerm] with
  override def substitute
    (
      v: VTerm,
      substitution: PartialSubstitution[VTerm],
      offset: Int,
    )
    (using Σ: Signature)
    (using TypingContext)
    : VTerm =
    VTermSubstituteTransformer.transformVTerm(v)(using (substitution, offset))

given SubstitutableCTerm: Substitutable[CTerm, VTerm] with
  override def substitute
    (
      c: CTerm,
      substitution: PartialSubstitution[VTerm],
      offset: Int,
    )
    (using Σ: Signature)
    (using TypingContext)
    : CTerm =
    VTermSubstituteTransformer.transformCTerm(c)(using (substitution, offset))

given SubstitutableTelescope: Substitutable[Telescope, VTerm] with
  override def substitute
    (
      telescope: Telescope,
      substitution: PartialSubstitution[VTerm],
      offset: Int,
    )
    (using Σ: Signature)
    (using TypingContext)
    : Telescope = telescope match
    case Nil => Nil
    case binding :: telescope =>
      binding.map(
        SubstitutableVTerm.substitute(_, substitution, offset),
      ) :: substitute(
        telescope,
        substitution,
        offset + 1,
      )

extension (c: CTerm)
  def subst
    (substitution: PartialSubstitution[VTerm])
    (using Σ: Signature)
    (using TypingContext)
    : CTerm =
    SubstitutableCTerm.substitute(c, substitution)
  def weakened(using Σ: Signature)(using TypingContext): CTerm = c.weaken(1, 0)
  def weaken(amount: Nat, at: Nat)(using Σ: Signature)(using TypingContext): CTerm =
    RaisableCTerm.raise(c, amount, at)
  def strengthened(using Σ: Signature)(using TypingContext): CTerm = c.strengthen(1, 0)
  def strengthen(amount: Nat, at: Nat)(using Σ: Signature)(using TypingContext): CTerm =
    RaisableCTerm.raise(c, -amount, at)

  /** Substitutes lower DeBruijn indices with the given terms. The first term substitutes the
    * highest index with the last substitutes 0. Then the result is raised so that the substituted
    * indices are taken by other (deeper) indices.
    */
  def substLowers(vTerms: VTerm*)(using Σ: Signature)(using TypingContext): CTerm =
    val count = vTerms.length
    c
      // for example, consider substitution happened when applying (4, 5) to the body of function \a,
      // b => a + b. In DeBruijn index the lambda body is `$1 + $0` and `vTerms` is `[4, 5]`. The
      // first argument `4` at index `0` should replace `$1`.
      .subst(i => vTerms.lift(count - 1 - i).map(_.weaken(count, 0)))
      // strengthen the resulted term so that even higher indices are correct.
      .strengthen(count, 0)

extension (b: Binding[VTerm])
  def subst
    (substitution: PartialSubstitution[VTerm])
    (using Σ: Signature)
    (using TypingContext)
    : Binding[VTerm] =
    b.map(_.subst(substitution))
  def weaken(amount: Nat, at: Nat)(using Σ: Signature)(using TypingContext): Binding[VTerm] =
    b.map(_.weaken(amount, at))
  def weakened(using Σ: Signature)(using TypingContext): Binding[VTerm] = b.map(_.weakened)
  def strengthened(using Σ: Signature)(using TypingContext): Binding[VTerm] = b.map(_.strengthened)
  def strengthen(amount: Nat, at: Nat)(using Σ: Signature)(using TypingContext): Binding[VTerm] =
    b.map(_.strengthen(amount, at))

  /** Substitutes lower DeBruijn indices with the given terms. The first term substitutes the
    * highest index with the last substitutes 0. Then the result is raised so that the substituted
    * indices are taken by other (deeper) indices.
    */
  def substLowers(vTerms: VTerm*)(using Σ: Signature)(using TypingContext): Binding[VTerm] =
    b.map(_.substLowers(vTerms*))

extension (v: VTerm)
  def subst
    (substitution: PartialSubstitution[VTerm])
    (using Σ: Signature)
    (using TypingContext)
    : VTerm =
    SubstitutableVTerm.substitute(v, substitution)
  def weaken(amount: Nat, at: Nat)(using Σ: Signature)(using TypingContext): VTerm =
    RaisableVTerm.raise(v, amount, at)
  def weakened(using Σ: Signature)(using TypingContext): VTerm = v.weaken(1, 0)
  def strengthened(using Σ: Signature)(using TypingContext): VTerm = v.strengthen(1, 0)
  def strengthen(amount: Nat, at: Nat)(using Σ: Signature)(using TypingContext): VTerm =
    RaisableVTerm.raise(v, -amount, at)

  /** Substitutes lower DeBruijn indices with the given terms. The first term substitutes the
    * highest index with the last substitutes 0. Then the result is raised so that the substituted
    * indices are taken by other (deeper) indices.
    */
  def substLowers(vTerms: VTerm*)(using Σ: Signature)(using TypingContext): VTerm =
    val count = vTerms.length
    v
      // for example, consider substitution happened when applying (4, 5) to the body of function \a,
      // b => a + b. In DeBruijn index the lambda body is `$1 + $0` and `vTerms` is `[4, 5]`. The
      // first argument `4` at index `0` should replace `$1`.
      .subst(i => vTerms.lift(count - 1 - i).map(_.weaken(count, 0)))
      // strengthen the resulted term so that even higher indices are correct.
      .strengthen(count, 0)

extension (e: Elimination[VTerm])
  def subst
    (substitution: PartialSubstitution[VTerm])
    (using Σ: Signature)
    (using TypingContext)
    : Elimination[VTerm] =
    e.map(v => SubstitutableVTerm.substitute(v, substitution))
  def weaken(amount: Nat, at: Nat)(using Σ: Signature)(using TypingContext): Elimination[VTerm] =
    e.map(v => RaisableVTerm.raise(v, amount, at))
  def weakened(using Σ: Signature)(using TypingContext): Elimination[VTerm] = e.weaken(1, 0)
  def strengthened(using Σ: Signature)(using TypingContext): Elimination[VTerm] = e.strengthen(1, 0)
  def strengthen
    (amount: Nat, at: Nat)
    (using Σ: Signature)
    (using TypingContext)
    : Elimination[VTerm] =
    e.map(v => RaisableVTerm.raise(v, -amount, at))

  /** Substitutes lower DeBruijn indices with the given terms. The first term substitutes the
    * highest index with the last substitutes 0. Then the result is raised so that the substituted
    * indices are taken by other (deeper) indices.
    */
  def substLowers(vTerms: VTerm*)(using Σ: Signature)(using TypingContext): Elimination[VTerm] =
    val count = vTerms.length
    e
      // for example, consider substitution happened when applying (4, 5) to the body of function \a,
      // b => a + b. In DeBruijn index the lambda body is `$1 + $0` and `vTerms` is `[4, 5]`. The
      // first argument `4` at index `0` should replace `$1`.
      .subst(i => vTerms.lift(count - 1 - i).map(_.weaken(count, 0)))
      // strengthen the resulted term so that even higher indices are correct.
      .strengthen(count, 0)

extension (v: Pattern)
  def subst
    (substitution: PartialSubstitution[Pattern])
    (using Σ: Signature)
    (using TypingContext)
    : Pattern =
    SubstitutablePattern.substitute(v, substitution)
  def weaken(amount: Nat, at: Nat)(using Σ: Signature)(using TypingContext): Pattern =
    RaisablePattern.raise(v, amount, at)
  def weakened(using Σ: Signature)(using TypingContext): Pattern = v.weaken(1, 0)
  def strengthened(using Σ: Signature)(using TypingContext): Pattern = v.strengthen(1, 0)
  def strengthen(amount: Nat, at: Nat)(using Σ: Signature)(using TypingContext): Pattern =
    RaisablePattern.raise(v, -amount, at)

  /** Substitutes lower DeBruijn indices with the given terms. The first term substitutes the
    * highest index with the last substitutes 0. Then the result is raised so that the substituted
    * indices are taken by other (deeper) indices.
    */
  def substLowers(vTerms: Pattern*)(using Σ: Signature)(using TypingContext): Pattern =
    val count = vTerms.length
    v
      // for example, consider substitution happened when applying (4, 5) to the body of function \a,
      // b => a + b. In DeBruijn index the lambda body is `$1 + $0` and `vTerms` is `[4, 5]`. The
      // first argument `4` at index `0` should replace `$1`.
      .subst(i => vTerms.lift(count - 1 - i).map(_.weaken(count, 0)))
      // strengthen the resulted term so that even higher indices are correct.
      .strengthen(count, 0)

extension (v: CoPattern)
  def subst
    (substitution: PartialSubstitution[Pattern])
    (using Σ: Signature)
    (using TypingContext)
    : CoPattern =
    SubstitutableCoPattern.substitute(v, substitution)
  def substTerm
    (substitution: PartialSubstitution[VTerm])
    (using Σ: Signature)
    (using TypingContext)
    : CoPattern =
    VTermSubstituteTransformer.transformCoPattern(v)(using (substitution, 0))
  def weaken(amount: Nat, at: Nat)(using Σ: Signature)(using TypingContext): CoPattern =
    RaisableCoPattern.raise(v, amount, at)
  def weakened(using Σ: Signature)(using TypingContext): CoPattern = v.weaken(1, 0)
  def strengthened(using Σ: Signature)(using TypingContext): CoPattern = v.strengthen(1, 0)
  def strengthen(amount: Nat, at: Nat)(using Σ: Signature)(using TypingContext): CoPattern =
    RaisableCoPattern.raise(v, -amount, at)

  /** Substitutes lower DeBruijn indices with the given terms. The first term substitutes the
    * highest index with the last substitutes 0. Then the result is raised so that the substituted
    * indices are taken by other (deeper) indices.
    */
  def substLowers(vTerms: Pattern*)(using Σ: Signature)(using TypingContext): CoPattern =
    val count = vTerms.length
    v
      // for example, consider substitution happened when applying (4, 5) to the body of function \a,
      // b => a + b. In DeBruijn index the lambda body is `$1 + $0` and `vTerms` is `[4, 5]`. The
      // first argument `4` at index `0` should replace `$1`.
      .subst(i => vTerms.lift(count - 1 - i).map(_.weaken(count, 0)))
      // strengthen the resulted term so that even higher indices are correct.
      .strengthen(count, 0)

extension (telescope: Telescope)
  def subst
    (substitution: PartialSubstitution[VTerm])
    (using Σ: Signature)
    (using TypingContext)
    : Telescope =
    SubstitutableTelescope.substitute(telescope, substitution)
  def weaken(amount: Nat, at: Nat)(using Σ: Signature)(using TypingContext): Telescope =
    RaisableTelescope.raise(telescope, amount, at)
  def weakened(using Σ: Signature)(using TypingContext): Telescope = telescope.weaken(1, 0)
  def strengthened(using Σ: Signature)(using TypingContext): Telescope = telescope.strengthen(1, 0)
  def strengthen(amount: Nat, at: Nat)(using Σ: Signature)(using TypingContext): Telescope =
    RaisableTelescope.raise(
      telescope,
      -amount,
      at,
    )

  /** Substitutes lower DeBruijn indices with the given terms. The first term substitutes the
    * highest index with the last substitutes 0. Then the result is raised so that the substituted
    * indices are taken by other (deeper) indices.
    */
  def substLowers(vTerms: VTerm*)(using Σ: Signature)(using TypingContext): Telescope =
    val count = vTerms.length
    telescope
      // for example, consider substitution happened when applying (4, 5) to the body of function \a,
      // b => a + b. In DeBruijn index the lambda body is `$1 + $0` and `vTerms` is `[4, 5]`. The
      // first argument `4` at index `0` should replace `$1`.
      .subst(i => vTerms.lift(count - 1 - i).map(_.weaken(count, 0)))
      // strengthen the resulted term so that even higher indices are correct.
      .strengthen(count, 0)

extension (ct: CaseTree)
  def subst
    (substitution: PartialSubstitution[VTerm])
    (using Σ: Signature)
    (using TypingContext)
    : CaseTree =
    VTermSubstituteTransformer.transformCaseTree(ct)(using (substitution, 0))
