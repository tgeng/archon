package com.github.tgeng.archon.core.ir

import com.github.tgeng.archon.common.*

import scala.annotation.targetName

trait DeBruijn[T]:
  def fromIndex(index: Nat): T
  def weaken(t: T, amount: Nat, bar: Nat)(using Signature): T
  def subst(t: T, s: Substitutor[T])(using Signature): T

given DeBruijnVTerm: DeBruijn[VTerm] with
  override def fromIndex(index: Nat): VTerm = VTerm.Var(index)
  override def weaken(v: VTerm, amount: Nat, bar: Nat)(using Signature) = v.weaken(amount, bar)

  override def subst(v: VTerm, s: Substitutor[VTerm])(using Signature) = v.subst(s)

given DeBruijnPattern: DeBruijn[Pattern] with
  override def fromIndex(index: Nat): Pattern = Pattern.PVar(index)
  override def weaken(p: Pattern, amount: Nat, bar: Nat)(using Signature) = p.weaken(amount, bar)

  override def subst(p: Pattern, s: Substitutor[Pattern])(using Signature) = p.subst(s)

/** Local references are represented as DeBruijn indices so `var 0` points to the right most entry in the context. In
  * this setting, a "trivial" mapping should map `var (sourceContextSize - 1)` to the first var in target context
  * (DeBruijn index targetContextSize - 1). [[nonTrivialMapping]] contains the mapping of the last variables in the
  * target context. If target context is longer than source context, then [[nonTrivialMapping]] must account for this
  * gap. In addition, it may go beyond this gap to account for more mapping. To an extreme, [[nonTrivialMapping]] can
  * have size [[targetContextSize]], in which case all the mappings are explicitly specified.
  */
class Substitutor[T: DeBruijn]
  (
    val sourceContextSize: Nat,
    val targetContextSize: Nat,
    /** nonTrivialMapping[0] corresponds to Var(0) in target context. That is, for example, if sourceContextSize == 5,
      * targetContextSize == 7 and nonTrivialMapping = [a, b, c], then the fully spelled out substitutor is
      *
      * ```
      * indices: 6       5       4       3       2  1  0
      * terms:   Var(4)  Var(3)  Var(2)  Var(1)  c  b  a
      * ```
      *
      * where a, b, c are some terms living in source context.
      */
    private var nonTrivialMapping: IndexedSeq[T],
  )
  extends PartialSubstitution[T]:

  assert(sourceContextSize >= 0)
  assert(targetContextSize >= 0)

  private inline def fromIndex(index: Nat): T =
    summon[DeBruijn[T]].fromIndex(index)

  /** @param boundIndex
    *   up to how many DeBruijn indices in the target context that materialization should happen. Default value makes
    *   materialization happens fully
    */
  private def materialize(boundIndex: Nat = targetContextSize): Unit =
    if nonTrivialMapping.length == boundIndex then return
    nonTrivialMapping ++= (targetContextSize - nonTrivialMapping.length)
      .until(targetContextSize - boundIndex, -1)
      .map(i => fromIndex(sourceContextSize - i))

  override def apply(index: Nat): Option[T] =
    if index < targetContextSize && 0 <= index then
      if index < nonTrivialMapping.length then Some(nonTrivialMapping(index))
      else Some(fromIndex(index + sourceContextSize - targetContextSize))
    else None

  def map[R: DeBruijn](f: T => R): Substitutor[R] = Substitutor(
    sourceContextSize,
    targetContextSize,
    nonTrivialMapping.map(f),
  )

  @targetName("uplus")
  infix def ⊎(that: Substitutor[T])(using Signature): Substitutor[T] =
    that.materialize()
    Substitutor(
      sourceContextSize + that.sourceContextSize,
      targetContextSize + that.targetContextSize,
      that.nonTrivialMapping ++ nonTrivialMapping.map(
        summon[DeBruijn[T]].weaken(_, that.sourceContextSize, 0),
      ),
    )

  infix def remove(index: Nat): Substitutor[T] =
    materialize(index)
    if nonTrivialMapping.length == index then Substitutor(sourceContextSize, targetContextSize - 1, nonTrivialMapping)
    else
      Substitutor(
        sourceContextSize,
        targetContextSize - 1,
        nonTrivialMapping.patch(index, IndexedSeq.empty, 1),
      )

  infix def add(index: Nat, t: T) =
    materialize(index)
    Substitutor(
      sourceContextSize,
      targetContextSize - 1,
      nonTrivialMapping.patch(index, IndexedSeq(t), 0),
    )

  @targetName("compose")
  infix def ∘(that: Substitutor[T])(using Signature): Substitutor[T] =
    assert(this.sourceContextSize == that.targetContextSize)
    this.materialize()
    Substitutor(
      that.sourceContextSize,
      this.targetContextSize,
      this.nonTrivialMapping.map(summon[DeBruijn[T]].subst(_, that)),
    )

  def drop(count: Nat): Substitutor[T] = Substitutor(
    sourceContextSize,
    targetContextSize - count,
    nonTrivialMapping.drop(count),
  )

object Substitutor:
  def id[T: DeBruijn](size: Nat): Substitutor[T] = Substitutor(size, size, IndexedSeq())

  def of[T: DeBruijn](sourceContextSize: Nat, terms: T*): Substitutor[T] =
    Substitutor(sourceContextSize, terms.size, terms.toIndexedSeq)

extension (s: Substitutor[Pattern])
  def toTermSubstitutor: Substitutor[VTerm] = s.map(
    _.toTerm
      .getOrElse(throw IllegalStateException("unexpected absurd pattern")),
  )
