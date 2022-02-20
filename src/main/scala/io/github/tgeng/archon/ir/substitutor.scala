package io.github.tgeng.archon.ir

import scala.annotation.targetName

trait DeBruijn[T]:
  def fromIndex(index: Nat): T

given DeBruijnVTerm: DeBruijn[VTerm] with
  override def fromIndex(index: Nat): VTerm = VTerm.Var(index)

given DeBruijnPattern: DeBruijn[Pattern] with
  override def fromIndex(index: Nat): Pattern = Pattern.PRef(index)

/**
 * Local references are represented as DeBruijn indices so `ref 0` points to the right most entry in
 * the context. In this setting, a "trivial" mapping should map `ref (sourceContextSize - 1)` to the first
 * var in target context (DeBruijn index targetContextSize - 1). [[nonTrivialMapping]] contains the
 * mapping of the last variables in the target context. If target context is longer than source
 * context, then [[nonTrivialMapping]] must account for this gap. In addition, it may go beyond this
 * gap to account for more mapping. To an extreme, [[nonTrivialMapping]] can have size
 * [[targetContextSize]], in which case all the mappings are explicitly specified.
 */
class Substitutor[T: DeBruijn](
  val sourceContextSize: Nat,
  val targetContextSize: Nat,
  private var nonTrivialMapping: IndexedSeq[T],
) extends PartialSubstitution[T] :

  assert(sourceContextSize >= 0)
  assert(targetContextSize >= 0)

  private inline def fromIndex(index: Nat): T = summon[DeBruijn[T]].fromIndex(index)

  /**
   * @param boundIndex up to how many DeBruijn indices in the target context that materialization
   *                   should happen. Default value makes materialization happens fully
   */
  private def materialize(boundIndex: Nat = targetContextSize): Unit =
    if nonTrivialMapping.length == boundIndex then return
      nonTrivialMapping ++= (targetContextSize - nonTrivialMapping.length)
        .until(targetContextSize - boundIndex, -1)
        .map(i => fromIndex(sourceContextSize - i))

  def apply(index: Nat): Option[T] =
    if index < targetContextSize && 0 <= index then
      if index < nonTrivialMapping.length then Some(nonTrivialMapping(index))
      else Some(fromIndex(index + sourceContextSize - targetContextSize))
    else None

  def map[R: DeBruijn](f: T => R): Substitutor[R] = Substitutor(
    sourceContextSize,
    targetContextSize,
    nonTrivialMapping.map(f)
  )

  @targetName("uplus")
  infix def ⊎(that: Substitutor[T]): Substitutor[T] =
    assert(that.sourceContextSize == sourceContextSize)
    that.materialize()
    Substitutor(
      sourceContextSize,
      targetContextSize + that.targetContextSize,
      that.nonTrivialMapping ++ nonTrivialMapping,
    )

  @targetName("delete")
  infix def \(index: Nat): Substitutor[T] =
    materialize(index)
    if nonTrivialMapping.length == index then
      Substitutor(sourceContextSize, targetContextSize - 1, nonTrivialMapping)
    else
      Substitutor(
        sourceContextSize,
        targetContextSize - 1,
        nonTrivialMapping.patch(index, IndexedSeq.empty, 1)
      )

  def drop(count: Nat): Substitutor[T] = Substitutor(
    sourceContextSize,
    targetContextSize - count,
    nonTrivialMapping.drop(count)
  )