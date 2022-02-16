package io.github.tgeng.archon.ir

import scala.annotation.targetName

trait DeBruijn[T]:
  def fromIndex(index: Nat): T

given DeBruijnVTerm: DeBruijn[VTerm] with
  override def fromIndex(index: Nat): VTerm = VTerm.LocalRef(index)

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
  private inline def fromIndex(index: Nat): T = summon[DeBruijn[T]].fromIndex(index)

  private def materialize(): Unit =
    if nonTrivialMapping.length == targetContextSize then return
      nonTrivialMapping = (1 to targetContextSize - nonTrivialMapping.length)
        .map(i => fromIndex(sourceContextSize - i)) ++
        nonTrivialMapping

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
  infix def ⊎(that: Substitutor[T]) : Substitutor[T] =
    assert(that.sourceContextSize == sourceContextSize)
    that.materialize()
    Substitutor(
      sourceContextSize,
      targetContextSize + that.targetContextSize,
      that.nonTrivialMapping ++ nonTrivialMapping,
    )
