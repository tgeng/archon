package com.github.tgeng.archon.core.ir

enum UnificationResult:
  case UYes(Δ: Context, σ: Substitutor[VTerm], τ: Substitutor[VTerm])
  case UNo
  case UUndecided

import UnificationResult.*

/** A syntax-based normalization is used here and hence the type parameter `_A` is not used.
  * Syntax-based normalization is sufficient for our use case because we assume UIP and injective
  * type constructors, both of which admit straightforward operational semantics. The downsides
  * are
  *   1. incompatible with univalence 2. incompatible with law of excluded middle and
  *      impredictivity But none of these downsides are important for our propose of making a
  *      practical language with efficient operational semantic.
  *
  * In future, it's possible to apply type-driven unification for erased terms and hence the type
  * parameter is retained here for future extension.
  */
def unify
  (u: VTerm, v: VTerm, _A: VTerm)
  (using Γ: Context)
  (using Σ: Signature)
  (using TypingContext)
  : Either[IrError, UnificationResult] =
  for
    u <- u.normalized
    v <- v.normalized
  yield (u, v) match
    case (u, v) if u == v => UYes(Γ, Substitutor.id(Γ.size), Substitutor.id(Γ.size))
    case _                => ???
