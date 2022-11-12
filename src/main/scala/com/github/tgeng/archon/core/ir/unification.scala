package com.github.tgeng.archon.core.ir

import com.github.tgeng.archon.common.*
import scala.math.{min, max}
import scala.annotation.targetName
import scala.annotation.compileTimeOnly

enum UnificationResult:
  case UYes
    (
      /** Solution context. This context should be no longer than the source context Γ, which is
        * used during unification, because some variables should have been unified to terms and
        * hence no longer need to be a standalone variable.
        *
        * Note that, comparing with [0], our source context Γ does not contain any equality types.
        * Hence, the recovering substitution τ does not contain any trailing `Refl` terms. This
        * simplifies implementation and usage, but could be difficult to extend in order to
        * support more sophisticated unification outlined in section 6 of [0].
        */
      Δ: Context,
      /** * The solution substitution σ: Δ -> Γ.
        */
      σ: Substitutor[VTerm],
      /** * The recovering substitution τ: Γ -> Δ.
        */
      τ: Substitutor[VTerm]
    )
  case UNo
  case UUndecided(ty: VTerm, u: VTerm, v: VTerm)

import UnificationResult.*
import VTerm.*

/** A syntax-based normalization is used here and hence the type parameter `ty` is only used to
  * determine term types. Syntax-based normalization is sufficient for our use case because we
  * assume UIP and injective type constructors, both of which admit straightforward operational
  * semantics. The downsides are
  *
  *   - incompatible with univalence
  *   - incompatible with law of excluded middle and impredictivity But none of these downsides
  *     are important for our propose of making a practical language with efficient operational
  *     semantic.
  *
  * In future, it's possible to apply type-driven unification for erased terms and hence the type
  * parameter is retained here for future extension.
  *
  * Comparing with [0], this function is finding the unifier from `Γ(e: u ≡_ty v)` to `Δ`.
  */
def unify
  (u: VTerm, v: VTerm, ty: VTerm)
  (using Γ: Context)
  (using Σ: Signature)
  (using TypingContext)
  : Either[IrError, UnificationResult] =
  for
    u <- u.normalized
    v <- v.normalized
    ty <- ty.normalized
    r <- (u, v, ty) match
      // delete
      case (u, v, _) if u == v => unify(Nil, Nil, Nil)

      // cycle
      case (u, v, _) if isCyclic(u, v) => Right(UNo)

      // solution
      case (Var(x), Var(y), _) => solution(Var(min(x, y)), Var(max(x, y)))
      case (x: Var, t, _) => solution(x, t)
      case (t, x: Var, _) => solution(x, t)

      case _ => ???
  yield r

private def solution
  (x: Var, term: VTerm)
  (using Γ: Context)
  (using Σ: Signature)
  (using TypingContext)
  : Either[IrError, UnificationResult] =
  val (_Γ1, _, _Γ2) = Γ.split(x)
  val Δ = _Γ1 ++ _Γ2.substLowers(term)
  // _Γ1 and _Γ2 part are just identity vars for σ and τ.
  val σ = Substitutor.id[VTerm](Δ.size).add(x.idx, term)
  val τ = Substitutor.id[VTerm](Γ.size).remove(x.idx)
  Right(UYes(Δ, σ, τ))

private def isCyclic(x: VTerm, y: VTerm): Boolean = ???

/** Comparing with [0], this function is finding the unifier from `Γ(e̅: u̅ ≡_tys v̅)` to `Δ`.
  * However, since the current implementation is naive and does not support equivalence lifted
  * over other type equivalence, the `tys` are terms at the same level (in the DeBruijn-index
  * sense), unlike a telescope.
  */
def unify
  (u̅ : List[VTerm], v̅ : List[VTerm], tys: List[VTerm])
  (using Γ: Context)
  (using Σ: Signature)
  (using TypingContext)
  : Either[IrError, UnificationResult] =
  infix def compose
    (u1: UnificationResult, u2: UnificationResult)
    (using Signature)
    : UnificationResult = (u1, u2) match
    case (UYes(_, σ1, τ1), UYes(_Δ, σ2, τ2)) => UYes(_Δ, σ1 ∘ σ2, τ2 ∘ τ1)
    case (_: UUndecided, _: UUndecided)      => u1
    case _                                   => UNo

  (u̅, v̅, tys) match
    case (Nil, Nil, Nil) => Right(UYes(Γ, Substitutor.id(Γ.size), Substitutor.id(Γ.size)))
    case (u :: u̅, v :: v̅, ty :: tys) =>
      for
        uRes <- unify(u, v, ty)
        r <- uRes match
          case UYes(_Δ, σ, τ) =>
            for uRes2 <- unify(u̅.map(_.subst(σ)), v̅.map(_.subst(σ)), tys.map(_.subst(σ)))(using
                _Δ
              )
            yield compose(uRes, uRes2)
          case u => Right(u)
      yield r
    case _ => throw IllegalArgumentException()

// [0] Jesper Cockx, Dominique Devriese, and Frank Piessens. 2016. Unifiers as equivalences:
//     proof-relevant unification of dependently typed data. SIGPLAN Not. 51, 9 (September 2016),
//     270–283. https://doi.org/10.1145/3022670.2951917
