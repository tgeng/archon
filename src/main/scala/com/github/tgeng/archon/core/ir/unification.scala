/** This file contains unification used during elboration (aka pattern matching clause elaboration).
  * Meta-variable unification is done separately in `typing.scala`. The major difference is that
  * unificaiton here creates substitutors that unifies a `Var` with a concrete terms, while
  * meta-variable unification solves meta-variables in the typing context.
  */
package com.github.tgeng.archon.core.ir

import com.github.tgeng.archon.common.*
import com.github.tgeng.archon.core.common.*
import scala.math.{min, max}
import scala.annotation.targetName
import scala.annotation.compileTimeOnly
import com.github.tgeng.archon.core.common.Name
import java.awt.PageAttributes.ColorType

enum UnificationFailureType:
  case UfCycle, UfConflict

import UnificationFailureType.*

enum UnificationResult:
  case UYes
    (
      /** Solution context. This context should be no longer than the source context Γ, which is
        * used during unification, because some variables should have been unified to terms and
        * hence no longer need to be a standalone variable.
        *
        * Note that, comparing with [0], our source context Γ does not contain any equality types.
        * Hence, the recovering substitution τ does not contain any trailing `Refl` terms. This
        * simplifies implementation and usage, but could be difficult to extend in order to support
        * more sophisticated unification outlined in section 6 of [0].
        */
      Δ: Context,
      /** * The solution substitution σ: Δ -> Γ.
        */
      σ: Substitutor[Pattern],
      /** * The recovering substitution τ: Γ -> Δ.
        */
      τ: Substitutor[Pattern],
    )
  case UNo(u: VTerm, v: VTerm, ty: VTerm, failureType: UnificationFailureType)
  case UUndecided(u: VTerm, v: VTerm, ty: VTerm)

import UnificationResult.*
import VTerm.*
import CTerm.*

/** A syntax-based normalization is used here and hence the type parameter `ty` is only used to
  * determine term types. Syntax-based normalization is sufficient for our use case because we
  * assume UIP and injective type constructors, both of which admit straightforward operational
  * semantics. The downsides are
  *
  *   - incompatible with univalence
  *   - incompatible with law of excluded middle and impredictivity
  *
  * But none of these downsides are important for our propose of making a practical language with
  * efficient operational semantic.
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
      case (u, v, _) if u == v => unifyAll(Nil, Nil, Nil)

      // solution and cycle
      case (Var(x), Var(y), ty) => solution(Var(min(x, y)), Var(max(x, y)))
      case (x: Var, t, ty)      => solutionOrCycle(x, t, ty)
      case (t, x: Var, ty)      => solutionOrCycle(x, t, ty)

      // injectivity
      case (ty @ Type(upperBound1), Type(upperBound2), _) => unify(upperBound1, upperBound2, ty)
      case (
          Top(l1, eqDecidability1),
          Top(l2, eqDecidability2),
          _,
        ) =>
        unifyAll(
          List(l1, eqDecidability1),
          List(l2, eqDecidability2),
          telescope(LevelType(LevelUpperBound()), EqDecidabilityType()),
        )
      // We do not unify any computation types since it does not seem to be very
      // useful. If someday we would add such support, we will need to extend
      // matching logic and case tree to support dispatching on computation types.
      // Anyway, below are some notes on how to unify function types.
      //
      // If we follow what's done with inductive types (for example sigma type is
      // defined by inductive type), we would need to introduce a lower-level
      // function type constructor that takes an explicit lambda as the body type.
      // That is, in `FunctionType(binding: Binding[VTerm], bodyTy: CTerm, ...)`,
      // instead of having a `bodyTy` is one DeBruijn level deeper, we would have a
      // bodyTy that is a lambda, which is at the same DeBruijn level as `binding`.
      // Then the surface language would need some syntax sugar for function type
      // declarations like `x: A -> B` becomes `FunctionType(A, (\x B x))`. If we
      // go down this path, then unification can not happen for function types
      // created by such desugaring because the body type is never a `Var`, which
      // allows apply "solution" rune. Note that this is indeed the case with sigma
      // type simulated with inductive types: to allow unification to happen, the
      // second arg of the sigma type must be a `Var` instead of a lambda that
      // returns a `Var`.
      //
      // Alternatively, it seems we can do special handling for pi types (this
      // special handling can can also be done with sigma type, or even generalize
      // to any inductive types, essentially allow unification to happen inside
      // lambda). This special handling is basically carve out a "forbidden zone"
      // of (lower) DeBruijn indices. Any DeBruijn indices in this "forbidden zone"
      // cannot be unified with the "solution" rule. For example, consider
      // unifying `(x: Nat) -> Vec String x` and `(x: Nat) -> Vec y 3`, where `y` is
      // bound earlier in the current context. For the body type, the forbidden zone
      // is `{x}` (or `{0}` with DeBruijn index). Hence, `x` in the former type is in
      // the forbidden zone and cannot be unified to `3`. On the other hand, `y` can
      // be unified to `String` because it's outside of the forbidden zone.
      //
      // None of the above is currently implemented in archon because it's unclear
      // what the benefits are, as injective type constructor is not a highly
      // sought-after feature anyway.
      case (U(_), U(_), _) => Right(UUndecided(u, v, ty))
      case (DataType(qn1, args1), DataType(qn2, args2), _) if qn1 == qn2 =>
        unifyAll(args1, args2, Σ.getData(qn1).tParamTys.map(_._1).toList)
      case (Con(name1, args1), Con(name2, args2), DataType(qn, tArgs)) if name1 == name2 =>
        unifyAll(args1, args2, Σ.getConstructor(qn, name1).paramTys.substLowers(tArgs: _*))
      case (CellType(heap1, ty1), CellType(heap2, ty2), _) =>
        unifyAll(List(heap1, ty1), List(heap2, ty2), telescope(HeapType(), Type(ty1)))
      // stuck
      case (_: Collapse | _: Thunk, _, _) => Right(UUndecided(u, v, ty))
      case (_, _: Collapse | _: Thunk, _) => Right(UUndecided(u, v, ty))

      case _ => Right(UNo(u, v, ty, UnificationFailureType.UfConflict))
  yield r

private def solutionOrCycle
  (x: Var, t: VTerm, ty: VTerm)
  (using Γ: Context)
  (using Σ: Signature)
  (using TypingContext)
  : Either[IrError, UnificationResult] =
  if isCyclic(x, t) then Right(UNo(x, t, ty, UfCycle))
  else solution(x, t)

private object CycleVisitor
  extends Visitor[
    (
      /* index causing the cycle */ Nat,
      /* whether a type or value constructor is encountered */ Boolean,
    ), /* cycle found */ Boolean,
  ]:
  override def combine(rs: Boolean*)(using ctx: (Nat, Boolean))(using Σ: Signature): Boolean =
    rs.foldLeft(false)(_ || _)

  override def withBindings
    (bindingNames: => Seq[Ref[Name]])
    (action: ((Nat, Boolean)) ?=> Boolean)
    (using ctx: (Nat, Boolean))
    (using Σ: Signature)
    : Boolean =
    action(using (ctx._1 + 1, ctx._2))

  override def visitVar(v: Var)(using ctx: (Nat, Boolean))(using Σ: Signature): Boolean =
    // Only report true (cyclic) if a type or value has been encountered from root term.
    ctx._2 && v.idx == ctx._1

  override def visitType(ty: Type)(using ctx: (Nat, Boolean))(using Σ: Signature): Boolean =
    super.visitType(ty)(using (ctx._1, true))

  override def visitTop(top: Top)(using ctx: (Nat, Boolean))(using Σ: Signature): Boolean =
    super.visitTop(top)(using (ctx._1, true))

  override def visitU(u: U)(using ctx: (Nat, Boolean))(using Σ: Signature): Boolean =
    super.visitU(u)(using (ctx._1, true))

  override def visitDataType
    (dataType: DataType)
    (using ctx: (Nat, Boolean))
    (using Σ: Signature)
    : Boolean =
    super.visitDataType(dataType)(using (ctx._1, true))

  override def visitCon(con: Con)(using ctx: (Nat, Boolean))(using Σ: Signature): Boolean =
    super.visitCon(con)(using (ctx._1, true))

  override def visitUsageType
    (usageType: UsageType)
    (using ctx: (Nat, Boolean))
    (using Σ: Signature)
    : Boolean =
    super.visitUsageType(usageType)(using (ctx._1, true))

  override def visitEqDecidabilityType
    (eqDecidabilityType: EqDecidabilityType)
    (using ctx: (Nat, Boolean))
    (using Σ: Signature)
    : Boolean =
    super.visitEqDecidabilityType(eqDecidabilityType)(using (ctx._1, true))

  override def visitEffectsType
    (effectsType: EffectsType)
    (using ctx: (Nat, Boolean))
    (using Σ: Signature)
    : Boolean =
    super.visitEffectsType(effectsType)(using (ctx._1, true))

  // visitLevelType and visitHeapType are not needed since Refl does not contain any nested terms.

  override def visitCellType
    (cellType: CellType)
    (using ctx: (Nat, Boolean))
    (using Σ: Signature)
    : Boolean =
    super.visitCellType(cellType)(using (ctx._1, true))

private def isCyclic(x: Var, t: VTerm)(using Σ: Signature): Boolean =
  CycleVisitor.visitVTerm(t)(using (x.idx, false))

private def solution
  (x: Var, t: VTerm)
  (using Γ: Context)
  (using Σ: Signature)
  (using TypingContext)
  : Either[IrError, UnificationResult] =
  val (_Γ1, _, _Γ2) = Γ.split(x)
  val Δ = _Γ1 ++ _Γ2.substLowers(t)
  // _Γ1 and _Γ2 part are just identity vars for σ and τ.
  val σ = Substitutor.id[Pattern](Δ.size).add(x.idx, Pattern.PForced(t))
  val τ = Substitutor.id[Pattern](Γ.size).remove(x.idx)
  Right(UYes(Δ, σ, τ))

private def telescope(tys: VTerm*)(using Signature): Telescope = (0 until tys.size).map { i =>
  Binding(tys(i).weaken(i, 0), Usage.UUnres)(gn"var$i")
}.toList

/** Comparing with [0], this function is finding the unifier from `Γ(e̅: u̅ ≡_tys v̅)` to `Δ`.
  * Note,u̅ and v̅ are at the same level as the leftmost element of telescope. That is, processing
  * further elements of telescope requires first substituting left elements of telescope with first
  * value of u̅ (after unification succeeds between first element of u̅ and v̅).
  */
def unifyAll
  (u̅ : List[VTerm], v̅ : List[VTerm], telescope: Telescope)
  (using Γ: Context)
  (using Σ: Signature)
  (using TypingContext)
  : Either[IrError, UnificationResult] =
  infix def compose
    (u1: UnificationResult, u2: UnificationResult)
    (using Signature)
    : UnificationResult = (u1, u2) match
    case (UYes(_, σ1, τ1), UYes(_Δ, σ2, τ2)) => UYes(_Δ, σ1 ∘ σ2, τ2 ∘ τ1)
    case (uRes: UNo, _)                      => uRes
    case (_, uRes: UNo)                      => uRes
    case (uRes: UUndecided, _)               => uRes
    case (_, uRes: UUndecided)               => uRes

  (u̅, v̅, telescope) match
    case (Nil, Nil, Nil) => Right(UYes(Γ, Substitutor.id(Γ.size), Substitutor.id(Γ.size)))
    case (u :: u̅, v :: v̅, binding :: telescope) =>
      for
        uRes <- unify(u, v, binding.ty)
        r <- uRes match
          case UYes(_Δ, σ, τ) =>
            val σt = σ.toTermSubstitutor
            for uRes2 <- unifyAll(
                u̅.map(_.subst(σt)),
                v̅.map(_.subst(σt)),
                telescope.substLowers(u).subst(σt),
              )(using
                _Δ,
              )
            yield compose(uRes, uRes2)
          case u => Right(u)
      yield r
    case _ => throw IllegalArgumentException()

// [0] Jesper Cockx, Dominique Devriese, and Frank Piessens. 2016. Unifiers as equivalences:
//     proof-relevant unification of dependently typed data. SIGPLAN Not. 51, 9 (September 2016),
//     270–283. https://doi.org/10.1145/3022670.2951917
