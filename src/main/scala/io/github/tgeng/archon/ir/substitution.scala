package io.github.tgeng.archon.ir

import scala.collection.mutable
import io.github.tgeng.archon.ir.VTerm.VUniverse
import io.github.tgeng.archon.common.*

import scala.collection.immutable.{ListMap, ListSet}

type PartialSubstitution[T] = Int => Option[T]

trait Raisable[T]:
  def raise(t: T, amount: Int, bar: Int = 0): T

trait Substitutable[S: Raisable, T]:
  def substitute(s: S, substitution: PartialSubstitution[T], offset: Int = 0): S

import VTerm.*
import CTerm.*

given RaisableVTerm: Raisable[VTerm] with
  override def raise(v: VTerm, amount: Int, bar: Int): VTerm = v match
    case Refl | EffectsType | LevelType | HeapType | _: Heap => v
    case VUniverse(level, upperBound) => VUniverse(
      level.map(raise(_, amount, bar)),
      raise(upperBound, amount, bar)
    )
    case VTop(level) => VTop(level.map(raise(_, amount, bar)))
    case Var(idx) => if idx >= bar then Var(idx + amount) else v
    case U(cty) => U(RaisableCTerm.raise(cty, amount, bar))
    case Thunk(c) => Thunk(RaisableCTerm.raise(c, amount, bar))
    case DataType(qn, args) => DataType(qn, args.map((v: VTerm) => raise(v, amount, bar)))
    case Con(name, args) => Con(name, args.map((v: VTerm) => raise(v, amount, bar)))
    case EqualityType(level, ty, left, right) => EqualityType(
      raise(level, amount, bar),
      raise(ty, amount, bar),
      raise(left, amount, bar),
      raise(right, amount, bar)
    )
    case Level(literal, maxOperands) => Level(
      literal,
      maxOperands.map { (k, v) => (raise(k, amount, bar).asInstanceOf[VTerm.Var], v) }
    )
    case Effects(literal, unionOperands) => Effects(
      literal, unionOperands.map(
        raise(_, amount, bar)
          .asInstanceOf[VTerm.Var]
      )
    )
    case CellType(heap, ty, status) => CellType(raise(heap, amount, bar), raise(ty, amount, bar), status)
    case Cell(heapKey, index, ty, status) => Cell(heapKey, index, raise(ty, amount, bar), status)

given RaisableCTerm: Raisable[CTerm] with
  override def raise(c: CTerm, amount: Int, bar: Int): CTerm = c match
    case Hole | _: Def => c
    case CUniverse(effects, level, upperBound) => CUniverse(
      RaisableVTerm.raise(effects, amount, bar),
      level.map(RaisableVTerm.raise(_, amount, bar)),
      raise(upperBound, amount, bar),
    )
    case CTop(effects, level) => CTop(
      RaisableVTerm.raise(effects, amount, bar),
      level.map(RaisableVTerm.raise(_, amount, bar)),
    )
    case Force(v) => Force(RaisableVTerm.raise(v, amount, bar))
    case F(effects, vTerm) => F(
      RaisableVTerm.raise(effects, amount, bar),
      RaisableVTerm.raise(vTerm, amount, bar)
    )
    case Return(v) => Return(RaisableVTerm.raise(v, amount, bar))
    case Let(t, eff, ty, ctx) => Let(
      raise(t, amount, bar),
      RaisableVTerm.raise(eff, amount, bar),
      ty.map(RaisableVTerm.raise(_, amount, bar)),
      raise(ctx, amount, bar + 1)
    )
    case FunctionType(effects, binding, bodyTy) => FunctionType(
      RaisableVTerm.raise(effects, amount, bar),
      binding.map(RaisableVTerm.raise(_, amount, bar)),
      raise(bodyTy, amount, bar + 1)
    )
    //    case Lambda(body) => Lambda(raise(body, amount, bar + 1))
    case Application(fun, arg) => Application(
      raise(fun, amount, bar),
      RaisableVTerm.raise(arg, amount, bar)
    )
    case RecordType(effects, qn, args) => RecordType(
      RaisableVTerm.raise(effects, amount, bar),
      qn,
      args.map(RaisableVTerm.raise(_, amount, bar))
    )
    //    case Record(fields) => Record(fields.view.mapValues(raise(_, amount, bar)).toMap)
    case Projection(rec, name) => Projection(raise(rec, amount, bar), name)
    //    case TypeCase(arg, cases, default) => TypeCase(
    //      RaisableVTerm.raise(arg, amount, bar),
    //      cases.view.mapValues { case (n, c) => (n, raise(c, amount, bar + n + 1)) }.toMap,
    //      raise(default, amount, bar + 1)
    //    )
    //    case DataCase(arg, cases) => DataCase(
    //      RaisableVTerm.raise(arg, amount, bar),
    //      cases.view.mapValues { case (n, c) => (n, raise(c, amount, bar + n + 1)) }.toMap
    //    )
    //    case EqualityCase(arg, body) => EqualityCase(
    //      RaisableVTerm.raise(arg, amount, bar),
    //      raise(body, amount, bar + 1)
    //    )
    case Continuation(capturedStack) => Continuation(
      capturedStack.map(raise(_, amount, bar)),
    )
    case OperatorCall(eff, name, args) => OperatorCall(
      eff.map(RaisableVTerm.raise(_, amount, bar)),
      name,
      args.map(RaisableVTerm.raise(_, amount, bar))
    )
    case Handler(eff, inputBinding, otherEffects, outputType, transform, handlers, input) => Handler(
      eff.map(RaisableVTerm.raise(_, amount, bar)),
      inputBinding.map(RaisableVTerm.raise(_, amount, bar)),
      RaisableVTerm.raise(otherEffects, amount, bar),
      raise(outputType, amount, bar),
      raise(transform, amount, bar + 1),
      handlers.view.mapValues { case (n, c) => (n, raise(c, amount, bar + n + 2)) }.toMap,
      raise(input, amount, bar),
    )
    case Alloc(heap, ty) => Alloc(
      RaisableVTerm.raise(heap, amount, bar),
      RaisableVTerm.raise(ty, amount, bar)
    )
    case Set(call, value) => Set(
      RaisableVTerm.raise(call, amount, bar),
      RaisableVTerm.raise(value, amount, bar)
    )
    case Get(cell) => Get(RaisableVTerm.raise(cell, amount, bar))
    case HeapHandler(inputBinding, otherEffects, key, heapContent, input) => HeapHandler(
      inputBinding.map(RaisableVTerm.raise(_, amount, bar)),
      RaisableVTerm.raise(otherEffects, amount, bar + 1),
      key,
      heapContent.map(_.map(RaisableVTerm.raise(_, amount, bar))),
      raise(input, amount, bar + 1)
    )

given RaisableTelescope: Raisable[Telescope] with
  override def raise(telescope: Telescope, amount: Int, bar: Int): Telescope = telescope match
    case Nil => Nil
    case binding :: telescope =>
      binding.map(RaisableVTerm.raise(_, amount, bar)) :: raise(telescope, amount, bar + 1)

given SubstitutableVTerm: Substitutable[VTerm, VTerm] with
  override def substitute(
    v: VTerm,
    substitution: PartialSubstitution[VTerm],
    offset: Int
  ): VTerm = v match
    case Refl | LevelType | EffectsType | HeapType | _: Heap => v
    case VUniverse(level, upperBound) => VUniverse(
      level.map(l => substitute(l, substitution, offset)),
      substitute(upperBound, substitution, offset),
    )
    case VTop(level) => VTop(level.map(substitute(_, substitution, offset)))
    case Var(idx) => substitution(idx - offset) match
      case Some(t) => RaisableVTerm.raise(t, offset)
      case _ => v
    case U(cty) => U(SubstitutableCTerm.substitute(cty, substitution, offset))
    case Thunk(cty) => Thunk(SubstitutableCTerm.substitute(cty, substitution, offset))
    case DataType(qn, args) => DataType(qn, args.map(substitute(_, substitution, offset)))
    case Con(name, args) => Con(name, args.map(substitute(_, substitution, offset)))
    case EqualityType(level, ty, left, right) => EqualityType(
      substitute(level, substitution, offset),
      substitute(ty, substitution, offset),
      substitute(left, substitution, offset),
      substitute(right, substitution, offset),
    )
    case Effects(literal, unionOperands) =>
      val operands = unionOperands.map(substitute(_, substitution, offset))
      val newLiteral = literal.to(mutable.ArrayBuffer)
      val newOperands = mutable.ArrayBuffer[Var]()
      for operand <- operands do
        operand match
          case r: Var => newOperands.append(r)
          case Effects(literal, operands) =>
            newLiteral.appendAll(literal)
            newOperands.appendAll(operands)
          case _ => throw IllegalArgumentException("type error")
      Effects(newLiteral.to(ListSet), newOperands.to(ListSet))
    case Level(literal, maxOperands) =>
      val operands = maxOperands.map { (ref, lOffset) =>
        (substitute(
          ref,
          substitution,
          offset
        ), lOffset)
      }
      var newLiteral = literal
      val newOperands = mutable.ArrayBuffer[(Var, Nat)]()
      for (t, lOffset) <- operands do
        t match
          case r: Var => newOperands.append((r, lOffset))
          case Level(literal, operands) =>
            val offsetOperands = operands.map { (r, o) => (r, o + lOffset) }
            newOperands.addAll(offsetOperands)
            newLiteral = (Seq(
              math.max(
                literal,
                newLiteral
              )
            ) ++ offsetOperands.map { (_, o) => o }).max
          case _ => throw IllegalArgumentException("type error")
      Level(newLiteral, ListMap.from(newOperands))
    case CellType(heap, ty, status) => CellType(
      substitute(heap, substitution, offset),
      substitute(ty, substitution, offset),
      status,
    )
    case Cell(heapKey, index, ty, status) => Cell(heapKey, index, substitute(ty, substitution, offset), status)

given SubstitutableCTerm: Substitutable[CTerm, VTerm] with
  override def substitute(
    c: CTerm,
    substitution: PartialSubstitution[VTerm],
    offset: Int
  ): CTerm = c match
    case Hole | _: Def => c
    case CUniverse(effects, level, upperBound) => CUniverse(
      SubstitutableVTerm.substitute(effects, substitution, offset),
      level.map(SubstitutableVTerm.substitute(_, substitution, offset)),
      substitute(upperBound, substitution, offset),
    )
    case CTop(effects, level) => CTop(
      SubstitutableVTerm.substitute(effects, substitution, offset),
      level.map(SubstitutableVTerm.substitute(_, substitution, offset))
    )
    case Force(v) => Force(SubstitutableVTerm.substitute(v, substitution, offset))
    case F(effects, vTerm) => F(
      SubstitutableVTerm.substitute(effects, substitution, offset),
      SubstitutableVTerm.substitute(vTerm, substitution, offset)
    )
    case Return(v) => Return(SubstitutableVTerm.substitute(v, substitution, offset))
    case Let(t, eff, ty, ctx) => Let(
      substitute(t, substitution, offset),
      SubstitutableVTerm.substitute(eff, substitution, offset),
      ty.map(SubstitutableVTerm.substitute(_, substitution, offset)),
      substitute(ctx, substitution, offset + 1)
    )
    case FunctionType(effects, binding, bodyTy) => FunctionType(
      SubstitutableVTerm.substitute(effects, substitution, offset),
      binding.map(SubstitutableVTerm.substitute(_, substitution, offset)),
      substitute(bodyTy, substitution, offset + 1)
    )
    //    case Lambda(body) => Lambda(substitute(body, substitution, offset + 1))
    case Application(fun, arg) => Application(
      substitute(fun, substitution, offset),
      SubstitutableVTerm.substitute(arg, substitution, offset)
    )
    case RecordType(effects, qn, args) => RecordType(
      SubstitutableVTerm.substitute(effects, substitution, offset),
      qn,
      args.map(SubstitutableVTerm.substitute(_, substitution, offset))
    )
    //    case Record(fields) => Record(fields.view.mapValues(substitute(_, substitution, offset)).toMap)
    case Projection(rec, name) => Projection(substitute(rec, substitution, offset), name)
    //    case TypeCase(arg, cases, default) => TypeCase(
    //      SubstitutableVTerm.substitute(arg, substitution, offset),
    //      cases.view.mapValues { case (n, c) => (n, substitute(c, substitution, offset + n + 1)) }.toMap,
    //      substitute(default, substitution, offset + 1)
    //    )
    //    case DataCase(arg, cases) => DataCase(
    //      SubstitutableVTerm.substitute(arg, substitution, offset),
    //      cases.view.mapValues { case (n, c) => (n, substitute(c, substitution, offset + n + 1)) }.toMap
    //    )
    //    case EqualityCase(arg, body) => EqualityCase(
    //      SubstitutableVTerm.substitute(arg, substitution, offset),
    //      substitute(body, substitution, offset + 1)
    //    )
    case Continuation(capturedStack) =>
      Continuation(
        capturedStack.map(substitute(_, substitution, offset)),
      )
    case OperatorCall(eff, name, args) => OperatorCall(
      eff.map(SubstitutableVTerm.substitute(_, substitution, offset)),
      name,
      args.map(SubstitutableVTerm.substitute(_, substitution, offset))
    )
    case Handler(eff, inputBinding, otherEffects, outputType, transform, handlers, input) => Handler(
      eff.map(SubstitutableVTerm.substitute(_, substitution, offset)),
      inputBinding.map(SubstitutableVTerm.substitute(_, substitution, offset)),
      SubstitutableVTerm.substitute(otherEffects, substitution, offset),
      substitute(outputType, substitution, offset),
      substitute(transform, substitution, offset + 1),
      handlers.view.mapValues { case (n, c) => (n, substitute(
        c,
        substitution,
        offset + n + 2
      ))
      }.toMap,
      substitute(input, substitution, offset),
    )
    case Alloc(heap, ty) => Alloc(
      SubstitutableVTerm.substitute(heap, substitution, offset),
      SubstitutableVTerm.substitute(ty, substitution, offset)
    )
    case Set(call, value) => Set(
      SubstitutableVTerm.substitute(call, substitution, offset),
      SubstitutableVTerm.substitute(value, substitution, offset)
    )
    case Get(cell) => Get(SubstitutableVTerm.substitute(cell, substitution, offset))
    case HeapHandler(inputBinding, otherEffects, key, heapContent, input) => HeapHandler(
      inputBinding.map(SubstitutableVTerm.substitute(_, substitution, offset)),
      SubstitutableVTerm.substitute(otherEffects, substitution, offset + 1),
      key,
      heapContent.map(_.map(SubstitutableVTerm.substitute(_, substitution, offset))),
      substitute(input, substitution, offset + 1)
    )

given SubstitutableTelescope: Substitutable[Telescope, VTerm] with
  override def substitute(
    telescope: Telescope,
    substitution: PartialSubstitution[VTerm],
    offset: Int
  ): Telescope = telescope match
    case Nil => Nil
    case binding :: telescope =>
      binding.map(SubstitutableVTerm.substitute(_, substitution, offset)) :: substitute(
        telescope,
        substitution,
        offset + 1
      )

extension (c: CTerm)
  def subst(substitution: PartialSubstitution[VTerm]) = SubstitutableCTerm.substitute(c, substitution)
  def weakened = c.weaken(1, 0)
  def weaken(amount: Nat, at: Nat) = RaisableCTerm.raise(c, amount, at)
  def strengthened = c.strengthen(1, 0)
  def strengthen(amount: Nat, at: Nat) = RaisableCTerm.raise(c, -amount, at)

  /**
   * Substitutes lower DeBruijn indices with the given terms. The first term substitutes the highest
   * index with the last substitutes 0. Then the result is raised so that the substituted indices
   * are taken by other (deeper) indices.
   */
  def substLowers(vTerms: VTerm*) = c
    // Here we use this trick to avoid first raise vTerm by one level and then lower resulted term
    .strengthen(vTerms.length, 0)
    // for example, consider substitution happened when applying (4, 5) to function \a, b => a + b. In DeBruijn index
    // the lambda body is `$1 + $0` and `vTerms` is `[4, 5]`. So after strengthening the lambda body becomes
    // `$-1 + $-2`. Hence, we plus 1 and take the negative to get the index to the array.
    .subst(i => vTerms.lift(-(i + 1)))

extension (v: VTerm)
  def subst(substitution: PartialSubstitution[VTerm]) = SubstitutableVTerm.substitute(v, substitution)
  def weaken(amount: Nat, at: Nat) = RaisableVTerm.raise(v, amount, at)
  def weakened = v.weaken(1, 0)
  def strengthened = v.strengthen(1, 0)
  def strengthen(amount: Nat, at: Nat) = RaisableVTerm.raise(v, -amount, at)

  /**
   * Substitutes lower DeBruijn indices with the given terms. The first term substitutes the highest
   * index with the last substitutes 0. Then the result is raised so that the substituted indices
   * are taken by other (deeper) indices.
   */
  def substLowers(vTerms: VTerm*) = v
    // Here we use this trick to avoid first raise vTerm by one level and then lower resulted term
    .strengthen(vTerms.length, 0)
    // for example, consider substitution happened when applying (4, 5) to function \a, b => a + b. In DeBruijn index
    // the lambda body is `$1 + $0` and `vTerms` is `[4, 5]`. So after strengthening the lambda body becomes
    // `$-1 + $-2`. Hence, we plus 1 and take the negative to get the index to the array.
    .subst(i => vTerms.lift(-(i + 1)))

extension (ul: ULevel)
  def subst(substitution: PartialSubstitution[VTerm]) = ul.map(SubstitutableVTerm.substitute(_, substitution))
  def weaken(amount: Nat, at: Nat) = ul.map(RaisableVTerm.raise(_, amount, at))
  def weakened = ul.weaken(1, 0)
  def strengthened = ul.strengthen(1, 0)
  def strengthen(amount: Nat, at: Nat) = ul.map(RaisableVTerm.raise(_, -amount, at))

  /**
   * Substitutes lower DeBruijn indices with the given terms. The first term substitutes the highest
   * index with the last substitutes 0. Then the result is raised so that the substituted indices
   * are taken by other (deeper) indices.
   */
  def substLowers(vTerms: VTerm*) = ul
    // Here we use this trick to avoid first raise vTerm by one level and then lower resulted term
    .strengthen(vTerms.length, 0)
    // for example, consider substitution happened when applying (4, 5) to function \a, b => a + b. In DeBruijn index
    // the lambda body is `$1 + $0` and `vTerms` is `[4, 5]`. So after strengthening the lambda body becomes
    // `$-1 + $-2`. Hence, we plus 1 and take the negative to get the index to the array.
    .subst(i => vTerms.lift(-(i + 1)))

extension (telescope: Telescope)
  def subst(substitution: PartialSubstitution[VTerm]) = SubstitutableTelescope.substitute(
    telescope,
    substitution
  )
  def weaken(amount: Nat, at: Nat) = RaisableTelescope.raise(telescope, amount, at)
  def weakened = telescope.weaken(1, 0)
  def strengthened = telescope.strengthen(1, 0)
  def strengthen(amount: Nat, at: Nat) = RaisableTelescope.raise(telescope, -amount, at)

  /**
   * Substitutes lower DeBruijn indices with the given terms. The first term substitutes the highest
   * index with the last substitutes 0. Then the result is raised so that the substituted indices
   * are taken by other (deeper) indices.
   */
  def substLowers(vTerms: VTerm*) = telescope
    // Here we use this trick to avoid first raise vTerm by one level and then lower resulted term
    .strengthen(vTerms.length, 0)
    // for example, consider substitution happened when applying (4, 5) to function \a, b => a + b. In DeBruijn index
    // the lambda body is `$1 + $0` and `vTerms` is `[4, 5]`. So after strengthening the lambda body becomes
    // `$-1 + $-2`. Hence, we plus 1 and take the negative to get the index to the array.
    .subst(i => vTerms.lift(-(i + 1)))
