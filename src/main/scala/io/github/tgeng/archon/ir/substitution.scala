package io.github.tgeng.archon.ir

import scala.collection.mutable
import io.github.tgeng.archon.ir.VTerm.VUniverse
import io.github.tgeng.archon.common.*

import scala.collection.immutable.{ListMap, ListSet}

type PartialSubstitution[T] = Int => Option[T]

trait Raisable[T]:
  def raise(t: T, amount: Int, bar: Int = 0): T

trait Substitutable[S: Raisable, T]:
  def substitute(s: S, substitutor: PartialSubstitution[T], offset: Int = 0): S

import VTerm.*
import CTerm.*

given RaisableVTerm: Raisable[VTerm] with
  override def raise(v: VTerm, amount: Int, bar: Int): VTerm = v match
    case Refl | EffectsType | LevelType | HeapType | _: Heap => v
    case VUniverse(level) => VUniverse(raise(level, amount, bar))
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
    case CellType(heap, ty) => CellType(raise(heap, amount, bar), raise(ty, amount, bar))
    case Cell(heapKey, index, ty) => Cell(heapKey, index, raise(ty, amount, bar))

given RaisableCTerm: Raisable[CTerm] with
  override def raise(c: CTerm, amount: Int, bar: Int): CTerm = c match
    case Computation | _: Def => c
    case CUniverse(effects, level) => CUniverse(
      RaisableVTerm.raise(effects, amount, bar),
      RaisableVTerm.raise(level, amount, bar)
    )
    case Force(v) => Force(RaisableVTerm.raise(v, amount, bar))
    case F(effects, vTerm) => F(
      RaisableVTerm.raise(effects, amount, bar),
      RaisableVTerm.raise(vTerm, amount, bar)
    )
    case Return(v) => Return(RaisableVTerm.raise(v, amount, bar))
    case Let(t, ctx) => Let(raise(t, amount, bar), raise(ctx, amount, bar + 1))
    case DLet(t, ctx) => DLet(raise(t, amount, bar), raise(ctx, amount, bar + 1))
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
    case Handler(eff, inputType, outputType, transform, handlers, input) => Handler(
      eff.map(RaisableVTerm.raise(_, amount, bar)),
      raise(inputType, amount, bar),
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
    case HeapHandler(inputType, outputType, key, heapContent, input) => HeapHandler(
      raise(inputType, amount, bar + 1),
      raise(outputType, amount, bar),
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
    substitutor: PartialSubstitution[VTerm],
    offset: Int
  ): VTerm = v match
    case Refl | LevelType | EffectsType | HeapType | _: Heap => v
    case VUniverse(level) => VUniverse(substitute(level, substitutor, offset))
    case Var(idx) => substitutor(idx - offset) match
      case Some(t) => RaisableVTerm.raise(t, offset)
      case _ => v
    case U(cty) => U(SubstitutableCTerm.substitute(cty, substitutor, offset))
    case Thunk(cty) => Thunk(SubstitutableCTerm.substitute(cty, substitutor, offset))
    case DataType(qn, args) => DataType(qn, args.map(substitute(_, substitutor, offset)))
    case Con(name, args) => Con(name, args.map(substitute(_, substitutor, offset)))
    case EqualityType(level, ty, left, right) => EqualityType(
      substitute(level, substitutor, offset),
      substitute(ty, substitutor, offset),
      substitute(left, substitutor, offset),
      substitute(right, substitutor, offset),
    )
    case Effects(literal, unionOperands) =>
      val operands = unionOperands.map(substitute(_, substitutor, offset))
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
          substitutor,
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
    case CellType(heap, ty) => CellType(
      substitute(heap, substitutor, offset),
      substitute(ty, substitutor, offset)
    )
    case Cell(heapKey, index, ty) => Cell(heapKey, index, substitute(ty, substitutor, offset))

given SubstitutableCTerm: Substitutable[CTerm, VTerm] with
  override def substitute(
    c: CTerm,
    substitutor: PartialSubstitution[VTerm],
    offset: Int
  ): CTerm = c match
    case Computation | _: Def => c
    case CUniverse(effects, level) => CUniverse(
      SubstitutableVTerm.substitute(effects, substitutor, offset),
      SubstitutableVTerm.substitute(level, substitutor, offset)
    )
    case Force(v) => Force(SubstitutableVTerm.substitute(v, substitutor, offset))
    case F(effects, vTerm) => F(
      SubstitutableVTerm.substitute(effects, substitutor, offset),
      SubstitutableVTerm.substitute(vTerm, substitutor, offset)
    )
    case Return(v) => Return(SubstitutableVTerm.substitute(v, substitutor, offset))
    case Let(t, ctx) => Let(
      substitute(t, substitutor, offset),
      substitute(ctx, substitutor, offset + 1)
    )
    case DLet(t, ctx) => DLet(
      substitute(t, substitutor, offset),
      substitute(ctx, substitutor, offset + 1)
    )
    case FunctionType(effects, binding, bodyTy) => FunctionType(
      SubstitutableVTerm.substitute(effects, substitutor, offset),
      binding.map(SubstitutableVTerm.substitute(_, substitutor, offset)),
      substitute(bodyTy, substitutor, offset + 1)
    )
    //    case Lambda(body) => Lambda(substitute(body, substitutor, offset + 1))
    case Application(fun, arg) => Application(
      substitute(fun, substitutor, offset),
      SubstitutableVTerm.substitute(arg, substitutor, offset)
    )
    case RecordType(effects, qn, args) => RecordType(
      SubstitutableVTerm.substitute(effects, substitutor, offset),
      qn,
      args.map(SubstitutableVTerm.substitute(_, substitutor, offset))
    )
    //    case Record(fields) => Record(fields.view.mapValues(substitute(_, substitutor, offset)).toMap)
    case Projection(rec, name) => Projection(substitute(rec, substitutor, offset), name)
    //    case TypeCase(arg, cases, default) => TypeCase(
    //      SubstitutableVTerm.substitute(arg, substitutor, offset),
    //      cases.view.mapValues { case (n, c) => (n, substitute(c, substitutor, offset + n + 1)) }.toMap,
    //      substitute(default, substitutor, offset + 1)
    //    )
    //    case DataCase(arg, cases) => DataCase(
    //      SubstitutableVTerm.substitute(arg, substitutor, offset),
    //      cases.view.mapValues { case (n, c) => (n, substitute(c, substitutor, offset + n + 1)) }.toMap
    //    )
    //    case EqualityCase(arg, body) => EqualityCase(
    //      SubstitutableVTerm.substitute(arg, substitutor, offset),
    //      substitute(body, substitutor, offset + 1)
    //    )
    case Continuation(capturedStack) =>
      Continuation(
        capturedStack.map(substitute(_, substitutor, offset)),
      )
    case OperatorCall(eff, name, args) => OperatorCall(
      eff.map(SubstitutableVTerm.substitute(_, substitutor, offset)),
      name,
      args.map(SubstitutableVTerm.substitute(_, substitutor, offset))
    )
    case Handler(eff, inputType, outputType, transform, handlers, input) => Handler(
      eff.map(SubstitutableVTerm.substitute(_, substitutor, offset)),
      substitute(inputType, substitutor, offset),
      substitute(outputType, substitutor, offset),
      substitute(transform, substitutor, offset + 1),
      handlers.view.mapValues { case (n, c) => (n, substitute(
        c,
        substitutor,
        offset + n + 2
      ))
      }.toMap,
      substitute(input, substitutor, offset),
    )
    case Alloc(heap, ty) => Alloc(
      SubstitutableVTerm.substitute(heap, substitutor, offset),
      SubstitutableVTerm.substitute(ty, substitutor, offset)
    )
    case Set(call, value) => Set(
      SubstitutableVTerm.substitute(call, substitutor, offset),
      SubstitutableVTerm.substitute(value, substitutor, offset)
    )
    case Get(cell) => Get(SubstitutableVTerm.substitute(cell, substitutor, offset))
    case HeapHandler(inputType, outputType, key, heapContent, input) => HeapHandler(
      substitute(inputType, substitutor, offset + 1),
      substitute(outputType, substitutor, offset),
      key,
      heapContent.map(_.map(SubstitutableVTerm.substitute(_, substitutor, offset))),
      substitute(input, substitutor, offset + 1)
    )

given SubstitutableTelescope: Substitutable[Telescope, VTerm] with
  override def substitute(
    telescope: Telescope,
    substitutor: PartialSubstitution[VTerm],
    offset: Int
  ): Telescope = telescope match
    case Nil => Nil
    case binding :: telescope =>
      binding.map(SubstitutableVTerm.substitute(_, substitutor, offset)) :: substitute(telescope, substitutor, offset + 1)

extension (c: CTerm)
  def subst(substitutor: PartialSubstitution[VTerm]) = SubstitutableCTerm.substitute(c, substitutor)
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
  def subst(substitutor: PartialSubstitution[VTerm]) = SubstitutableVTerm.substitute(v, substitutor)
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

extension (telescope: Telescope)
  def subst(substitutor: PartialSubstitution[VTerm]) = SubstitutableTelescope.substitute(telescope, substitutor)
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
