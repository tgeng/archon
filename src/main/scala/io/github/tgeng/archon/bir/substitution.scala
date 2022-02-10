package io.github.tgeng.archon.bir

import io.github.tgeng.archon.bir.VTerm.VUniverse
import io.github.tgeng.archon.common.*

type PartialSubstitution = Int => Option[VTerm]

trait Raisable[T]:
  def raise(t: T, amount: Int, bar: Int = 0): T

trait Substitutable[S: Raisable]:
  def substitute(s: S, substitutor: PartialSubstitution, offset: Int = 0): S

import VTerm.*
import CTerm.*

given RaisableVTerm: Raisable[VTerm] with
  override def raise(v: VTerm, amount: Int, bar: Int): VTerm = v match
    case Refl | EffectsType | LevelType | _: LevelLiteral | HeapType | GlobalHeap | _: Heap | _: Cell => v
    case VUniverse(level) => VUniverse(raise(level, amount, bar))
    case LocalRef(idx) => if idx >= bar then LocalRef(idx + amount) else v
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
    case EffectsLiteral(effects) => EffectsLiteral(effects.map(_.map(raise(_, amount, bar))))
    case EffectsUnion(effects1, effects2) => EffectsUnion(raise(effects1, amount, bar), raise(effects2, amount, bar))
    case CompoundLevel(offset, operands) => CompoundLevel(offset, operands.map((v: VTerm) => raise(v, amount, bar)))
    case CellType(heap, ty) => CellType(raise(heap, amount, bar), raise(ty, amount, bar))

given RaisableCTerm: Raisable[CTerm] with
  override def raise(c: CTerm, amount: Int, bar: Int): CTerm = c match
    case Hole | _: GlobalRef => c
    case CUniverse(effects, level) => CUniverse(
      RaisableVTerm.raise(effects, amount, bar),
      RaisableVTerm.raise(level, amount, bar)
    )
    case Force(v) => Force(RaisableVTerm.raise(v, amount, bar))
    case F(effects, vTerm) => F(RaisableVTerm.raise(effects, amount, bar), RaisableVTerm.raise(vTerm, amount, bar))
    case Return(v) => Return(RaisableVTerm.raise(v, amount, bar))
    case Let(t, ctx) => Let(raise(t, amount, bar), raise(ctx, amount, bar))
    case DLet(t, ctx) => DLet(raise(t, amount, bar), raise(ctx, amount, bar))
    case FunctionType(effects, binding, bodyTy) => FunctionType(
      RaisableVTerm.raise(effects, amount, bar),
      binding.map(RaisableVTerm.raise(_, amount, bar)),
      raise(bodyTy, amount, bar + 1)
    )
    case Lambda(body) => Lambda(raise(body, amount, bar + 1))
    case Application(fun, arg) => Application(raise(fun, amount, bar), RaisableVTerm.raise(arg, amount, bar))
    case RecordType(effects, qn, args) => RecordType(
      RaisableVTerm.raise(effects, amount, bar),
      qn,
      args.map(RaisableVTerm.raise(_, amount, bar))
    )
    case Record(fields) => Record(fields.view.mapValues(raise(_, amount, bar)).toMap)
    case Projection(rec, name) => Projection(raise(rec, amount, bar), name)
    case TypeCase(arg, cases, default) => TypeCase(
      RaisableVTerm.raise(arg, amount, bar),
      cases.view.mapValues { case (n, c) => (n, raise(c, amount, bar + n + 1)) }.toMap,
      raise(default, amount, bar + 1)
    )
    case DataCase(arg, cases) => DataCase(
      RaisableVTerm.raise(arg, amount, bar),
      cases.view.mapValues { case (n, c) => (n, raise(c, amount, bar + n + 1)) }.toMap
    )
    case EqualityCase(arg, body) => EqualityCase(
      RaisableVTerm.raise(arg, amount, bar),
      raise(body, amount, bar + 1)
    )
    case Continuation(inputType, outputType, stack) => Continuation(
      RaisableVTerm.raise(inputType, amount, bar),
      raise(outputType, amount, bar),
      stack.map(raise(_, amount, bar)),
    )
    case OperatorCall(eff, name, args) => OperatorCall(
      eff.map(RaisableVTerm.raise(_, amount, bar)),
      name,
      args.map(RaisableVTerm.raise(_, amount, bar))
    )
    case OperatorEffectMarker(outputType) => OperatorEffectMarker(raise(outputType, amount, bar))
    case Handler(eff, parameterType, inputEffects, inputType, outputType, transform, handlers, parameter, input) => Handler(
      eff.map(RaisableVTerm.raise(_, amount, bar)),
      RaisableVTerm.raise(parameterType, amount, bar),
      RaisableVTerm.raise(inputEffects, amount, bar),
      RaisableVTerm.raise(inputType, amount, bar),
      raise(outputType, amount, bar),
      raise(transform, amount, bar + 1),
      handlers.view.mapValues{ case (n, c) => (n, raise(c, amount, bar + n + 2))}.toMap,
      RaisableVTerm.raise(parameter, amount, bar),
      raise(input, amount, bar),
    )
    case Set(call, value) => Set(RaisableVTerm.raise(call, amount, bar), RaisableVTerm.raise(value, amount, bar))
    case Get(cell) => Get(RaisableVTerm.raise(cell, amount, bar))
    case Alloc(heap, ty) => Alloc(RaisableVTerm.raise(heap, amount, bar), RaisableVTerm.raise(ty, amount, bar))
    case HeapHandler(otherEffects, inputType, outputType, key, input) => HeapHandler(
      RaisableVTerm.raise(otherEffects, amount, bar),
      RaisableVTerm.raise(inputType, amount, bar + 1),
      raise(outputType, amount, bar),
      key,
      raise(input, amount, bar + 1)
    )

given SubstitutableVTerm: Substitutable[VTerm] with
  override def substitute(v: VTerm, substitutor: PartialSubstitution, offset: Int): VTerm = v match
    case Refl | EffectsType | LevelType | _: LevelLiteral | HeapType | GlobalHeap | _: Heap | _: Cell => v
    case VUniverse(level) => VUniverse(substitute(level, substitutor, offset))
    case LocalRef(idx) => substitutor(idx - offset) match
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
    case EffectsLiteral(effects) => EffectsLiteral(effects.map(_.map(substitute(_, substitutor, offset))))
    case EffectsUnion(effects1, effects2) => EffectsUnion(
      substitute(effects1, substitutor, offset),
      substitute(effects2, substitutor, offset)
    )
    case CompoundLevel(offset, operands) => CompoundLevel(
      offset,
      operands.map((v: VTerm) => substitute(v, substitutor, offset))
    )
    case CellType(heap, ty) => CellType(substitute(heap, substitutor, offset), substitute(ty, substitutor, offset))

given SubstitutableCTerm: Substitutable[CTerm] with
  override def substitute(c: CTerm, substitutor: PartialSubstitution, offset: Int): CTerm = c match
    case Hole | _: GlobalRef => c
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
    case Let(t, ctx) => Let(substitute(t, substitutor, offset), substitute(ctx, substitutor, offset))
    case DLet(t, ctx) => DLet(substitute(t, substitutor, offset), substitute(ctx, substitutor, offset))
    case FunctionType(effects, binding, bodyTy) => FunctionType(
      SubstitutableVTerm.substitute(effects, substitutor, offset),
      binding.map(SubstitutableVTerm.substitute(_, substitutor, offset)),
      substitute(bodyTy, substitutor, offset + 1)
    )
    case Lambda(body) => Lambda(substitute(body, substitutor, offset + 1))
    case Application(fun, arg) => Application(
      substitute(fun, substitutor, offset),
      SubstitutableVTerm.substitute(arg, substitutor, offset)
    )
    case RecordType(effects, qn, args) => RecordType(
      SubstitutableVTerm.substitute(effects, substitutor, offset),
      qn,
      args.map(SubstitutableVTerm.substitute(_, substitutor, offset))
    )
    case Record(fields) => Record(fields.view.mapValues(substitute(_, substitutor, offset)).toMap)
    case Projection(rec, name) => Projection(substitute(rec, substitutor, offset), name)
    case TypeCase(arg, cases, default) => TypeCase(
      SubstitutableVTerm.substitute(arg, substitutor, offset),
      cases.view.mapValues { case (n, c) => (n, substitute(c, substitutor, offset + n + 1)) }.toMap,
      substitute(default, substitutor, offset + 1)
    )
    case DataCase(arg, cases) => DataCase(
      SubstitutableVTerm.substitute(arg, substitutor, offset),
      cases.view.mapValues { case (n, c) => (n, substitute(c, substitutor, offset + n + 1)) }.toMap
    )
    case EqualityCase(arg, body) => EqualityCase(
      SubstitutableVTerm.substitute(arg, substitutor, offset),
      substitute(body, substitutor, offset + 1)
    )
    case Continuation(inputType, outputType, stack) => Continuation(
      SubstitutableVTerm.substitute(inputType, substitutor, offset),
      substitute(outputType, substitutor, offset),
      stack.map(substitute(_, substitutor, offset))
    )
    case OperatorCall(eff, name, args) => OperatorCall(
      eff.map(SubstitutableVTerm.substitute(_, substitutor, offset)),
      name,
      args.map(SubstitutableVTerm.substitute(_, substitutor, offset))
    )
    case OperatorEffectMarker(outputType) => OperatorEffectMarker(substitute(outputType, substitutor, offset))
    case Handler(eff, parameterType, inputEffects, inputType, outputType, transform, handlers, parameter, input) => Handler(
      eff.map(SubstitutableVTerm.substitute(_, substitutor, offset)),
      SubstitutableVTerm.substitute(parameterType, substitutor, offset),
      SubstitutableVTerm.substitute(inputEffects, substitutor, offset),
      SubstitutableVTerm.substitute(inputType, substitutor, offset),
      substitute(outputType, substitutor, offset),
      substitute(transform, substitutor, offset + 1),
      handlers.view.mapValues{ case (n, c) => (n, substitute(c, substitutor, offset + n + 2)) }.toMap,
      SubstitutableVTerm.substitute(parameter, substitutor, offset),
      substitute(input, substitutor, offset),
    )
    case Set(call, value) => Set(
      SubstitutableVTerm.substitute(call, substitutor, offset),
      SubstitutableVTerm.substitute(value, substitutor, offset)
    )
    case Get(cell) => Get(SubstitutableVTerm.substitute(cell, substitutor, offset))
    case Alloc(heap, ty) => Alloc(
      SubstitutableVTerm.substitute(heap, substitutor, offset),
      SubstitutableVTerm.substitute(ty, substitutor, offset)
    )
    case HeapHandler(otherEffects, inputType, outputType, key, input) => HeapHandler(
      SubstitutableVTerm.substitute(otherEffects, substitutor, offset),
      SubstitutableVTerm.substitute(inputType, substitutor, offset + 1),
      substitute(outputType, substitutor, offset),
      key,
      substitute(input, substitutor, offset + 1)
    )

extension (c: CTerm)
  def substitute(substitutor: PartialSubstitution) = SubstitutableCTerm.substitute(c, substitutor)
  def weaken(amount: Nat, at: Nat) = RaisableCTerm.raise(c, amount, at)
  def strengthen(amount: Nat, at: Nat) = RaisableCTerm.raise(c, -amount, at)

  def substHead(vTerms: VTerm*) = c
    // Here we use this trick to avoid first raise vTerm by one level and then lower resulted term
    .strengthen(vTerms.length, 0)
    // for example, consider substitution happened when applying (4, 5) to function \a, b => a + b. In DeBruijn index
    // the lambda body is `$1 + $0` and `vTerms` is `[4, 5]`. So after strengthening the lambda body becomes
    // `$-1 + $-2`. Hence, we plus 1 and take the negative to get the index to the array.
    .substitute(i => vTerms.lift(-(i + 1)))

extension (v: VTerm)
  def subst(substitutor: PartialSubstitution) = SubstitutableVTerm.substitute(v, substitutor)
  def weaken(amount: Nat, at: Nat) = RaisableVTerm.raise(v, amount, at)
  def strengthen(amount: Nat, at: Nat) = RaisableVTerm.raise(v, -amount, at)
