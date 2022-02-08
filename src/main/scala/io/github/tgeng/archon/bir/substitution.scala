package io.github.tgeng.archon.bir

import io.github.tgeng.archon.bir.VTerm.VUniverse
import io.github.tgeng.archon.common.*

type Substitutor = Map[Int, VTerm]

trait Raisable[T]:
  def raise(t: T, amount: Int, bar: Int = 0): T

trait Substitutable[S: Raisable]:
  def substitute(s: S, substitutor: Substitutor, offset: Int = 0): S

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
    case CUniverse(level, effects) => CUniverse(
      RaisableVTerm.raise(level, amount, bar),
      RaisableVTerm.raise(effects, amount, bar)
    )
    case Force(v) => Force(RaisableVTerm.raise(v, amount, bar))
    case F(vTerm, effects) => F(RaisableVTerm.raise(vTerm, amount, bar), RaisableVTerm.raise(effects, amount, bar))
    case Return(v) => Return(RaisableVTerm.raise(v, amount, bar))
    case Let(t, ctx) => Let(raise(t, amount, bar), raise(ctx, amount, bar))
    case DLet(t, ctx) => DLet(raise(t, amount, bar), raise(ctx, amount, bar))
    case FunctionType(binding, bodyTy, effects) => FunctionType(
      binding.map(RaisableVTerm.raise(_, amount, bar)),
      raise(bodyTy, amount, bar + 1),
      RaisableVTerm.raise(effects, amount, bar)
    )
    case Lambda(body) => Lambda(raise(body, amount, bar + 1))
    case Application(fun, arg) => Application(raise(fun, amount, bar), RaisableVTerm.raise(arg, amount, bar))
    case RecordType(qn, args, effects) => RecordType(
      qn,
      args.map(RaisableVTerm.raise(_, amount, bar)),
      RaisableVTerm.raise(effects, amount, bar)
    )
    case Record(fields) => Record(fields.map(raise(_, amount, bar)))
    case Projection(rec, name) => Projection(raise(rec, amount, bar), name)
    case TypeCase(arg, cases, default) => TypeCase(
      RaisableVTerm.raise(arg, amount, bar),
      cases.view.mapValues{ case (n, c) => (n, raise(c, amount, bar + n + 1)) }.toMap,
      raise(default, amount, bar + 1)
    )
    case DataCase(arg, cases) => DataCase(
      RaisableVTerm.raise(arg, amount, bar),
      cases.view.mapValues{ case (n, c) => (n, raise(c, amount, bar + n + 1)) }.toMap
    )
    case EqualityCase(arg, body) => EqualityCase(
      RaisableVTerm.raise(arg, amount, bar),
      raise(body, amount, bar + 1)
    )
    case OperatorCall(eff, name, args) => OperatorCall(eff.map(RaisableVTerm.raise(_, amount, bar)), name, args.map(RaisableVTerm.raise(_, amount, bar)))
    case OperatorEffectMarker(outputType) => OperatorEffectMarker(raise(outputType, amount, bar))
    case Handler(eff, parameterType, inputType, outputType, transform, handlers, parameter, input) => Handler(
      eff.map(RaisableVTerm.raise(_, amount, bar)),
      RaisableVTerm.raise(parameterType, amount, bar),
      raise(inputType, amount, bar),
      raise(outputType, amount, bar),
      raise(transform, amount, bar + 1),
      handlers.view.mapValues(raise(_, amount, bar)).toMap,
      RaisableVTerm.raise(parameter, amount, bar),
      raise(input, amount, bar),
    )
    case Set(call, value) => Set(RaisableVTerm.raise(call, amount, bar), RaisableVTerm.raise(value, amount, bar))
    case Get(cell) => Get(RaisableVTerm.raise(cell, amount, bar))
    case Alloc(heap, ty) => Alloc(RaisableVTerm.raise(heap, amount, bar), RaisableVTerm.raise(ty, amount, bar))
    case HeapHandler(inputType, outputType, key, input) => HeapHandler(
      raise(inputType, amount, bar + 1),
      raise(outputType, amount, bar),
      key,
      raise(input, amount, bar + 1)
    )

given SubstitutableVTerm: Substitutable[VTerm] with
  override def substitute(v: VTerm, substitutor: Substitutor, offset: Int): VTerm = v match
    case Refl | EffectsType | LevelType | _: LevelLiteral | HeapType | GlobalHeap | _: Heap | _: Cell => v
    case VUniverse(level) => VUniverse(substitute(level, substitutor, offset))
    case LocalRef(idx) => substitutor.get(idx - offset) match
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
    case EffectsUnion(effects1, effects2) => EffectsUnion(substitute(effects1, substitutor, offset), substitute(effects2, substitutor, offset))
    case CompoundLevel(offset, operands) => CompoundLevel(offset, operands.map((v: VTerm) => substitute(v, substitutor, offset)))
    case CellType(heap, ty) => CellType(substitute(heap, substitutor, offset), substitute(ty, substitutor, offset))

given SubstitutableCTerm: Substitutable[CTerm] with
  override def substitute(c: CTerm, substitutor: Substitutor, offset: Int): CTerm = c match
    case Hole | _: GlobalRef => c
    case CUniverse(level, effects) => CUniverse(
      SubstitutableVTerm.substitute(level, substitutor, offset),
      SubstitutableVTerm.substitute(effects, substitutor, offset)
    )
    case Force(v) => Force(SubstitutableVTerm.substitute(v, substitutor, offset))
    case F(vTerm, effects) => F(SubstitutableVTerm.substitute(vTerm, substitutor, offset), SubstitutableVTerm.substitute(effects, substitutor, offset))
    case Return(v) => Return(SubstitutableVTerm.substitute(v, substitutor, offset))
    case Let(t, ctx) => Let(substitute(t, substitutor, offset), substitute(ctx, substitutor, offset))
    case DLet(t, ctx) => DLet(substitute(t, substitutor, offset), substitute(ctx, substitutor, offset))
    case FunctionType(binding, bodyTy, effects) => FunctionType(
      binding.map(SubstitutableVTerm.substitute(_, substitutor, offset)),
      substitute(bodyTy, substitutor, offset + 1),
      SubstitutableVTerm.substitute(effects, substitutor, offset)
    )
    case Lambda(body) => Lambda(substitute(body, substitutor, offset + 1))
    case Application(fun, arg) => Application(substitute(fun, substitutor, offset), SubstitutableVTerm.substitute(arg, substitutor, offset))
    case RecordType(qn, args, effects) => RecordType(
      qn,
      args.map(SubstitutableVTerm.substitute(_, substitutor, offset)),
      SubstitutableVTerm.substitute(effects, substitutor, offset)
    )
    case Record(fields) => Record(fields.map(substitute(_, substitutor, offset)))
    case Projection(rec, name) => Projection(substitute(rec, substitutor, offset), name)
    case TypeCase(arg, cases, default) => TypeCase(
      SubstitutableVTerm.substitute(arg, substitutor, offset),
      cases.view.mapValues{ case (n, c) => (n, substitute(c, substitutor, offset + n + 1)) }.toMap,
      substitute(default, substitutor, offset + 1)
    )
    case DataCase(arg, cases) => DataCase(
      SubstitutableVTerm.substitute(arg, substitutor, offset),
      cases.view.mapValues{ case (n, c) => (n, substitute(c, substitutor, offset + n + 1)) }.toMap
    )
    case EqualityCase(arg, body) => EqualityCase(
      SubstitutableVTerm.substitute(arg, substitutor, offset),
      substitute(body, substitutor, offset + 1)
    )
    case OperatorCall(eff, name, args) => OperatorCall(eff.map(SubstitutableVTerm.substitute(_, substitutor, offset)), name, args.map(SubstitutableVTerm.substitute(_, substitutor, offset)))
    case OperatorEffectMarker(outputType) => OperatorEffectMarker(substitute(outputType, substitutor, offset))
    case Handler(eff, parameterType, inputType, outputType, transform, handlers, parameter, input) => Handler(
      eff.map(SubstitutableVTerm.substitute(_, substitutor, offset)),
      SubstitutableVTerm.substitute(parameterType, substitutor, offset),
      substitute(inputType, substitutor, offset),
      substitute(outputType, substitutor, offset),
      substitute(transform, substitutor, offset + 1),
      handlers.view.mapValues(substitute(_, substitutor, offset)).toMap,
      SubstitutableVTerm.substitute(parameter, substitutor, offset),
      substitute(input, substitutor, offset),
    )
    case Set(call, value) => Set(SubstitutableVTerm.substitute(call, substitutor, offset), SubstitutableVTerm.substitute(value, substitutor, offset))
    case Get(cell) => Get(SubstitutableVTerm.substitute(cell, substitutor, offset))
    case Alloc(heap, ty) => Alloc(SubstitutableVTerm.substitute(heap, substitutor, offset), SubstitutableVTerm.substitute(ty, substitutor, offset))
    case HeapHandler(inputType, outputType, key, input) => HeapHandler(
      substitute(inputType, substitutor, offset + 1),
      substitute(outputType, substitutor, offset),
      key,
      substitute(input, substitutor, offset + 1)
    )
