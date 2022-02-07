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
    case EffectsUnion(effects1, effects2) => EffectsUnion(raise(effects1, amount, bar), raise(effects2, amount, bar))
    case EffectsLiteral(effects) => EffectsLiteral(effects.map(_.map(raise(_, amount, bar))))
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