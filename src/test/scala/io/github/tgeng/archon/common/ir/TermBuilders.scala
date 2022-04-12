package io.github.tgeng.archon.common.ir

import io.github.tgeng.archon.common.*
import io.github.tgeng.archon.ir.*
import ULevel.*
import VTerm.*
import CTerm.*

import scala.collection.immutable.ListSet

object TermBuilders:

  given Conversion[Long, ULevel] = i => USimpleLevel(LevelLiteral(i.toInt))

  given Conversion[Long, VTerm] = i => LevelLiteral(i.toInt)

  given Conversion[VTerm, ULevel] = USimpleLevel(_)

  case class Type[+T](ul: ULevel, upperBound: Option[T] = None, effects: Effects = Total)

  given Conversion[Type[VTerm], VTerm] = _ match
    case Type(ul, Some(upperBound), _) => VType(ul, upperBound)
    case Type(ul, None, _) => VType(ul, VTop(ul))

  given Conversion[Type[CTerm], CTerm] = _ match
    case Type(ul, Some(upperBound), effects) => CType(ul, upperBound, effects)
    case Type(ul, None, effects) => CType(ul, CTop(ul, Total), effects)

  given Conversion[CTerm, VTerm] = Thunk(_)

  given Conversion[VTerm, CTerm] = Return(_)

  extension (i: Int)
    infix def unary_! = Var(i)

  extension (tm: VTerm)
    infix def ∨(tm2: VTerm) = LevelMax(tm, tm2)
    infix def ∪(tm2: VTerm) = EffectsUnion(tm, tm2)

  enum Elim:
    case Arg(v: VTerm)
    case Proj(n: Name)

  import Elim.*

  case class SomeCall[F](f: F, args: List[Elim])

  given(using Σ: Signature): Conversion[SomeCall[QualifiedName], Elim] = Elim.Arg(_)

  given(using Σ: Signature): Conversion[SomeCall[QualifiedName], VTerm] = _ match
    case SomeCall(qn, elims) =>
      val args = elims.map(_.asInstanceOf[Arg].v)
      Σ.getDataOption(qn).map(_ => DataType(qn, args)).orElse(
        Σ.getEffectOption(qn).map(_ => EffectsLiteral(ListSet((qn, args))))
      ).get

  given(using Σ: Signature): Conversion[SomeCall[QualifiedName], Eff] = _ match
    case SomeCall(qn, elims) =>
      val args = elims.map(_.asInstanceOf[Arg].v)
      Σ.getEffectOption(qn).map(_ => (qn, args)).get

  def op(eff: Eff, name: Name, args: VTerm*) = OperatorCall(eff, name, args.toList)

  given Conversion[SomeCall[Name], VTerm] = _ match
    case SomeCall(n, elims) => Con(n, elims.map(_.asInstanceOf[Arg].v))

  given(using Σ: Signature): Conversion[SomeCall[QualifiedName], Binding[VTerm]] =
    c => Binding(v(c))(gn"arg")

  extension (qn: QualifiedName)
    def apply(elims: Elim*) = SomeCall(qn, elims.toList)

  extension (n: Name)
    def apply(elims: Elim*) = SomeCall(n, elims.toList)

  extension (tm: CTerm)
    def apply(elims: Elim*) = elims.foldLeft(tm) {
      case (f, Arg(t)) => Application(f, t)
      case (f, Proj(n)) => Projection(f, n)
    }

    infix def >>=:(ctx: CTerm) = Let(tm, ctx)

  extension (argTy: VTerm)
    infix def ->:(bodyTy: CTerm) = FunctionType(Binding(argTy)(gn"Arg"), bodyTy, Total)

    infix def ->:(effAndBody: (VTerm, CTerm)) =
      FunctionType(
        Binding(argTy)(gn"Arg"),
        effAndBody._2,
        effAndBody._1
      )

  given Conversion[VTerm, Elim] = Arg(_)

  given Conversion[Name, Elim] = Proj(_)

  given(using Σ: Signature): Conversion[SomeCall[QualifiedName], CTerm] = _ match
    case SomeCall(qn, elims) =>
      Σ.getRecordOption(qn).flatMap { record =>
        if record.tParamTys.size == elims.size then
          Some(RecordType(qn, elims.map(_.asInstanceOf[Arg].v), Total))
        else
          None
      }.orElse(
        Σ.getDefinitionOption(qn).map { _ =>
          elims.foldLeft(Def(qn)) {
            case (f, Arg(t)) => Application(f, t)
            case (f, Proj(n)) => Projection(f, n)
          }
        }
      ).get

  given Conversion[SomeCall[Name], Elim] = Elim.Arg(_)

  given Conversion[SomeCall[Name], Constructor] = _ match
    case SomeCall(n, elims) => Constructor(n, elims.map(_.asInstanceOf[Arg].v))

  given Conversion[VTerm, Binding[VTerm]] = Binding(_)(gn"_")

  def v(tm: VTerm): VTerm = tm

  def c(tm: CTerm): CTerm = tm

  def constructor(name: Name, args: Binding[VTerm]*)
    (equalities: Binding[VTerm.EqualityType]*): Constructor =
    Constructor(name, args.toList, equalities.toList)
