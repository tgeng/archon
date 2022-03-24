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
    case Type(ul, Some(upperBound), effects) => CType(effects, ul, upperBound)
    case Type(ul, None, effects) => CType(effects, ul, CTop(Total, ul))

  given Conversion[CTerm, VTerm] = Thunk(_)

  given Conversion[VTerm, CTerm] = Return(_)

  extension (i: Int)
    infix def unary_! = Var(i)
    infix def unary_~ = UωLevel(i)

  extension (tm: VTerm)
    infix def ∪(tm2: VTerm) = LevelMax(tm, tm2)

  case class SomeCall[F, A](f: F, args: List[A])

  extension (qn: QualifiedName)
    def apply(args: VTerm*) = SomeCall(qn, args.toList)

  extension (n: Name)
    def apply(args: VTerm*) = SomeCall(n, args.toList)

  given(using Σ: Signature): Conversion[SomeCall[QualifiedName, VTerm], VTerm] = _ match
    case SomeCall(qn, args) =>
      Σ.getDataOption(qn).map(_ => DataType(qn, args)).orElse(
        Σ.getEffectOption(qn).map(_ => EffectsLiteral(ListSet((qn, args))))
      ).get

  given Conversion[SomeCall[Name, VTerm], VTerm] = _ match
    case SomeCall(n, args) => Con(n, args)

  given(using Σ: Signature): Conversion[SomeCall[QualifiedName, Either[Name, VTerm]], CTerm] = _ match
    case SomeCall(qn, args) =>
      Σ.getRecordOption(qn).flatMap { record =>
        if record.tParamTys.size == args.size then
          Some(RecordType(Total, qn, args.map(_.asRight)))
        else
          None
      }.orElse(
        Σ.getDefinitionOption(qn).map { _ =>
          args.foldLeft(Def(qn)){
            case (f, Right(t)) => Application(f, t)
            case (f, Left(n)) => Projection(f, n)
          }
        }
      ).get