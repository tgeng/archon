package io.github.tgeng.archon.ir

import scala.collection.immutable.{ListMap, ListSet}
import io.github.tgeng.archon.common.*
import VTerm.*
import CTerm.*
import Error.*

trait ConstraintSystem:
  def addEquality(t1: VTerm, t2: VTerm)(using Γ: Context)(using Σ: Signature): Either[Error, Unit]

  def addEquality(t1: CTerm, t2: CTerm)(using Γ: Context)(using Σ: Signature): Either[Error, Unit]

  def newVHole(ty: VTerm)(using Γ: Context)(using Σ: Signature): VTerm

  def newCHole(ty: CTerm)(using Γ: Context)(using Σ: Signature): CTerm

def checkVType(tm: VTerm, ty: VTerm)
  (using Γ: Context)
  (using Σ: Signature)
  (using sys: ConstraintSystem): Either[Error, Unit] =
  tm match
    case VUniverse(l1) =>
      sys.addEquality(VUniverse(LevelSuc(l1)), ty) >>
        checkVType(l1, LevelType)
    case r: Var => sys.addEquality(Γ(r).ty, ty)
    case U(cty) =>
      val level = sys.newVHole(LevelType)
      sys.addEquality(ty, VUniverse(level)) >> checkCType(cty, CUniverse(Total, level))
    case Thunk(c) =>
      val level = sys.newVHole(LevelType)
      val cty = sys.newCHole(CUniverse(Total, level))
      sys.addEquality(ty, U(cty)) >> checkCType(c, cty)
    case DataType(qn, args) =>
      val data = Σ.getData(qn)
      sys.addEquality(data.ty.substLowers(args: _*), ty) >>
        checkVTypes(args, data.paramTys)
    case Con(name, args) => ty match
      case DataType(qn, tArgs) =>
        val data = Σ.getData(qn)
        data.cons.first { c => if c.name == name then Some(c) else None } match
          case None => Left(VTypeError(tm, ty))
          case Some(con) => checkVTypes(args, con.argTys.substLowers(tArgs: _*))
      case _ => Left(VTypeError(tm, ty))
    case EqualityType(level, ty1, left, right) =>
      sys.addEquality(VUniverse(level), ty) >>
        checkVType(ty1, VUniverse(level)) >>
        checkVType(left, ty1) >>
        checkVType(right, ty1)
    case Refl =>
      val level = sys.newVHole(LevelType)
      val a = sys.newVHole(VUniverse(level))
      val t = sys.newVHole(a)
      sys.addEquality(ty, EqualityType(level, a, t, t))
    case EffectsType => sys.addEquality(ty, VUniverse(LevelLiteral(0)))
    case Effects(literal, unionOperands) =>
      sys.addEquality(ty, EffectsType) >>
        allRight(
          literal.map { (qn, args) =>
            val effect = Σ.getEffect(qn)
            checkVTypes(args, effect.paramTys)
          }
        ) >>
        allRight(unionOperands.map { ref => checkVType(ref, EffectsType) })
    case LevelType => sys.addEquality(ty, VUniverse(LevelLiteral(0)))
    case Level(literal, maxOperands) =>
      sys.addEquality(ty, LevelType) >>
        allRight(maxOperands.map { (ref, _) => checkVType(ref, LevelType) })
    case HeapType => sys.addEquality(ty, VUniverse(LevelLiteral(0)))
    case Heap(_) => sys.addEquality(ty, HeapType)
    case CellType(heap, ty1) =>
      val level = sys.newVHole(LevelType)
      val u = sys.newVHole(VUniverse(level))
      sys.addEquality(ty, u) >>
        checkVType(ty1, u) >>
        checkVType(heap, HeapType)
    case Cell(heapKey, _, a) =>
      val level = sys.newVHole(LevelType)
      val u = sys.newVHole(VUniverse(level))
      sys.addEquality(ty, CellType(Heap(heapKey), a)) >>
        checkVType(a, u)

def checkVTypes(tms: List[VTerm], tys: Telescope)
  (using Γ: Context)
  (using Σ: Signature)
  (using sys: ConstraintSystem): Either[Error, Unit] =
  if tms.length != tys.length then Left(TelescopeLengthMismatch(tms, tys))
  else allRight(tms.zip(tys).map{ (tm, binding) => checkVType(tm, binding.ty) })

def checkCType(tm: CTerm, ty: CTerm)
  (using Γ: Context)
  (using Σ: Signature)
  (using sys: ConstraintSystem): Either[Error, Unit] = tm match
  case Computation => throw IllegalArgumentException(s"$tm not expected for type checking")
  case CUniverse(effects, l1) =>
    sys.addEquality(ty, CUniverse(Total, LevelSuc(l1))) >>
      checkVType(effects, EffectsType) >>
      checkVType(l1, LevelType)
  case Def(qn) =>
    val definition = Σ.getDef(qn)
    sys.addEquality(ty, definition.ty)
  case Force(v) => ???
  case _ => ???

def allRight[L](es: Iterable[Either[L, ?]]): Either[L, Unit] =
  es.first {
    case Left(l) => Some(l)
    case _ => None
  } match
    case Some(l) => Left(l)
    case _ => Right(())

extension[L, R1] (e1: Either[L, R1])
  private inline infix def >>[R2](e2: Either[L, R2]): Either[L, R2] = e1.flatMap(_ => e2)
