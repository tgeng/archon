package io.github.tgeng.archon.ir

import scala.collection.immutable.{ListMap, ListSet}
import io.github.tgeng.archon.common.*
import VTerm.*
import CTerm.*
import ULevel.*
import Error.*

trait ConstraintSystem:
  /**
   * Note that subsumption on non-types or values other than level and effects is treated as
   * equivalence. That is, `addSubsumption(Nat(1), Nat(2), Nat)` is an error yet
   * `addSubsumption(LevelLLiteral(1), LevelLiteral(2), LevelType)` succeeds.
   */
  def addSubsumption(sub: VTerm, sup: VTerm, ty: VTerm)
    (using Γ: Context)
    (using Σ: Signature): Either[Error, Unit]

  def addSubsumption(sub: CTerm, sup: CTerm, ty: CTerm)
    (using Γ: Context)
    (using Σ: Signature): Either[Error, Unit]

  def addSubtyping(sub: VTerm, sup: VTerm)
    (using Γ: Context)
    (using Σ: Signature): Either[Error, Unit]

  def addSubtyping(sub: CTerm, sup: CTerm)
    (using Γ: Context)
    (using Σ: Signature): Either[Error, Unit]

  def addULevelSubsumption(sub: ULevel, sup: ULevel)
    (using Γ: Context)
    (using Σ: Signature): Either[Error, Unit] =
    (sub, sup) match
      case (USimpleLevel(l1), USimpleLevel(l2)) =>
        addSubsumption(l1, l2, LevelType)
      case (UωLevel(layer1), UωLevel(layer2)) =>
        if layer1 <= layer2 then
          Right(())
        else
          Left(ULevelError(sub, sup))
      case (_, _: UωLevel) => Right(())
      case _ => Left(ULevelError(sub, sup))

  def newVUnfVar()(using Γ: Context)(using Σ: Signature): VTerm

  def newCUnfVar()(using Γ: Context)(using Σ: Signature): CTerm

  def newULevelUnfVar()(using Γ: Context)(using Σ: Signature): ULevel

def checkIsVType(ty: VTerm)
  (using Γ: Context)
  (using Σ: Signature)
  (using sys: ConstraintSystem): Either[Error, Unit] = ???

def checkVType(tm: VTerm, ty: VTerm)
  (using Γ: Context)
  (using Σ: Signature)
  (using sys: ConstraintSystem): Either[Error, Unit] =
  tm match
    case VUniverse(ul1, upperBound1) =>
      checkVType(upperBound1, tm) >>
        sys.addSubtyping(VUniverse(ULevelSuc(ul1), tm), ty)
    case VTop(ul) => sys.addSubtyping(VUniverse(ul, tm), ty)
    case r: Var => sys.addSubtyping(Γ(r).ty, ty)
    case U(cty) =>
      val uLevel = sys.newULevelUnfVar()
      sys.addSubtyping(VUniverse(uLevel, tm), ty) >>
        checkCType(cty, CUniverse(Total, uLevel, cty))
    case Thunk(c) =>
      val cty = sys.newCUnfVar()
      sys.addSubtyping(U(cty), ty) >> checkCType(c, cty)
    case DataType(qn, args) =>
          val data = Σ.getData(qn)
          sys.addSubtyping(data.ty.substLowers(args: _*), ty) >>
            checkVTypes(args, data.tParamTys)
    case Con(name, args) => ty match
          case DataType(qn, tArgs) =>
            val data = Σ.getData(qn)
            data.cons.first { c => if c.name == name then Some(c) else None } match
              case None => Left(VTypeError(tm, ty))
              case Some(con) => checkVTypes(args, con.paramTys.substLowers(tArgs: _*))
          case _ => Left(VTypeError(tm, ty))
    case EqualityType(l, a, left, right) =>
      sys.addSubtyping(VUniverse(USimpleLevel(l), tm), ty) >>
        checkVType(a, VUniverse(USimpleLevel(l), a)) >>
        checkVType(left, a) >>
        checkVType(right, a)
    case Refl => ty match
      case EqualityType(level, ty, left, right) =>
        sys.addSubsumption(left, right, ty) >> sys.addSubsumption(right, left, ty)
      case _ => Left(VTypeError(tm, ty))
    case EffectsType => sys.addSubtyping(VUniverse(USimpleLevel(LevelLiteral(0)), EffectsType), ty)
    case Effects(literal, unionOperands) =>
      sys.addSubtyping(EffectsType, ty) >>
        allRight(
          literal.map { (qn, args) =>
            val effect = Σ.getEffect(qn)
            checkVTypes(args, effect.tParamTys)
          }
        ) >>
        allRight(unionOperands.map { ref => checkVType(ref, EffectsType) })
    case LevelType => sys.addSubtyping(VUniverse(USimpleLevel(LevelLiteral(0)), LevelType), ty)
    case Level(literal, maxOperands) =>
      sys.addSubtyping(LevelType, ty) >>
        allRight(maxOperands.map { (ref, _) => checkVType(ref, LevelType) })
    case HeapType => sys.addSubtyping(VUniverse(USimpleLevel(LevelLiteral(0)), HeapType), ty)
    case Heap(_) => sys.addSubtyping(HeapType, ty)
    case CellType(heap, a) => checkVType(heap, HeapType) >> checkVType(a, ty)
    case Cell(heapKey, _, a) => sys.addSubtyping(CellType(Heap(heapKey), a), ty)

def checkIsCType(ty: CTerm)
  (using Γ: Context)
  (using Σ: Signature)
  (using sys: ConstraintSystem): Either[Error, Unit] = ???

def checkVTypes(tms: List[VTerm], tys: Telescope)
  (using Γ: Context)
  (using Σ: Signature)
  (using sys: ConstraintSystem): Either[Error, Unit] =
  if tms.length != tys.length then Left(TelescopeLengthMismatch(tms, tys))
  else allRight(
    tms.zip(tys).map { (tm, binding) => checkVType(tm, binding.ty) }
  )

def checkCType(tm: CTerm, ty: CTerm)
  (using Γ: Context)
  (using Σ: Signature)
  (using sys: ConstraintSystem): Either[Error, Unit] =
  ???
//  tm match
//    case Hole => throw IllegalArgumentException(s"$tm not expected for type checking")
//    case CUniverse(effects, l1) =>
//      sys.addEquality(ty, CUniverse(Total, LevelSuc(l1))) >>
//        checkVType(effects, EffectsType) >>
//        checkVType(l1, LevelType)
//    case Def(qn) =>
//      val definition = Σ.getDef(qn)
//      sys.addEquality(ty, definition.ty)
//    case Force(v) => checkVType(v, U(ty))
//    case F(effects, vTerm) =>
//      val level = sys.newHole(LevelType)
//      sys.addEquality(ty, CUniverse(Total, level)) >>
//        checkVType(effects, EffectsType) >> checkVType(vTerm, VUniverse(level))
//    case Return(v) =>
//      val level = sys.newHole(LevelType)
//      val vTy = sys.newHole(VUniverse(level))
//      sys.addEquality(ty, F(Total, vTy)) >> checkVType(v, vTy)
//    case _ => ???

//private def checkIsSomeType(vTerm: VTerm)
//  (using Γ: Context)
//  (using Σ: Signature)
//  (using sys: ConstraintSystem): Either[Error, Unit] =
//  val level = sys.newHole(LevelType)
//  checkVType(vTerm, VUniverse(level, VTop(level)))
//
//private def checkIsSomeType(cTerm: CTerm, effects: VTerm = Total)
//  (using Γ: Context)
//  (using Σ: Signature)
//  (using sys: ConstraintSystem): Either[Error, Unit] =
//  val level = sys.newHole(LevelType)
//  checkCType(cTerm, CUniverse(effects, level, CTop(level)))

def allRight[L](es: Iterable[Either[L, ?]]): Either[L, Unit] =
  es.first {
    case Left(l) => Some(l)
    case _ => None
  } match
    case Some(l) => Left(l)
    case _ => Right(())

extension[L, R1] (e1: Either[L, R1])
  private inline infix def >>[R2](e2: Either[L, R2]): Either[L, R2] = e1.flatMap(_ => e2)
