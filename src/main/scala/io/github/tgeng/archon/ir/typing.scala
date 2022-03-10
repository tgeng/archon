package io.github.tgeng.archon.ir

import scala.collection.immutable.{ListMap, ListSet}
import io.github.tgeng.archon.common.*
import VTerm.*
import CTerm.*
import ULevel.*
import Error.*
import io.github.tgeng.archon.ir.Reducible.reduce

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

  def addEffectConstraint(cTy: CTerm, requiredEffect: VTerm)
    (using Γ: Context)
    (using Σ: Signature): Either[Error, Unit]

  def newVUnfVar()(using Γ: Context)(using Σ: Signature): VTerm

  def newCUnfVar()(using Γ: Context)(using Σ: Signature): CTerm

  def newULevelUnfVar()(using Γ: Context)(using Σ: Signature): ULevel

  def solve(cUnfVar: CTerm): Either[Error, CTerm]

  def solve(vUnfVar: VTerm): Either[Error, VTerm]

private def checkIsULevel(ul: ULevel)(using Γ: Context)
  (using Σ: Signature)
  (using sys: ConstraintSystem): Either[Error, Unit] = ul match
  case USimpleLevel(l) => checkVType(l, LevelType)
  case UωLevel(layer) =>
    assert(layer >= 0)
    Right(())

def checkIsVType(ty: VTerm)
  (using Γ: Context)
  (using Σ: Signature)
  (using sys: ConstraintSystem): Either[Error, Unit] = ty match
  case VUniverse(ul, upperBound) => checkIsULevel(ul) >> checkVType(upperBound, ty)
  case U(cty) => checkIsCType(cty) >> Right(())
  case DataType(qn, args) => checkVTypes(args, Σ.getData(qn).tParamTys)
  case EqualityType(level, ty, left, right) =>
    checkVType(level, LevelType) >>
      checkIsVType(ty) >>
      checkVType(left, ty) >>
      checkVType(right, ty)
  case EffectsType | LevelType | HeapType => Right(())
  case CellType(heap, a) => checkIsVType(a)
  case _ => Left(NotVTypeError(ty))

def checkVType(tm: VTerm, ty: VTerm)
  (using Γ: Context)
  (using Σ: Signature)
  (using sys: ConstraintSystem): Either[Error, Unit] =
  checkIsVType(ty) >>
    (tm match
      case VUniverse(ul1, upperBound1) =>
        checkIsVType(tm) >> sys.addSubtyping(VUniverse(ULevelSuc(ul1), tm), ty)
      case VTop(ul) => checkIsVType(tm) >> sys.addSubtyping(VUniverse(ul, tm), ty)
      case r: Var => sys.addSubtyping(Γ(r).ty, ty)
      case U(cty) =>
        // skip checking `tm` is a VType or `cty` is a CType because that's done during `checkCType`
        val uLevel = sys.newULevelUnfVar()
          sys
        .addSubtyping(VUniverse(uLevel, tm), ty) >>
        checkCType(cty, CUniverse(Total, uLevel, cty))
      case Thunk(c) =>
        val cty = sys.newCUnfVar()
          sys
        .addSubtyping(U(cty), ty) >> checkCType(c, cty)
      case DataType(qn, args) =>
        checkIsVType(tm) >> sys.addSubtyping(Σ.getData(qn).ty.substLowers(args: _*), ty)
      case Con(name, args) => ty match
        case DataType(qn, tArgs) =>
          val data = Σ.getData(qn)
            data
          .cons.first { c => if c.name == name then Some(c) else None } match
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
      case EffectsType => sys.addSubtyping(
        VUniverse(USimpleLevel(LevelLiteral(0)), EffectsType),
        ty
      )
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
      )

private def inferVType
(tm: VTerm)
  (using Γ: Context)
  (using Σ: Signature)
  (using sys: ConstraintSystem): Either[Error, VTerm] =
  val inferred = sys.newVUnfVar()
  checkVType(tm, inferred) >> sys.solve(inferred)

def checkVTypes(tms: List[VTerm], tys: Telescope)
  (using Γ: Context)
  (using Σ: Signature)
  (using sys: ConstraintSystem): Either[Error, Unit] =
  if tms.length != tys.length then Left(TelescopeLengthMismatch(tms, tys))
  else allRight(
    tms.zip(tys).zipWithIndex.map {
      case ((tm, binding), index) => checkVType(tm, binding.ty.substLowers(tms.take(index): _*))
    }
  )

def checkIsCType(ty: CTerm)
  (using Γ: Context)
  (using Σ: Signature)
  (using sys: ConstraintSystem): Either[Error, CTerm] =
  ty match
    case CUniverse(effects, ul, upperBound) =>
      for _ <- checkVType(effects, EffectsType)
          _ <- checkIsULevel(ul)
          upperBound <- checkIsCType(upperBound)
          _ <- checkCType(upperBound, ty)
      yield CUniverse(effects, ul, upperBound)
    case CTop(effects, ul) => checkVType(effects, EffectsType) >> checkIsULevel(ul) >> Right(ty)
    case F(effects, vTy) => checkVType(effects, EffectsType) >> checkIsVType(vTy) >> Right(ty)
    case FunctionType(effects, binding, bodyTy) =>
      for _ <- checkVType(effects, EffectsType)
          _ <- checkIsVType(binding.ty)
          bodyTy <- checkIsCType(bodyTy)(using Γ :+ binding)
      yield FunctionType(effects, binding, bodyTy)
    case RecordType(effects, qn, args) =>
      val record = Σ.getRecord(qn)
      record.ty match
        case CUniverse(effects, _, _) if effects == Total =>
          for _ <- checkVType(effects, EffectsType)
              _ <- checkVTypes(args, record.tParamTys)
          yield ty
        case CUniverse(_, _, _) => Left(EffectfulCType(ty))
        case _ => throw IllegalArgumentException(s"invalid record type declaration $qn")
    case Def(qn) =>
      val definition = Σ.getDef(qn)
      for tyTy <- checkIsCType(definition.ty)
          r <- tyTy match
            case CUniverse(effects, _, _) if effects == Total => reduce(ty)
            case _: CUniverse => Left(EffectfulCType(ty))
            case _ => Left(NotCTypeError(ty))
      yield r
    case Application(fun, arg) =>
      for funTy <- inferCType(fun)
          r <- funTy match
            case FunctionType(eff1, binding, bodyTy) if eff1 == Total =>
              for bodyTy <- checkIsCType(bodyTy.substLowers(arg))
                  r <- bodyTy match
                    case CUniverse(eff2, _, _) if eff2 == Total => reduce(ty)
                    case _: CUniverse => Left(EffectfulCType(ty))
                    case _ => Left(NotCTypeError(bodyTy))
              yield r
            case _: FunctionType => Left(EffectfulCType(ty))
            case _ => Left(NotCTypeError(ty))
      yield r
    case Projection(rec, name) =>
      for recTy <- inferCType(rec)
          r <- recTy match
            case RecordType(eff1, qn, args) if eff1 == Total =>
              val rec = Σ.getRecord(qn)
              rec.fields.first { f => if f.name == name then Some(f) else None } match
                case None => throw IllegalArgumentException(s"nonexistent field $name in record $qn")
                case Some(f) => f.ty match
                  case CUniverse(eff2, _, _) if eff2 == Total => reduce(ty)
                  case _: CUniverse => Left(EffectfulCType(ty))
                  case _ => Left(NotCTypeError(ty))
            case _: RecordType => Left(EffectfulCType(ty))
            case _ => Left(NotCTypeError(ty))
      yield r
    case Force(v) =>
      for vTy <- inferVType(v)
          r <- vTy match
            case U(CUniverse(effects, _, _)) =>
              if effects == Total then reduce(ty)
              else Left(EffectfulCType(ty))
            case _ => Left(NotCTypeError(ty))
      yield r
    case Let(t, binding, ctx) =>
      val eff1 = sys.newVUnfVar()
      for _ <- checkCType(t, F(eff1, binding.ty))
          r <- if eff1 == Total then
            for ctxTy <- inferCType(ctx)(using Γ :+ binding)
                r <- ctxTy match
                  case CUniverse(eff2, _, _) if eff2 == Total => reduce(ty)
                  case _: CUniverse => Left(EffectfulCType(ty))
                  case _ => Left(NotCTypeError(ty))
            yield r
          else
            Left(EffectfulCType(ty))
      yield r
    case Handler(_, _, outputType, _, _, _) =>
      for outputType <- checkIsCType(outputType)
          r <- outputType match
            case CUniverse(eff, _, _) if eff == Total => reduce(ty)
            case _: CUniverse => Left(EffectfulCType(ty))
            case _ => Left(NotCTypeError(ty))
      yield r
    case HeapHandler(_, outputType, _, _, _) =>
      for outputType <- checkIsCType(outputType)
          r <- outputType match
            case CUniverse(eff, _, _) if eff == Total => reduce(ty)
            case _: CUniverse => Left(EffectfulCType(ty))
            case _ => Left(NotCTypeError(ty))
      yield r
    case _ => Left(NotCTypeError(ty))

private def inferCType
(tm: CTerm)
  (using Γ: Context)
  (using Σ: Signature)
  (using sys: ConstraintSystem): Either[Error, CTerm] =
  val inferred = sys.newCUnfVar()
  checkCType(tm, inferred) >> sys.solve(inferred)

def checkCType(tm: CTerm, ty: CTerm)
  (using Γ: Context)
  (using Σ: Signature)
  (using sys: ConstraintSystem): Either[Error, Unit] =
  for ty <- checkIsCType(ty)
      r <- tm match
        case Hole => throw IllegalArgumentException("hole should only be present during reduction")
        case CUniverse(effects, ul, upperBound) => checkIsCType(tm) >>
          sys.addSubtyping(CUniverse(effects, ULevelSuc(ul), tm), ty)
        case CTop(effects, ul) =>
          checkIsCType(tm) >>
            sys.addSubtyping(CUniverse(effects, ul, tm), ty)
        case Def(qn) => sys.addSubtyping(Σ.getDef(qn).ty, ty)
        case Force(v) => checkVType(v, U(ty))
        case F(effects, vTy) =>
          val uLevel = sys.newULevelUnfVar()
          checkIsCType(tm) >>
            sys.addSubtyping(CUniverse(Total, uLevel, tm), ty) >>
            checkVType(vTy, VUniverse(uLevel, vTy))
        case Return(v) => ty match
          case F(eff, vTy) => checkVType(v, vTy)
          case _ =>
            val vTy = sys.newVUnfVar()
            checkVType(v, vTy) >>
              sys.addSubtyping(F(Total, vTy), ty)
        case Let(t, binding, ctx) =>
          val eff = sys.newVUnfVar()
          checkCType(t, F(eff, binding.ty)) >>
            sys.addEffectConstraint(ty, eff) >>
            checkCType(ctx, ty.weakened)(using Γ :+ binding)
        case FunctionType(effects, binding, bodyTy) =>
          val ul = sys.newULevelUnfVar()
          checkIsCType(tm) >>
            checkVType(binding.ty, VUniverse(ul, binding.ty)) >>
            checkCType(bodyTy, CUniverse(Total, ul, bodyTy)) >>
            sys.addSubtyping(CUniverse(Total, ul, tm), ty)
        case Application(fun, arg) =>
          for funTy <- inferCType(fun)
              r <- funTy match
                case FunctionType(effects, binding, bodyTy) =>
                  checkVType(arg, binding.ty) >>
                    sys.addSubtyping(bodyTy.substLowers(arg), ty) >>
                    sys.addEffectConstraint(ty, effects)
                // TODO: case UnfVar => Left(UnificationFailure(...))
                case _ => Left(CTypeError(tm, ty))
          yield r
        case RecordType(effects, qn, args) =>
          val record = Σ.getRecord(qn)
          checkIsCType(tm) >>
            checkVTypes(args, record.tParamTys) >>
            sys.addSubtyping(record.ty.substLowers(args: _*), ty)
        case Projection(rec, name) =>
          for recTy <- inferCType(rec)
              r <- recTy match
                case RecordType(effects, qn, args) =>
                  val record = Σ.getRecord(qn)
                  record.fields.first { f => if f.name == name then Some(f) else None } match
                    case None => throw IllegalArgumentException(s"unexpected record field $name for $qn")
                    case Some(f) =>
                      sys.addSubtyping(f.ty.substLowers(args :+ Thunk(tm): _*), ty) >>
                        sys.addEffectConstraint(ty, effects)
                // TODO: case UnfVar => Left(UnificationFailure(...))
                case _ => Left(CTypeError(tm, ty))
          yield r
        case OperatorCall(eff@(qn, tArgs), name, args) =>
          val effect = Σ.getEffect(qn)
          effect.operators.first { o => if o.name == name then Some(o) else None } match
            case None => throw IllegalArgumentException(s"unexpected operator $name for $qn")
            case Some(op) => checkVTypes(tArgs, effect.tParamTys) >>
              checkVTypes(args, op.paramTys.substLowers(tArgs: _*)) >>
              sys.addSubtyping(
                F(
                  EffectsLiteral(ListSet(eff)),
                  op.resultTy.substLowers(tArgs ++ args: _*)
                ), ty
              )
        case _: Continuation => throw IllegalArgumentException(
          "continuation is only created in reduction and hence should not be type checked."
        )
        case Handler(eff, inputType, outputType, transform, handlers, input) => ???
        case Alloc(heap, vTy) => checkIsVType(vTy) >>
          sys.addSubtyping(
            F(
              EffectsLiteral(ListSet((Builtins.HeapEf, heap :: Nil))),
              CellType(heap, vTy),
            ),
            ty
          )
        case Set(cell, value) =>
          val vTy = sys.newVUnfVar()
          val heap = sys.newVUnfVar()
          checkVType(cell, CellType(heap, vTy)) >>
            checkVType(value, vTy) >>
            sys.addSubtyping(
              F(
                EffectsLiteral(ListSet((Builtins.HeapEf, heap :: Nil))),
                Builtins.UnitTy
              ),
              ty
            )
        case Get(cell) =>
          val vTy = sys.newVUnfVar()
          val heap = sys.newVUnfVar()
          checkVType(cell, CellType(heap, vTy)) >>
            sys.addSubtyping(
              F(
                EffectsLiteral(ListSet((Builtins.HeapEf, heap :: Nil))),
                vTy
              ),
              ty
            )
        case HeapHandler(inputType, outputType, key, heapContent, input) => ???
  yield r

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
