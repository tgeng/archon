package io.github.tgeng.archon.ir

import scala.collection.immutable.{ListMap, ListSet}
import io.github.tgeng.archon.common.*
import io.github.tgeng.archon.ir.Reducible.reduce
import VTerm.*
import CTerm.*
import ULevel.*
import Error.*

import javax.swing.text.WrappedPlainView

trait TypingContext

private def checkULevel(ul: ULevel)
  (using Γ: Context)
  (using Σ: Signature)
  (using ctx: TypingContext)
: Either[Error, Unit] = ul match
  case ULevel.USimpleLevel(l) => checkType(l, LevelType)
  case _ => Right(())

def inferType(tm: VTerm)
  (using Γ: Context)
  (using Σ: Signature)
  (using ctx: TypingContext)
: Either[Error, VTerm] = tm match
  case VUniverse(level, upperBound) =>
    checkULevel(level) >>
      checkType(upperBound, tm) >>
      Right(VUniverse(ULevelSuc(level), tm))
  case Pure(ul) => Right(VUniverse(ul, tm))
  case VTop(ul) => Right(VUniverse(ul, tm))
  case r: Var => Right(Γ(r).ty)
  case U(cty) =>
    for ctyTy <- inferType(cty)
        r <- ctyTy match
          case CUniverse(eff, ul, _) if eff == Total => Right(VUniverse(ul, tm))
          case CUniverse(_, ul, _) => Left(EffectfulCType(cty))
          case _ => Left(NotVTypeError(tm))
    yield r
  case Thunk(c) =>
    for cty <- inferType(c)
      yield U(cty)
  case DataType(qn, args) =>
    val data = Σ.getData(qn)
    checkTypes(args, data.tParamTys.map(_._1)) >> Right(data.ty.substLowers(args: _*))
  case _: Con => throw IllegalArgumentException("cannot infer type")
  case EqualityType(level, ty, left, right) =>
    val ul = USimpleLevel(level)
    checkType(ty, VUniverse(ul, ty)) >>
      checkType(left, ty) >>
      checkType(right, ty) >>
      Right(VUniverse(ul, tm))
  case Refl => throw IllegalArgumentException("cannot infer type")
  case EffectsType => Right(VUniverse(ULevel.USimpleLevel(LevelLiteral(0)), EffectsType))
  case Effects(literal, unionOperands) =>
    allRight(
      literal.map { (qn, args) =>
        val effect = Σ.getEffect(qn)
        checkTypes(args, effect.tParamTys)
      }
    ) >> allRight(
      unionOperands.map { ref => checkType(ref, EffectsType) }
    ) >> Right(EffectsType)
  case LevelType => Right(VUniverse(UωLevel(0), LevelType))
  case Level(literal, maxOperands) =>
    allRight(maxOperands.map { (ref, _) => checkType(ref, LevelType) }) >> Right(LevelType)
  case HeapType => Right(VUniverse(USimpleLevel(LevelLiteral(0)), HeapType))
  case _: Heap => Right(HeapType)
  case CellType(heap, ty, _) =>
    for _ <- checkType(heap, HeapType)
        tyTy <- inferType(ty)
        r <- tyTy match
          case _: VUniverse => Right(tyTy)
          case _ => Left(NotVTypeError(ty))
    yield r
  case Cell(heapKey, _) => throw IllegalArgumentException("cannot infer type")

def checkType(tm: VTerm, ty: VTerm)
  (using Γ: Context)
  (using Σ: Signature)
  (using ctx: TypingContext)
: Either[Error, Unit] =
  checkIsType(ty) >>
    (tm match
      case Con(name, args) => ty match
        case DataType(qn, tArgs) =>
          val data = Σ.getData(qn)
            data
          .cons.first { c => if c.name == name then Some(c) else None } match
          case None => Left(MissingConstructor(name, qn))
          case Some(con) => checkTypes(args, con.paramTys.substLowers(tArgs: _*))
        case _ => Left(ExpectDataType(ty))
      case Refl => ty match
        case EqualityType(level, ty, left, right) => checkConversion(left, right, Some(ty))
        case _ => Left(ExpectEqualityType(ty))
      case Cell(heapKey, _) => ty match
        case CellType(heap, _, _) if Heap(heapKey) == heap => Right(())
        case _: CellType => Left(ExpectCellTypeWithHeap(heapKey))
        case _ => Left(ExpectCellType(ty))
      case _ =>
        for inferred <- inferType(tm)
            r <- checkSubsumption(inferred, ty, None)
        yield r)

def inferType(tm: CTerm)
  (using Γ: Context)
  (using Σ: Signature)
  (using ctx: TypingContext)
: Either[Error, CTerm] = tm match
  case Hole => throw IllegalArgumentException("hole should only be present during reduction")
  case CUniverse(effects, ul, upperBound) =>
    checkType(effects, EffectsType) >>
      checkULevel(ul) >>
      checkType(upperBound, tm) >>
      Right(CUniverse(Total, ULevelSuc(ul), tm))
  case CTop(effects, ul) =>
    checkType(effects, EffectsType) >>
      checkULevel(ul) >>
      Right(CUniverse(Total, ul, tm))
  case Def(qn) => Right(Σ.getDef(qn).ty)
  case Force(v) =>
    for vTy <- inferType(v)
        r <- vTy match
          case U(cty) => Right(cty)
          case _ => Left(ExpectUType(vTy))
    yield r
  case F(effects, vTy) =>
    for _ <- checkType(effects, EffectsType)
        vTyTy <- inferType(vTy)
        r <- vTyTy match
          case VUniverse(ul, _) => Right(CUniverse(Total, ul, tm))
          case _ => Left(NotVTypeError(vTy))
    yield r
  case Return(v) =>
    for vTy <- inferType(v)
      yield F(Total, vTy)
  case Let(t, effects, binding, ctx) =>
    for _ <- checkIsType(binding.ty)
        _ <- checkType(t, F(effects, binding.ty))
        ctxTy <- if effects == Total then
        // Do the reduction onsite so that type checking in sub terms can leverage the more specific
        // type.
          for t <- reduce(t)
              r <- t match
                case Return(v) => inferType(ctx.substLowers(v))
                case _ => throw IllegalStateException(
                  "impossible since we have checked type of t to be F(...)"
                )
          yield r
        // Otherwise, just add the binding to the context and continue type checking.
        else inferType(ctx)(using Γ :+ binding).map(_.weakened)
    // TODO: in case weakened failed, provide better error message: ctxTy cannot depend on
    //  the bound variable
    yield augmentEffect(effects, ctxTy)
  case FunctionType(effects, binding, bodyTy) =>
    for _ <- checkType(effects, EffectsType)
        tyTy <- inferType(binding.ty)
        r <- tyTy match
          case VUniverse(ul1, _) =>
            for bodyTyTy <- inferType(bodyTy)(using Γ :+ binding)
                r <- bodyTyTy match
                  case CUniverse(_, ul2, _) => Right(
                    CUniverse(
                      Total,
                      ULevelMax(ul1, ul2.weakened),
                      tm
                    )
                  )
                  case _ => Left(NotCTypeError(bodyTy))
            yield r
          case _ => Left(NotVTypeError(binding.ty))
    yield r
  case Application(fun, arg) =>
    for funTy <- inferType(fun)
        r <- funTy match
          case FunctionType(effects, binding, bodyTy) =>
            checkType(arg, binding.ty) >>
              Right(augmentEffect(effects, bodyTy.substLowers(arg)))
          case _ => Left(ExpectFunction(fun))
    yield r
  case RecordType(effects, qn, args) =>
    val record = Σ.getRecord(qn)
    checkType(effects, EffectsType) >>
      checkTypes(args, record.tParamTys.map(_._1)) >>
      Right(record.ty.substLowers(args: _*))
  case Projection(rec, name) =>
    for recTy <- inferType(rec)
        r <- recTy match
          case RecordType(effects, qn, args) =>
            val record = Σ.getRecord(qn)
            record.fields.first { f => if f.name == name then Some(f) else None } match
              case None => throw IllegalArgumentException(s"unexpected record field $name for $qn")
              case Some(f) => Right(augmentEffect(effects, f.ty.substLowers(args :+ Thunk(tm): _*)))
          case _ => Left(ExpectRecord(rec))
    yield r
  case OperatorCall(eff@(qn, tArgs), name, args) =>
    val effect = Σ.getEffect(qn)
    effect.operators.first { o => if o.name == name then Some(o) else None } match
      case None => throw IllegalArgumentException(s"unexpected operator $name for $qn")
      case Some(op) => checkTypes(tArgs, effect.tParamTys) >>
        checkTypes(args, op.paramTys.substLowers(tArgs: _*)) >>
        Right(F(EffectsLiteral(ListSet(eff)), op.resultTy.substLowers(tArgs ++ args: _*)))
  case _: Continuation => throw IllegalArgumentException(
    "continuation is only created in reduction and hence should not be type checked."
  )
  case Handler(
  eff@(qn, args),
  inputBinding,
  otherEffects,
  outputType,
  transform,
  handlers,
  input
  ) =>
    val effect = Σ.getEffect(qn)
    if handlers.size != effect.operators.size ||
      handlers.keySet != effect.operators.map(_.name).toSet then
      Left(UnmatchedHandlerImplementation(qn, handlers.keys))
    else
      val outputCType = F(otherEffects, outputType)
      for _ <- checkTypes(args, effect.tParamTys)
          _ <- checkIsType(inputBinding.ty)
          _ <- checkType(
            input,
            F(EffectsUnion(EffectsLiteral(ListSet(eff)), otherEffects), inputBinding.ty)
          )
          _ <- checkType(transform, outputCType.weakened)(using Γ :+ inputBinding)
          _ <- allRight(
            effect.operators.map { opDecl =>
              val (n, handlerBody) = handlers(opDecl.name)
              assert(n == opDecl.paramTys.size)
              checkType(
                handlerBody,
                outputCType.weaken(n + 1, 0)
              )(
                using Γ ++
                  opDecl.paramTys :+
                  Binding(
                    U(
                      FunctionType(
                        otherEffects,
                        Binding(opDecl.resultTy)(gn"output"),
                        F(otherEffects, opDecl.resultTy)
                      )
                    )
                  )(gn"resume")
              )
            }
          )
      yield outputCType
  case Alloc(heap, vTy) =>
    checkType(heap, HeapType) >>
      checkIsType(vTy) >>
      Right(
        F(
          EffectsLiteral(ListSet((Builtins.HeapEf, heap :: Nil))),
          CellType(heap, vTy, CellStatus.Uninitialized),
        )
      )
  case Set(cell, value) =>
    for cellTy <- inferType(cell)
        r <- cellTy match
          case CellType(heap, vTy, status) => checkType(value, vTy) >>
            Right(
              F(
                EffectsLiteral(ListSet((Builtins.HeapEf, heap :: Nil))),
                CellType(heap, vTy, CellStatus.Initialized),
              )
            )
          case _ => Left(ExpectCell(cell))
    yield r
  case Get(cell) =>
    for cellTy <- inferType(cell)
        r <- cellTy match
          case CellType(heap, vTy, status) if status == CellStatus.Initialized =>
            Right(
              F(
                EffectsLiteral(ListSet((Builtins.HeapEf, heap :: Nil))),
                CellType(heap, vTy, CellStatus.Initialized),
              )
            )
          case _: CellType => Left(UninitializedCell(tm))
          case _ => Left(ExpectCell(cell))
    yield r
  case HeapHandler(inputBinding, otherEffects, key, heapContent, input) =>
    val heapVarBinding = Binding[VTerm](HeapType)(gn"heap")
    checkIsType(inputBinding.ty) >>
      // TODO: check heap variable is not leaked.
      checkType(
        input,
        F(EffectsUnion(Var(0), otherEffects.weakened), inputBinding.ty.weakened)
      )(using Γ :+ heapVarBinding) >>
      Right(F(otherEffects, inputBinding.ty))

def checkType(tm: CTerm, ty: CTerm)
  (using Γ: Context)
  (using Σ: Signature)
  (using ctx: TypingContext)
: Either[Error, Unit] = tm match
  case _ =>
    for tmTy <- inferType(tm)
        ty <- reduceForTyping(ty)
        r <- checkSubsumption(tmTy, ty, None)
    yield r

def checkSubsumption(sub: VTerm, sup: VTerm, ty: Option[VTerm])
  (using Γ: Context)
  (using Σ: Signature)
  (using ctx: TypingContext)
: Either[Error, Unit] =
  if sub == sup then return Right(())
  (sub, sup) match
    case (VUniverse(ul1, upperBound1), VUniverse(ul2, upperBound2)) =>
      checkULevelSubsumption(ul1, ul2) >> checkSubsumption(upperBound1, upperBound2, None)
    case (VTop(ul1), VTop(ul2)) => checkULevelSubsumption(ul1, ul2)
    case (Pure(ul1), Pure(ul2)) => checkULevelSubsumption(ul1, ul2)
    case (U(cty1), U(cty2)) => checkSubsumption(cty1, cty2, None)
    case (DataType(qn1, args1), DataType(qn2, args2)) if qn1 == qn2 =>
      val data = Σ.getData(qn1)
      var Γ2 = Γ
      allRight(
        args1.zip(args2).zip(data.tParamTys).map {
          case ((arg1, arg2), (binding, variance)) =>
            val r = variance match
              case Variance.INVARIANT => checkConversion(arg1, arg2, Some(binding.ty))(using Γ2)
              case Variance.COVARIANT => checkSubsumption(arg1, arg2, Some(binding.ty))(using Γ2)
              case Variance.CONTRAVARIANT => checkSubsumption(arg2, arg1, Some(binding.ty))(using Γ2)
            Γ2 = Γ2 :+ binding
            r
        }
      )
    case (CellType(heap1, ty1, status1), CellType(heap2, ty2, status2)) =>
      for r <- checkConversion(heap1, heap2, Some(HeapType)) >>
        checkConversion(ty1, ty2, ty) >>
        (if status1 == status2 || status1 == CellStatus.Initialized then Right(()) else Left(
          NotVSubsumption(sub, sup, ty)
        ))
      yield r
    case _ => Left(NotVSubsumption(sub, sup, ty))

def checkSubsumption(sub: CTerm, sup: CTerm, ty: Option[CTerm])
  (using Γ: Context)
  (using Σ: Signature)
  (using ctx: TypingContext)
: Either[Error, Unit] =
  val isTotal = ty.asInstanceOf[CType].effects == Total
  for sub <- if isTotal then reduce(sub) else Right(sub)
      sup <- if isTotal then reduce(sup) else Right(sup)
      r <- (sub, sup, ty) match
        case (_, _, _) if sub == sup => Right(())
        case (_, _, Some(FunctionType(_, binding, bodyTy))) =>
          checkSubsumption(
            Application(sub.weakened, Var(0)),
            Application(sup.weakened, Var(0)),
            Some(bodyTy),
          )(using Γ :+ binding)
        case (_, _, Some(RecordType(_, qn, args))) =>
          val record = Σ.getRecord(qn)
          allRight(
            record.fields.map { field =>
              checkSubsumption(Projection(sub, field.name), Projection(sup, field.name), Some(field.ty))
            }
          )
        case (CUniverse(eff1, ul1, upperBound1), CUniverse(eff2, ul2, upperBound2), _) =>
          checkEffSubsumption(eff1, eff2) >>
            checkULevelSubsumption(ul1, ul2) >>
            checkSubsumption(upperBound1, upperBound2, Some(sup))
        case (CTop(eff1, ul1), CTop(eff2, ul2), _) =>
          checkEffSubsumption(eff1, eff2) >>
            checkULevelSubsumption(ul1, ul2)
        case (F(eff1, vTy1), F(eff2, vTy2), _) =>
          for _ <- checkEffSubsumption(eff1, eff2)
              r <- checkSubsumption(vTy1, vTy2, None)
          yield r
        // TODO: keep doing this part
        case _ => Left(NotCSubsumption(sub, sup, ty))
  yield r

private def checkEffSubsumption(eff1: VTerm, eff2: VTerm): Either[Error, Unit] = (eff1, eff2) match
  case (_, _) if eff1 == eff2 => Right(())
  case (Effects(literals1, unionOperands1), Effects(literals2, unionOperands2))
    if literals1.subsetOf(literals2) && unionOperands1.subsetOf(unionOperands2) => Right(())
  case _ => Left(NotEffectSubsumption(eff1, eff2))

/**
 * Check that `ul1` is lower or equal to `ul2`.
 */
private def checkULevelSubsumption(ul1: ULevel, ul2: ULevel): Either[Error, Unit] = (ul1, ul2) match
  case (_, _) if ul1 == ul2 => Right(())
  case (USimpleLevel(Level(l1, maxOperands1)), USimpleLevel(Level(l2, maxOperands2)))
    if l1 <= l2 &&
      maxOperands1.forall { (k, v) => maxOperands2.getOrElse(k, -1) >= v } => Right(())
  case (USimpleLevel(_), UωLevel(_)) => Right(())
  case (UωLevel(l1), UωLevel(l2)) if l1 <= l2 => Right(())
  case _ => Left(NotLevelSubsumption(ul1, ul2))

/**
 * @param ty can be [[None]] if `a` and `b` are types
 */
def checkConversion(a: VTerm, b: VTerm, ty: Option[VTerm])
  (using Γ: Context)
  (using Σ: Signature)
  (using ctx: TypingContext)
: Either[Error, Unit] =
// We have specifically designed pure value terms to respect object equality.
  (a, b, ty) match
    case (_, _, _) if a == b => Right(())
    case (Thunk(a), Thunk(b), Some(U(ty))) => checkConversion(a, b, Some(ty))
    case (U(a), U(b), _) => checkConversion(a, b, None)
    case _ => Left(VConversionFailure(a, b, ty))

/**
 * @param ty can be [[None]] if `a` and `b` are types
 */
private def checkConversion(a: CTerm, b: CTerm, ty: Option[CTerm])
  (using Γ: Context)
  (using Σ: Signature)
  (using ctx: TypingContext)
: Either[Error, Unit] =
  val isTotal = ty.asInstanceOf[CType].effects == Total
  for a <- if isTotal then reduce(a) else Right(a)
      b <- if isTotal then reduce(b) else Right(b)
      r <- (a, b, ty) match
        case (_, _, Some(FunctionType(_, binding, bodyTy))) =>
          checkConversion(
            Application(a.weakened, Var(0)),
            Application(b.weakened, Var(0)),
            Some(bodyTy),
          )(using Γ :+ binding)
        case (_, _, Some(RecordType(_, qn, args))) =>
          val record = Σ.getRecord(qn)
          allRight(
            record.fields.map { field =>
              checkConversion(Projection(a, field.name), Projection(b, field.name), Some(field.ty))
            }
          )
        case (Force(v1), Force(v2), Some(ty)) => checkConversion(v1, v2, Some(U(ty)))
        case (F(eff1, vTy1), F(eff2, vTy2), _) => ???
        // TODO: add more cases.
        case (Let(t1, eff1, binding1, ctx1), Let(t2, eff2, binding2, ctx2), _) => ???
        case _ => Left(CConversionFailure(a, b, ty))
  yield r

def checkTypes(tms: Seq[VTerm], tys: Telescope)
  (using Γ: Context)
  (using Σ: Signature)
  (using ctx: TypingContext)
: Either[Error, Unit] =
  if tms.length != tys.length then Left(TelescopeLengthMismatch(tms, tys))
  else allRight(
    tms.zip(tys).zipWithIndex.map {
      case ((tm, binding), index) => checkType(tm, binding.ty.substLowers(tms.take(index): _*))
    }
  )

private def checkIsType(vTy: VTerm)
  (using Γ: Context)
  (using Σ: Signature)
  (using ctx: TypingContext)
: Either[Error, Unit] =
  for vTyTy <- inferType(vTy)
      r <- vTyTy match
        case VUniverse(_, _) => Right(())
        case _ => Left(NotVTypeError(vTy))
  yield r

private def checkIsType(cTy: CTerm)
  (using Γ: Context)
  (using Σ: Signature)
  (using ctx: TypingContext)
: Either[Error, Unit] =
  for cTyTy <- inferType(cTy)
      r <- cTyTy match
        case CUniverse(eff, _, _) if eff == Total => Right(())
        case _: CUniverse => Left(EffectfulCType(cTy))
        case _ => Left(NotCTypeError(cTy))
  yield r

private def reduceForTyping(cTy: CTerm)
  (using Γ: Context)
  (using Σ: Signature)
  (using ctx: TypingContext)
: Either[Error, CTerm] =
  for cTyTy <- inferType(cTy)
      r <- cTyTy match
        case CUniverse(eff, _, _) if eff == Total => reduce(cTy)
        case _: CUniverse => Left(EffectfulCType(cTy))
        case _ => Left(NotCTypeError(cTy))
  yield r

private def augmentEffect(eff: VTerm, cty: CTerm): CTerm = cty match
  case CUniverse(effects, ul, upperBound) => CUniverse(EffectsUnion(eff, effects), ul, upperBound)
  case CTop(effects, ul) => CTop(EffectsUnion(eff, effects), ul)
  case F(effects, vTy) => F(EffectsUnion(eff, effects), vTy)
  case FunctionType(effects, binding, bodyTy) => FunctionType(
    EffectsUnion(eff, effects),
    binding,
    bodyTy
  )
  case RecordType(effects, qn, args) => RecordType(EffectsUnion(eff, effects), qn, args)
  case _ => throw IllegalArgumentException()

def allRight[L](es: Iterable[Either[L, ?]]): Either[L, Unit] =
  es.first {
    case Left(l) => Some(l)
    case _ => None
  } match
    case Some(l) => Left(l)
    case _ => Right(())

extension[L, R1] (e1: Either[L, R1])
  private inline infix def >>[R2](e2: Either[L, R2]): Either[L, R2] = e1.flatMap(_ => e2)
