package io.github.tgeng.archon.ir

import scala.collection.immutable.{ListMap, ListSet}
import io.github.tgeng.archon.common.*
import io.github.tgeng.archon.ir.Reducible.reduce
import VTerm.*
import CTerm.*
import ULevel.*
import Error.*
import Declaration.*

trait TypingContext

def checkDataType(qn: QualifiedName)
  (using Σ: Signature)
  (using ctx: TypingContext)
: Either[Error, Unit] =
  given Context = IndexedSeq()
  val data = Σ.getData(qn)
  checkParameterTypeDeclarations(data.tParamTys.map(_._1)) >>
    checkULevel(data.ul)

def checkDataConstructors(qn: QualifiedName)
  (using Σ: Signature)
  (using ctx: TypingContext)
: Either[Error, Unit] =
  given Context = IndexedSeq()
  val data = Σ.getData(qn)
  allRight(
    Σ.getConstructors(qn).map { con =>
      given Γ: Context = data.tParamTys.map(_._1).toIndexedSeq
      for _ <- checkParameterTypeDeclarations(con.paramTys, Some(data.ul))
          _ <- allRight(con.paramTys.map(binding => checkIsPureType(binding.ty)))
          _ <- checkParameterTypeDeclarations(con.idTys, Some(data.ul))(using Γ ++ con.paramTys)
      yield
        // binding of positiveVars must be either covariant or invariant
        // binding of negativeVars must be either contravariant or invariant
        val (positiveVars, negativeVars) = getFreeVars(con.paramTys)(using 0)
        val tParamTysSize = data.tParamTys.size
        val bindingWithIncorrectUsage = data.tParamTys.zipWithIndex.filter {
          case ((binding, variance), reverseIndex) =>
            val index = tParamTysSize - reverseIndex - 1
            variance match
              case Variance.INVARIANT => false
              case Variance.COVARIANT => negativeVars(index)
              case Variance.CONTRAVARIANT => positiveVars(index)
        }
        if bindingWithIncorrectUsage.isEmpty then ()
        else Left(IllegalVarianceInData(data.qn, bindingWithIncorrectUsage.map(_._2)))
    }
  )

def checkRecordType(qn: QualifiedName)
  (using Σ: Signature)
  (using ctx: TypingContext)
: Either[Error, Unit] =
  given Context = IndexedSeq()
  val record = Σ.getRecord(qn)
  checkParameterTypeDeclarations(record.tParamTys.map(_._1)) >>
    checkULevel(record.ul)

def checkRecordFields(qn: QualifiedName)
  (using Σ: Signature)
  (using ctx: TypingContext)
: Either[Error, Unit] =
  given Context = IndexedSeq()
  val record = Σ.getRecord(qn)
  allRight(
    Σ.getFields(qn).map { field =>
      given Context = record.tParamTys.map(_._1).toIndexedSeq :+ getRecordSelfBinding(record)
      for _ <- checkIsCType(field.ty, Some(record.ul.weakened))
        yield
          // binding of positiveVars must be either covariant or invariant
          // binding of negativeVars must be either contravariant or invariant
          val (positiveVars, negativeVars) = getFreeVars(field.ty)(using 0)
          val tParamTysSize = record.tParamTys.size
          val bindingWithIncorrectUsage = record.tParamTys.zipWithIndex.filter {
            case ((binding, variance), reverseIndex) =>
              val index = tParamTysSize - reverseIndex // Offset by 1 to accommodate self reference
              variance match
                case Variance.INVARIANT => false
                case Variance.COVARIANT => negativeVars(index)
                case Variance.CONTRAVARIANT => positiveVars(index)
          }
          if bindingWithIncorrectUsage.isEmpty then ()
          else Left(IllegalVarianceInRecord(record.qn, bindingWithIncorrectUsage.map(_._2)))
    }
  )

def getRecordSelfBinding(record: Record): Binding[VTerm] = Binding(
  U(
    RecordType(
      Total,
      record.qn,
      (record.tParamTys.size - 1).to(0, -1).map(Var(_)).toList
    )
  )
)(gn"self")

private def checkParameterTypeDeclarations(tParamTys: Telescope, levelBound: Option[ULevel] = None)
  (using Γ: Context)
  (using Σ: Signature)
  (using ctx: TypingContext)
: Either[Error, Unit] = tParamTys match
  case Nil => Right(())
  case binding :: rest => checkIsVType(binding.ty, levelBound) >> checkParameterTypeDeclarations(
    rest
  )(using Γ :+ binding)

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
    checkTypes(
      args,
      data.tParamTys.map(_._1)
    ) >> Right(VUniverse(data.ul.map(_.substLowers(args: _*)), tm))
  case _: Con => throw IllegalArgumentException("cannot infer type")
  case EqualityType(ty, left, right) =>
    for tyTy <- inferType(ty)
        r <- tyTy match
          case VUniverse(ul, _) =>
            checkType(left, ty) >>
              checkType(right, ty) >>
              Right(VUniverse(ul, tm))
          case _ => Left(NotVTypeError(ty))
    yield r
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
  checkIsVType(ty) >>
    (tm match
      case Con(name, args) => ty match
        case DataType(qn, tArgs) =>
          Σ.getConstructors(qn).first { c => if c.name == name then Some(c) else None } match
            case None => Left(MissingConstructor(name, qn))
            case Some(con) => checkTypes(args, con.paramTys.substLowers(tArgs: _*))
        case _ => Left(ExpectDataType(ty))
      case Refl => ty match
        case EqualityType(ty, left, right) => checkSubsumption(
          left,
          right,
          Some(ty)
        )(using CONVERSION)
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
    for _ <- checkIsVType(binding.ty)
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
      Right(CUniverse(Total, record.ul.map(_.substLowers(args: _*)), tm))
  case Projection(rec, name) =>
    for recTy <- inferType(rec)
        r <- recTy match
          case RecordType(effects, qn, args) =>
            Σ.getFields(qn).first { f => if f.name == name then Some(f) else None } match
              case None => throw IllegalArgumentException(s"unexpected record field $name for $qn")
              case Some(f) => Right(augmentEffect(effects, f.ty.substLowers(args :+ Thunk(tm): _*)))
          case _ => Left(ExpectRecord(rec))
    yield r
  case OperatorCall(eff@(qn, tArgs), name, args) =>
    val effect = Σ.getEffect(qn)
    Σ.getOperators(qn).first { o => if o.name == name then Some(o) else None } match
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
    val operators = Σ.getOperators(qn)
    if handlers.size != operators.size ||
      handlers.keySet != operators.map(_.name).toSet then
      Left(UnmatchedHandlerImplementation(qn, handlers.keys))
    else
      val outputCType = F(otherEffects, outputType)
      for _ <- checkTypes(args, effect.tParamTys)
          _ <- checkIsVType(inputBinding.ty)
          _ <- checkType(
            input,
            F(EffectsUnion(EffectsLiteral(ListSet(eff)), otherEffects), inputBinding.ty)
          )
          _ <- checkType(transform, outputCType.weakened)(using Γ :+ inputBinding)
          _ <- allRight(
            operators.map { opDecl =>
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
  case AllocOp(heap, vTy) =>
    checkType(heap, HeapType) >>
      checkIsVType(vTy) >>
      Right(
        F(
          EffectsLiteral(ListSet((Builtins.HeapEf, heap :: Nil))),
          CellType(heap, vTy, CellStatus.Uninitialized),
        )
      )
  case SetOp(cell, value) =>
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
  case GetOp(cell) =>
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
    checkIsVType(inputBinding.ty) >>
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

enum CheckSubsumptionMode:
  case SUBSUMPTION, CONVERSION

import CheckSubsumptionMode.*

given CheckSubsumptionMode = SUBSUMPTION

/**
 * @param ty can be [[None]] if `a` and `b` are types
 */
def checkSubsumption(sub: VTerm, sup: VTerm, ty: Option[VTerm])
  (using mode: CheckSubsumptionMode)
  (using Γ: Context)
  (using Σ: Signature)
  (using ctx: TypingContext)
: Either[Error, Unit] =
  if sub == sup then return Right(())
  (sub, sup, ty) match
    case (VUniverse(ul1, upperBound1), VUniverse(ul2, upperBound2), _) =>
      checkULevelSubsumption(ul1, ul2) >> checkSubsumption(upperBound1, upperBound2, None)
    case (ty, VTop(ul2), _) =>
      for tyTy <- inferType(ty)
          r <- tyTy match
            case VUniverse(ul1, _) => checkULevelSubsumption(ul1, ul2)
            case _ => Left(NotVTypeError(sub))
      yield r
    case (ty, Pure(ul2), _) =>
      for tyTy <- inferType(ty)
          r <- tyTy match
            case VUniverse(ul1, _) => checkULevelSubsumption(ul1, ul2) >> checkIsPureType(ty)
            case _ => Left(NotVTypeError(sub))
      yield r
    case (U(cty1), U(cty2), _) => checkSubsumption(cty1, cty2, None)
    case (Thunk(c1), Thunk(c2), Some(U(ty))) => checkSubsumption(c1, c2, Some(ty))
    case (DataType(qn1, args1), DataType(qn2, args2), _) if qn1 == qn2 =>
      val data = Σ.getData(qn1)
      var args = IndexedSeq[VTerm]()
      allRight(
        args1.zip(args2).zip(data.tParamTys).map {
          case ((arg1, arg2), (binding, variance)) =>
            variance match
              case Variance.INVARIANT =>
                val r = checkSubsumption(arg1, arg2, Some(binding.ty.substLowers(args: _*)))(
                  using CONVERSION
                )
                args = args :+ arg1
                r
              case Variance.COVARIANT =>
                val r = checkSubsumption(arg1, arg2, Some(binding.ty.substLowers(args: _*)))
                args = args :+ arg1
                r
              case Variance.CONTRAVARIANT =>
                val r = checkSubsumption(arg2, arg1, Some(binding.ty.substLowers(args: _*)))
                args = args :+ arg2
                r
        }
      )
    case (Con(name1, args1), Con(name2, args2), Some(DataType(qn, tArgs))) if name1 == name2 =>
      val con = Σ.getConstructors(qn).getFirstOrDefault(
        _.name == name1,
        throw IllegalArgumentException(s"missing constructor $name1 in data $qn")
      )
      var args = IndexedSeq[VTerm]()
      allRight(
        args1.zip(args2).zip(con.paramTys).map {
          case ((arg1, arg2), binding) =>
            val r = checkSubsumption(arg1, arg2, Some(binding.ty.substLowers(args: _*)))
            args = args :+ arg1
            r
        }
      )
    case (EqualityType(ty1, a1, b1), EqualityType(ty2, a2, b2), _) =>
      checkSubsumption(ty1, ty2, None) >>
        checkSubsumption(a1, a2, Some(ty1)) >>
        checkSubsumption(b1, b2, Some(ty1))
    case (CellType(heap1, ty1, status1), CellType(heap2, ty2, status2), _) =>
      for r <- checkSubsumption(heap1, heap2, Some(HeapType)) >>
        checkSubsumption(ty1, ty2, None)(using CONVERSION) >>
        (if status1 == status2 || status1 == CellStatus.Initialized then Right(()) else Left(
          NotVSubsumption(sub, sup, ty, mode)
        ))
      yield r
    case _ => Left(NotVSubsumption(sub, sup, ty, mode))

/**
 * @param ty can be [[None]] if `a` and `b` are types
 */
def checkSubsumption(sub: CTerm, sup: CTerm, ty: Option[CTerm])
  (using mode: CheckSubsumptionMode)
  (using Γ: Context)
  (using Σ: Signature)
  (using ctx: TypingContext)
: Either[Error, Unit] =
  val isTotal = ty.forall(_.asInstanceOf[CType].effects == Total)
  for sub <- if isTotal then reduce(sub) else Right(sub)
      sup <- if isTotal then reduce(sup) else Right(sup)
      r <- (sub, sup, ty) match
        case (_, _, _) if sub == sup => Right(())
        case (_, _, Some(FunctionType(_, binding, bodyTy))) =>
          checkSubsumption(
            Application(sub.weakened, Var(0)),
            Application(sup.weakened, Var(0)),
            Some(bodyTy),
          )(using mode)(using Γ :+ binding)
        case (_, _, Some(RecordType(_, qn, args))) => allRight(
          Σ.getFields(qn).map { field =>
            checkSubsumption(
              Projection(sub, field.name),
              Projection(sup, field.name),
              Some(field.ty)
            )
          }
        )
        case (CUniverse(eff1, ul1, upperBound1), CUniverse(eff2, ul2, upperBound2), _) =>
          checkEffSubsumption(eff1, eff2) >>
            checkULevelSubsumption(ul1, ul2) >>
            checkSubsumption(upperBound1, upperBound2, Some(sup))
        case (ty: CType, CTop(eff2, ul2), _) =>
          for tyTy <- inferType(sub)
              r <- tyTy match
                case CUniverse(_, ul1, _) => checkEffSubsumption(ty.effects, eff2) >>
                  checkULevelSubsumption(ul1, ul2)
                case _ => Left(NotCTypeError(sub))
          yield r
        case (F(eff1, vTy1), F(eff2, vTy2), _) =>
          for _ <- checkEffSubsumption(eff1, eff2)
              r <- checkSubsumption(vTy1, vTy2, None)
          yield r
        case (Return(v1), Return(v2), Some(F(_, ty))) => checkSubsumption(v1, v2, Some(ty))
        case (Let(t1, eff1, binding1, ctx1), Let(t2, eff2, binding2, ctx2), ty) =>
          checkSubsumption(eff1, eff2, Some(EffectsType)) >>
            checkSubsumption(binding1.ty, binding2.ty, None) >>
            checkSubsumption(t1, t2, Some(F(eff1, binding1.ty))) >>
            checkSubsumption(ctx1, ctx2, ty.map(_.weakened))(using mode)(using Γ :+ binding1)
        case (FunctionType(eff1, binding1, bodyTy1), FunctionType(eff2, binding2, bodyTy2), _) =>
          checkSubsumption(eff1, eff2, Some(EffectsType)) >>
            checkSubsumption(binding2.ty, binding1.ty, None) >>
            checkSubsumption(bodyTy1, bodyTy2, None)(using mode)(using Γ :+ binding2)
        case (Application(fun1, arg1), Application(fun2, arg2), _) =>
          for fun1Ty <- inferType(fun1)
              fun2Ty <- inferType(fun2)
              _ <- checkSubsumption(fun1Ty, fun2Ty, None)
              _ <- checkSubsumption(fun1, fun2, Some(fun1Ty))
              r <- fun1Ty match
                case FunctionType(_, binding, _) => checkSubsumption(
                  arg1,
                  arg2,
                  Some(binding.ty)
                )
                case _ => Left(NotCSubsumption(sub, sup, ty, mode))
          yield r
        case (RecordType(eff1, qn1, args1), RecordType(eff2, qn2, args2), _) if qn1 == qn2 =>
          val record = Σ.getRecord(qn1)
          var args = IndexedSeq[VTerm]()
          checkSubsumption(eff1, eff2, Some(EffectsType)) >>
            allRight(
              args1.zip(args2).zip(record.tParamTys).map {
                case ((arg1, arg2), (binding, variance)) =>
                  variance match
                    case Variance.INVARIANT =>
                      val r = checkSubsumption(
                        arg1,
                        arg2,
                        Some(binding.ty.substLowers(args: _*))
                      )(using CONVERSION)
                      args = args :+ arg1
                      r
                    case Variance.COVARIANT =>
                      val r = checkSubsumption(arg1, arg2, Some(binding.ty.substLowers(args: _*)))
                      args = args :+ arg1
                      r
                    case Variance.CONTRAVARIANT =>
                      val r = checkSubsumption(arg2, arg1, Some(binding.ty.substLowers(args: _*)))
                      args = args :+ arg2
                      r
              }
            )
        case (Projection(rec1, name1), Projection(rec2, name2), _) if name1 == name2 =>
          for rec1Ty <- inferType(rec1)
              rec2Ty <- inferType(rec2)
              r <- checkSubsumption(rec1Ty, rec2Ty, None)
          yield r
        case (OperatorCall(
        eff1@(qn1, tArgs1), name1, args1
        ), OperatorCall(
        eff2@(qn2, tArgs2), name2, args2
        ), _) if qn1 == qn2 && name1 == name2 =>
          val effect = Σ.getEffect(qn1)
          val operator = Σ.getOperators(qn1).getFirstOrDefault(
            _.name == name1,
            throw IllegalArgumentException(s"expect effect $qn1 to have operation $name1")
          )
          var args = IndexedSeq[VTerm]()
          allRight(
            args1.zip(args2).zip(operator.paramTys).map {
              case ((arg1, arg2), binding) =>
                val r = checkSubsumption(arg1, arg2, Some(binding.ty))
                args = args :+ arg1
                r
            }
          )
        // For now, we skip the complex logic checking subsumption of handler and continuations. It
        // seems not all that useful to keep those. But we can always add them later if it's deemed
        // necessary.
        case _ => Left(NotCSubsumption(sub, sup, ty, mode))
  yield r

private def checkIsPureType(ty: VTerm)
  (using Γ: Context)
  (using Σ: Signature)
  (using ctx: TypingContext): Either[Error, Unit] = ty match
  // Here we check if upper bound is pure because otherwise, the this universe type does not admit a
  // normalized representation.
  case VUniverse(_, upperBound) => checkIsPureType(upperBound)
  case CellType(_, ty, _) => checkIsPureType(ty)
  case DataType(qn, _) => Σ.getData(qn).isPure match
    case true => Right(())
    case false => Left(NotPureVType(ty))
  case _: U => Left(NotPureVType(ty))
  case _: VTop | _: Pure | _: EqualityType | EffectsType | LevelType | HeapType => Right(())
  case v: Var => Γ(v).ty match
    case VUniverse(ul, upperBound) => checkSubsumption(upperBound, Pure(ul), None)
    case _ => throw IllegalArgumentException(s"$v not a type")
  case _: Thunk | _: Con | Refl | _: Effects | _: Level | _: Heap | _: Cell =>
    throw IllegalArgumentException(s"$ty not a type")

private def checkEffSubsumption(eff1: VTerm, eff2: VTerm)
  (using mode: CheckSubsumptionMode): Either[Error, Unit] = (eff1, eff2) match
  case (_, _) if eff1 == eff2 => Right(())
  case (Effects(literals1, unionOperands1), Effects(literals2, unionOperands2))
    if mode == CheckSubsumptionMode && literals1.subsetOf(literals2) && unionOperands1.subsetOf(
      unionOperands2
    ) => Right(())
  case _ => Left(NotEffectSubsumption(eff1, eff2, mode))

/**
 * Check that `ul1` is lower or equal to `ul2`.
 */
private def checkULevelSubsumption(ul1: ULevel, ul2: ULevel)
  (using mode: CheckSubsumptionMode): Either[Error, Unit] = (ul1, ul2) match
  case _ if ul1 == ul2 => Right(())
  case _ if mode == CONVERSION => Left(NotLevelSubsumption(ul1, ul2, mode))
  case (USimpleLevel(Level(l1, maxOperands1)), USimpleLevel(Level(l2, maxOperands2)))
    if l1 <= l2 &&
      maxOperands1.forall { (k, v) => maxOperands2.getOrElse(k, -1) >= v } => Right(())
  case (USimpleLevel(_), UωLevel(_)) => Right(())
  case (UωLevel(l1), UωLevel(l2)) if l1 <= l2 => Right(())
  case _ => Left(NotLevelSubsumption(ul1, ul2, mode))

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

def checkIsVType(vTy: VTerm, levelBound: Option[ULevel] = None)
  (using Γ: Context)
  (using Σ: Signature)
  (using ctx: TypingContext)
: Either[Error, Unit] =
  for vTyTy <- inferType(vTy)
      r <- vTyTy match
        case VUniverse(ul, _) => levelBound match
          case Some(bound) => checkULevelSubsumption(ul, bound)
          case _ => Right(())
        case _ => Left(NotVTypeError(vTy))
  yield r

def checkIsCType(cTy: CTerm, levelBound: Option[ULevel] = None)
  (using Γ: Context)
  (using Σ: Signature)
  (using ctx: TypingContext)
: Either[Error, Unit] =
  for cTyTy <- inferType(cTy)
      r <- cTyTy match
        case CUniverse(eff, ul, _) if eff == Total => levelBound match
          case Some(bound) => checkULevelSubsumption(ul, bound)
          case _ => Right(())
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
