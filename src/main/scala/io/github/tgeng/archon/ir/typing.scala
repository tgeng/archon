package io.github.tgeng.archon.ir

import scala.collection.immutable.{ListMap, ListSet}
import io.github.tgeng.archon.common.*
import io.github.tgeng.archon.ir.Reducible.reduce
import VTerm.*
import CTerm.*
import ULevel.*
import Error.*

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
    checkTypes(args, data.tParamTys) >> Right(data.ty.substLowers(args: _*))
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
  case CellType(heap, ty, _) => checkType(heap, HeapType) >> inferType(ty)
  case Cell(heapKey, _, ty, status) => Right(CellType(Heap(heapKey), ty, status))

def checkType(tm: VTerm, ty: VTerm)
  (using Γ: Context)
  (using Σ: Signature)
  (using ctx: TypingContext)
: Either[Error, Unit] = tm match
  case Con(name, args) => ty match
    case DataType(qn, tArgs) =>
      val data = Σ.getData(qn)
      data
        .cons.first { c => if c.name == name then Some(c) else None } match
        case None => Left(VTypeError(tm, ty))
        case Some(con) => checkTypes(args, con.paramTys.substLowers(tArgs: _*))
    case _ => Left(VTypeError(tm, ty))
  case Refl => ty match
    case EqualityType(level, ty, left, right) => checkConversion(left, right, ty)
    case _ => Left(VTypeError(tm, ty))
  case _ =>
    for inferred <- inferType(tm)
        r <- checkSubtyping(inferred, ty)
    yield r

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
    for _ <- checkType(t, F(effects, binding.ty))
        ctxTy <- inferType(ctx)(using Γ :+ binding)
    // TODO: in case weakened failed, provide better error message: ctxTy cannot depend on
    //  the bound variable
    yield augmentEffect(effects, ctxTy.weakened)
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
      checkTypes(args, record.tParamTys) >>
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
  case OperatorCall(eff@(qn, tArgs), name, args) => ???
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
  ) => ???
//          val effect = Σ.getEffect(qn)
//          if handlers.size != effect.operators.size ||
//            handlers.keySet != effect.operators.map(_.name).toSet then
//            Left(UnmatchedHandlerImplementation(qn, handlers.keys))
//          else
//            checkVTypes(args, effect.tParamTys) >>
//              checkIsVType(inputBinding.ty) >>
//              checkCType(
//                input,
//                F(EffectsUnion(EffectsLiteral(ListSet(eff)), otherEffects), inputBinding.ty)
//              ) >>
//              sys.addEffectConstraint(otherEffects, outputType) >>
//              checkCType(transform, outputType.weakened)(using Γ :+ inputBinding) >>
//              allRight(
//                effect.operators.map { opDecl =>
//                  val (n, handlerBody) = handlers(opDecl.name)
//                  assert(n == opDecl.paramTys.size)
//                  checkCType(
//                    handlerBody,
//                    outputType
//                  )(
//                    using Γ ++
//                      opDecl.paramTys :+
//                      Binding(
//                        U(
//                          FunctionType(
//                            otherEffects,
//                            Binding(opDecl.resultTy)(gn"output"),
//                            outputType
//                          )
//                        )
//                      )(gn"resume")
//                  )
//                }
//              )
//
//        case Alloc(heap, vTy) => checkIsVType(vTy) >>
//          sys.addSubtyping(
//            F(
//              EffectsLiteral(ListSet((Builtins.HeapEf, heap :: Nil))),
//              CellType(heap, vTy, CellStatus.Uninitialized),
//            ),
//            ty
//          )
//        case Set(cell, value) =>
//          val vTy = sys.newVUnfVar()
//          val heap = sys.newVUnfVar()
//          checkVType(cell, CellType(heap, vTy, CellStatus.Uninitialized)) >>
//            checkVType(value, vTy) >>
//            sys.addSubtyping(
//              F(
//                EffectsLiteral(ListSet((Builtins.HeapEf, heap :: Nil))),
//                CellType(heap, vTy, CellStatus.Initialized),
//              ),
//              ty
//            )
//        case Get(cell) =>
//          val vTy = sys.newVUnfVar()
//          val heap = sys.newVUnfVar()
//          checkVType(cell, CellType(heap, vTy, CellStatus.Initialized)) >>
//            sys.addSubtyping(
//              F(
//                EffectsLiteral(ListSet((Builtins.HeapEf, heap :: Nil))),
//                vTy
//              ),
//              ty
//            )
//        case HeapHandler(inputBinding, otherEffects, key, heapContent, input) =>
//          val heapVarBinding = Binding[VTerm](HeapType)(gn"heap")
//          checkIsVType(inputBinding.ty) >>
//          // TODO: check heap variable is not leaked.
//            checkCType(
//              input,
//              F(EffectsUnion(Var(0), otherEffects.weakened), inputBinding.ty.weakened)
//            )(using Γ :+ heapVarBinding)


def checkType(tm: CTerm, ty: CTerm)
  (using Γ: Context)
  (using Σ: Signature)
  (using ctx: TypingContext)
: Either[Error, Unit] = tm match
  case _ =>
    for tmTy <- inferType(tm)
        r <- checkSubtyping(tmTy, ty)
    yield r

def checkSubtyping(sub: VTerm, sup: VTerm)
  (using Γ: Context)
  (using Σ: Signature)
  (using ctx: TypingContext)
: Either[Error, Unit] = ???

def checkSubtyping(sub: CTerm, sup: CTerm)
  (using Γ: Context)
  (using Σ: Signature)
  (using ctx: TypingContext)
: Either[Error, Unit] = ???

def checkConversion(a: VTerm, b: VTerm, ty: VTerm)
  (using Γ: Context)
  (using Σ: Signature)
  (using ctx: TypingContext)
: Either[Error, Unit] = ???

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

private def reduceForTyping(cTy: CTerm): Either[Error, CTerm] = ???

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
