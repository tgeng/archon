package com.github.tgeng.archon.core.ir

import com.github.tgeng.archon.common.*
import com.github.tgeng.archon.core.common.*

import SourceInfo.*
import Declaration.*
import CTerm.*
import VTerm.*
import IrError.*
import Variance.*
import PreDeclaration.*

private given Γ0: Context = IndexedSeq()
def elaborateSignature
  (data: PreData)
  (using Signature)
  (using ctx: TypingContext)
  : Either[IrError, Data] =
  ctx.trace(s"elaborating data signature ${data.qn}") {
    def elaborateTy
      (ty: CTerm)
      (using Γ: Context)
      (using Signature)
      (using ctx: TypingContext)
      : Either[IrError, (TTelescope, ULevel, VTerm, VTerm)] =
      for
        ty <- reduceCType(ty)
        r <- ty match
          // Here and below we do not care about the declared effect types because data type 
          // constructors are always total. Declaring non-total signature is not necessary (nor 
          // desirable) but acceptable.
          case F(Type(Top(ul, usage, eqDecidability)), _, _) => Right((Nil, ul, usage, eqDecidability))
          case F(t, _, _)           => Left(ExpectVType(t))
          case FunctionType(binding, bodyTy, _) =>
            elaborateTy(bodyTy)(using Γ :+ binding).map { case (telescope, ul, usage, eqDecidability) =>
              ((binding, INVARIANT) :: telescope, ul, usage, eqDecidability)
            }
          case _ => Left(NotDataTypeType(ty))
      yield r

    for
      tParamTys <- elaborateTTelescope(data.tParamTys)
      elaboratedTy <- elaborateTy(data.ty)(using Γ0 ++ tParamTys.map(_._1))
    yield elaboratedTy match
      case (tIndices, ul, usage, eqDecidability) =>
        Data(data.qn)(tParamTys.size, tParamTys ++ tIndices, ul, usage, eqDecidability)
  }

def elaborateBody
  (preData: PreData)
  (using Σ: Signature)
  (using ctx: TypingContext)
  : Either[IrError, List[Constructor]] =
  ctx.trace(s"elaborating data body ${preData.qn}") {
    val data = Σ.getData(preData.qn)

    def elaborateTy
      (ty: CTerm)
      (using Γ: Context)
      (using Signature)
      (using ctx: TypingContext)
      : Either[IrError, (Telescope, /* args */ List[VTerm])] =
      for
        ty <- reduceCType(ty)
        r <- ty match
          // Here and below we do not care the declared effect types because data type constructors
          // are always total. Declaring non-total signature is not necessary (nor desirable) but
          // acceptable.
          case F(DataType(qn, args), _, _) if qn == data.qn && args.size == data.tParamTys.size =>
            Right((Nil, args))
          case F(t, _, _) => Left(ExpectDataType(t, Some(data.qn)))
          case FunctionType(binding, bodyTy, _) =>
            elaborateTy(bodyTy)(using Γ :+ binding).map { case (telescope, ul) =>
              (binding :: telescope, ul)
            }
          case _ => Left(NotDataTypeType(ty))
      yield r

    // number of index arguments
    given Context = data.tParamTys.map(_._1).toIndexedSeq

    val indexCount = data.tParamTys.size - preData.tParamTys.size
    transpose(
      preData.constructors.map { constructor =>
        ctx.trace(s"elaborating constructor ${constructor.name}") {
          // weaken to accommodate data type indices
          val ty = constructor.ty.weaken(indexCount, 0)
          elaborateTy(ty).map { case (paramTys, args) =>
            Constructor(constructor.name, paramTys, args)
          }
        }
      }
    )
  }

def elaborateSignature
  (record: PreRecord)
  (using Signature)
  (using ctx: TypingContext)
  : Either[IrError, Record] =
  ctx.trace(s"elaborating record signature ${record.qn}") {
    for
      tParamTys <- elaborateTTelescope(record.tParamTys)
      ty <- reduceCType(record.ty)(using tParamTys.map(_._1).toIndexedSeq)
      r <- ty match
        case CType(CTop(ul, _), _) => Right(new Record(record.qn)(tParamTys, ul))
        case t               => Left(ExpectCType(t))
    yield r
  }

def elaborateBody
  (preRecord: PreRecord)
  (using Σ: Signature)
  (using ctx: TypingContext)
  : Either[IrError, List[Field]] =
  ctx.trace(s"elaborating record body ${preRecord.qn}") {
    val record = Σ.getRecord(preRecord.qn)

    given SourceInfo = SiEmpty

    given Context = record.tParamTys.map(_._1).toIndexedSeq :+
      Binding(U(RecordType(record.qn, vars(record.tParamTys.size - 1))), ???)(
        record.selfName
      )

    transpose(
      preRecord.fields.map { field =>
        ctx.trace(s"elaborating field ${field.name}") {
          for ty <- reduceCType(field.ty)
          yield Field(field.name, ty)
        }
      }
    )
  }

def elaborateSignature
  (definition: PreDefinition)
  (using Signature)
  (using ctx: TypingContext)
  : Either[IrError, Definition] =
  given SourceInfo = SiEmpty

  ctx.trace(s"elaborating def signature ${definition.qn}") {
    for
      paramTys <- elaborateTelescope(definition.paramTys)
      ty <- reduceCType(definition.ty)(using paramTys.toIndexedSeq)
    yield Definition(definition.qn)(
      paramTys.foldRight(ty) { (binding, bodyTy) =>
        FunctionType(binding, bodyTy)
      }
    )
  }

def elaborateBody
  (preDefinition: PreDefinition)
  (using Σ: Signature)
  (using ctx: TypingContext)
  : Either[IrError, List[Clause]] =
  ctx.trace(s"elaborating def body ${preDefinition.qn}") {
    for
      paramTys <- elaborateTelescope(preDefinition.paramTys)
      r <- {
        given Γ: Context = paramTys.toIndexedSeq
        Right(???)

        // transpose(
        //   preDefinition.clauses.zipWithIndex.flatMap { (clause, index) =>
        //     clause.rhs match
        //       case None => List()
        //       case Some(rhs) =>
        //         List(
        //           ctx.trace(s"elaborating clause $index") {
        //             for
        //               bindings <- elaborateTelescope(clause.bindings)
        //               ty <- reduceCType(clause.ty)(using Γ ++ bindings)
        //             yield
        //               val allBindings = paramTys ++ bindings
        //               Clause(
        //                 allBindings,
        //                 CoPattern.pVars(
        //                   allBindings.size - 1,
        //                   bindings.size
        //                 ) ++ clause.lhs,
        //                 rhs,
        //                 ty
        //               )
        //           }
        //         )
        //   }
        // )
      }
    yield r
  }

def elaborateSignature
  (effect: PreEffect)
  (using Signature)
  (using ctx: TypingContext)
  : Either[IrError, Effect] =
  ctx.trace(s"elaborating effect signature ${effect.qn}") {
    elaborateTelescope(effect.tParamTys).map(Effect(effect.qn)(_))
  }

def elaborateBody
  (preEffect: PreEffect)
  (using Σ: Signature)
  (using ctx: TypingContext)
  : Either[IrError, List[Operator]] =
  val effect = Σ.getEffect(preEffect.qn)

  given Context = effect.tParamTys.toIndexedSeq

  ctx.trace(s"elaborating effect body ${effect.qn}") {
    def elaborateTy
      (ty: CTerm)
      (using Γ: Context)
      (using Signature)
      (using ctx: TypingContext)
      : Either[IrError, (Telescope, /* operator return type */ VTerm)] =
      for
        ty <- reduceCType(ty)
        r <- ty match
          // Here and below we do not care the declared effect types because data type constructors
          // are always total. Declaring non-total signature is not necessary (nor desirable) but
          // acceptable.
          case F(ty, _, _) => Right((Nil, ty))
          case FunctionType(binding, bodyTy, _) =>
            elaborateTy(bodyTy)(using Γ :+ binding).map { case (telescope, ul) =>
              (binding :: telescope, ul)
            }
          case _ => Left(ExpectFType(ty))
      yield r

    transpose(
      preEffect.operators.map { operator =>
        ctx.trace(s"elaborating operator ${operator.name}") {
          elaborateTy(operator.ty).map { case (paramTys, resultTy) =>
            Operator(operator.name, paramTys, resultTy, ???)
          }
        }
      }
    )
  }

private def elaborateTTelescope
  (tTelescope: PreTTelescope)
  (using Γ: Context)
  (using Signature)
  (using ctx: TypingContext)
  : Either[IrError, TTelescope] =
  elaborateTelescope(tTelescope.map(_._1)).map(_.zip(tTelescope.map(_._2)))

private def elaborateTelescope
  (telescope: PreTelescope)
  (using Γ: Context)
  (using Signature)
  (using ctx: TypingContext)
  : Either[IrError, Telescope] = telescope match
  case Nil => Right(Nil)
  case binding :: telescope =>
    ctx.trace("elaborating telescope") {
      for
        ty <- reduceVType(binding.ty)
        newBinding = Binding(ty, ???)(binding.name)
        telescope <- elaborateTelescope(telescope)(using Γ :+ newBinding)
      yield newBinding :: telescope
    }
