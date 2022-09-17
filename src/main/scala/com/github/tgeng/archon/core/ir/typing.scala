package com.github.tgeng.archon.core.ir

import scala.collection.immutable.{Map, Set}
import com.github.tgeng.archon.common.*
import com.github.tgeng.archon.core.common.*
import com.github.tgeng.archon.core.ir.Reducible.reduce
import VTerm.*
import CTerm.*
import ULevel.*
import IrError.*
import Declaration.*
import Elimination.*
import SourceInfo.*
import Usage.*
import EqDecidability.*

import scala.annotation.tailrec
import PrettyPrinter.pprint
import WrapPolicy.*
import IndentPolicy.*
import DelimitPolicy.*

private val ANSI_RESET = "\u001b[0m"
private val ANSI_GRAY = "\u001b[90m"
private val ANSI_RED = "\u001b[31m"
private val ANSI_GREEN = "\u001b[32m"
private val ANSI_YELLOW = "\u001b[33m"
private val ANSI_BLUE = "\u001b[34m"
private val ANSI_CYAN = "\u001b[36m"
private val ANSI_WHITE = "\u001b[37m"

def yellow(s: Any): String = ANSI_YELLOW + s.toString + ANSI_RESET
def green(s: Any): String = ANSI_GREEN + s.toString + ANSI_RESET

trait TypingContext(var traceLevel: Int, var enableDebugging: Boolean):

  inline def trace[L, R](
    title: => String,
    description: => Block | String = "",
    successMsg: R => Block | String = (_: R) => "",
    failureMsg: L => Block | String = (l: L) => l.toString,
  )
    (action: => Either[L, R])(using Γ: Context)(using Signature): Either[L, R] =
    val indent = "│ " * traceLevel
    lazy val result: Either[L, R] = action
    if enableDebugging then
      println(indent)
      println(
        indent + "   " + ANSI_BLUE + pprint(Γ.toList)(using IndexedSeq[Binding[VTerm]]()).toString.replaceAll("\n", "\n" + indent + "   ") + ANSI_RESET
      )
      val stacktrace = Thread.currentThread().!!.getStackTrace.!!
      println(indent + "┌─ " + title + " " + ANSI_WHITE + "@" + stacktrace(2).toString + ANSI_RESET)
      if description != "" then
        println((indent + "│  " + description).replaceAll("\n", "\n" + indent + "│  "))
      traceLevel += 1
      val endMessage = result match
        case Right(r) => "✅ " + (ANSI_GREEN + successMsg(r)).replaceAll(
          "\n",
          "\n" + indent + "     "
        )
        case Left(l) => "❌ " + (ANSI_RED + failureMsg(l)).replaceAll("\n", "\n" + indent + "     ")
      traceLevel -= 1
      println(indent + "└─ " + endMessage + ANSI_RESET)
    result

  inline def debug[T](inline t: T): T =
    if enableDebugging then
      val indent = "│ " * traceLevel
      println(indent + " " + ANSI_CYAN + stringify(t) + " = " + t + ANSI_RESET)
    t

  def breakpoint: Unit = {
    if enableDebugging then
      val i = 1
  }

type Usages = Seq[VTerm]

object Usages:
  def zero(using Γ: Context): Usages = Seq.fill(Γ.size)(UsageLiteral(Usage.U0))

  def single(v: VTerm.Var, u: VTerm = VTerm.UsageLiteral(Usage.U1))(using Γ: Context): Usages =
    (Seq.fill(Γ.size - v.idx - 1)(UsageLiteral(Usage.U0)) :+ u)
      ++ Seq.fill(v.idx)(UsageLiteral(Usage.U0))

extension (us1: Usages)
  infix def +(us2: Usages): Usages =
    if us1.size != us2.size then throw IllegalArgumentException("mismatched size")
    else us1.zip(us2).map { (u1, u2) => UsageSum(u1, u2) }

  infix def *(scalar: VTerm): Usages = us1.map(u => UsageProd(u, scalar))
  infix def *(scalar: Usage)(using SourceInfo): Usages = us1.map(u => UsageProd(u, UsageLiteral(scalar)))


def checkData(data: Data)
  (using Σ: Signature)
  (using ctx: TypingContext)
: Either[IrError, Unit] = ctx.trace(s"checking data signature ${data.qn}") {
  given Context = IndexedSeq()

  val tParams = data.tParamTys.map(_._1)
  checkParameterTypeDeclarations(tParams) >>
    checkULevel(data.ul)(using tParams.toIndexedSeq) >> Right(())
}

def checkDataConstructor(qn: QualifiedName, con: Constructor)
  (using Σ: Signature)
  (using ctx: TypingContext)
: Either[IrError, Unit] = ctx.trace(s"checking data constructor $qn.${con.name}") {
  Σ.getDataOption(qn) match
    case None => Left(MissingDeclaration(qn))
    case Some(data) =>
      given Γ: Context = data.tParamTys.map(_._1).toIndexedSeq

      for _ <- checkParameterTypeDeclarations(con.paramTys, Some(data.ul))
          _ <- {
            given Γ2: Context = Γ ++ con.paramTys

            // Note, weakening data.tParamTys is not necessary because data.tParamTys contains no free
            // vars
            checkTypes(con.tArgs, data.tParamTys.map(_._1))
          }
      yield
        // binding of positiveVars must be either covariant or invariant
        // binding of negativeVars must be either contravariant or invariant
        val (positiveVars, negativeVars) = getFreeVars(con.paramTys)(using 0)
        val tParamTysSize = data.tParamTys.size
        val bindingWithIncorrectUsage = data.tParamTys.zipWithIndex.filter {
          case ((_, variance), reverseIndex) =>
            val index = tParamTysSize - reverseIndex - 1
            variance match
              case Variance.INVARIANT => false
              case Variance.COVARIANT => negativeVars(index)
              case Variance.CONTRAVARIANT => positiveVars(index)
        }
        if bindingWithIncorrectUsage.isEmpty then ()
        else Left(IllegalVarianceInData(data.qn, bindingWithIncorrectUsage.map(_._2)))
}

def checkDataConstructors(qn: QualifiedName, constructors: Seq[Constructor])
  (using Σ: Signature)
  (using ctx: TypingContext)
: Either[IrError, Unit] =
  given Context = IndexedSeq()


  allRight(constructors.map { con => checkDataConstructor(qn, con) }) >>
    checkInherentEqDecidable(Σ.getData(qn), constructors)

def checkRecord(record: Record)
  (using Σ: Signature)
  (using ctx: TypingContext)
: Either[IrError, Unit] = ctx.trace(s"checking record signature ${record.qn}") {
  given Context = IndexedSeq()

  val tParams = record.tParamTys.map(_._1)
  checkParameterTypeDeclarations(tParams) >>
    checkULevel(record.ul)(using tParams.toIndexedSeq) >> Right(())
}

def checkRecordField(qn: QualifiedName, field: Field)
  (using Σ: Signature)
  (using ctx: TypingContext)
: Either[IrError, Unit] = ctx.trace(s"checking record field $qn.${field.name}") {
  Σ.getRecordOption(qn) match
    case None => Left(MissingDeclaration(qn))
    case Some(record) =>
      given Context = record.tParamTys.map(_._1).toIndexedSeq :+ getRecordSelfBinding(record)

      for _ <- checkIsCType(field.ty, Some(record.ul.weakened))
        yield
          // binding of positiveVars must be either covariant or invariant
          // binding of negativeVars must be either contravariant or invariant
          val (positiveVars, negativeVars) = getFreeVars(field.ty)(using 0)
          val tParamTysSize = record.tParamTys.size
          val bindingWithIncorrectUsage = record.tParamTys.zipWithIndex.filter {
            case ((_, variance), reverseIndex) =>
              val index = tParamTysSize - reverseIndex // Offset by 1 to accommodate self reference
              variance match
                case Variance.INVARIANT => false
                case Variance.COVARIANT => negativeVars(index)
                case Variance.CONTRAVARIANT => positiveVars(index)
          }
          if bindingWithIncorrectUsage.isEmpty then ()
          else Left(IllegalVarianceInRecord(record.qn, bindingWithIncorrectUsage.map(_._2)))
}

def checkRecordFields(qn: QualifiedName, fields: Seq[Field])
  (using Σ: Signature)
  (using ctx: TypingContext)
: Either[IrError, Unit] =
  given Context = IndexedSeq()

  allRight(fields.map { field => checkRecordField(qn, field) })

def getRecordSelfBinding(record: Record): Binding[VTerm] = Binding(
  U(
    RecordType(
      record.qn,
      (record.tParamTys.size - 1).to(0, -1).map(Var(_)).toList,
      Total
    )
  ),
  U1
)(record.selfName)

def checkDef(definition: Definition)
  (using Σ: Signature)
  (using ctx: TypingContext)
: Either[IrError, Unit] = ctx.trace(s"checking def signature ${definition.qn}") {
  given Context = IndexedSeq()

  checkIsCType(definition.ty)
}

def checkClause(qn: QualifiedName, clause: Clause)
  (using Σ: Signature)
  (using ctx: TypingContext)
: Either[IrError, Unit] = ctx.trace(s"checking def clause $qn") {
  val lhs = clause.lhs.foldLeft(Some(Def(qn)): Option[CTerm]) {
    case (Some(f), p) => p.toElimination match
      case Some(ETerm(t)) => Some(Application(f, t))
      case Some(EProj(name)) => Some(Projection(f, name))
      case None => None
    case (None, _) => None
  }
  lhs match
    case None => Right(()) // skip checking absurd clauses
    case Some(lhs) =>
      given Context = clause.bindings.toIndexedSeq

      checkType(lhs, clause.ty) >> checkType(clause.rhs, clause.ty) >> Right(())
}

def checkClauses(qn: QualifiedName, clauses: Seq[Clause])
  (using Σ: Signature)
  (using ctx: TypingContext)
: Either[IrError, Unit] =
  allRight(clauses.map { clause => checkClause(qn, clause) })

def checkEffect(effect: Effect)
  (using Σ: Signature)
  (using ctx: TypingContext)
: Either[IrError, Unit] = ctx.trace(s"checking effect signature ${effect.qn}") {
  given Context = IndexedSeq()

  checkParameterTypeDeclarations(effect.tParamTys) >> checkAreEqDecidableTypes(effect.tParamTys)
}

def checkOperator(qn: QualifiedName, operator: Operator)
  (using Σ: Signature)
  (using ctx: TypingContext)
: Either[IrError, Unit] = ctx.trace(s"checking effect operator $qn.${operator.name}") {
  Σ.getEffectOption(qn) match
    case None => Left(MissingDeclaration(qn))
    case Some(effect) =>
      val Γ = effect.tParamTys.toIndexedSeq

      checkParameterTypeDeclarations(operator.paramTys)(using Γ) >>
        checkIsType(operator.resultTy)(using Γ ++ operator.paramTys)
}

def checkOperators(qn: QualifiedName, operators: Seq[Operator])
  (using Σ: Signature)
  (using ctx: TypingContext)
: Either[IrError, Unit] =
  allRight(operators.map { operator => checkOperator(qn, operator) })

private def checkParameterTypeDeclarations(tParamTys: Telescope, levelBound: Option[ULevel] = None)
  (using Γ: Context)
  (using Σ: Signature)
  (using ctx: TypingContext)
: Either[IrError, Unit] = tParamTys match
  case Nil => Right(())
  case binding :: rest =>
    checkIsType(binding.ty, levelBound) >>
      checkIsEqDecidableTypes(binding.ty) >>
      checkSubsumption(binding.usage, UsageLiteral(UUnres), Some(UsageType(None))) >>
      checkParameterTypeDeclarations(rest)(using Γ :+ binding)

private def checkULevel(ul: ULevel)
  (using Γ: Context)
  (using Σ: Signature)
  (using ctx: TypingContext)
: Either[IrError, Usages] = ul match
  case ULevel.USimpleLevel(l) => checkType(l, LevelType())
  case ULevel.UωLevel(_) => Right(Usages.zero)

def inferType(tm: VTerm)
  (using Γ: Context)
  (using Σ: Signature)
  (using ctx: TypingContext)
: Either[IrError, (VTerm, Usages)] =
  debugInfer(
    tm, tm match
      case Type(ul, upperBound) =>
        for ulUsages <- checkULevel(ul)
            (upperBoundTy, upperBoundUsages) <- inferType(upperBound)
            _ <- upperBoundTy match
              case Type(ul2, _) =>
                checkULevelSubsumption(ul, ul2)(using CheckSubsumptionMode.CONVERSION)
              case _ => Left(ExpectVType(upperBound))
        yield (Type(ULevelSuc(ul), tm), (ulUsages + upperBoundUsages) * UUnres)
      case Top(ul, u, eqD) =>
        for
          ulUsage <- checkULevel(ul)
          uUsage <- checkType(u, UsageType(None))
          eqDUsage <- checkType(eqD, EqDecidabilityType())
        yield (Type(ul, tm), (ulUsage + uUsage + eqDUsage) * UUnres)
      case r: Var => Right((Γ.resolve(r).ty), Usages.single(r))
      case Collapse(cTm) =>
        for (cTy, usage) <- inferType(cTm)
            r <- cTy match
              case F(vTy, eff, _) if eff == Total => Right(vTy)
              case F(_, _, _) => Left(CollapsingEffectfulTerm(cTm))
              case _ => Left(NotCollapsable(cTm))
        yield (r, usage)
      case U(cty) =>
        for (ctyTy, usage) <- inferType(cty)
            r <- ctyTy match
              case CType(ul, _, eff) if eff == Total => Right(Type(ul, tm))
              // Automatically promote SomeVType to F(SomeVType)
              case F(Type(ul, _), eff, _) if eff == Total => Right(Type(ul, tm))
              case CType(_, _, _) | F(Type(_, _), _, _) => Left(EffectfulCTermAsType(cty))
              case _ => Left(NotTypeError(tm))
        yield (r, usage * UUnres)
      case Thunk(c) =>
        for (cty, usage) <- inferType(c)
          yield (U(cty), usage)
      case DataType(qn, args) =>
        Σ.getDataOption(qn) match
          case None => Left(MissingDeclaration(qn))
          case Some(data) =>
            for
              usage <- checkTypes(args, data.tParamTys.map(_._1))
            yield (Type(data.ul.map(_.substLowers(args: _*)), tm), usage * UUnres)
      case _: Con => throw IllegalArgumentException("cannot infer type")
      case EqualityType(ty, left, right) =>
        for (tyTy, tyUsage) <- inferType(ty)
            r <- tyTy match
              case Type(ul, _) =>
                for leftUsage <- checkType(left, ty)
                    rightUsage <- checkType(right, ty)
                yield (Type(ul, tm), (tyUsage + leftUsage + rightUsage) * UUnres)
              case _ => Left(NotTypeError(ty))
        yield r
      case Refl() => throw IllegalArgumentException("cannot infer type")
      case UsageLiteral(u) => Right(UsageType(Some(u)), Usages.zero)
      case UsageCompound(_, operands) =>
        for usagesSeq <- transpose(operands.multiToSeq.map(o => checkType(o, UsageType(None))))
            usages = usagesSeq.reduce(_ + _)
            bound <- tm.normalized match
              case Right(UsageLiteral(u)) => Right(Some(u))
              case _ => Right(None)
        yield (UsageType(bound), usages)
      case u: UsageType => Right(Type(ULevel.USimpleLevel(LevelLiteral(0)), u), Usages.zero)
      case eqD: EqDecidabilityType => Right(Type(ULevel.USimpleLevel(LevelLiteral(0)), eqD), Usages.zero)
      case _: EqDecidabilityLiteral => Right(EqDecidabilityType(), Usages.zero)
      case e: EffectsType => Right(Type(ULevel.USimpleLevel(LevelLiteral(0)), e), Usages.zero)
      case Effects(literal, unionOperands) =>
        for
          literalUsages <- transpose(
            literal.map { (qn, args) =>
              Σ.getEffectOption(qn) match
                case None => Left(MissingDeclaration(qn))
                case Some(effect) => checkTypes(args, effect.tParamTys)
            }
          ).map(_.reduce(_ + _))
          operandsUsages <- transpose(
            unionOperands.map { ref => checkType(ref, EffectsType()) }
          ).map(_.reduce(_ + _))
        yield (EffectsType(), literalUsages + operandsUsages)
      case LevelType() => Right((Type(UωLevel(0), LevelType())), Usages.zero)
      case Level(_, maxOperands) =>
        for
          usages <- transpose(maxOperands.map { (ref, _) => checkType(ref, LevelType()) }.toList).map(_.reduce(_ + _))
        yield (LevelType(), usages)
      case HeapType() => Right((Type(USimpleLevel(LevelLiteral(0)), HeapType())), Usages.zero)
      case _: Heap => Right(HeapType(), Usages.zero)
      case cellType@CellType(heap, ty, _) =>
        for heapUsages <- checkType(heap, HeapType())
            (tyTy, tyUsages) <- inferType(ty)
            r <- tyTy match
              case Type(ul, _) => Right(Type(ul, cellType))
              case _ => Left(NotTypeError(ty))
        yield (r, (heapUsages + tyUsages) * UUnres)
      case Cell(_, _) => throw IllegalArgumentException("cannot infer type")
  )

def checkType(tm: VTerm, ty: VTerm)
  (using Γ: Context)
  (using Σ: Signature)
  (using ctx: TypingContext)
: Either[IrError, Usages] = debugCheck(
  tm, ty, tm match
    case Con(name, args) => ty match
      case DataType(qn, tArgs) =>
        Σ.getConstructorOption(qn, name) match
          case None => Left(MissingConstructor(name, qn))
          case Some(con) => checkTypes(args, con.paramTys.substLowers(tArgs: _*))
      case _ => Left(ExpectDataType(ty))
    case Refl() => ty match
      case EqualityType(ty, left, right) =>
        for _ <- checkSubsumption(left, right, Some(ty))(using CONVERSION)
        yield Usages.zero
      case _ => Left(ExpectEqualityType(ty))
    case Cell(heapKey, _) => ty match
      case CellType(heap, _, _) if Heap(heapKey) == heap => Right(Usages.zero)
      case _: CellType => Left(ExpectCellTypeWithHeap(heapKey))
      case _ => Left(ExpectCellType(ty))
    case _ =>
      for (inferred, usages) <- inferType(tm)
          _ <- checkSubsumption(inferred, ty, None)
      yield usages
)


def inferType(tm: CTerm)
  (using Γ: Context)
  (using Σ: Signature)
  (using ctx: TypingContext)
: Either[IrError, (CTerm, Usages)] =
  debugInfer(
    tm, tm match
      case Hole => throw IllegalArgumentException("hole should only be present during reduction")
      case CType(ul, upperBound, effects) =>
        for effUsages <- checkType(effects, EffectsType())
            ulUsages <- checkULevel(ul)
            (upperBoundTy, upperBoundUsages) <- inferType(upperBound)
            _ <- upperBoundTy match
              case CType(ul2, _, _) => checkULevelSubsumption(
                ul,
                ul2
              )(using CheckSubsumptionMode.CONVERSION)
              case _ => Left(ExpectCType(upperBound))
        yield (CType(ULevelSuc(ul), tm, Total), (effUsages + ulUsages + upperBoundUsages) * UUnres)
      case CTop(ul, effects) =>
        for uUsages <- checkType(effects, EffectsType())
            ulUsages <- checkULevel(ul)
        yield (CType(ul, tm, Total), (uUsages + ulUsages) * UUnres)
      case Def(qn) => Σ.getDefinitionOption(qn) match
        case None => Left(MissingDeclaration(qn))
        case Some(d) => Right((d.ty, Usages.zero))
      case Force(v) =>
        for (vTy, vUsages) <- inferType(v)
            cTy <- vTy match
              case U(cty) => Right(cty)
              case _ => Left(ExpectUType(vTy))
        yield (cTy, vUsages)
      case F(vTy, effects, usage) =>
        for effUsages <- checkType(effects, EffectsType())
            uUsages <- checkType(usage, UsageType(None))
            (vTyTy, vTyUsages) <- inferType(vTy)
            cTyTy <- vTyTy match
              case Type(ul, _) => Right(CType(ul, tm, Total))
              case _ => Left(NotTypeError(vTy))
        yield (cTyTy, (effUsages + uUsages + vTyUsages) * UUnres)
      case Return(v, usage) =>
        for (vTy, vUsages) <- inferType(v)
          yield (F(vTy, Total), vUsages * usage)
      case Let(t, body) =>
        for (tTy, tUsages) <- inferType(t)
            r <- tTy match
              case F(ty, effects, tBindingUsage) =>
                for 
                  tyInherentUsage <- deriveTypeInherentUsage(ty)
                  tyUsage = UsageProd(tyInherentUsage, tBindingUsage)
                  (bodyTy, usages) <- {
                      def isTUnrestricted: Boolean =
                        (for 
                          _ <- checkUsageSubsumption(tyUsage, UsageLiteral(UUnres))(using SUBSUMPTION)
                        yield ()) match
                          case Right(_) => true
                          case Left(_) => false
                      if effects == Total && isTUnrestricted then
                      // Do the reduction onsite so that type checking in sub terms can leverage the
                      // more specific type. More importantly, this way we do not need to reference
                      // the result of a computation in the inferred type.
                        for t <- reduce(t)
                            r <- t match
                              case Return(v, _) => inferType(body.substLowers(v))
                              case c => inferType(body.substLowers(Collapse(c)))
                        yield r
                      // Otherwise, just add the binding to the context and continue type checking.
                      else
                        for (bodyTy, bodyUsages) <- inferType(body)(using Γ :+ Binding(ty, tBindingUsage)(gn"v"))
                            // Report an error if the type of `body` needs to reference the effectful
                            // computation. User should use a dependent sum type to wrap such
                            // references manually to avoid the leak.
                            // TODO: in case weakened failed, provide better error message: ctxTy cannot depend on
                            //  the bound variable
                            _ <- checkVar0Leak(
                              bodyTy,
                              LeakedReferenceToEffectfulComputationResult(t)
                            )
                            _ <- checkUsageSubsumption(UsageProd(bodyUsages.last, tyInherentUsage), tyUsage)(using SUBSUMPTION)
                        yield (bodyTy.strengthened, bodyUsages.dropRight(1))
                }
                yield (augmentEffect(effects, bodyTy), usages)
              case _ => Left(ExpectFType(tTy))
        yield r
      case FunctionType(binding, bodyTy, effects) =>
        for effUsages <- checkType(effects, EffectsType())
            (tyTy, tyUsages) <- inferType(binding.ty)
            (funTyTy, bodyTyUsages) <- tyTy match
              case Type(ul1, _) =>
                for (bodyTyTy, bodyTyUsages) <- inferType(bodyTy)(using Γ :+ binding)
                    r <- bodyTyTy match
                      case CType(ul2, _, eff) if eff == Total =>
                        // strengthen is safe here because if it references the binding, then the
                        // binding must be at level ω and hence ULevelMax would return big type.
                        Right((CType(ULevelMax(ul1, ul2.strengthened), tm, Total)), bodyTyUsages.dropRight(1))
                      // Automatically promote Return(SomeVType) to F(SomeVType) and proceed type
                      // inference.
                      case F(Type(ul2, _), eff, _) if eff == Total =>
                        Right(CType(ULevelMax(ul1, ul2.strengthened), tm, Total), bodyTyUsages.dropRight(1))
                      case CType(_, _, _) | F(Type(_, _), _, _) =>
                        Left(EffectfulCTermAsType(bodyTy))
                      case _ => Left(NotCTypeError(bodyTy))
                yield r
              case _ => Left(NotTypeError(binding.ty))
        yield (funTyTy, (effUsages + tyUsages + bodyTyUsages) * UUnres)
      case Application(fun, arg) =>
        for (funTy, funUsages) <- inferType(fun)
            r <- funTy match
              case FunctionType(binding, bodyTy, effects) =>
                for argUsages <- checkType(arg, binding.ty)
                    bodyTy <- reduceCType(bodyTy.substLowers(arg))
                yield (augmentEffect(effects, bodyTy), funUsages + argUsages)
              case _ => Left(ExpectFunction(fun))
        yield r
      case RecordType(qn, args, effects) =>
        Σ.getRecordOption(qn) match
          case None => Left(MissingDeclaration(qn))
          case Some(record) =>
            for
              effUsages <- checkType(effects, EffectsType())
              argsUsages <- checkTypes(args, record.tParamTys.map(_._1))
            yield (CType(record.ul.map(_.substLowers(args: _*)), tm, Total), (effUsages + argsUsages) * UUnres)
      case Projection(rec, name) =>
        for (recTy, recUsages) <- inferType(rec)
            ty <- recTy match
              case RecordType(qn, args, effects) =>
                Σ.getFieldOption(qn, name) match
                  case None => Left(MissingField(name, qn))
                  case Some(f) => Right(
                    augmentEffect(
                      effects,
                      f.ty.substLowers(args :+ Thunk(rec): _*)
                    )
                  )
              case _ => Left(ExpectRecord(rec))
        yield (ty, recUsages)
      case OperatorCall(eff@(qn, tArgs), name, args) =>
        Σ.getEffectOption(qn) match
          case None => Left(MissingDeclaration(qn))
          case Some(effect) =>
            Σ.getOperatorOption(qn, name) match
              case None => Left(MissingDefinition(qn))
              case Some(op) => 
                for
                  effUsages <- checkTypes(tArgs, effect.tParamTys)
                  argsUsages <- checkTypes(args, op.paramTys.substLowers(tArgs: _*))
                yield (F(op.resultTy.substLowers(tArgs ++ args: _*), EffectsLiteral(Set(eff))), effUsages + argsUsages)
      case _: Continuation => throw IllegalArgumentException(
        "continuation is only created in reduction and hence should not be type checked."
      )
      case h@Handler(
      eff@(qn, args),
      otherEffects,
      outputType,
      transform,
      handlers,
      input
      ) =>
        Σ.getEffectOption(qn) match
          case None => Left(MissingDeclaration(qn))
          case Some(effect) =>
            Σ.getOperatorsOption(qn) match
              case None => Left(MissingDefinition(qn))
              case Some(operators) =>
                if handlers.size != operators.size ||
                  handlers.keySet != operators.map(_.name).toSet then
                  Left(UnmatchedHandlerImplementation(qn, handlers.keys))
                else
                  val outputCType = F(outputType, otherEffects)
                  for _ <- checkTypes(args, effect.tParamTys)
                      inputCTy <- inferType(input)
                      r <- inputCTy match
                        case F(inputTy, inputEff, _) =>
                          for _ <- checkType(
                            transform,
                            outputCType.weakened
                          )(using Γ :+ Binding(inputTy, ???)(gn"v"))
                              _ <- checkSubsumption(
                                inputEff,
                                EffectsUnion(otherEffects, EffectsLiteral(Set(eff))),
                                Some(EffectsType())
                              )
                              _ <- allRight(
                                operators.map { opDecl =>
                                  val handlerBody = handlers(opDecl.name)
                                  val (argNames, resumeName) = h.handlersBoundNames(opDecl.name)
                                  val opParamTys = opDecl.paramTys.substLowers(args: _*).zip(
                                    argNames
                                  ).map {
                                    case (binding, argName) => Binding(binding.ty, ???)(argName)
                                  }
                                  val opResultTy = opDecl.resultTy.substLowers(args: _*)
                                  checkType(
                                    handlerBody,
                                    outputCType.weaken(opParamTys.size + 1, 0)
                                  )(
                                    using Γ ++
                                      opParamTys :+
                                      Binding(
                                        U(
                                          FunctionType(
                                            Binding(opResultTy, ???)(gn"res"),
                                            F(
                                              outputType.weaken(opParamTys.size + 1, 0),
                                              otherEffects.weaken(opParamTys.size + 1, 0)
                                            ),
                                            Total
                                          )
                                        ),
                                        ???
                                      )(resumeName)
                                  )
                                }
                              )
                          yield outputCType
                        case _ => Left(ExpectFType(inputCTy))
                  yield r
      case AllocOp(heap, vTy) =>
        checkType(heap, HeapType()) >>
          checkIsType(vTy) >>
          Right(
            F(
              CellType(heap, vTy, CellStatus.Uninitialized),
              EffectsLiteral(Set((Builtins.HeapEffQn, heap :: Nil))),
            )
          )
      case SetOp(cell, value) =>
        for cellTy <- inferType(cell)
            r <- cellTy match
              case CellType(heap, vTy, _) => checkType(value, vTy) >>
                Right(
                  F(
                    CellType(heap, vTy, CellStatus.Initialized),
                    EffectsLiteral(Set((Builtins.HeapEffQn, heap :: Nil))),
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
                    vTy,
                    EffectsLiteral(Set((Builtins.HeapEffQn, heap :: Nil))),
                  )
                )
              case _: CellType => Left(UninitializedCell(tm))
              case _ => Left(ExpectCell(cell))
        yield r
      case h@HeapHandler(otherEffects, _, _, input) =>
        val heapVarBinding = Binding[VTerm](HeapType(), ???)(h.boundName)

        given Context = Γ :+ heapVarBinding

        for inputCTy <- inferType(input)
            r <- inputCTy match
              case F(inputTy, eff, _) =>
                for
                  _ <- checkSubsumption(
                    eff,
                    EffectsUnion(
                      EffectsLiteral(Set((Builtins.HeapEffQn, Var(0) :: Nil))),
                      otherEffects.weakened
                    ),
                    Some(EffectsType())
                  )(using SUBSUMPTION)
                  // TODO: Use more sophisticated check here to catch leak through wrapping heap
                  //  variable inside things. If it's leaked, there is no point using this handler at
                  //  all. Simply using GlobalHeapKey is the right thing to do. This is because a
                  //  creating a leaked heap key itself is performing a side effect with global heap.
                  _ <- checkVar0Leak(inputTy, LeakedReferenceToHeapVariable(input))
                yield F(inputTy.strengthened, otherEffects)
              case _ => Left(ExpectFType(inputCTy))
        yield r
  )

def checkType(tm: CTerm, ty: CTerm)
  (using Γ: Context)
  (using Σ: Signature)
  (using ctx: TypingContext)
: Either[IrError, Usages] = debugCheck(
  tm,
  ty,
  for tmTy <- inferType(tm)
      ty <- reduceCType(ty)
      r <- checkSubsumption(tmTy, ty, None)
  yield r
)

enum CheckSubsumptionMode:
  case SUBSUMPTION, CONVERSION

import CheckSubsumptionMode.*

given CheckSubsumptionMode = SUBSUMPTION

/**
 * @param ty can be [[None]] if `a` and `b` are types
 */
def checkSubsumption(rawSub: VTerm, rawSup: VTerm, rawTy: Option[VTerm])
  (using mode: CheckSubsumptionMode)
  (using Γ: Context)
  (using Σ: Signature)
  (using ctx: TypingContext)
: Either[IrError, Unit] =
  def impl: Either[IrError, Unit] =
    if rawSub == rawSup then return Right(())
    val ty = rawTy.map(_.normalized) match
      case None => None
      case Some(Right(v)) => Some(v)
      case Some(Left(e)) => return Left(e)
    (rawSub.normalized, rawSup.normalized) match
      case (Left(e), _) => Left(e)
      case (_, Left(e)) => Left(e)
      case (Right(sub), Right(sup)) =>
        (sub, sup, ty) match
          case (Type(ul1, upperBound1), Type(ul2, upperBound2), _) =>
            checkULevelSubsumption(ul1, ul2) >> checkSubsumption(upperBound1, upperBound2, None)
          case (ty, Top(ul2, usage2, eqD2), _) =>
            for tyTy <- inferType(ty)
                usage1 <- deriveTypeInherentUsage(ty)
                _ <- checkUsageSubsumption(usage1, usage2)
                eqD1 <- deriveTypeInherentEqDecidability(ty)
                _ <- checkEqDecidabilitySubsumption(eqD1, eqD2)
                r <- tyTy match
                  case Type(ul1, _) => checkULevelSubsumption(ul1, ul2)
                  case _ => Left(NotTypeError(sub))
            yield r
          case (U(cty1), U(cty2), _) => checkSubsumption(cty1, cty2, None)
          case (Thunk(c1), Thunk(c2), Some(U(ty))) => checkSubsumption(c1, c2, Some(ty))
          case (DataType(qn1, args1), DataType(qn2, args2), _) if qn1 == qn2 =>
            Σ.getDataOption(qn1) match
              case None => Left(MissingDeclaration(qn1))
              case Some(data) =>
                var args = IndexedSeq[VTerm]()
                allRight(
                  args1.zip(args2).zip(data.tParamTys).map {
                    case ((arg1, arg2), (binding, variance)) =>
                      variance match
                        case Variance.INVARIANT =>
                          val r = checkSubsumption(
                            arg1,
                            arg2,
                            Some(binding.ty.substLowers(args: _*))
                          )(
                            using CONVERSION
                          )
                          args = args :+ arg1
                          r
                        case Variance.COVARIANT =>
                          val r = checkSubsumption(
                            arg1,
                            arg2,
                            Some(binding.ty.substLowers(args: _*))
                          )
                          args = args :+ arg1
                          r
                        case Variance.CONTRAVARIANT =>
                          val r = checkSubsumption(
                            arg2,
                            arg1,
                            Some(binding.ty.substLowers(args: _*))
                          )
                          args = args :+ arg2
                          r
                  }
                )
          case (Con(name1, args1), Con(name2, args2), Some(DataType(qn, _))) if name1 == name2 =>
            Σ.getConstructorOption(qn, name1) match
              case None => Left(MissingConstructor(name1, qn))
              case Some(con) =>
                var args = IndexedSeq[VTerm]()
                allRight(
                  args1.zip(args2).zip(con.paramTys).map {
                    case ((arg1, arg2), binding) =>
                      val r = checkSubsumption(arg1, arg2, Some(binding.ty.substLowers(args: _*)))
                      args = args :+ arg1
                      r
                  }
                )
          case (UsageType(Some(u1)), UsageType(Some(u2)), _) if mode == SUBSUMPTION && u1 >= u2 =>
            Right(())
          case (UsageType(Some(_)), UsageType(None), _) if mode == SUBSUMPTION => Right(())
          case (EqualityType(ty1, a1, b1), EqualityType(ty2, a2, b2), _) =>
            checkSubsumption(ty1, ty2, None) >>
              checkSubsumption(a1, a2, Some(ty1)) >>
              checkSubsumption(b1, b2, Some(ty1))
          case (CellType(heap1, ty1, status1), CellType(heap2, ty2, status2), _) =>
            for r <- checkSubsumption(heap1, heap2, Some(HeapType())) >>
              checkSubsumption(ty1, ty2, None)(using CONVERSION) >>
              (if status1 == status2 || status1 == CellStatus.Initialized then
                Right(())
              else Left(
                NotVSubsumption(sub, sup, ty, mode)
              ))
            yield r
          case (_, Heap(GlobalHeapKey), Some(HeapType())) if mode == SUBSUMPTION => Right(())
          case (v: Var, ty2, _) if mode == CheckSubsumptionMode.SUBSUMPTION => Γ.resolve(v).ty match
            case Type(_, upperBound) => checkSubsumption(upperBound, ty2, None)
            case _ => Left(NotVSubsumption(sub, sup, ty, mode))
          case (Collapse(c), v, ty) => checkSubsumption(c, Return(v), ty.map(F(_)))
          case (v, Collapse(c), ty) => checkSubsumption(Return(v), c, ty.map(F(_)))
          case _ => Left(NotVSubsumption(sub, sup, ty, mode))

  debugSubsumption(rawSub, rawSup, rawTy, impl)

/**
 * @param ty can be [[None]] if `a` and `b` are types
 */
def checkSubsumption(sub: CTerm, sup: CTerm, ty: Option[CTerm])
  (using mode: CheckSubsumptionMode)
  (using Γ: Context)
  (using Σ: Signature)
  (using ctx: TypingContext)
: Either[IrError, Unit] = debugSubsumption(
  sub, sup, ty, {
    val isTotal = ty.forall(_.asInstanceOf[IType].effects == Total)
    for sub <- if isTotal then reduce(sub) else Right(sub)
        sub <- simplifyLet(sub)
        sup <- if isTotal then reduce(sup) else Right(sup)
        sup <- simplifyLet(sup)
        r <- (sub, sup, ty) match
          case (_, _, _) if sub == sup => Right(())
          case (_, _, Some(FunctionType(binding, bodyTy, _))) =>
            checkSubsumption(
              Application(sub.weakened, Var(0)),
              Application(sup.weakened, Var(0)),
              Some(bodyTy),
            )(using mode)(using Γ :+ binding)
          case (_, _, Some(RecordType(qn, _, _))) =>
            Σ.getFieldsOption(qn) match
              case None => Left(MissingDefinition(qn))
              case Some(fields) => allRight(
                fields.map { field =>
                  checkSubsumption(
                    Projection(sub, field.name),
                    Projection(sup, field.name),
                    Some(field.ty)
                  )
                }
              )
          case (CType(ul1, upperBound1, eff1), CType(ul2, upperBound2, eff2), _) =>
            checkEffSubsumption(eff1, eff2) >>
              checkULevelSubsumption(ul1, ul2) >>
              checkSubsumption(upperBound1, upperBound2, Some(sup))
          case (ty: IType, CTop(ul2, eff2), _) =>
            for tyTy <- inferType(sub)
                r <- tyTy match
                  case CType(ul1, _, _) => checkEffSubsumption(ty.effects, eff2) >>
                    checkULevelSubsumption(ul1, ul2)
                  case _ => Left(NotCTypeError(sub))
            yield r
          case (F(vTy1, eff1, u1), F(vTy2, eff2, u2), _) =>
            for _ <- checkEffSubsumption(eff1, eff2)
                _ <- checkUsageSubsumption(u1, u2)
                r <- checkSubsumption(vTy1, vTy2, None)
            yield r
          case (Return(v1), Return(v2), Some(F(ty, _, _))) => checkSubsumption(v1, v2, Some(ty))
          case (Let(t1, ctx1), Let(t2, ctx2), ty) =>
            for t1CTy <- inferType(t1)
                r <- t1CTy match
                  case F(t1Ty, _, _) =>
                    for t2CTy <- inferType(t2)
                        _ <- checkSubsumption(t1CTy, t2CTy, None)
                        _ <- checkSubsumption(t1, t2, Some(t2CTy))
                        r <- checkSubsumption(
                          ctx1,
                          ctx2,
                          ty.map(_.weakened)
                        )(using mode)(using Γ :+ Binding(t1Ty, ???)(gn"v"))
                    yield r
                  case _ => Left(ExpectFType(t1CTy))
            yield r
          case (FunctionType(binding1, bodyTy1, eff1), FunctionType(binding2, bodyTy2, eff2), _) =>
            checkSubsumption(eff1, eff2, Some(EffectsType())) >>
              checkSubsumption(binding2.ty, binding1.ty, None) >>
              checkSubsumption(bodyTy1, bodyTy2, None)(using mode)(using Γ :+ binding2)
          case (Application(fun1, arg1), Application(fun2, arg2), _) =>
            for fun1Ty <- inferType(fun1)
                fun2Ty <- inferType(fun2)
                _ <- checkSubsumption(fun1Ty, fun2Ty, None)
                _ <- checkSubsumption(fun1, fun2, Some(fun1Ty))
                r <- fun1Ty match
                  case FunctionType(binding, _, _) => checkSubsumption(
                    arg1,
                    arg2,
                    Some(binding.ty)
                  )
                  case _ => Left(NotCSubsumption(sub, sup, ty, mode))
            yield r
          case (RecordType(qn1, args1, eff1), RecordType(qn2, args2, eff2), _) if qn1 == qn2 =>
            Σ.getRecordOption(qn1) match
              case None => Left(MissingDeclaration(qn1))
              case Some(record) =>
                var args = IndexedSeq[VTerm]()
                checkSubsumption(eff1, eff2, Some(EffectsType())) >>
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
                            val r = checkSubsumption(
                              arg1,
                              arg2,
                              Some(binding.ty.substLowers(args: _*))
                            )
                            args = args :+ arg1
                            r
                          case Variance.CONTRAVARIANT =>
                            val r = checkSubsumption(
                              arg2,
                              arg1,
                              Some(binding.ty.substLowers(args: _*))
                            )
                            args = args :+ arg2
                            r
                    }
                  )
          case (Projection(rec1, name1), Projection(rec2, name2), _) if name1 == name2 =>
            for rec1Ty <- inferType(rec1)
                rec2Ty <- inferType(rec2)
                r <- checkSubsumption(rec1Ty, rec2Ty, None)
            yield r
          case (OperatorCall((qn1, tArgs1), name1, args1),
          OperatorCall((qn2, tArgs2), name2, args2), _) if qn1 == qn2 && name1 == name2 =>
            Σ.getOperatorOption(qn1, name1) match
              case None => Left(MissingOperator(name1, qn1))
              case Some(operator) =>
                var args = IndexedSeq[VTerm]()
                Σ.getEffectOption(qn1) match
                  case None => Left(MissingDeclaration(qn1))
                  case Some(effect) =>
                    allRight(
                      tArgs1.zip(tArgs2).zip(effect.tParamTys).map {
                        case ((tArg1, tArg2), binding) =>
                          val r = checkSubsumption(tArg1, tArg2, Some(binding.ty))
                          args = args :+ tArg1
                          r
                      }
                    ) >> allRight(
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
  }
)

private def simplifyLet(t: CTerm)
  (using Γ: Context)
  (using Σ: Signature)
  (using ctx: TypingContext)
: Either[IrError, CTerm] = ctx.trace[IrError, CTerm](
  s"simplify",
  s"${yellow(t.sourceInfo)} ${pprint(t)}",
  successMsg = tm => s"${yellow(tm.sourceInfo)} ${green(pprint(tm))}"
) {
  t match
    case Let(t, ctx) =>
      for
        tTy <- inferType(t)
        r <- tTy match
          case F(_, eff, _) if eff == Total =>
            simplifyLet(ctx.substLowers(Collapse(t))).flatMap(reduce)
          case _ => Right(t)
      yield r
    case _ => Right(t)
}

private def checkInherentUsage(
  data: Data,
  constructors: Seq[Constructor],
)
  (using Σ: Signature)
  (using ctx: TypingContext): Either[IrError, Unit] = data.inherentUsage match
  case UsageLiteral(U1) => Right(())
  case _ =>
    given Γ: Context = data.tParamTys.map(_._1).toIndexedSeq

    def checkTelescope(telescope: Telescope, dataInherentUsage: VTerm)(using Γ: Context): Either[IrError, Unit] = telescope match
      case Nil => Right(())
      case (b@Binding(ty, declaredUsage)) :: telescope =>
        for inherentUsage <- deriveTypeInherentUsage(ty)
            providedUsage = UsageProd(inherentUsage, declaredUsage)
            consumedUsage = UsageProd(inherentUsage, declaredUsage, dataInherentUsage)
            _ <- checkSubsumption(providedUsage, consumedUsage, Some(UsageType(None)(using SiEmpty)))(using SUBSUMPTION)
            _ <- checkTelescope(telescope, dataInherentUsage.weakened)(using Γ :+ b)
        yield ()

      allRight(constructors.map(c => checkTelescope(c.paramTys, data.inherentUsage)))
end checkInherentUsage

private def deriveTypeInherentUsage(ty: VTerm)
  (using Γ: Context)
  (using Σ: Signature)
  (using ctx: TypingContext): Either[IrError, VTerm] = ty match
  case _: Type |  _: UsageType | _: EffectsType | _: LevelType | _: HeapType | _: CellType =>
    Right(UsageLiteral(UUnres))
  case _: EqualityType => Right(UsageLiteral(U0))
  case _: U => Right(UsageLiteral(U1))
  case Top(_, u, _) => Right(u)
  case _: Var | _: Collapse =>
    for tyTy <- inferType(ty)
        r <- tyTy match
          case Type(_, upperBound) => deriveTypeInherentUsage(upperBound)
          case _ => Left(ExpectVType(ty))
    yield r
  case d: DataType => Σ.getDataOption(d.qn) match
    case Some(data) => Right(data.inherentUsage.substLowers(d.args: _*))
    case _ => Left(MissingDeclaration(d.qn))
  case _ => Left(ExpectVType(ty))
end deriveTypeInherentUsage

private def checkInherentEqDecidable(
  data: Data,
  constructors: Seq[Constructor],
)
  (using Σ: Signature)
  (using ctx: TypingContext): Either[IrError, Unit] =
  given Γ: Context = data.tParamTys.map(_._1).toIndexedSeq

  // 1. check that eqD of component type ⪯ eqD of data
  def checkComponentTypes(tys: Telescope, dataEqD: VTerm)
    (using Γ: Context): Either[IrError, Unit] = tys match
    case Nil => Right(())
    case binding :: rest =>
      for
        eqD <- deriveTypeInherentEqDecidability(binding.ty)
        _ <- checkSubsumption(eqD, dataEqD, Some(EqDecidabilityType()))(using SUBSUMPTION)
        _ <- checkComponentTypes(rest, dataEqD.weakened)(using Γ :+ binding)
      yield ()

  // 2. inductively define a set of constructor params and this set must contain all constructor
  //    params in order for the data to be non-EqUnres
  //  base: constructor type and component types whose binding has non-0 usage (component usage is
  //        calculated by product of declared usage in binding and data.inherentUsage).
  //  inductive: bindings that are referenced (not through Collapse to root of the term) inductively
  def checkComponentUsage(constructor: Constructor) =
    val numParams = constructor.paramTys.size
    val inherentUsage = data.inherentUsage.weaken(numParams, 0)
    // all paramTys and usages are weakened to be in the same context with constructor.tArgs
    val allParams: Map[ /* dbIndex */ Nat, ( /* ty */ VTerm, /* usage */ VTerm)] = constructor.paramTys.zipWithIndex
      .map { (binding, i) =>
        (numParams - i, (binding.ty.weaken(numParams - i, 0), binding.usage.weaken(
          numParams - i,
          0
        )))
      }.toMap

    val validatedParams = allParams.filter {
      case (_, (_, usage)) => checkSubsumption(
        UsageProd(usage, inherentUsage),
        UsageLiteral(U1),
        Some(UsageType(None))
      )(
        using SUBSUMPTION
      ) match
        case Right(_) => true
        case _ => false
    }

    def getReferencedConstructorArgs(tm: VTerm): Set[Nat] =
      val (positive, negative) = SkippingCollapseFreeVarsVisitor.visitVTerm(tm)(using 0)
      (positive ++ negative).filter(_ < numParams)

    val startingValidatedParamIndices: Set[Int] = validatedParams.map(numParams - _._1).to(Set) ++ constructor.tArgs.flatMap(
      getReferencedConstructorArgs
    )

    // Note that we do not add usage because the usage of a component is not present at runtime
    val allValidatedParamIndices = startingValidatedParamIndices.bfs(
      dbIndex => getReferencedConstructorArgs(
        allParams(dbIndex)._1
      )
    ).iterator.to(Set)
    if allValidatedParamIndices.size == constructor.paramTys.size then
      Right(())
    else
      Left(NotEqDecidableDueToConstructor(data.qn, constructor.name))

  // 3. check that either data.inherentUsage subsumes U1 OR there is zero or one constructor
  def dataIsPresentAtRuntimeOrThereIsSingleConstructor() =
    if constructors.size <= 1 then
      Right(())
    else
      checkSubsumption(data.inherentUsage, UsageLiteral(U1), Some(UsageType(None)))(using SUBSUMPTION)

  checkSubsumption(
    data.inherentEqDecidability,
    EqDecidabilityLiteral(EqUnres),
    Some(EqDecidabilityType())
  )(using CONVERSION) match
    // short circuit since there is no need to do any check
    case Right(_) => Right(())
    // Call 1, 2, 3
    case _ => dataIsPresentAtRuntimeOrThereIsSingleConstructor() >>
      allRight(
        constructors.map { constructor =>
          checkComponentTypes(constructor.paramTys, data.inherentEqDecidability) >>
            checkComponentUsage(constructor)
        }
      )

private object SkippingCollapseFreeVarsVisitor extends FreeVarsVisitor :
  override def visitCollapse(collapse: Collapse)
    (using bar: Nat)
    (using Σ: Signature): ( /* positive */ Set[Nat], /* negative */ Set[Nat]) = this.combine()


private def deriveTypeInherentEqDecidability(ty: VTerm)
  (using Γ: Context)
  (using Σ: Signature)
  (using ctx: TypingContext): Either[IrError, VTerm] = ty match
  case _: Type | _: EqualityType | _: UsageType | _: EqDecidabilityType | _: EffectsType | _: LevelType | _: HeapType | _: CellType =>
    Right(EqDecidabilityLiteral(EqDecidable))
  case Top(_, _, eqDecidability) => Right(eqDecidability)
  case _: Var | _: Collapse =>
    for tyTy <- inferType(ty)
        r <- tyTy match
          case Type(_, upperBound) => deriveTypeInherentEqDecidability(upperBound)
          case _ => Left(ExpectVType(ty))
    yield r
  case _: U => Right(EqDecidabilityLiteral(EqUnres))
  case d: DataType => Σ.getDataOption(d.qn) match
    case Some(data) => Right(data.inherentEqDecidability.substLowers(d.args: _*))
    case _ => Left(MissingDeclaration(d.qn))
  case _ => Left(ExpectVType(ty))

private def checkIsEqDecidableTypes(ty: VTerm)
  (using Γ: Context)
  (using Σ: Signature)
  (using ctx: TypingContext): Either[IrError, Unit] =
  for
    eqD <- deriveTypeInherentEqDecidability(ty)
    _ <- checkSubsumption(
      eqD, EqDecidabilityLiteral(EqDecidable), Some(EqDecidabilityType())
    )(using CONVERSION)
  yield ()

private def checkAreEqDecidableTypes(telescope: Telescope)
  (using Γ: Context)
  (using Σ: Signature)
  (using ctx: TypingContext): Either[IrError, Unit] = telescope match
  case Nil => Right(())
  case binding :: telescope =>
    for
      _ <- checkIsEqDecidableTypes(binding.ty)
      _ <- checkAreEqDecidableTypes(telescope)(using Γ :+ binding)
    yield ()


private def checkEqDecidabilitySubsumption(eqD1: VTerm, eqD2: VTerm)
  (using mode: CheckSubsumptionMode)
  (using Γ: Context)
  (using Σ: Signature)
  (using ctx: TypingContext)
: Either[IrError, Unit] = (eqD1.normalized, eqD2.normalized) match
  case (Left(e), _) => Left(e)
  case (_, Left(e)) => Left(e)
  case (Right(eqD1), Right(eqD2)) if eqD1 == eqD2 => Right(())
  case (Right(EqDecidabilityLiteral(EqDecidability.EqDecidable)), _) | (_, Right(EqDecidabilityLiteral(EqDecidability.EqUnres))) if mode == SUBSUMPTION =>
    Right(())
  case _ => Left(NotEqDecidabilitySubsumption(eqD1, eqD2, mode))


private def checkUsageSubsumption(usage1: VTerm, usage2: VTerm)
  (using mode: CheckSubsumptionMode)
  (using Γ: Context)
  (using Σ: Signature)
  (using ctx: TypingContext)
: Either[IrError, Unit] = (usage1.normalized, usage2.normalized) match
  case (Left(e), _) => Left(e)
  case (_, Left(e)) => Left(e)
  case (Right(usage1), Right(usage2)) if usage1 == usage2 => Right(())
  // Note on direction of usage comparison: UUnres > U1 but UUnres subsumes U1 when counting usage
  case (Right(UsageLiteral(u1)), Right(UsageLiteral(u2))) if u1 >= u2 && mode == SUBSUMPTION => Right(())
  case (Right(UsageLiteral(UUnres)), _) if mode == SUBSUMPTION => Right(())
  case (Right(v@Var(_)), Right(UsageLiteral(u2))) if mode == SUBSUMPTION => Γ.resolve(v).ty match
    case UsageType(Some(u1Bound)) if u1Bound >= u2 => Right(())
    case _ => Left(NotEqDecidabilitySubsumption(usage1, usage2, mode))
  case _ => Left(NotEqDecidabilitySubsumption(usage1, usage2, mode))

private def checkEffSubsumption(eff1: VTerm, eff2: VTerm)
  (using mode: CheckSubsumptionMode)
  (using Γ: Context)
  (using Σ: Signature)
  (using ctx: TypingContext)
: Either[IrError, Unit] =
  (eff1.normalized, eff2.normalized) match
    case (Left(e), _) => Left(e)
    case (_, Left(e)) => Left(e)
    case (Right(eff1), Right(eff2)) if eff1 == eff2 => Right(())
    case (Right(Effects(literals1, unionOperands1)), Right(Effects(literals2, unionOperands2)))
      if mode == CheckSubsumptionMode.SUBSUMPTION &&
        literals1.subsetOf(literals2) && unionOperands1.subsetOf(unionOperands2) =>
      Right(())
    case _ => Left(NotEffectSubsumption(eff1, eff2, mode))

/**
 * Check that `ul1` is lower or equal to `ul2`.
 */
private def checkULevelSubsumption(ul1: ULevel, ul2: ULevel)
  (using mode: CheckSubsumptionMode)
  (using Γ: Context)
  (using Σ: Signature)
  (using TypingContext)
: Either[IrError, Unit] =
  val ul1Normalized = ul1 match
    case USimpleLevel(v) => v.normalized match
      case Left(e) => return Left(e)
      case Right(v: Var) => USimpleLevel(Level(0, Map(v -> 0)))
      case Right(v) => USimpleLevel(v)
    case _ => ul1
  val ul2Normalized = ul2 match
    case USimpleLevel(v) => v.normalized match
      case Left(e) => return Left(e)
      case Right(v: Var) => USimpleLevel(Level(0, Map(v -> 0)))
      case Right(v) => USimpleLevel(v)
    case _ => ul2

  (ul1Normalized, ul2Normalized) match
    case _ if ul1Normalized == ul2Normalized => Right(())
    case _ if mode == CONVERSION => Left(NotLevelSubsumption(ul1Normalized, ul2Normalized, mode))
    case (USimpleLevel(Level(l1, maxOperands1)), USimpleLevel(Level(l2, maxOperands2)))
      if l1 <= l2 &&
        maxOperands1.forall { (k, v) => maxOperands2.getOrElse(k, -1) >= v } => Right(())
    case (USimpleLevel(_), UωLevel(_)) => Right(())
    case (UωLevel(l1), UωLevel(l2)) if l1 <= l2 => Right(())
    case _ => Left(NotLevelSubsumption(ul1Normalized, ul2Normalized, mode))

def checkTypes(tms: Seq[VTerm], tys: Telescope)
  (using Γ: Context)
  (using Σ: Signature)
  (using ctx: TypingContext)
: Either[IrError, Usages] = ctx.trace("checking multiple terms") {
  if tms.length != tys.length then Left(TelescopeLengthMismatch(tms, tys))
  else transpose(
    tms.zip(tys).zipWithIndex.map {
      case ((tm, binding), index) => checkType(tm, binding.ty.substLowers(tms.take(index): _*))
    }
  ).map(_.reduce(_ + _))
}

def checkIsType(vTy: VTerm, levelBound: Option[ULevel] = None)
  (using Γ: Context)
  (using Σ: Signature)
  (using ctx: TypingContext)
: Either[IrError, Unit] = ctx.trace("checking is type") {
  for vTyTy <- inferType(vTy)
      r <- vTyTy match
        case Type(ul, _) => levelBound match
          case Some(bound) => checkULevelSubsumption(ul, bound)
          case _ => Right(())
        case _ => Left(NotTypeError(vTy))
  yield r
}

def checkIsCType(cTy: CTerm, levelBound: Option[ULevel] = None)
  (using Γ: Context)
  (using Σ: Signature)
  (using ctx: TypingContext)
: Either[IrError, Unit] = ctx.trace("checking is C type") {
  for cTyTy <- inferType(cTy)
      r <- cTyTy match
        case CType(ul, _, eff) if eff == Total => levelBound match
          case Some(bound) => checkULevelSubsumption(ul, bound)
          case _ => Right(())
        case _: CType => Left(EffectfulCTermAsType(cTy))
        case _ => Left(NotCTypeError(cTy))
  yield r
}

def reduceVType(vTy: CTerm)
  (using Γ: Context)
  (using Σ: Signature)
  (using ctx: TypingContext)
: Either[IrError, VTerm] = ctx.trace("reduce V type", Block(yellow(vTy.sourceInfo), pprint(vTy))) {
  for tyTy <- inferType(vTy)
      r <- tyTy match
        case F(Type(_, _), effect, _) if effect == Total =>
          for reducedTy <- reduce(vTy)
              r <- reducedTy match
                case Return(vTy) => Right(vTy)
                case _ => throw IllegalStateException(
                  "type checking has bugs: reduced value of type `F ...` must be `Return ...`."
                )
          yield r
        case F(_, _, _) => Left(EffectfulCTermAsType(vTy))
        case _ => Left(ExpectFType(vTy))
  yield r
}

def reduceCType(cTy: CTerm)
  (using Γ: Context)
  (using Σ: Signature)
  (using ctx: TypingContext)
: Either[IrError, CTerm] = ctx.trace("reduce C type", Block(yellow(cTy.sourceInfo), pprint(cTy))) {
  cTy match
    case _: CType | _: F | _: FunctionType | _: RecordType | _: CTop => Right(cTy)
    case _ =>
      for cTyTy <- inferType(cTy)
          r <- cTyTy match
            case CType(_, _, eff) if eff == Total => reduce(cTy)
            case F(_, eff, _) if eff == Total =>

              def unfoldLet(cTy: CTerm): Either[IrError, CTerm] = cTy match
                // Automatically promote a SomeVType to F(SomeVType).
                case Return(vty) => Right(F(vty)(using cTy.sourceInfo))
                case Let(t, ctx) => reduce(ctx.substLowers(Collapse(t))).flatMap(unfoldLet)
                case c => throw IllegalStateException(s"type checking has bugs: $c should be of form `Return(...)`")

              reduce(cTy).flatMap(unfoldLet)
            case _: CType => Left(EffectfulCTermAsType(cTy))
            case _ => Left(NotCTypeError(cTy))
      yield r
}

private def augmentEffect(eff: VTerm, cty: CTerm): CTerm = cty match
  case CType(ul, upperBound, effects) => CType(ul, upperBound, EffectsUnion(eff, effects))
  case CTop(ul, effects) => CTop(ul, EffectsUnion(eff, effects))
  case F(vTy, effects, usage) => F(vTy, EffectsUnion(eff, effects), usage)
  case FunctionType(binding, bodyTy, effects) => FunctionType(
    binding,
    bodyTy,
    EffectsUnion(eff, effects)
  )
  case RecordType(qn, args, effects) => RecordType(qn, args, EffectsUnion(eff, effects))
  case _ => throw IllegalArgumentException(s"trying to augment $cty with $eff")

private def checkVar0Leak(ty: CTerm | VTerm, error: => IrError)
  (using Σ: Signature): Either[IrError, Unit] =
  val (positiveFreeVars, negativeFreeVars) = ty match
    case ty: CTerm => getFreeVars(ty)(using 0)
    case ty: VTerm => getFreeVars(ty)(using 0)
  if positiveFreeVars(0) || negativeFreeVars(0) then
    Left(error)
  else
    Right(())

def allRight[L](es: Iterable[Either[L, ?]]): Either[L, Unit] =
  es.first {
    case Left(l) => Some(l)
    case _ => None
  } match
    case Some(l) => Left(l)
    case _ => Right(())

extension[L, R1] (e1: Either[L, R1])
  private inline infix def >>[R2](e2: => Either[L, R2]): Either[L, R2] = e1.flatMap(_ => e2)

private def debugCheck[L, R](
  tm: CTerm | VTerm,
  ty: CTerm | VTerm,
  result: => Either[L, R]
)
  (using Context)(using Signature)(using ctx: TypingContext): Either[L, R] =
  ctx.trace(
    s"checking",
    Block(
      ChopDown,
      Aligned,
      yellow(tm.sourceInfo),
      pprint(tm),
      ":",
      yellow(ty.sourceInfo),
      pprint(ty)
    )
  )(
    result
  )

private inline def debugInfer[L, R <: (CTerm | VTerm, ?)](
  tm: CTerm | VTerm,
  result: => Either[L, R]
)
  (using Context)(using Signature)(using ctx: TypingContext): Either[L, R] =
  ctx.trace[L, R](
    s"inferring type",
    Block(ChopDown, Aligned, yellow(tm.sourceInfo), pprint(tm)),
    ty => Block(ChopDown, Aligned, yellow(ty._1.sourceInfo), green(pprint(ty)))
  )(result.map(_._1.withSourceInfo(SiTypeOf(tm.sourceInfo)).asInstanceOf[R]))

private inline def debugSubsumption[L, R](
  rawSub: CTerm | VTerm,
  rawSup: CTerm | VTerm,
  rawTy: Option[CTerm | VTerm],
  result: => Either[L, R]
)
  (using mode: CheckSubsumptionMode)
  (using Context)
  (using Signature)
  (using ctx: TypingContext)
: Either[L, R] =
  val modeString = mode match
    case CheckSubsumptionMode.SUBSUMPTION => "⪯"
    case CheckSubsumptionMode.CONVERSION => "≡"
  ctx.trace(
    s"deciding",
    Block(
      ChopDown, Aligned,
      yellow(rawSub.sourceInfo),
      pprint(rawSub),
      modeString,
      yellow(rawSup.sourceInfo),
      pprint(rawSup),
      ":",
      yellow(rawTy.map(_.sourceInfo).getOrElse(SiEmpty)),
      rawTy.map(pprint)
    )
  )(result)
