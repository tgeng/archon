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

def checkData(data: Data)
  (using Σ: Signature)
  (using ctx: TypingContext)
: Either[IrError, Unit] = ctx.trace(s"checking data signature ${data.qn}") {
  given Context = IndexedSeq()

  val tParams = data.tParamTys.map(_._1)
  checkParameterTypeDeclarations(tParams) >>
    checkULevel(data.ul)(using tParams.toIndexedSeq)
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
          _ <-
            if data.isIndexable then
              // TODO: use essentiality to guide this check here. Also think about additional
              // requirements for indexable types on top of unrestricted types.
              allRight(con.paramTys.map(binding => checkIsIndexable(binding.ty)(using Γ.size)))
            else
              Right(())
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

  allRight(constructors.map { con => checkDataConstructor(qn, con) })

def checkRecord(record: Record)
  (using Σ: Signature)
  (using ctx: TypingContext)
: Either[IrError, Unit] = ctx.trace(s"checking record signature ${record.qn}") {
  given Context = IndexedSeq()

  val tParams = record.tParamTys.map(_._1)
  checkParameterTypeDeclarations(tParams) >>
    checkULevel(record.ul)(using tParams.toIndexedSeq)
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
  )
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

      checkType(lhs, clause.ty) >> checkType(clause.rhs, clause.ty)
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

  checkParameterTypeDeclarations(effect.tParamTys) >> checkAreIndexableTypes(effect.tParamTys)
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
  case binding :: rest => checkIsType(binding.ty, levelBound) >> checkParameterTypeDeclarations(
    rest
  )(using Γ :+ binding)

private def checkULevel(ul: ULevel)
  (using Γ: Context)
  (using Σ: Signature)
  (using ctx: TypingContext)
: Either[IrError, Unit] = ul match
  case ULevel.USimpleLevel(l) => checkType(l, LevelType())
  case _ => Right(())

def inferType(tm: VTerm)
  (using Γ: Context)
  (using Σ: Signature)
  (using ctx: TypingContext)
: Either[IrError, VTerm] =
  debugInfer(
    tm, tm match
      case Type(ul, upperBound) =>
        for _ <- checkULevel(ul)
            upperBoundTy <- inferType(upperBound)
            _ <- upperBoundTy match
              case Type(ul2, _) => checkULevelSubsumption(
                ul,
                ul2
              )(using CheckSubsumptionMode.CONVERSION)
              case _ => Left(ExpectVType(upperBound))
        yield Type(ULevelSuc(ul), tm)
      case Indexable(ul) => Right(Type(ul, tm))
      case Top(ul) => Right(Type(ul, tm))
      case r: Var => Right(Γ.resolve(r).ty)
      case Collapse(cTm) =>
        for cTy <- inferType(cTm)
            r <- cTy match
              case F(vTy, eff) if eff == Total => Right(vTy)
              case F(_, _) => Left(CollapsingEffectfulTerm(cTm))
              case _ => Left(NotCollapsable(cTm))
        yield r
      case U(cty) =>
        for ctyTy <- inferType(cty)
            r <- ctyTy match
              case CType(ul, _, eff) if eff == Total => Right(Type(ul, tm))
              // Automatically promote SomeVType to F(SomeVType)
              case F(Type(ul, _), eff) if eff == Total => Right(Type(ul, tm))
              case CType(_, _, _) | F(Type(_, _), _) => Left(EffectfulCTermAsType(cty))
              case _ => Left(NotTypeError(tm))
        yield r
      case Thunk(c) =>
        for cty <- inferType(c)
          yield U(cty)
      case DataType(qn, args) =>
        Σ.getDataOption(qn) match
          case None => Left(MissingDeclaration(qn))
          case Some(data) =>
            checkTypes(
              args,
              data.tParamTys.map(_._1)
            ) >> Right(Type(data.ul.map(_.substLowers(args: _*)), tm))
      case _: Con => throw IllegalArgumentException("cannot infer type")
      case EqualityType(ty, left, right) =>
        for tyTy <- inferType(ty)
            r <- tyTy match
              case Type(ul, _) =>
                checkType(left, ty) >>
                  checkType(right, ty) >>
                  Right(Type(ul, tm))
              case _ => Left(NotTypeError(ty))
        yield r
      case Refl() => throw IllegalArgumentException("cannot infer type")
      case EffectsType() => Right(Type(ULevel.USimpleLevel(LevelLiteral(0)), EffectsType()))
      case Effects(literal, unionOperands) =>
        allRight(
          literal.map { (qn, args) =>
            Σ.getEffectOption(qn) match
              case None => Left(MissingDeclaration(qn))
              case Some(effect) => checkTypes(args, effect.tParamTys)
          }
        ) >> allRight(
          unionOperands.map { ref => checkType(ref, EffectsType()) }
        ) >> Right(EffectsType())
      case LevelType() => Right(Type(UωLevel(0), LevelType()))
      case Level(_, maxOperands) =>
        allRight(maxOperands.map { (ref, _) => checkType(ref, LevelType()) }) >> Right(LevelType())
      case HeapType() => Right(Type(USimpleLevel(LevelLiteral(0)), HeapType()))
      case _: Heap => Right(HeapType())
      case cellType@CellType(heap, ty, _) =>
        for _ <- checkType(heap, HeapType())
            tyTy <- inferType(ty)
            r <- tyTy match
              case Type(ul, _) => Right(Type(ul, cellType))
              case _ => Left(NotTypeError(ty))
        yield r
      case Cell(_, _) => throw IllegalArgumentException("cannot infer type")
  )

def checkType(tm: VTerm, ty: VTerm)
  (using Γ: Context)
  (using Σ: Signature)
  (using ctx: TypingContext)
: Either[IrError, Unit] = debugCheck(
  tm, ty, tm match
    case Con(name, args) => ty match
      case DataType(qn, tArgs) =>
        Σ.getConstructorOption(qn, name) match
          case None => Left(MissingConstructor(name, qn))
          case Some(con) => checkTypes(args, con.paramTys.substLowers(tArgs: _*))
      case _ => Left(ExpectDataType(ty))
    case Refl() => ty match
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
      yield r
)


def inferType(tm: CTerm)
  (using Γ: Context)
  (using Σ: Signature)
  (using ctx: TypingContext)
: Either[IrError, CTerm] =
  debugInfer(
    tm, tm match
      case Hole => throw IllegalArgumentException("hole should only be present during reduction")
      case CType(ul, upperBound, effects) =>
        for _ <- checkType(effects, EffectsType())
            _ <- checkULevel(ul)
            upperBoundTy <- inferType(upperBound)
            _ <- upperBoundTy match
              case CType(ul2, _, _) => checkULevelSubsumption(
                ul,
                ul2
              )(using CheckSubsumptionMode.CONVERSION)
              case _ => Left(ExpectCType(upperBound))
        yield CType(ULevelSuc(ul), tm, Total)
      case CTop(ul, effects) =>
        checkType(effects, EffectsType()) >>
          checkULevel(ul) >>
          Right(CType(ul, tm, Total))
      case Def(qn) => Σ.getDefinitionOption(qn) match
        case None => Left(MissingDeclaration(qn))
        case Some(d) => Right(d.ty)
      case Force(v) =>
        for vTy <- inferType(v)
            r <- vTy match
              case U(cty) => Right(cty)
              case _ => Left(ExpectUType(vTy))
        yield r
      case F(vTy, effects) =>
        for _ <- checkType(effects, EffectsType())
            vTyTy <- inferType(vTy)
            r <- vTyTy match
              case Type(ul, _) => Right(CType(ul, tm, Total))
              case _ => Left(NotTypeError(vTy))
        yield r
      case Return(v) =>
        for vTy <- inferType(v)
          yield F(vTy, Total)
      case Let(t, body) =>
        for tTy <- inferType(t)
            r <- tTy match
              case F(ty, effects) =>
                for ctxTy <-
                      if effects == Total then
                      // Do the reduction onsite so that type checking in sub terms can leverage the
                      // more specific type. More importantly, this way we do not need to reference
                      // the result of a computation in the inferred type.
                        for t <- reduce(t)
                            r <- t match
                              case Return(v) => inferType(body.substLowers(v))
                              case c => inferType(body.substLowers(Collapse(c)))
                        yield r
                      // Otherwise, just add the binding to the context and continue type checking.
                      else
                        for ctxTy <- inferType(body)(using Γ :+ Binding(ty)(gn"v"))
                            // Report an error if the type of `body` needs to reference the effectful
                            // computation. User should use a dependent sum type to wrap such
                            // references manually to avoid the leak.
                            _ <- checkVar0Leak(
                              ctxTy,
                              LeakedReferenceToEffectfulComputationResult(t)
                            )
                        yield ctxTy.strengthened
                yield augmentEffect(effects, ctxTy)
              case _ => Left(ExpectFType(tTy))
        // TODO: in case weakened failed, provide better error message: ctxTy cannot depend on
        //  the bound variable
        yield r
      case FunctionType(binding, bodyTy, effects) =>
        for _ <- checkType(effects, EffectsType())
            tyTy <- inferType(binding.ty)
            r <- tyTy match
              case Type(ul1, _) =>
                for bodyTyTy <- inferType(bodyTy)(using Γ :+ binding)
                    r <- bodyTyTy match
                      case CType(ul2, _, eff) if eff == Total =>
                        // strengthen is safe here because if it references the binding, then the
                        // binding must be at level ω and hence ULevelMax would return big type.
                        Right(CType(ULevelMax(ul1, ul2.strengthened), tm, Total))
                      // Automatically promote Return(SomeVType) to F(SomeVType) and proceed type
                      // inference.
                      case F(Type(ul2, _), eff) if eff == Total =>
                        Right(CType(ULevelMax(ul1, ul2.strengthened), tm, Total))
                      case CType(_, _, _) | F(Type(_, _), _) =>
                        Left(EffectfulCTermAsType(bodyTy))
                      case _ => Left(NotCTypeError(bodyTy))
                yield r
              case _ => Left(NotTypeError(binding.ty))
        yield r
      case Application(fun, arg) =>
        for funTy <- inferType(fun)
            r <- funTy match
              case FunctionType(binding, bodyTy, effects) =>
                for _ <- checkType(arg, binding.ty)
                    bodyTy <- reduceCType(bodyTy.substLowers(arg))
                yield augmentEffect(effects, bodyTy)
              case _ => Left(ExpectFunction(fun))
        yield r
      case RecordType(qn, args, effects) =>
        Σ.getRecordOption(qn) match
          case None => Left(MissingDeclaration(qn))
          case Some(record) =>
            checkType(effects, EffectsType()) >>
              checkTypes(args, record.tParamTys.map(_._1)) >>
              Right(CType(record.ul.map(_.substLowers(args: _*)), tm, Total))
      case Projection(rec, name) =>
        for recTy <- inferType(rec)
            r <- recTy match
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
        yield r
      case OperatorCall(eff@(qn, tArgs), name, args) =>
        Σ.getEffectOption(qn) match
          case None => Left(MissingDeclaration(qn))
          case Some(effect) =>
            Σ.getOperatorOption(qn, name) match
              case None => Left(MissingDefinition(qn))
              case Some(op) => checkTypes(tArgs, effect.tParamTys) >>
                checkTypes(args, op.paramTys.substLowers(tArgs: _*)) >>
                Right(F(op.resultTy.substLowers(tArgs ++ args: _*), EffectsLiteral(Set(eff))))
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
                        case F(inputTy, inputEff) =>
                          for _ <- checkType(
                            transform,
                            outputCType.weakened
                          )(using Γ :+ Binding(inputTy)(gn"v"))
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
                                    case (binding, argName) => Binding(binding.ty)(argName)
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
                                            Binding(opResultTy)(gn"res"),
                                            F(
                                              outputType.weaken(opParamTys.size + 1, 0),
                                              otherEffects.weaken(opParamTys.size + 1, 0)
                                            ),
                                            Total
                                          )
                                        )
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
        val heapVarBinding = Binding[VTerm](HeapType())(h.boundName)

        given Context = Γ :+ heapVarBinding

        for inputCTy <- inferType(input)
            r <- inputCTy match
              case F(inputTy, eff) =>
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
: Either[IrError, Unit] = debugCheck(
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
          case (_, _, Some(EffectsType())) => checkEffSubsumption(sub, sup)
          case (Type(ul1, upperBound1), Type(ul2, upperBound2), _) =>
            checkULevelSubsumption(ul1, ul2) >> checkSubsumption(upperBound1, upperBound2, None)
          case (ty, Top(ul2), _) =>
            for tyTy <- inferType(ty)
                r <- tyTy match
                  case Type(ul1, _) => checkULevelSubsumption(ul1, ul2)
                  case _ => Left(NotTypeError(sub))
            yield r
          case (ty, Indexable(ul2), _) =>
            for tyTy <- inferType(ty)
                r <- tyTy match
                  case Type(ul1, _) => checkULevelSubsumption(ul1, ul2) >> checkIsIndexable(ty)(using 0)
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
          case (F(vTy1, eff1), F(vTy2, eff2), _) =>
            for _ <- checkEffSubsumption(eff1, eff2)
                r <- checkSubsumption(vTy1, vTy2, None)
            yield r
          case (Return(v1), Return(v2), Some(F(ty, _))) => checkSubsumption(v1, v2, Some(ty))
          case (Let(t1, ctx1), Let(t2, ctx2), ty) =>
            for t1CTy <- inferType(t1)
                r <- t1CTy match
                  case F(t1Ty, _) =>
                    for t2CTy <- inferType(t2)
                        _ <- checkSubsumption(t1CTy, t2CTy, None)
                        _ <- checkSubsumption(t1, t2, Some(t2CTy))
                        r <- checkSubsumption(
                          ctx1,
                          ctx2,
                          ty.map(_.weakened)
                        )(using mode)(using Γ :+ Binding(t1Ty)(gn"v"))
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
          case F(
          _,
          eff
          ) if eff == Total => simplifyLet(ctx.substLowers(Collapse(t))).flatMap(reduce)
          case _ => Right(t)
      yield r
    case _ => Right(t)
}

private def checkAreIndexableTypes(telescope: Telescope)
  (using Γ: Context)
  (using Σ: Signature)
  (using ctx: TypingContext): Either[IrError, Unit] = telescope match
  case Nil => Right(())
  case binding :: telescope => checkTypeIsIndexable(binding.ty)(using 0) >> checkAreIndexableTypes(
    telescope
  )(
    using Γ :+ binding
  )

private def checkDataUsage(
  d: Data,
  constructors: Seq[Constructor],
  usage: Usage
)
  (using Σ: Signature)
  (using ctx: TypingContext): Either[IrError, Unit] = ???

private def deriveTypeInherentUsage(ty: VTerm)
  (using Γ: Context)
  (using Σ: Signature)
  (using ctx: TypingContext): Either[IrError, Usage] = ty match
  case _: Type | _: Indexable | _: EqualityType | _: UsageType | _: EffectsType | _: LevelType | _: HeapType | _: CellType =>
    Right(UUnres)
  case _: U => Right(U1)
  case Top(_, u) => Right(u)
  case _: Var | _: Collapse =>
    for tyTy <- inferType(ty)
        r <- tyTy match
          case Type(_, upperBound) => deriveTypeInherentUsage(upperBound)
          case _ => Left(ExpectVType(ty))
    yield r
  case d: DataType => Σ.getDataOption(d.qn) match
    case Some(d) => Right(d.inherentUsage)
    case _ => Left(MissingDeclaration(d.qn))
  case _ => Left(ExpectVType(ty))
end deriveTypeInherentUsage

private def checkDataIsIndexable(
  tm: VTerm,
  constructors: Seq[Constructor],
  usage: Usage
)
  (using Σ: Signature)
  (using ctx: TypingContext): Either[IrError, Unit] = ???


// TODO: reconsider how this should be implemented. Basically it needs to:
//  1. disallow nested thunks
//  2. inherent usage is unrestricted
//  3. runtime available information is sufficient to determine identity
//     a. U0 params must be referenced in types with non-U0 usage, for example Vect is indexable
private def checkTypeIsIndexable(ty: VTerm)
  (using numDataTParams: Nat)
  (using Γ: Context)
  (using Σ: Signature)
  (using ctx: TypingContext): Either[IrError, Unit] = tm match
  // Here we check if upper bound is indexable because otherwise, the this Type type does not admit a
  // normalized representation.
  case Type(_, upperBound) => checkTypeIsIndexable(upperBound)

  case DataType(qn, tArgs) => Σ.getDataOption(qn) match
    case None => Left(MissingDeclaration(qn))
    case Some(data) =>
      if data.isIndexable then
        // TODO: use essentiality as a guide to determine which args need to be checked
        allRight(tArgs.map(checkIsIndexable))
      else
        Left(NotIndexableType(tm))
  case _: U => Left(NotIndexableType(tm))
  case _: Top | _: Indexable | _: EqualityType | EffectsType() | LevelType() | HeapType() | _: CellType =>
    Right(())
  // Treat data type tParams as indexable automatically when checking purity of a data type declaration.
  // This along with the above `DataType` branch works together to delay rejecting something as
  // imindexable at data type instantiation time.
  case Var(idx) if Γ.size - idx <= numDataTParams => Right(())
  case _: Var | _: Collapse =>
    for ty <- inferType(tm)
        r <- ty match
          case Type(ul, upperBound) => checkSubsumption(upperBound, Indexable(ul), None)
          case _ => Right(())
    yield r
  // Any non-type values are considered indexable because the only place that we would invoke this
  // function with non-type value is when checking data type args, where any non-type values would
  // not affect the normalized forms of values created by constructors of this data type.
  case _: Thunk | _: Con | Refl() | _: Effects | _: Level | _: Heap | _: Cell => Right(())

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
: Either[IrError, Unit] = ctx.trace("checking multiple terms") {
  if tms.length != tys.length then Left(TelescopeLengthMismatch(tms, tys))
  else allRight(
    tms.zip(tys).zipWithIndex.map {
      case ((tm, binding), index) => checkType(tm, binding.ty.substLowers(tms.take(index): _*))
    }
  )
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
        case F(Type(_, _), effect) if effect == Total =>
          for reducedTy <- reduce(vTy)
              r <- reducedTy match
                case Return(vTy) => Right(vTy)
                case _ => throw IllegalStateException(
                  "type checking has bugs: reduced value of type `F ...` must be `Return ...`."
                )
          yield r
        case F(_, _) => Left(EffectfulCTermAsType(vTy))
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
            case F(_, eff) if eff == Total =>

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
  case F(vTy, effects) => F(vTy, EffectsUnion(eff, effects))
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

private inline def debugInfer[L, R <: (CTerm | VTerm)](
  tm: CTerm | VTerm,
  result: => Either[L, R]
)
  (using Context)(using Signature)(using ctx: TypingContext): Either[L, R] =
  ctx.trace[L, R](
    s"inferring type",
    Block(ChopDown, Aligned, yellow(tm.sourceInfo), pprint(tm)),
    ty => Block(ChopDown, Aligned, yellow(ty.sourceInfo), green(pprint(ty)))
  )(result.map(_.withSourceInfo(SiTypeOf(tm.sourceInfo)).asInstanceOf[R]))

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