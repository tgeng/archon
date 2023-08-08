package com.github.tgeng.archon.core.ir

import com.github.tgeng.archon.common.*
import com.github.tgeng.archon.core.common.*
import com.github.tgeng.archon.core.ir.ULevel.USimpleLevel

import SourceInfo.*

trait DerivedSignature extends Signature:
  override type S <: DerivedSignature
  override def getDefinitionOption(qn: QualifiedName): Option[Declaration.Definition] =
    getDataDerivedDefinitionOption(qn)
      .orElse(getDataConDerivedDefinitionOption(qn))
      .orElse(getRecordDerivedDefinitionOption(qn))
      .orElse(getRecordFieldDerivedDefinitionOption(qn))
      .orElse(getEffectDerivedDefinitionOption(qn))
      .orElse(getEffectOpDerivedDefinitionOption(qn))
      .orElse(getDeclaredDefinitionOption(qn))
      .orElse(getBigType(qn).map(_._1))

  def getDeclaredDefinitionOption(qn: QualifiedName): Option[Declaration.Definition]

  override def getClausesOption(qn: QualifiedName): Option[IndexedSeq[Clause]] =
    getDeclaredClausesOption(qn)
      .orElse(getDataDerivedClausesOption(qn))
      .orElse(getDataConDerivedClausesOption(qn))
      .orElse(getRecordDerivedClausesOption(qn))
      .orElse(getRecordFieldDerivedClausesOption(qn))
      .orElse(getEffectDerivedClausesOption(qn))
      .orElse(getEffectOpDerivedClausesOption(qn))
      .orElse(getBigType(qn).map(_._2))

  def getDeclaredClausesOption(qn: QualifiedName): Option[IndexedSeq[Clause]]

  override def getCaseTreeOption(qn: QualifiedName): Option[CaseTree] =
    getDeclaredCaseTreeOption(qn)
      .orElse(getDataDerivedCaseTreeOption(qn))
      .orElse(getDataConDerivedCaseTreeOption(qn))
      .orElse(getRecordDerivedCaseTreeOption(qn))
      .orElse(getRecordFieldDerivedCaseTreeOption(qn))
      .orElse(getEffectDerivedCaseTreeOption(qn))
      .orElse(getEffectOpDerivedCaseTreeOption(qn))
      .orElse(getBigType(qn).map(_._3))

  def getDeclaredCaseTreeOption(qn: QualifiedName): Option[CaseTree]

  import VTerm.*
  import CTerm.*
  import ULevel.*
  import Usage.*
  import CoPattern.*
  import CaseTree.*
  import QualifiedName.*
  import Declaration.*
  given SourceInfo = SiEmpty
  given Signature = this

  /** Usage paramter itself is only used in typing and hence has U0 */
  private def usageBinding = Binding(UsageType(), UsageLiteral(U0))(n"u")

  private def getBigType
    (qn: QualifiedName)
    : Option[(Definition, IndexedSeq[Clause], CaseTree)] =
    // TODO[P3]: it seems big SubtypeOf is not that useful so I will skip it for now.
    import Name.*
    import QualifiedName.*
    import Builtins.*
    for
      (isComputation, layer) <-
        qn match
          case Node(BuiltinType, Normal(name)) if name.startsWith("TYPE") =>
            name.drop(4).toIntOption.map((false, _))
          case Node(BuiltinType, Normal(name)) if name.startsWith("CTYPE") =>
            name.drop(5).toIntOption.map((true, _))
          case _ => None
      if layer >= 0
    yield (
      new Definition(qn)(
        if isComputation then CType(CType(CTop(UωLevel(layer))))
        else F(Type(Type(Top(UωLevel(layer))))),
      ),
      IndexedSeq(
        Clause(
          IndexedSeq(),
          Nil,
          if isComputation then CType(CTop(UωLevel(layer)))
          else Return(Type(Top(UωLevel(layer)))),
          if isComputation then CType(CType(CTop(UωLevel(layer))))
          else F(Type(Type(Top(UωLevel(layer))))),
        ),
      ),
      if isComputation then CtTerm(CType(CTop(UωLevel(layer))))
      else CtTerm(Return(Type(Top(UωLevel(layer))))),
    )

  def getDataDerivedDefinitionOption
    (qn: QualifiedName)
    : Option[Declaration.Definition] =
    // First parameter is usage type. Declared paramters and indexes follow after.
    for
      data <- getDataOption(qn)
      allParams = data.tParamTys.map(_._1) ++ data.tIndexTys
    yield Definition(qn)(
      FunctionType(
        usageBinding,
        allParams.zipWithIndex.foldRight[CTerm](
          F(Type(DataType(qn, vars(allParams.size - 1))), Var(allParams.size)),
        ) { (bindingAndUsage, bodyTy) =>
          bindingAndUsage match
            case (binding, i) =>
              FunctionType(
                Binding(binding.ty, UsageProd(binding.usage, Var(i)))(binding.name),
                bodyTy,
              )
        },
      ),
    )

  def getDataDerivedClausesOption(qn: QualifiedName): Option[IndexedSeq[Clause]] =
    for data <- getDataOption(qn)
    yield
      val highestDbIndex = data.tParamTys.size
      IndexedSeq(
        Clause(
          usageBinding +: (data.tParamTys.map(_._1) ++ data.tIndexTys).zipWithIndex.map {
            case (binding, i) => Binding(binding.ty, UsageProd(binding.usage, Var(i)))(binding.name)
          },
          qVars(highestDbIndex),
          Return(DataType(qn, vars(highestDbIndex - 1))),
          F(Type(DataType(qn, vars(highestDbIndex - 1))), Var(highestDbIndex)),
        ),
      )

  def getDataConDerivedDefinitionOption(qn: QualifiedName): Option[Declaration.Definition] =
    qn match
      case Node(dataQn, conName) =>
        for
          data <- getDataOption(dataQn)
          constructor <- getConstructorOption(dataQn, conName)
        yield
          val typeParams = data.tParamTys.map(_._1)
          val numTypeParams = typeParams.size
          val constructorParams = constructor.paramTys
          val numAllParams = typeParams.size + constructor.paramTys.size
          val constructorType = constructorParams.foldRight[CTerm](
            F(
              DataType(dataQn, vars(numAllParams - 1, constructorParams.size) ++ constructor.tArgs),
              Var(numTypeParams + constructorParams.size),
            ),
          ) { (binding, ty) =>
            FunctionType(binding, ty)
          }
          Definition(qn)(
            FunctionType(
              usageBinding,
              typeParams
                .foldRight[CTerm](
                  constructorType,
                ) { (binding, ty) =>
                  // Constructor does not consume any type parameters since they only appear in types
                  FunctionType(Binding(binding.ty, U0)(binding.name), ty)
                },
            ),
          )
      case _ => None

  def getDataConDerivedClausesOption(qn: QualifiedName): Option[IndexedSeq[Clause]] =
    qn match
      case Node(dataQn, conName) =>
        for
          data <- getDataOption(dataQn)
          constructor <- getConstructorOption(dataQn, conName)
        yield
          val typeParams = data.tParamTys.map(_._1)
          val constructorParams = constructor.paramTys
          val numAllParams = typeParams.size + constructor.paramTys.size
          IndexedSeq(
            Clause(
              usageBinding +: (typeParams.map(b => Binding(b.ty, U0)(b.name),
              ) ++ constructor.paramTys),
              qVars(numAllParams),
              Return(Con(conName, vars(constructor.paramTys.size - 1))),
              F(
                DataType(
                  dataQn,
                  vars(numAllParams - 1, constructorParams.size) ++ constructor.tArgs,
                ),
                Var(numAllParams),
              ),
            ),
          )
      case _ => None

  def getRecordDerivedDefinitionOption(qn: QualifiedName): Option[Declaration.Definition] =
    for record <- getRecordOption(qn)
    yield Definition(qn)(
      record.tParamTys.foldRight[CTerm](
        CType(RecordType(qn, vars(record.tParamTys.size - 1))),
      ) { (bindingAndVariance, bodyTy) =>
        bindingAndVariance match
          case (binding, _) => FunctionType(binding, bodyTy)
      },
    )

  def getRecordDerivedClausesOption(qn: QualifiedName): Option[IndexedSeq[Clause]] =
    for record <- getRecordOption(qn)
    yield {
      val highestDbIndex = record.tParamTys.size - 1
      IndexedSeq(
        Clause(
          record.tParamTys.map(_._1),
          qVars(highestDbIndex),
          RecordType(qn, vars(highestDbIndex)),
          CType(RecordType(qn, vars(highestDbIndex))),
        ),
      )
    }

  def getRecordFieldDerivedDefinitionOption(qn: QualifiedName): Option[Declaration.Definition] =
    qn match
      case Node(recordQn, fieldName) =>
        for
          record <- getRecordOption(qn)
          field <- getFieldOption(qn, fieldName)
        yield Definition(qn)(
          record.tParamTys.foldRight[CTerm](
            FunctionType(
              Binding(
                U(RecordType(recordQn, vars(record.tParamTys.size - 1))),
                UsageLiteral(U1),
              )(record.selfName),
              field.ty,
            ),
          ) { (bindingAndVariance, bodyTy) =>
            bindingAndVariance match
              case (binding, _) => FunctionType(binding, bodyTy)
          },
        )
      case _ => None

  def getRecordFieldDerivedClausesOption(qn: QualifiedName): Option[IndexedSeq[Clause]] =
    qn match
      case Node(recordQn, fieldName) =>
        for
          record <- getRecordOption(qn)
          field <- getFieldOption(qn, fieldName)
        yield IndexedSeq(
          Clause(
            record.tParamTys.map(_._1) :+ Binding(
              U(
                RecordType(
                  recordQn,
                  vars(record.tParamTys.size - 1),
                ),
              ),
              UsageLiteral(U1),
            )(record.selfName),
            qVars(record.tParamTys.size),
            Projection(Force(Var(0)), fieldName),
            field.ty,
          ),
        )
      case _ => None

  def getEffectDerivedDefinitionOption(qn: QualifiedName): Option[Declaration.Definition] =
    for effect <- getEffectOption(qn)
    yield Definition(qn)(
      FunctionType(
        usageBinding,
        effect.tParamTys.zipWithIndex
          .foldRight[CTerm](F(EffectsType(), Var(effect.tParamTys.size))) {
            case ((binding, i), bodyTy) =>
              FunctionType(
                Binding(binding.ty, UsageProd(binding.usage, Var(i)))(binding.name),
                bodyTy,
              )
          },
      ),
    )

  def getEffectDerivedClausesOption(qn: QualifiedName): Option[IndexedSeq[Clause]] =
    for effect <- getEffectOption(qn)
    yield {
      val highestDbIndex = effect.tParamTys.size
      IndexedSeq(
        Clause(
          usageBinding +: effect.tParamTys.zipWithIndex.map((binding, i) =>
            Binding(binding.ty, UsageProd(binding.usage, Var(i)))(binding.name),
          ),
          qVars(highestDbIndex),
          Return(EffectsLiteral(Set((qn, vars(highestDbIndex - 1))))),
          F(EffectsType(), Var(highestDbIndex)),
        ),
      )
    }

  def getEffectOpDerivedDefinitionOption(qn: QualifiedName): Option[Declaration.Definition] =
    qn match
      case Node(effectQn, opName) =>
        for
          eff <- getEffectOption(effectQn)
          op <- getOperationOption(effectQn, opName)
        yield
          val allParamTys = eff.tParamTys ++ op.paramTys
          Definition(qn)(
            allParamTys
              .foldRight[CTerm](
                F(
                  op.resultTy,
                  EffectsLiteral(
                    Set(
                      (effectQn, vars(allParamTys.size - 1, op.paramTys.size)),
                    ),
                  ),
                ),
              ) { (binding, ty) =>
                FunctionType(binding, ty)
              },
          )
      case _ => None

  def getEffectOpDerivedClausesOption(qn: QualifiedName): Option[IndexedSeq[Clause]] =
    qn match
      case Node(effectQn, opName) =>
        for
          eff <- getEffectOption(effectQn)
          op <- getOperationOption(effectQn, opName)
        yield
          val allBindings = eff.tParamTys ++ op.paramTys
          IndexedSeq(
            Clause(
              allBindings,
              qVars(allBindings.size - 1),
              OperationCall(
                (effectQn, vars(allBindings.size - 1, op.paramTys.size)),
                opName,
                vars(op.paramTys.size - 1),
              ),
              F(op.resultTy),
            ),
          )
      case _ => None

  def getDataDerivedCaseTreeOption(qn: QualifiedName): Option[CaseTree] =
    for data <- getDataOption(qn)
    yield data.tParamTys.foldRight(CtTerm(Return(DataType(qn, vars(data.tParamTys.size - 1))))) {
      case ((binding, _), _Q) => CtLambda(_Q)(binding.name)
    }

  def getDataConDerivedCaseTreeOption(qn: QualifiedName): Option[CaseTree] =
    qn match
      case Node(dataQn, conName) =>
        for
          data <- getDataOption(dataQn)
          constructor <- getConstructorOption(dataQn, conName)
        yield (data.tParamTys.map(_._1) ++ constructor.paramTys)
          .foldRight(CtTerm(Return(Con(conName, vars(constructor.paramTys.size - 1))))) {
            case (binding, _Q) => CtLambda(_Q)(binding.name)
          }
      case _ => None

  def getRecordDerivedCaseTreeOption(qn: QualifiedName): Option[CaseTree] =
    for record <- getRecordOption(qn)
    yield record.tParamTys.foldRight(CtTerm(RecordType(qn, vars(record.tParamTys.size - 1)))) {
      case ((binding, _), _Q) => CtLambda(_Q)(binding.name)
    }

  def getRecordFieldDerivedCaseTreeOption(qn: QualifiedName): Option[CaseTree] =
    qn match
      case Node(recordQn, fieldName) =>
        for
          record <- getRecordOption(qn)
          field <- getFieldOption(qn, fieldName)
        yield record.tParamTys.foldRight(
          CtLambda(CtTerm(Projection(Force(Var(0)), fieldName)))(record.selfName),
        ) { case ((binding, _), _Q) =>
          CtLambda(_Q)(binding.name)
        }

      case _ => None

  def getEffectDerivedCaseTreeOption(qn: QualifiedName): Option[CaseTree] =
    for effect <- getEffectOption(qn)
    yield effect.tParamTys.foldRight(
      CtTerm(Return(Effects(Set((qn, vars(effect.tParamTys.size - 1))), Set.empty))),
    ) { case (binding, _Q) =>
      CtLambda(_Q)(binding.name)
    }

  def getEffectOpDerivedCaseTreeOption(qn: QualifiedName): Option[CaseTree] =
    qn match
      case Node(effectQn, opName) =>
        for
          eff <- getEffectOption(effectQn)
          op <- getOperationOption(effectQn, opName)
        yield
          val allBindings = eff.tParamTys ++ op.paramTys
          allBindings.foldRight(
            CtTerm(
              OperationCall(
                (effectQn, vars(allBindings.size - 1, op.paramTys.size)),
                opName,
                vars(op.paramTys.size - 1),
              ),
            ),
          ) { case (binding, _Q) => CtLambda(_Q)(binding.name) }
      case _ => None
