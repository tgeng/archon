package com.github.tgeng.archon.core.ir

import com.github.tgeng.archon.common.*
import com.github.tgeng.archon.core.common.*
import com.github.tgeng.archon.core.ir.ULevel.USimpleLevel

import SourceInfo.*

enum Variance:
  case INVARIANT, COVARIANT, CONTRAVARIANT

type TTelescope = List[(Binding[VTerm], Variance)]

given SourceInfo = SiEmpty

enum Declaration:
  case Data(val qn: QualifiedName)
    (
      val tParamTys: TTelescope = Nil,
      /* binding + tParamTys */ val ul: ULevel = ULevel.USimpleLevel(VTerm.LevelLiteral(0)),

      /**
       * Number of parameters among `tParamTys`, the rest are index arguments. This parameter also
       * affects how many arguments should be present in the derived constructor function.
       */
      val numParams: Nat,
      val isPure: Boolean = true,
    )
  case Record(val qn: QualifiedName)
    (
      val tParamTys: TTelescope = Nil, /* binding + tParamTys */
      val ul: ULevel = ULevel.USimpleLevel(VTerm.LevelLiteral(0)),
      val selfName: Ref[Name] = n"self",
    )
  case Definition(val qn: QualifiedName)
    (
      val ty: CTerm,
    )

  /**
   * Note: `tParamTys` can only contain pure value terms. That is, `U` or types that nest `U` are
   * not allowed. This is necessary because type-based handler matching needs a "simple" way to
   * efficiently locate the corresponding handler. Arbitrary logic that can happen during conversion
   * would make it very difficult to implement dynamic handlers efficiently. Also note that this
   * means we also need to conservatively reject `tParamTys` like `[A: Type, a: A]` because
   * there is no way to statically know if `A` could be `U`. In addition, this also rules out any
   * data type that wraps impure computation inside.
   */
  case Effect(val qn: QualifiedName)(val tParamTys: Telescope = Nil)

  def qn: QualifiedName

import Declaration.*

case class Constructor(
  name: Name,
  paramTys: Telescope = Nil, /* + tParamTys */
  /**
   * Arguments passed to the data type constructor. For non-indexed type this should just be a
   * sequence of variables referencing the `tParamTys`. For indexed families, the argument here
   * can be any expressions. For example, for `Vec : (A: Type) -> (n: Nat) -> Type`, this would be
   * [A, 0] for `Nil` and `[A, n + 1]` for `Cons`.
   *
   * Semantically, this is simply adding some equality constraints that requires `tParamTys` to be
   * convertible to these args.
   */
  tArgs: Arguments = Nil, /* + tParamTys + paramTys */
)

case class Field(name: Name, /* + tParamTys + 1 for self */ ty: CTerm)

case class Clause(
  bindings: Telescope,
  lhs: List[CoPattern], /* + bindings */
  rhs: CTerm, /* + bindings */
  ty: CTerm /* + bindings */
)

case class Operator(
  name: Name,
  paramTys: Telescope, /* + tParamTys */
  resultTy: VTerm /* + tParamTys + paramTys */
)

trait Signature:
  given Signature = this

  def getDataOption(qn: QualifiedName): Option[Data]

  def getData(qn: QualifiedName): Data = getDataOption(qn).get

  def getConstructorsOption(qn: QualifiedName): Option[IndexedSeq[Constructor]]

  def getConstructors(qn: QualifiedName): IndexedSeq[Constructor] = getConstructorsOption(qn).get

  def getConstructorOption(qn: QualifiedName, conName: Name): Option[Constructor] =
    for
      constructors <- getConstructorsOption(qn)
      r <- constructors.collectFirst {
        case con if con.name == conName => con
      }
    yield r


  def getRecordOption(qn: QualifiedName): Option[Record]

  def getRecord(qn: QualifiedName): Record = getRecordOption(qn).get

  def getFieldsOption(qn: QualifiedName): Option[IndexedSeq[Field]]

  def getFields(qn: QualifiedName): IndexedSeq[Field] = getFieldsOption(qn).get

  def getFieldOption(qn: QualifiedName, fieldName: Name): Option[Field] =
    for
      fields <- getFieldsOption(qn)
      r <- fields.collectFirst {
        case field if field.name == fieldName => field
      }
    yield r


  def getDefinitionOption(qn: QualifiedName): Option[Definition]

  def getDefinition(qn: QualifiedName): Definition = getDefinitionOption(qn).get

  def getClausesOption(qn: QualifiedName): Option[IndexedSeq[Clause]]

  def getClauses(qn: QualifiedName): IndexedSeq[Clause] = getClausesOption(qn).get

  def getCaseTreeOption(qn: QualifiedName): Option[CaseTree]

  def getCaseTree(qn: QualifiedName): CaseTree = getCaseTreeOption(qn).get


  def getEffectOption(qn: QualifiedName): Option[Effect]

  def getEffect(qn: QualifiedName): Effect = getEffectOption(qn).get

  def getOperatorsOption(qn: QualifiedName): Option[IndexedSeq[Operator]]

  def getOperators(qn: QualifiedName): IndexedSeq[Operator] = getOperatorsOption(qn).get

  def getOperatorOption(qn: QualifiedName, conName: Name): Option[Operator] =
    for
      operators <- getOperatorsOption(qn)
      r <- operators.collectFirst {
        case op if op.name == conName => op
      }
    yield r


  def getOperator(qn: QualifiedName, name: Name): Operator =
    getOperators(qn).getFirstOrDefault(_.name == name, throw IllegalArgumentException())

  import VTerm.*
  import CTerm.*
  import CoPattern.*
  import QualifiedName.*
  given SourceInfo = SiEmpty

  def getDataDerivedDefinitionOption(qn: QualifiedName): Option[Declaration.Definition] =
    for
      data <- getDataOption(qn)
    yield Definition(qn)(
      data.tParamTys.foldRight[CTerm](
        F(Type(data.ul, DataType(qn, vars(data.tParamTys.size - 1))))
      ) { (bindingAndVariance, bodyTy) =>
        bindingAndVariance match
          case (binding, _) => FunctionType(binding, bodyTy)
      }
    )

  def getDataDerivedClausesOption(qn: QualifiedName): Option[IndexedSeq[Clause]] =
    for
      data <- getDataOption(qn)
    yield {
      val highestDbIndex = data.tParamTys.size - 1
      IndexedSeq(
        Clause(
          data.tParamTys.map(_._1),
          pVars(highestDbIndex),
          Return(DataType(qn, vars(highestDbIndex))),
          F(Type(data.ul, DataType(qn, vars(highestDbIndex))))
        )
      )
    }

  def getDataConDerivedDefinitionOption(qn: QualifiedName): Option[Declaration.Definition] =
    qn match
      case Node(dataQn, conName) =>
        for
          data <- getDataOption(dataQn)
          constructor <- getConstructorOption(dataQn, conName)
        yield
          val numIndexArgs = data.tParamTys.size - data.numParams
          Definition(qn)(
            (data.tParamTys.take(data.numParams).map(_._1) ++
              constructor.paramTys.strengthen(numIndexArgs, 0))
              .foldRight[CTerm](
                F(
                  DataType(
                    dataQn,
                    constructor.tArgs.map(_.strengthen(numIndexArgs, constructor.paramTys.size))
                  )
                )
              ) { (binding, ty) =>
                FunctionType(binding, ty)
              }
          )
      case _ => None


  def getDataConDerivedClausesOption(qn: QualifiedName): Option[IndexedSeq[Clause]] =
    qn match
      case Node(dataQn, conName) =>
        for
          data <- getDataOption(dataQn)
          constructor <- getConstructorOption(dataQn, conName)
        yield
          val numIndexArgs = data.tParamTys.size - data.numParams
          val allBindings = data.tParamTys.take(data.numParams).map(_._1) ++
            constructor.paramTys.strengthen(numIndexArgs, 0)
          IndexedSeq(
            Clause(
              allBindings,
              pVars(allBindings.size - 1),
              Return(Con(conName, vars(constructor.paramTys.size - 1))),
              F(DataType(dataQn, constructor.tArgs.map(_.strengthen(numIndexArgs, 0))))
            )
          )
      case _ => None

  def getRecordDerivedDefinitionOption(qn: QualifiedName): Option[Declaration.Definition] =
    for
      record <- getRecordOption(qn)
    yield Definition(qn)(
      record.tParamTys.foldRight[CTerm](
        CType(record.ul, RecordType(qn, vars(record.tParamTys.size - 1)))
      ) { (bindingAndVariance, bodyTy) =>
        bindingAndVariance match
          case (binding, _) => FunctionType(binding, bodyTy)
      }
    )

  def getRecordDerivedClausesOption(qn: QualifiedName): Option[IndexedSeq[Clause]] =
    for
      record <- getRecordOption(qn)
    yield {
      val highestDbIndex = record.tParamTys.size - 1
      IndexedSeq(
        Clause(
          record.tParamTys.map(_._1),
          pVars(highestDbIndex),
          RecordType(qn, vars(highestDbIndex)),
          CType(record.ul, RecordType(qn, vars(highestDbIndex)))
        )
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
              Binding(U(RecordType(recordQn, vars(record.tParamTys.size - 1))))(record.selfName),
              field.ty
            )
          ) { (bindingAndVariance, bodyTy) =>
            bindingAndVariance match
              case (binding, _) => FunctionType(binding, bodyTy)
          }
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
                  vars(record.tParamTys.size - 1)
                )
              )
            )(record.selfName),
            pVars(record.tParamTys.size),
            Projection(Force(Var(0)), fieldName),
            field.ty
          )
        )
      case _ => None

  def getEffectDerivedDefinitionOption(qn: QualifiedName): Option[Declaration.Definition] =
    for
      effect <- getEffectOption(qn)
    yield Definition(qn)(
      effect.tParamTys.foldRight[CTerm](F(EffectsType())) {
        case (binding, bodyTy) => FunctionType(binding, bodyTy)
      }
    )

  def getEffectDerivedClausesOption(qn: QualifiedName): Option[IndexedSeq[Clause]] =
    for
      effect <- getEffectOption(qn)
    yield {
      val highestDbIndex = effect.tParamTys.size - 1
      IndexedSeq(
        Clause(
          effect.tParamTys,
          pVars(highestDbIndex),
          Return(EffectsLiteral(Set((qn, vars(highestDbIndex))))),
          F(EffectsType())
        )
      )
    }

  def getEffectOpDerivedDefinitionOption(qn: QualifiedName): Option[Declaration.Definition] =
    qn match
      case Node(effectQn, opName) =>
        for
          eff <- getEffectOption(effectQn)
          op <- getOperatorOption(effectQn, opName)
        yield
          val allParamTys = eff.tParamTys ++ op.paramTys
          Definition(qn)(
            allParamTys
              .foldRight[CTerm](
                F(
                  op.resultTy,
                  EffectsLiteral(Set((effectQn, vars(allParamTys.size - 1, op.paramTys.size))))
                )
              ) { (binding, ty) =>
                FunctionType(binding, ty)
              }
          )
      case _ => None

  def getEffectOpDerivedClausesOption(qn: QualifiedName): Option[IndexedSeq[Clause]] =
    qn match
      case Node(effectQn, opName) =>
        for
          eff <- getEffectOption(effectQn)
          op <- getOperatorOption(effectQn, opName)
        yield
          val allBindings = eff.tParamTys ++ op.paramTys
          IndexedSeq(
            Clause(
              allBindings,
              pVars(allBindings.size - 1),
              OperatorCall(
                (effectQn, vars(allBindings.size - 1, op.paramTys.size)),
                opName,
                vars(op.paramTys.size - 1)
              ),
              F(op.resultTy)
            )
          )
      case _ => None

trait BuiltinSignature extends Signature :
  override def getDataOption(qn: QualifiedName): Option[Declaration.Data] =
    Builtins.builtinData.get(qn).map(_._1)
      .orElse(getUserDataOption(qn))

  def getUserDataOption(qn: QualifiedName): Option[Declaration.Data]

  override def getConstructorsOption(qn: QualifiedName): Option[IndexedSeq[Constructor]] =
    Builtins.builtinData.get(qn).map(_._2)
      .orElse(getUserConstructorsOption(qn))

  def getUserConstructorsOption(qn: QualifiedName): Option[IndexedSeq[Constructor]]


  override def getRecordOption(qn: QualifiedName): Option[Declaration.Record] =
    Builtins.builtinRecords.get(qn).map(_._1)
      .orElse(getUserRecordOption(qn))

  def getUserRecordOption(qn: QualifiedName): Option[Declaration.Record]

  override def getFieldsOption(qn: QualifiedName): Option[IndexedSeq[Field]] =
    Builtins.builtinRecords.get(qn).map(_._2)
      .orElse(getUserFieldsOption(qn))

  def getUserFieldsOption(qn: QualifiedName): Option[IndexedSeq[Field]]


  override def getDefinitionOption(qn: QualifiedName): Option[Declaration.Definition] =
    Builtins.builtinDefinitions.get(qn).map(_._1)
      .orElse(getDataDerivedDefinitionOption(qn))
      .orElse(getDataConDerivedDefinitionOption(qn))
      .orElse(getRecordDerivedDefinitionOption(qn))
      .orElse(getRecordFieldDerivedDefinitionOption(qn))
      .orElse(getEffectDerivedDefinitionOption(qn))
      .orElse(getEffectOpDerivedDefinitionOption(qn))
      .orElse(getUserDefinitionOption(qn))
      .orElse(Builtins.getBigType(qn).map(_._1))

  def getUserDefinitionOption(qn: QualifiedName): Option[Declaration.Definition]

  override def getClausesOption(qn: QualifiedName): Option[IndexedSeq[Clause]] =
    Builtins.builtinDefinitions.get(qn).map(_._2)
      .orElse(getDataDerivedClausesOption(qn))
      .orElse(getDataConDerivedClausesOption(qn))
      .orElse(getRecordDerivedClausesOption(qn))
      .orElse(getRecordFieldDerivedClausesOption(qn))
      .orElse(getEffectDerivedClausesOption(qn))
      .orElse(getEffectOpDerivedClausesOption(qn))
      .orElse(getUserClausesOption(qn))
      .orElse(Builtins.getBigType(qn).map(_._2))

  def getUserClausesOption(qn: QualifiedName): Option[IndexedSeq[Clause]]

  // TODO: getUserCaseTree...

  override def getEffectOption(qn: QualifiedName): Option[Declaration.Effect] =
    Builtins.builtinEffects.get(qn).map(_._1)
      .orElse(getUserEffectOption(qn))

  def getUserEffectOption(qn: QualifiedName): Option[Declaration.Effect]

  override def getOperatorsOption(qn: QualifiedName): Option[IndexedSeq[Operator]] =
    Builtins.builtinEffects.get(qn).map(_._2)
      .orElse(getUserOperatorsOption(qn))

  def getUserOperatorsOption(qn: QualifiedName): Option[IndexedSeq[Operator]]
