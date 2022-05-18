package com.github.tgeng.archon.core.ast

import collection.mutable
import com.github.tgeng.archon.common.*
import com.github.tgeng.archon.core.common.*
import com.github.tgeng.archon.core.ir.Binding
import com.github.tgeng.archon.core.ir.Builtins
import com.github.tgeng.archon.core.ir.CellStatus
import com.github.tgeng.archon.core.ir.Elimination
import com.github.tgeng.archon.core.ir.TTelescope
import com.github.tgeng.archon.core.ir.Variance
import com.github.tgeng.archon.parser.combinators.single.given
import com.github.tgeng.archon.parser.combinators.{*, given}
import AstTerm.*
import Statement.*
import AstPattern.*
import AstCoPattern.*
import AstDeclaration.*

class AstParser(
  private val globalNameMap: Name => List[QualifiedName]
):

  def dataDecl: StrParser[AstData] = P {
    val constructor: StrParser[AstConstructor] = P {
      for
        name <- name <%< P.from(":") << P.whitespaces
        ty <- rhs <%< P.from(";") << P.whitespaces
      yield AstConstructor(name, ty)
    }

    for
      isPure <- P.from("pure").?.map(_.nonEmpty) << P.whitespaces
      name <- P.from("data") >%> name << P.whitespaces
      tParamTys <- tParamTys <%< P.from(":") << P.whitespaces
      ty <- rhs <%< P.from(";") << P.whitespaces
      constructors <- constructor sepBy P.whitespaces
    yield AstData(name, tParamTys, ty, isPure, constructors)
  }

  def recordDecl: StrParser[AstRecord] = P {
    val field: StrParser[AstField] = P {
      for
        name <- name <%< P.from(":") << P.whitespaces
        ty <- rhs <%< P.from(";") << P.whitespaces
      yield AstField(name, ty)
    }
    for
      name <- P.from("record") >%> name << P.whitespaces
      tParamTys <- tParamTys <%< P.from(":") << P.whitespaces
      ty <- rhs <%< P.from(";") << P.whitespaces
      fields <- field sepBy P.whitespaces
    yield AstRecord(name, tParamTys, ty, fields)
  }

  def defDecl: StrParser[AstDefinition] = P {
    val clause: StrParser[AstClause] = P {
      for
        bindings <- telescope << P.whitespaces
        lhs <- (copattern sepBy P.whitespaces) << P.whitespaces
        _rhs <- (P.from("->") >%> rhs).? << P.whitespaces
        ty <- P.from(":") >%> rhs <%< P.from(";") << P.whitespaces
      yield AstClause(bindings, lhs, _rhs, ty)
    }
    for
      name <- name <%< P.from(":") << P.whitespaces
      ty <- rhs <%< P.from(";") << P.whitespaces
      clauses <- clause sepBy P.whitespaces
    yield AstDefinition(name, ty, clauses)
  }

  def effectDecl: StrParser[AstEffect] = P {
    val operator: StrParser[AstOperator] = P {
      for
        name <- name <%< P.from(":") << P.whitespaces
        ty <- rhs <%< P.from(";") << P.whitespaces
      yield AstOperator(name, ty)
    }
    for
      name <- P.from("effect") >%> name << P.whitespaces
      tParamTys <- tParamTys <%< P.from(";") << P.whitespaces
      operators <- operator sepBy P.whitespaces
      // note: in production code, we should report error if variance is not "invariant"
    yield AstEffect(name, tParamTys.map(_._1), operators)
  }

  private def tParamTys: StrParser[AstTTelescope] = P {
    val variance = (P.from("+").as(Variance.COVARIANT) | P.from("-").as(Variance.CONTRAVARIANT))
      .?.map(_.getOrElse(Variance.INVARIANT))
    val unnamedBinding = atom.map(Binding(_)(n"_"))
    val namedBinding =
      for
        name <- P.from("(") >%> name <%< P.from(":") << P.whitespaces
        ty <- rhs <%< P.from(")")
      yield Binding(ty)(name)
    val bindingWithVariance =
      for
        variance <- variance
        binding <- namedBinding | unnamedBinding
      yield (binding, variance)
    bindingWithVariance sepBy P.whitespaces
  }

  private def telescope: StrParser[AstTelescope] = P {
    val binding: StrParser[Binding[AstTerm]] = P {
      for
        name <- name <%< P.from(":") << P.whitespaces
        ty <- rhs
      yield Binding(ty)(name)
    }
    P.from("{") >%> (binding sepBy (P.whitespaces >> P.from(",") << P.whitespaces)) << P.from("}")
  }

  def copattern: StrParser[AstCoPattern] = P {
    pattern.map(AstCPattern(_)) | P.from("#") >> name.map(AstCProjection(_))
  }

  private def pattern: StrParser[AstPattern] = P {
    val pVar = name.map(AstPVar(_))

    val dataType =
      for qn <- qualifiedName << P.whitespaces
          args <- P.from("{") >%> (pattern sepBy P.whitespaces) <%< P.from("}")
      yield AstPDataType(qn, args)
    val forcedDataType = P.from(".") >> dataType

    val con =
      for name <- name << P.whitespaces
          args <- P.from("{") >%> (pattern sepBy P.whitespaces) <%< P.from("}")
      yield AstPConstructor(name, args)
    val forcedCon = P.from(".") >> con

    val forced = P.from(".(") >%> term.map(AstPForced(_)) <%< P.from(")")

    val absurd = P.from("(") >%> P.from(")").as(AstPAbsurd)

    pVar | dataType | forcedDataType | con | forcedCon | forced | absurd
  }

  def term: StrParser[AstTerm] = P {
    (statement sepBy (P.whitespaces >> P.from(";") << P.whitespaces)).map {
      case STerm(t) :: Nil => t
      case SBinding(_, t) :: Nil => t
      case statements => AstBlock(statements)
    }
  }

  private def statement: StrParser[Statement] = P {
    sBinding | sHandler | sHeapHandler | sTerm
  }

  private enum Handler:
    case HTransform(varName: Name, body: AstTerm)
    case HOp(opName: Name, argsName: List[Name], resumeName: Name, body: AstTerm)

  import Handler.*

  private def sHandler: StrParser[SHandler] = P {

    val transformHandler: StrParser[Handler] =
      for
        name <- P.from("rtn") >%> name <%< P.from("->") << P.whitespaces
        body <- rhs
      yield HTransform(name, body)

    val opHandler: StrParser[Handler] =
      for
        handlerName <- name << P.whitespaces
        argNames <- name sepBy1 P.whitespaces
        _ <- P.whitespaces >> P.from("->") << P.whitespaces
        body <- rhs
      yield HOp(handlerName, argNames.dropRight(1), argNames.last, body)
    for
      _ <- P.from("hdl") << P.whitespaces
      eff <- astEff << P.whitespaces
      otherEffects <- atom << P.whitespaces
      outputType <- atom << P.whitespaces
      _ <- P.from("{") << P.whitespaces
      allHandlers <- (transformHandler | opHandler) sepBy (P.whitespaces >> P.from(";") << P.whitespaces)
      _ <- P.from("}")
    yield
      val handlers = mutable.Map[Name, ( /* op args */ List[Name], /* resume */ Name, AstTerm)]()
      var transformHandler = (n"x", AstVar(n"x"))

      for (h <- allHandlers) { // Use old syntax here because IntelliJ's formatter keeps messing up indentations
        h match
          case HOp(name, opArgs, resume, body) => handlers(name) = (opArgs, resume, body)
          case HTransform(name, t) => transformHandler = (name, t)
      }

      SHandler(
        eff,
        otherEffects,
        outputType,
        transformHandler._1,
        transformHandler._2,
        handlers.toMap
      )
  }

  private def sHeapHandler: StrParser[SHeapHandler] = P {
    for
      _ <- P.from("hpv") << P.whitespaces
      heapVarName <- name << P.whitespaces
      otherEffects <- atom << P.whitespaces
    yield SHeapHandler(otherEffects, heapVarName)
  }

  private def sBinding: StrParser[SBinding] = P {
    for name <- P.from("let") >%> name <%< P.from("=") << P.whitespaces
        t <- rhs
    yield SBinding(name, t)
  }

  private def sTerm: StrParser[STerm] = P(rhs.map(STerm(_)))

  private def app: StrParser[AstTerm] = P(builtins | redux)

  private def rhs: StrParser[AstTerm] = P {
    val argBinding: StrParser[( /* eff */ AstTerm, /* arg name */ Name, /* arg type */ AstTerm)] =
      for
        eff <- eff.?.map(_.getOrElse(AstDef(Builtins.TotalQn)))
        argName <- (name <%< P.from(":") << P.whitespaces).?.map(_.getOrElse(gn"_"))
        argTy <- app
      yield (eff, argName, argTy)

    for
      bindings <- (argBinding <%< P.from("->") << P.whitespaces).*
      bodyTy <- app
    yield bindings.foldRight(bodyTy) { (binding, bodyTy) =>
      binding match
        case (eff, argName, argTy) => AstFunctionType(argName, argTy, bodyTy, eff)
    }
  }

  private def eff: StrParser[AstTerm] = P {

    val effUnion: StrParser[AstTerm] = (app sepBy1 (P.whitespaces >> P.from("|") << P.whitespaces))
      .map {
        case Nil => throw IllegalStateException()
        case t :: rest => rest.foldLeft(t) { (a, b) =>
          AstRedux(
            AstDef(Builtins.EffectsUnionQn),
            Elimination.ETerm(a) :: Elimination.ETerm(b) :: Nil
          )
        }
      }

    P.from("<") >%> effUnion.?.map(_.getOrElse(AstDef(Builtins.TotalQn))) <%< P.from(">") << P.whitespaces
  }

  private def redux: StrParser[AstTerm] = P {
    val elim: StrParser[Elimination[AstTerm]] = P(
      P.from("#") >> name.map(Elimination.EProj(_)) | atom.map(Elimination.ETerm(_))
    )

    for
      head <- atom
      _ <- P.whitespaces
      elims <- elim sepBy P.whitespaces
    yield elims match
      case Nil => head
      case elims => AstRedux(head, elims)
  }

  private def builtins: StrParser[AstTerm] = P {
    (for
      head <- P.stringFrom("clp|U|thk|Cell|UCell|Equality|frc".r)
      _ <- P.whitespaces
      args <- atom sepBy P.whitespaces
      r <- (head, args) match
        case ("clp", t :: Nil) => P.pure(AstCollapse(t))
        case ("U", t :: Nil) => P.pure(AstU(t))
        case ("thk", t :: Nil) => P.pure(AstThunk(t))
        case ("frc", t :: Nil) => P.pure(AstForce(t))
        case _ => P.fail(s"Unexpected number of args for $head")
    yield r) |
      (
        for
          eff <- eff
          t <- atom
        yield AstF(t, eff)
        )
  }

  private def atom: StrParser[AstTerm] = P {
    val astLevelLiteral = P(
      P.from("L") >> P.nat.map(AstLevelLiteral(_))
    )

    val astTotal = P(P.from("<>").map(_ => AstDef(Builtins.TotalQn)))

    val astDef = P(qualifiedName.map(AstDef(_)))

    val astVar = P(name.map(AstVar(_)))

    astTotal |
      astLevelLiteral |
      astVar |
      astDef |
      P.from("(") >%> term <%< P.from(")")
  }

  private def astEff: StrParser[AstEff] = P {
    for qn <- qualifiedName
        args <- P.from("{") >%> (atom sepBy P.whitespaces) <%< P.from("}")
    yield (qn, args)
  }


  private def qualifiedName: StrParser[QualifiedName] = P {
    for
      name <- name
      r <- globalNameMap(name) match
        case qn :: Nil => P.pure(qn)
        case Nil => P.fail(s"'$name' not found")
        case allNames => P.fail(s"'$name' can be any of $allNames")
    yield r
  }

  private def name: StrParser[Name] = P {
    val nameComponent: StrParser[String] = word | symbol

    val underscore: StrParser[String] = P.stringFrom("_".r)

    (for headUnderscore <- underscore.orEmptyString
         components <- nameComponent sepBy1 underscore
         tailUnderscore <- underscore.orEmptyString
    yield Name.Normal(components.mkString(headUnderscore, "_", tailUnderscore))) |
      "`" >> P.stringFrom("[^`]+".r).map(Name.Normal(_)) << "`"
  }

  private val keyWords = Set(
    "hdl",
    "hpv",
    "rtn",
    "let",
    "U",
    "clp",
    "U",
    "thk",
    "frc",

    "pure",
    "data",
    "record",
    "effect",
    "def",
  )

  private def word: StrParser[String] =
    P.stringFrom("(?U)\\p{Alpha}\\p{Alnum}*".r).withFilter(!keyWords(_))

  private val reservedSymbols = Set("|", "#", "->", "<", ">", "<>", ":")

  private def symbol: StrParser[String] =
    P.stringFrom("(?U)[\\p{Graph}&&[^\\p{Alnum}_`.,;(){}]]+".r).withFilter(!reservedSymbols(_))
