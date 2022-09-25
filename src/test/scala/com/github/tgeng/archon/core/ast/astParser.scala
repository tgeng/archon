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
import com.github.tgeng.archon.core.ir.SourceInfo
import com.github.tgeng.archon.core.ir.Range
import com.github.tgeng.archon.parser.combinators.{*, given}
import AstTerm.*
import Statement.*
import AstPattern.*
import AstCoPattern.*
import AstDeclaration.*
import SourceInfo.*

object AstParser:
  def declarations: StrParser[List[AstDeclaration]] =
    (dataDecl | recordDecl | defDecl | effectDecl) sepBy P.whitespaces

  def binding: StrParser[Binding[AstTerm]] =
    for
      name <- name <%< P.from(":") << P.whitespaces
      ty <- rhs
    yield Binding(ty)(name)

  def dataDecl: StrParser[AstData] = P {
    val constructor: StrParser[AstConstructor] = P {
      for
        name <- name <%< P.from(":") << P.whitespaces
        ty <- rhs <%< P.from(";") << P.whitespaces
      yield AstConstructor(name, ty)
    }

    for
      isPure <- P.from("pure").??.map(_.nonEmpty) << P.whitespaces
      name <- P.from("data") >%> name << P.whitespaces
      tParamTys <- tParamTys <%< P.from(":") << P.whitespaces
      ty <- rhs <%< P.from(";") << P.whitespaces
      constructors <- constructor sepByGreedy P.whitespaces
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
      fields <- field sepByGreedy P.whitespaces
    yield AstRecord(name, tParamTys, ty, fields)
  }

  def defDecl: StrParser[AstDefinition] = P {
    val clause: StrParser[AstClause] = P {
      for
        bindings <- telescope << P.whitespaces
        lhs <- (copattern sepByGreedy P.whitespaces) << P.whitespaces
        _rhs <- (P.from("=") >%> rhs).? << P.whitespaces
        ty <- P.from(":") >%> rhs <%< P.from(";") << P.whitespaces
      yield AstClause(bindings, lhs, _rhs, ty)
    }
    for
      name <- P.from("def") >%> name << P.whitespaces
      paramTys <- tParamTys.map(_.map(_._1)) <%< P.from(":") << P.whitespaces
      ty <- rhs <%< P.from(";") << P.whitespaces
      clauses <- clause sepByGreedy P.whitespaces
    yield AstDefinition(name, paramTys, ty, clauses)
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
      operators <- operator sepByGreedy P.whitespaces
    // note: in production code, we should report error if variance is not "invariant"
    yield AstEffect(name, tParamTys.map(_._1), operators)
  }

  private def tParamTys: StrParser[AstTTelescope] = P {
    val variance = (P.from("+").as(Variance.COVARIANT) || P
      .from("-")
      .as(Variance.CONTRAVARIANT)).??.map(_.getOrElse(Variance.INVARIANT))
    val unnamedBinding = atom.map(Binding(_)(Name.Unreferenced))
    val namedBinding =
      for
        name <- P.from("(") >%> name <%< P.from(":") << P.whitespaces
        ty <- rhs <%< P.from(")")
      yield Binding(ty)(name)
    val bindingWithVariance =
      for
        variance <- variance
        binding <- namedBinding || unnamedBinding
      yield (binding, variance)
    bindingWithVariance sepByGreedy P.whitespaces
  }

  private def telescope: StrParser[AstTelescope] = P {
    val binding: StrParser[Binding[AstTerm]] = P {
      for
        name <- name <%< P.from(":") << P.whitespaces
        ty <- rhs
      yield Binding(ty)(name)
    }
    P.from("{") >%>
      (binding sepByGreedy (P.whitespaces >> P.from(",") << P.whitespaces))
      << P.from("}")
  }

  def copattern: StrParser[AstCoPattern] = P {
    pattern.map(AstCPattern(_)) || si(P.from("#") >> name)(AstCProjection(_))
  }

  private def pattern: StrParser[AstPattern] = P {
    val pVar = si(name)(AstPVar(_))

    val conParts =
      for
        name <- name << P.whitespaces
        args <- P.from("{") >%> (pattern sepByGreedy P.whitespaces) <%< P.from(
          "}"
        )
      yield (name, args)
    val con = P(si(conParts)(AstPConstructor(_, _)))
    val forcedCon = P(si(P.from(".") >> conParts)(AstPForcedConstructor(_, _)))

    val forced = si(P.from(".(") >%> term <%< P.from(")"))(AstPForced(_))

    val absurd = si(P.from("(") >%> P.from(")"))(_ => AstPAbsurd())

    forcedCon || con || forced || pVar || absurd
  }

  def term: StrParser[AstTerm] = P {
    si(statement sepByGreedy (P.whitespaces >> P.from(";") << P.whitespaces)) {
      case STerm(t) :: Nil       => t
      case SBinding(_, t) :: Nil => t
      case statements            => AstBlock(statements)
    }
  }

  private def statement: StrParser[Statement] = P {
    sBinding || sHandler || sHeapHandler || sTerm
  }

  private enum Handler:
    case HTransform(varName: Name, body: AstTerm)
    case HOp(opName: Name, argsName: List[Name], body: AstTerm)

  import Handler.*

  private def sHandler: StrParser[SHandler] = P {

    val transformHandler: StrParser[Handler] = P {
      for
        name <- P.stringFrom("rtn\\b".r) >%> name <%< P.from(
          "->"
        ) << P.whitespaces
        body <- rhs
      yield HTransform(name, body)
    }

    val opHandler: StrParser[Handler] = P {
      for
        handlerName <- name << P.whitespaces
        argNames <- name sepBy P.whitespaces
        _ <- P.whitespaces >> P.from("->") << P.whitespaces
        body <- rhs
      yield HOp(handlerName, argNames, body)
    }

    for
      _ <- P.stringFrom("hdl\\b".r) << P.whitespaces
      eff <- astEff << P.whitespaces
      outputEffects <- effect << P.whitespaces
      outputType <- atom << P.whitespaces
      _ <- P.from("{") << P.whitespaces
      allHandlers <- ((transformHandler || opHandler) <%< P.from(
        ";"
      ) << P.whitespaces).*
      _ <- P.from("}")
    yield
      val handlers = mutable.Map[Name, ( /* op args */ List[Name], AstTerm)]()
      var transformHandler: (Name, AstTerm) =
        (gn"x", AstIdentifier(gn"x")(using SiEmpty))

      for (h <- allHandlers) { // Use old syntax here because IntelliJ's formatter keeps messing up indentations
        h match
          case HOp(name, opArgs, body) => handlers(name) = (opArgs, body)
          case HTransform(name, t)     => transformHandler = (name, t)
      }

      SHandler(
        eff,
        outputEffects,
        outputType,
        transformHandler._1,
        transformHandler._2,
        handlers.toMap
      )
  }

  private def sHeapHandler: StrParser[SHeapHandler] = P {
    for
      _ <- P.stringFrom("hpv\\b".r) << P.whitespaces
      heapVarName <- name << P.whitespaces
      outputEffects <- effect << P.whitespaces
    yield SHeapHandler(outputEffects, heapVarName)
  }

  private def sBinding: StrParser[SBinding] = P {
    for
      name <- P.stringFrom("let\\b".r) >%> name <%< P.from("=") << P.whitespaces
      t <- rhs
    yield SBinding(name, t)
  }

  private def sTerm: StrParser[STerm] = P(rhs.map(STerm(_)))

  private def app: StrParser[AstTerm] = P(builtins || redux)

  private def rhs: StrParser[AstTerm] = P {
    val argBinding
      : StrParser[
        (
          /* eff */ AstTerm, /* arg name */ Name, /* arg type */ AstTerm,
          SourceInfo
        )
      ] =
      si(
        for
          eff <- effect.??.map(
            _.getOrElse(AstDef(Builtins.TotalQn)(using SiEmpty))
          )
          argName <- (name <%< P.from(":") << P.whitespaces).??.map(
            _.getOrElse(Name.Unreferenced)
          )
          argTy <- app
        yield (eff, argName, argTy)
      ) { case (eff, argName, argTy) =>
        (eff, argName, argTy, summon[SourceInfo])
      }

    for
      bindings <- (argBinding <%< P.from("->") << P.whitespaces).*
      bodyTy <- app
    yield bindings.foldRight(bodyTy) { (binding, bodyTy) =>
      binding match
        case (eff, argName, argTy, sourceInfo) =>
          AstFunctionType(argName, argTy, bodyTy, eff)(
            using siMerge(sourceInfo, bodyTy.sourceInfo)
          )
    }
  }

  private def effect: StrParser[AstTerm] = P {

    val effUnion: StrParser[AstTerm] =
      (app sepBy1 (P.whitespaces >> P.from("||") << P.whitespaces))
        .map {
          case Nil => throw IllegalStateException()
          case t :: rest =>
            rest.foldLeft(t) { (a, b) =>
              AstRedux(
                AstDef(Builtins.EffectsUnionQn)(using SiEmpty),
                Elimination.ETerm(a)(using a.sourceInfo) :: Elimination.ETerm(
                  b
                )(using a.sourceInfo) :: Nil
              )(using siMerge(a.sourceInfo, b.sourceInfo))
            }
        }

    si(P.from("<") >%> effUnion.?? <%< P.from(">"))(
      _.getOrElse(AstDef(Builtins.TotalQn))
    ) << P.whitespaces
  }

  private def redux: StrParser[AstTerm] = P {
    val elim: StrParser[Elimination[AstTerm]] = P(
      si(P.from("#") >> name)(Elimination.EProj(_)) || si(atom)(
        Elimination.ETerm(_)
      )
    )

    si(
      for
        head <- atom
        _ <- P.whitespaces
        elims <- elim sepByGreedy P.whitespaces
      yield (head, elims)
    ) {
      case (head, Nil)   => head
      case (head, elims) => AstRedux(head, elims)
    }
  }

  private def builtins: StrParser[AstTerm] = P {
    si(
      for
        head <- P.stringFrom("(clp|U|thk|frc)\\b".r)
        _ <- P.whitespaces
        args <- atom sepByGreedy P.whitespaces
        _ <- head match
          case "clp" | "U" | "thk" | "frc" => P.pure(())
          case _                           => P.fail(s"Unexpected number of args for $head")
      yield (head, args)
    ) {
      case ("clp", t :: Nil) => AstCollapse(t)
      case ("U", t :: Nil)   => AstU(t)
      case ("thk", t :: Nil) => AstThunk(t)
      case ("frc", t :: Nil) => AstForce(t)
      case _                 => throw IllegalStateException()
    }
    ||(
      si(
        for
          eff <- effect
          t <- rhs
        yield (t, eff)
      )(AstF(_, _))
    )
  }

  private def atom: StrParser[AstTerm] = P {
    val astLevelLiteral = P(
      si(P.from("L") >> P.nat)(AstLevelLiteral(_))
    )

    val astTotal = P(si(P.from("<>"))(_ => AstDef(Builtins.TotalQn)))

    val astIdentifier = P(si(name)(AstIdentifier(_)))

    astTotal ||
    astLevelLiteral ||
    astIdentifier ||
    P.from("(") >%> term <%< P.from(")")
  }

  private def astEff: StrParser[AstEff] = P {
    for
      name <- name
      args <- P.from("{") >%> (atom sepByGreedy P.whitespaces) <%< P.from("}")
    yield (name, args)
  }

  private def name: StrParser[Name] = P {
    val nameComponent: StrParser[String] = word || symbol

    val underscore: StrParser[String] = P.stringFrom("_".r)

    (for
      headUnderscore <- underscore.orEmptyString
      components <- nameComponent sepBy1 underscore
      tailUnderscore <- underscore.orEmptyString
    yield Name.Normal(
      components.mkString(headUnderscore, "_", tailUnderscore)
    )) ||
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
    "def"
  )

  private def word: StrParser[String] =
    P.stringFrom("(?U)\\p{Alpha}\\p{Alnum}*".r).withFilter(!keyWords(_))

  private val reservedSymbols = Set("|", "#", "->", "<", ">", "<>", ":", "=")

  private def symbol: StrParser[String] =
    P.stringFrom("(?U)[\\p{Graph}&&[^\\p{Alnum}_`.,;(){}]]+".r)
      .withFilter(!reservedSymbols(_))

  private def si[T, R](t: => StrParser[T])(f: SiText ?=> T => R): StrParser[R] =
    for
      (input, startIndex) <- P.info((_, _))
      t <- t
      endIndex <- P.info { (_, endIndex) => endIndex }
    yield f(using SiText(input.mkString, Range(startIndex, endIndex)))(t)

extension(ctx: StringContext)
  def t(args: String*): AstTerm =
    (P.whitespaces >> AstParser.term << P.whitespaces).parseOrThrow(
      ctx.s(args: _*)
    )
  def d(args: String*): List[AstDeclaration] =
    (P.whitespaces >> AstParser.declarations << P.whitespaces).parseOrThrow(
      ctx.s(args: _*)
    )
  def b(args: String*): Binding[AstTerm] =
    (P.whitespaces >> AstParser.binding << P.whitespaces).parseOrThrow(
      ctx.s(args: _*)
    )
