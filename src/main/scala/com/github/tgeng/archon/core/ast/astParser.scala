package com.github.tgeng.archon.core.ast

import collection.mutable
import com.github.tgeng.archon.common.*
import com.github.tgeng.archon.core.common.*
import com.github.tgeng.archon.core.ir.Builtins
import com.github.tgeng.archon.core.ir.CellStatus
import com.github.tgeng.archon.core.ir.Elimination
import com.github.tgeng.archon.parser.combinators.{*, given}
import com.github.tgeng.archon.parser.combinators.single.given
import AstTerm.*
import Statement.*

object AstParser:
  def pattern: StrParser[AstPattern] = P(
    ???
  )

  def term: StrParser[AstTerm] = P(
    (statement sepBy (P.whitespaces >> P.from(";") << P.whitespaces)).map {
      case STerm(t) :: Nil => t
      case SBinding(_, t) :: Nil => t
      case statements => AstBlock(statements)
    }
  )

  def statement: StrParser[Statement] = P(
    sBinding | sHandler | sHeapHandler | sTerm
  )

  private enum Handler:
    case HTransform(varName: Name, body: AstTerm)
    case HOp(opName: Name, argsName: List[Name], resumeName: Name, body: AstTerm)

  import Handler.*


  def sHandler: StrParser[SHandler] = P(
    for
      _ <- P.from("hdl") << P.whitespaces
      eff <- astEff << P.whitespaces
      otherEffects <- atom << P.whitespaces
      outputType <- atom << P.whitespaces
      _ <- P.from("(") << P.whitespaces
      allHandlers <- transformOrOpHandler sepBy (P.whitespaces >> P.from(";") << P.whitespaces)
      _ <- P.from(")")
    yield
      val handlers = mutable.Map[Name, ( /* op args */ List[Name], /* resume */ Name, AstTerm)]()
      var transformHandler = (n"x", AstVar(n"x"))
      for h <- allHandlers do
        h match
          case HOp(name, opArgs, resume, body) => handlers(name) = (opArgs, resume, body)
          case HTransform(name, t) => transformHandler = (name, t)
      SHandler(eff, otherEffects, outputType, transformHandler._1, transformHandler._2, handlers.toMap)
  )

  private def transformOrOpHandler : StrParser[Handler] =
    transformHandler | opHandler

  private def transformHandler: StrParser[Handler] = P(
    for
      name <- P.from("rtn") >%> name <%< P.from("->") << P.whitespaces
      body <- rhs
    yield HTransform(name, body)
  )

  private def opHandler: StrParser[Handler] = P(
    for
      handlerName <- name << P.whitespaces
      argNames <- name sepBy1 P.whitespaces
      _ <- P.whitespaces >> P.from("->") << P.whitespaces
      body <- rhs
    yield HOp(handlerName, argNames.dropRight(1), argNames.last, body)
  )

  def sHeapHandler: StrParser[SHeapHandler] = P(
    for
      _ <- P.from("hpv") << P.whitespaces
      heapVarName <- name << P.whitespaces
      otherEffects <- atom << P.whitespaces
    yield SHeapHandler(otherEffects, heapVarName)
  )

  def sBinding: StrParser[SBinding] = P(
    for name <- P.from("let") >%> name <%< P.from("=") << P.whitespaces
        t <- rhs
    yield SBinding(name, t)
  )

  def sTerm: StrParser[STerm] = P(rhs.map(STerm(_)))

  def app: StrParser[AstTerm] = P(opCall | builtins | redux)

  def effUnion: StrParser[AstTerm] = (app sepBy1 (P.whitespaces >> P.from("|") << P.whitespaces))
    .map {
      case Nil => throw IllegalStateException()
      case t :: rest => rest.foldLeft(t) { (a, b) =>
        AstRedux(
          AstDef(Builtins.EffectsUnionQn),
          Elimination.ETerm(a) :: Elimination.ETerm(b) :: Nil
        )
      }
    }

  def rhs: StrParser[AstTerm] =
    for
      bindings <- (argBinding <%< P.from("->") << P.whitespaces).*
      bodyTy <- app
    yield bindings.foldRight(bodyTy) { (binding, bodyTy) =>
      binding match
        case (eff, argName, argTy) => AstFunctionType(argName, argTy, bodyTy, eff)
    }

  def argBinding: StrParser[( /* eff */ AstTerm, /* arg name */ Name, /* arg type */ AstTerm)] =
    for
      eff <- eff.?.map(_.getOrElse(AstTotal))
      argName <- (name <%< P.from(":") << P.whitespaces).?.map(_.getOrElse(gn"_"))
      argTy <- app
    yield (eff, argName, argTy)

  def eff: StrParser[AstTerm] = (P.from("<") >%>
    effUnion.?.map(_.getOrElse(AstTotal))
    <%< P.from(">") << P.whitespaces)

  def redux: StrParser[AstTerm] = P(
    for
      head <- atom
      _ <- P.whitespaces
      elims <- elim sepBy P.whitespaces
    yield elims match
      case Nil => head
      case elims => AstRedux(head, elims)
  )

  def elim: StrParser[Elimination[AstTerm]] = P(
    P.from("#") >> name.map(Elimination.EProj(_)) | atom.map(Elimination.ETerm(_))
  )

  def builtins: StrParser[AstTerm] = P(
    (for
      head <- P.stringFrom("clp|U|thk|Cell|UCell|Equality|frc".r)
      _ <- P.whitespaces
      args <- atom sepBy P.whitespaces
      r <- (head, args) match
        case ("clp", t :: Nil) => P.pure(AstCollapse(t))
        case ("U", t :: Nil) => P.pure(AstU(t))
        case ("thk", t :: Nil) => P.pure(AstThunk(t))
        case ("Cell", heap :: ty :: Nil) => P.pure(AstCellType(heap, ty, CellStatus.Initialized))
        case ("UCell", heap :: ty :: Nil) => P.pure(
          AstCellType(
            heap,
            ty,
            CellStatus.Uninitialized
          )
        )
        case ("Equality", ty :: left :: right :: Nil) => P.pure(AstEqualityType(ty, left, right))
        case ("frc", t :: Nil) => P.pure(AstForce(t))
        case _ => P.fail(s"Unexpected number of args for $head")
    yield r) |
      (
        for
          eff <- eff
          t <- atom
        yield AstF(t, eff)
        )
  )

  def atom: StrParser[AstTerm] = P(
    astRefl |
      astTotal |
      astLevelLiteral |
      P.from("(") >%> term <%< P.from(")") |
      astVar |
      astDef
  )

  def opCall: StrParser[AstTerm] = P(
    for
      name <- name
      _ <- P.whitespaces
      eff <- astEff
      _ <- P.whitespaces
      args <- atom sepBy P.whitespaces
    yield AstOperatorCall(eff, name, args)
  )

  def astDef = P(qualifiedName.map(AstDef(_)))

  def astVar = P(name.map(AstVar(_)))

  def astEff: StrParser[AstEff] = P(P.from("@") >%> (astEffWithArgs | astEffAtom))

  def astEffWithArgs: StrParser[AstEff] = P(
    for _ <- P.from("(") << P.whitespaces
        qn <- qualifiedName << P.whitespaces
        args <- atom sepBy P.whitespaces
        _ <- P.whitespaces >> P.from(")")
    yield (qn, args)
  )

  def astEffAtom: StrParser[AstEff] =
    for qn <- qualifiedName
      yield (qn, Nil)

  def astLevelLiteral = P(
    P.from("L") >> P.nat.map(AstLevelLiteral(_))
  )

  def astRefl = P(P.from("Refl").map(_ => AstRefl))

  def astTotal = P(P.from("<>").map(_ => AstTotal))

  def qualifiedName: StrParser[QualifiedName] = P(
    for
      _ <- P.from(".")
      parts <- (P.from(".") >> name).+
    yield QualifiedName.from(parts)
  )

  def name: StrParser[Name] = P(
    (
      for headUnderscore <- underscore.orEmptyString
          components <- nameComponent sepBy1 underscore
          tailUnderscore <- underscore.orEmptyString
      yield Name.Normal(components.mkString(headUnderscore, "_", tailUnderscore))
      ) |
      "`" >> P.stringFrom("[^`]+".r).map(Name.Normal(_)) << "`"
  )

  def nameComponent: StrParser[String] = word | symbol

  def underscore: StrParser[String] = P.stringFrom("_".r)

  def keyWords = Set(
    "hdl",
    "hpv",
    "rtn",
    "let",
    "U",
    "clp",
    "U",
    "thk",
    "Cell",
    "UCell",
    "Equality",
    "frc",
    "Refl",
  )

  def word: StrParser[String] =
    P.stringFrom("(?U)\\p{Alpha}\\p{Alnum}*".r).withFilter(!keyWords(_))

  def reservedSymbols = Set("(", ")", "|", "@", "@(", "#", "->", "<", ">", "<>", ":")

  def symbol: StrParser[String] =
    P.stringFrom("(?U)[\\p{Graph}&&[^\\p{Alnum}_`.;]]+".r).withFilter(!reservedSymbols(_))
