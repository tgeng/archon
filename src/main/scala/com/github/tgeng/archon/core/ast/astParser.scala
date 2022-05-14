package com.github.tgeng.archon.core.ast

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

  def sHandler: StrParser[SHandler] = P(
    for
      _ <- P.from(".handler") << P.whitespaces
      eff <- astEff << P.whitespaces
      otherEffects <- atom << P.whitespaces
      outputType <- atom << P.whitespaces
      _ <- P.from("(")
      (transformInputName, transform) <- transformHandler
      handlers <- opHandlers
      _ <- P.from(")")
    yield SHandler(eff, otherEffects, outputType, transformInputName, transform, handlers)
  )

  def transformHandler: StrParser[(Name, AstTerm)] = P(
    (for
      name <- P.from(".return") >%> name <%< P.from("->") << P.whitespaces
      body <- rhs <%< P.from(";")
    yield (name, body)).?.map {
      case Some(t) => t
      case None => (n"x", AstVar(n"x"))
    }
  )

  def opHandlers: StrParser[Map[Name, ( /* op args */ List[Name], /* resume */ Name, AstTerm)]] = P(
    opHandler.*.map(_.toMap)
  )

  def opHandler: StrParser[(Name, (List[Name], Name, AstTerm))] = P(
    for
      handlerName <- name << P.whitespaces
      argNames <- name sepBy1 P.whitespaces
      _ <- P.whitespaces >> P.from("->") << P.whitespaces
      body <- rhs <%< P.from(";")
    yield (handlerName, (argNames.dropRight(1), argNames.last, body))
  )

  def sHeapHandler: StrParser[SHeapHandler] = P(
    for
      _ <- P.from(".heap") << P.whitespaces
      heapVarName <- name << P.whitespaces
      otherEffects <- atom << P.whitespaces
    yield SHeapHandler(otherEffects, heapVarName)
  )

  def sBinding: StrParser[SBinding] = P(
    for name <- P.from(".let") >%> name <%< P.from("=") << P.whitespaces
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
      head <- P.stringFrom("(\\.(collapse|U|thunk|Cell|UCell|Equality|force|return))".r)
      _ <- P.whitespaces
      args <- atom sepBy P.whitespaces
      r <- (head, args) match
        case (".collapse", t :: Nil) => P.pure(AstCollapse(t))
        case (".U", t :: Nil) => P.pure(AstU(t))
        case (".thunk", t :: Nil) => P.pure(AstThunk(t))
        case (".Cell", heap :: ty :: Nil) => P.pure(AstCellType(heap, ty, CellStatus.Initialized))
        case (".UCell", heap :: ty :: Nil) => P.pure(
          AstCellType(
            heap,
            ty,
            CellStatus.Uninitialized
          )
        )
        case (".Equality", ty :: left :: right :: Nil) => P.pure(AstEqualityType(ty, left, right))
        case (".force", t :: Nil) => P.pure(AstForce(t))
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
    P.from(".L") >> P.nat.map(AstLevelLiteral(_))
  )

  def astRefl = P(P.from(".refl").map(_ => AstRefl))

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

  def word: StrParser[String] =
    P.stringFrom("(?U)\\p{Alpha}\\p{Alnum}*".r)

  def reservedSymbols = Set("(", ")", "|", "@", "#", "->", "<", ">", "<>", ":")

  def symbol: StrParser[String] =
    P.stringFrom("(?U)[\\p{Graph}&&[^\\p{Alnum}_`.;]]+".r).withFilter(!reservedSymbols(_))
