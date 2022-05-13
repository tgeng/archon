package com.github.tgeng.archon.core.ast

import com.github.tgeng.archon.common.*
import com.github.tgeng.archon.core.common.*
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
    sTerm | sBinding | sHandler | sHeapHandler
  )

  def sHandler: StrParser[SHandler] = P(
    ???
  )

  def sHeapHandler: StrParser[SHeapHandler] = P(
    ???
  )

  def sBinding: StrParser[SBinding] = P(
    for name <- P.from(".let") >%> name <%< P.from("=") << P.whitespaces
        t <- rhs
    yield SBinding(name, t)
  )

  def sTerm: StrParser[STerm] = P(rhs.map(STerm(_)))

  def rhs: StrParser[AstTerm] = P(opCall | builtins | redux)

  def redux: StrParser[AstTerm] = P(
    for
      head <- atom
      _ <- P.whitespaces
      elims <- elim sepBy P.whitespaces
    yield AstRedux(head, elims)
  )

  def elim: StrParser[Elimination[AstTerm]] = P(
    P.from("#") >> name.map(Elimination.EProj(_)) | atom.map(Elimination.ETerm(_))
  )

  def builtins: StrParser[AstTerm] = P(
    for
      head <- P.stringFrom("\\.(collapse|U|thunk|Cell|UCell|Equality|force|F|return)".r)
      _ <- P.whitespaces
      args <- atom sepBy P.whitespaces
      r <- (head, args) match
        case ("collapse", t :: Nil) => P.pure(AstCollapse(t))
        case ("U", t :: Nil) => P.pure(AstU(t))
        case ("thunk", t :: Nil) => P.pure(AstThunk(t))
        case ("Cell", heap :: ty :: Nil) => P.pure(AstCellType(heap, ty, CellStatus.Initialized))
        case ("UCell", heap :: ty :: Nil) => P.pure(AstCellType(heap, ty, CellStatus.Uninitialized))
        case ("Equality", ty :: left :: right :: Nil) => P.pure(AstEqualityType(ty, left, right))
        case ("force", t :: Nil) => P.pure(AstForce(t))
        case ("F", t :: eff :: Nil) => P.pure(AstF(t, eff))
        case ("return", t :: Nil) => P.pure(AstReturn(t))
        case _ => P.fail(s"Unexpected number of args for $head")
    yield r
  )

  def atom: StrParser[AstTerm] = P(
    astRefl |
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

  def reservedSymbols = Set("(", ")", "|", "@", "#")

  def symbol: StrParser[String] =
    P.stringFrom("(?U)[\\p{Graph}&&[^\\p{Alnum}_`.;]]+".r).withFilter(!reservedSymbols(_))
