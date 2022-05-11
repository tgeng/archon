package io.github.tgeng.archon.core.ast

import io.github.tgeng.archon.common.*
import io.github.tgeng.archon.parser.combinators.{*, given}
import io.github.tgeng.archon.parser.combinators.single.given

object AstParser:
  def term: StrParser[AstTerm] = P(

    ???
  )

  def pattern: StrParser[AstPattern] = P(
    ???
  )

  def identifier: StrParser[String] = P(
    (
      for headUnderscore <- underscore.orEmptyString
          components <- identifierComponent sepBy1 underscore
          tailUnderscore <- underscore.orEmptyString
      yield components.mkString(headUnderscore, "_", tailUnderscore)
      ) |
    "`" >> P.stringFrom("[^`]+".r) << "`"
  )

  private def identifierComponent: StrParser[String] = word | symbol

  private def underscore: StrParser[String] = P.stringFrom("_".r)

  private def word: StrParser[String] =
    P.stringFrom("(?U)\\p{Alpha}\\p{Alnum}*".r)

  private def symbol: StrParser[String] =
    P.stringFrom("(?U)[\\p{Graph}&&[^\\p{Alnum}_`.]]+".r)
