package io.github.tgeng.archon.parser

import io.github.tgeng.archon.common.MonadPlus
import scala.util.matching.Regex
import scala.util.matching.Regex.Match

type StrParser[T] = ParserT[Char, T, Option]
type MultiStrParser[T] = ParserT[Char, T, List]

extension[M[+_]] (using pm: MonadPlus[ParserM[Char, M]])(using mm: MonadPlus[M])(e: P.type)
  def space = P.anyOf(" ")
  def spaces = P.space.*.map(_.size)
  def cr = P.from("\r")
  def lf = P.from("\n")
  def newline = "\r\n" | P.lf
  def newlines = P.newline.*.map(_.size)
  def whitespace = P.anyOf(" \n\t\r") as ()
  def whitespaces = P.whitespace.*

  def from(s: String) : ParserT[Char, String, M] = P.satisfy(
    s"'$s'",
    input => if (input.startsWith(s)) Some(s.length, s) else None
  )

  def from(r: Regex) : ParserT[Char, Match, M] = P.satisfy(
    s"/$r/",
    input => r.findPrefixMatchOf(SeqCharSequence(input)) match
      case Some(regexMatch) => Some((regexMatch.matched.length, regexMatch))
      case _ => None
  )


given [M[+_]] (using pm: MonadPlus[ParserM[Char, M]])(using mm: MonadPlus[M]): Conversion[String, ParserT[Char, String, M]] = P.from(_)
given [M[+_]] (using pm: MonadPlus[ParserM[Char, M]])(using mm: MonadPlus[M]): Conversion[Regex, ParserT[Char, Match, M]] = P.from(_)
