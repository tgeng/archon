package io.github.tgeng.archon.parser

import io.github.tgeng.archon.common.*
import scala.util.matching.Regex
import scala.util.matching.Regex.Match

type StrParser[T] = ParserT[Char, T, Option]
type MultiStrParser[T] = ParserT[Char, T, List]

extension[M[+_]] (using pm: MonadPlus[ParserM[Char, M]])(using mm: MonadPlus[M])(e: P.type)
  def space = P.anyOf(" ") withDescription "' '"
  def spaces = P.space.*.map(_.size)
  def cr = P.from("\r") withDescription "'\r'"
  def lf = P.from("\n") withDescription "'\n'"
  def newline = "\r\n" | P.lf withDescription "<newline>"
  def newlines = P.newline.*.map(_.size)
  def whitespace = P.anyOf(" \n\t\r") as () withDescription "<whitespace>"
  def whitespaces = P.whitespace.*

  def digit = P.satisfySingle("<digit>", Character.isDigit)
  def alphabetic = P.satisfySingle("<alphabetic>", Character.isAlphabetic)
  def upper = P.satisfySingle("<upper case>", Character.isUpperCase)
  def lower = P.satisfySingle("<lower case>", Character.isLowerCase)
  def alphanum = P.digit | P.alphabetic
  def word = P.from("""\p{Alpha}+""".r).map(_.matched)
  def integer = P.from("""\d+""".r).map(_.matched.toInt) withDescription "<integer>"
  def decimal = P.from("""[-+]?[0-9]*\.?[0-9]+([eE][-+]?[0-9]+)?""".r).map(_.matched.toDouble) withDescription "<decimal>"

  def quoted(quoteSymbol: Char = '"',
              escapeSymbol: Char = '\\',
              additionalEscapeMapping: Map[Char, Char] = Map(
                'n' -> '\n',
                'r' -> '\r',
                't' -> '\t',
                'b' -> '\b',
                'f' -> '\f',
              )
            ) =
    val allEscapeMapping = additionalEscapeMapping + (quoteSymbol -> quoteSymbol) + (escapeSymbol -> escapeSymbol)
    val needEscaping = allEscapeMapping.values.toSet
    val literal = P.satisfySingle(s"<none of $needEscaping>", !needEscaping(_))
    val special = escapeSymbol >> P.satisfySingle(s"<one of ${allEscapeMapping.keySet}>", allEscapeMapping.keySet).map(allEscapeMapping)

    quoteSymbol >> (literal | special).*.map(_.mkString("")) << quoteSymbol

  def from(c: Char) : ParserT[Char, Char, M] = P.satisfySingle(s"'$c'", _ == c)

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


given [M[+_]] (using pm: MonadPlus[ParserM[Char, M]])(using mm: MonadPlus[M]): Conversion[Char, ParserT[Char, Char, M]] = P.from(_)
given [M[+_]] (using pm: MonadPlus[ParserM[Char, M]])(using mm: MonadPlus[M]): Conversion[String, ParserT[Char, String, M]] = P.from(_)
given [M[+_]] (using pm: MonadPlus[ParserM[Char, M]])(using mm: MonadPlus[M]): Conversion[Regex, ParserT[Char, Match, M]] = P.from(_)

extension (failure: ParseResult.Failure[?, ?])
  def mkString(input: String) : String =
    val lines = input.linesIterator.toIndexedSeq
    val sb = StringBuilder()
    for ((targets, index), es) <- failure.errors.groupBy(e => (e.targets, e.index))
      do
        val (line, column) = indexToLineColumn(input, index)
        val lineAndColumn = s"[${line + 1}:${column + 1}]"
        sb.append(s"when parsing ${targets.mkString("/")}:\n")
        sb.append(s"$lineAndColumn ${lines.lift(line).getOrElse("")}\n")
        sb.append(" " * (lineAndColumn.length + column + 1) + s"^ expect ${es.map(_.description).distinct.mkString(" | ")}\n")
    sb.toString.trim.!!
