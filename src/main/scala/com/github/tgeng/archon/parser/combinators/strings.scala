package com.github.tgeng.archon.parser.combinators

import com.github.tgeng.archon.common.*

import scala.util.matching.Regex
import scala.util.matching.Regex.Match

type StrParser[T] = ParserT[Char, T, Option]
type MultiStrParser[T] = ParserT[Char, T, List]

extension[T, M[+_]]
  (using Functor[ParserT[Char, *, M]])
  (using Applicative[ParserT[Char, *, M]])
  (using Monad[ParserT[Char, *, M]])
  (using Alternative[ParserT[Char, *, M]])
  (using Applicative[M])
  (using Monad[M])
  (using Alternative[M])
  (p: ParserT[Char, T, M])
  def <%<(q: => ParserT[Char, ?, M]) = p << P.whitespaces << q
  def >%>[S](q: => ParserT[Char, S, M]) = p >> P.whitespaces >> q
  def <%%<(q: => ParserT[Char, ?, M])(using indent: Indent) = p << P.whitespacesWithIndent << q
  def >%%>[S](q: => ParserT[Char, S, M])(using indent: Indent) = p >> P.whitespacesWithIndent >> q
  def % = P.whitespaces >> p << P.whitespaces

opaque type Indent = Int

extension[M[+_]]
  (using Functor[ParserT[Char, *, M]])
  (using Applicative[ParserT[Char, *, M]])
  (using Monad[ParserT[Char, *, M]])
  (using Alternative[ParserT[Char, *, M]])
  (using Applicative[M])
  (using Monad[M])
  (using Alternative[M])
  (e: P.type)
  def getColumn: ParserT[Char, Int, M] = P.info((input, index) =>
    val lineStart = input.lastIndexOf('\n', index) + 1
      index - lineStart
  )

  def getIndent: ParserT[Char, Int, M] = P.info((input, index) =>
    val lineStart = input.lastIndexOf('\n', index) + 1
    val result = input.indexWhere(_ != ' ', lineStart)
    if result == -1 then input.length - lineStart
    else result - lineStart
  )

  def space = P.from(" ")
  def spaces = P.space.*.map(_.size)
  def spaceOrTab = P.anyOf(" \t") asAtom "<space or tab>"
  def cr = P.from("\r") asAtom "'\r'"
  def lf = P.from("\n") asAtom "'\n'"
  def newline = "\r\n" | P.lf asAtom "<newline>"
  def newlines = P.newline.*.map(_.size)
  def whitespace = P.anyOf(" \n\t\r") as () asAtom "<whitespace>"
  def whitespaces = P.whitespace.*

  def indentedBlock[T](p: Indent ?=> ParserT[Char, T, M]): ParserT[Char, T, M] =
    for
      _ <- P.whitespaces
      indent <- P.getIndent
      r <- p(using indent)
    yield r

  def indentedBlockFromHere[T](p: Indent ?=> ParserT[Char, T, M]): ParserT[Char, T, M] =
    for
      indent <- P.getColumn
      r <- p(using indent)
    yield r

  def indent(using indent: Indent) = P.space.repeat(indent)

  def newlineWithIndent(using indent: Indent) =
    (for
      _ <- P.newline sepBy1 P.spaceOrTab.*
      _ <- P.indent
    yield ()) asAtom "<newlinesWithIndent>"

  def whitespacesWithIndent(using indent: Indent) = P.newlineWithIndent.? >> P.spaceOrTab.* asAtom "<whitespacesWithIndent>"

  def eob(using indent: Indent) =
    (for
      _ <- P.newline sepBy1 P.spaceOrTab.*
      currentIndent <- P.getIndent
      r <- if currentIndent < indent then
        P.pure(())
      else
        P.fail("whatever, doesn't matter")
    yield r) | P.eos asAtom "<eob>"

  def digit = P.satisfySingle("<digit>", Character.isDigit)
  def alphabetic = P.satisfySingle("<alphabetic>", Character.isAlphabetic)
  def upper = P.satisfySingle("<upper case>", Character.isUpperCase)
  def lower = P.satisfySingle("<lower case>", Character.isLowerCase)
  def alphanum = P.digit | P.alphabetic
  def word = P.from("""\p{Alpha}+""".r).map(_.matched)
  def nat = P.from("""\d+""".r).map(_.matched.toInt) asAtom "<nat>"
  def integer = P.from("""[-+]?\d+""".r).map(_.matched.toInt) asAtom "<integer>"
  def decimal = P.from("""[-+]?[0-9]*\.?[0-9]+([eE][-+]?[0-9]+)?""".r).map(_.matched.toDouble) asAtom "<decimal>"

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
    val literal = P.satisfySingle(s"<char other than ${allEscapeMapping.keys.map(c => s"${escapeSymbol}$c").mkString("")}>", !needEscaping(_))
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

  def stringFrom(r: Regex) : ParserT[Char, String, M] = P.from(r).map(_.matched)


given [M[+_] : Alternative : Monad : Applicative]
  (using Functor[ParserT[Char, *, M]])
  (using Applicative[ParserT[Char, *, M]])
  (using Monad[ParserT[Char, *, M]])
  (using Alternative[ParserT[Char, *, M]])
  : Conversion[Char, ParserT[Char, Char, M]] = P.from(_)
given [M[+_] : Alternative : Monad : Applicative]
  (using Functor[ParserT[Char, *, M]])
  (using Applicative[ParserT[Char, *, M]])
  (using Monad[ParserT[Char, *, M]])
  (using Alternative[ParserT[Char, *, M]])
  : Conversion[String, ParserT[Char, String, M]] = P.from(_)
given [M[+_] : Alternative : Monad : Applicative]
  (using Functor[ParserT[Char, *, M]])
  (using Applicative[ParserT[Char, *, M]])
  (using Monad[ParserT[Char, *, M]])
  (using Alternative[ParserT[Char, *, M]])
  : Conversion[Regex, ParserT[Char, Match, M]] = P.from(_)

extension (failure: ParseResult[?, ?])
  def mkErrorString(input: String) : String =
    val lines = input.linesIterator.toIndexedSeq
    val sb = StringBuilder()
    for ((targets, index), es) <- failure.errors.groupBy(e => (e.targets, e.index))
      do
        val (line, column) = indexToLineColumn(input, index)
        val lineAndColumn = s"[${line + 1}:${column + 1}]"
        sb.append(s"when parsing ${targets.mkString("->")}:\n")
        sb.append(s"$lineAndColumn ${lines.lift(line).getOrElse("")}\n")
        sb.append(" " * (lineAndColumn.length + column + 1) + s"^ expect ${es.map(_.description).distinct.mkString(" | ")}\n")
    sb.toString.trim.!!

extension [M[+_]]
  (using Functor[ParserT[Char, *, M]])
  (using Applicative[ParserT[Char, *, M]])
  (using Monad[ParserT[Char, *, M]])
  (using Alternative[ParserT[Char, *, M]])
  (using Applicative[M])
  (using Monad[M])
  (using Alternative[M])
  (p: ParserT[Char, String, M])
  infix def +++ (q: ParserT[Char, String, M]) =
    for p <- p
        q <- q
    yield p + q

  def orEmptyString: ParserT[Char, String, M] = p.?.map {
    case Some(s) => s
    case None => ""
  }
