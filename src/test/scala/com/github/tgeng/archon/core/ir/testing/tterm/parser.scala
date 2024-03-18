package com.github.tgeng.archon.core.ir.testing.tterm

import com.github.tgeng.archon.core.common.QualifiedName
import com.github.tgeng.archon.core.common.QualifiedName.Root
import com.github.tgeng.archon.core.ir.{SourceInfo, TokenRange}
import fastparse.NoWhitespace.{*, given}
import fastparse.{*, given}
import os.Path

import scala.language.unsafeNulls

class Parser(val text: String, val path: Option[Path]) {
  private inline def PT[$: P, T, R](p: => P[T])(f: SourceInfo ?=> T => R): P[R] =
    P((Index ~ p ~ Index).map { case (start, t, end) =>
      f(using SourceInfo.SiText(text, path, Seq(TokenRange(start, end))))(t)
    })
  private def id[$: P]: P[String] = P((CharIn("a-zA-Z_") ~ CharIn("a-zA-Z0-9_").rep).!)
  private def tId[$: P]: P[TTerm] = PT(id)(TTerm.TId(_))
  private def tDef[$: P]: P[TTerm] =
    PT(("." ~ id).rep(1).!)(s => TTerm.TDef(QualifiedName.from(s.drop(1))))
  private def tTerm[$: P]: P[TTerm] = P(tId | tDef)
}

object Parser:
  def parse(path: Path): TTerm =
    val text = os.read(path)
    val parser = new Parser(text, Some(path))
    fastparse.parse(text, parser.tTerm(using _)) match
      case Parsed.Success(value, _)    => value
      case Parsed.Failure(_, _, extra) => throw new RuntimeException(extra.trace().longMsg)
