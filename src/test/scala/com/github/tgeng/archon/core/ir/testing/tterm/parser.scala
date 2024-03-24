package com.github.tgeng.archon.core.ir.testing.tterm

import com.github.tgeng.archon.core.common.QualifiedName
import com.github.tgeng.archon.core.ir.{Builtins, SourceInfo, TokenRange}
import fastparse.SingleLineWhitespace.{*, given}
import fastparse.{*, given}
import os.Path

import scala.language.unsafeNulls

class Parser(val text: String, val path: Option[Path]) {
  private val keywords = Set("U", "force", "thunk", "auto", "F", "let", "handler", "_")
  private inline def PT[$: P, T, R](p: => P[T])(f: SourceInfo ?=> T => R): P[R] =
    P((Index ~ p ~ Index).map { case (start, t, end) =>
      f(using SourceInfo.SiText(text, path, Seq(TokenRange(start, end))))(t)
    })
  private def tAuto[$: P]: P[TTerm] = PT("_")(_ => TTerm.TAuto())
  private def id[$: P]: P[String] = P((CharIn("a-zA-Z_") ~~ CharIn("a-zA-Z0-9_").rep).!)
  private def tId[$: P]: P[TTerm] = PT(id.filter(!keywords(_)))(TTerm.TId(_))
  private def tLevelLiteral[$: P]: P[TTerm] =
    PT(CharIn("0-9").rep(1).! ~ "L")(s => TTerm.TLevelLiteral(s.toInt))
  private def tDef[$: P]: P[TTerm] =
    PT(("." ~ id).rep(1).!)(s => TTerm.TDef(QualifiedName.from(s.drop(1))))
  private def atom[$: P]: P[TTerm] = P(
    tAuto | tId | tDef | tLevelLiteral | tForce | "(" ~/ tTerm ~ ")",
  )
  private def tU[$: P]: P[TTerm] = PT("U" ~/ tTerm)(TTerm.TU(_))
  private def tForce[$: P]: P[TTerm] = PT("force" ~/ atom)(TTerm.TForce(_))
  private def tThunk[$: P]: P[TTerm] = PT("thunk" ~/ tTerm)(TTerm.TThunk(_))
  private def tF[$: P]: P[TTerm] =
    PT("<" ~/ tTerm.? ~ ">" ~ ("[" ~/ tTerm ~ "]").? ~ tTerm)((effect, usage, ty) =>
      TTerm.TF(ty, effect.getOrElse(TTerm.TDef(Builtins.TotalQn)), usage.getOrElse(TTerm.TAuto())),
    )
  private def tLet[$: P]: P[TTerm] =
    PT(
      "let" ~/ id ~ (":" ~/ ("<" ~/ tTerm ~ ">").? ~ ("[" ~/ tTerm ~ "]").? ~ tTerm).? ~ "=" ~/ tTerm ~ "in" ~ tTerm,
    ) {
      case (name, Some(effect, usage, ty), value, body) =>
        TTerm.TLet(
          name,
          value,
          ty,
          effect.getOrElse(TTerm.TAuto()),
          usage.getOrElse(TTerm.TAuto()),
          body,
        )
      case (name, None, value, body) =>
        TTerm.TLet(name, value, TTerm.TAuto(), TTerm.TAuto(), TTerm.TAuto(), body)
    }
  private def tApp[$: P]: P[TTerm] =
    (atom ~ atom.rep).map((f, args) => args.foldLeft(f)(TTerm.TApp(_, _)))
  private def tTerm[$: P]: P[TTerm] = P(tU | tForce | tThunk | atom)
  private def tTermEnd[$: P]: P[TTerm] = P(tTerm ~ End)
}

object Parser:
  def parseTTerm(path: Path): TTerm =
    val text = os.read(path)
    val parser = new Parser(text, Some(path))
    fastparse.parse(text, parser.tTermEnd(using _)) match
      case Parsed.Success(value, _)    => value
      case Parsed.Failure(_, _, extra) => throw new RuntimeException(extra.trace().longMsg)
