package com.github.tgeng.archon.core.ir.testing.tterm

import com.github.tgeng.archon.common.parsing.{SignificantWhitespace, indexToColumn}
import com.github.tgeng.archon.core.common.{Name, QualifiedName}
import com.github.tgeng.archon.core.ir.*
import com.github.tgeng.archon.core.ir.EscapeStatus.EsUnknown
import com.github.tgeng.archon.core.ir.SourceInfo.SiEmpty
import com.github.tgeng.archon.core.ir.testing.tterm.TDeclaration.*
import fastparse.{*, given}
import os.Path

import scala.language.unsafeNulls

class Parser(val text: String, val path: Option[Path], val indent: Int):
  given whitespace: Whitespace = SignificantWhitespace(indent)
  private val keywords =
    Set("U", "force", "thunk", "auto", "F", "let", "handler", "_", "loc", "ret", "esc")
  private inline def PT[$: P, T, R](p: => P[T])(f: SourceInfo ?=> T => R): P[R] =
    P((Index ~~ p ~~ Index).map:
      case (start, t, end) =>
        f(using SourceInfo.SiText(text, path, Seq(TokenRange(start, end))))(t),
    )
  private def tAuto[$: P]: P[TTerm] = PT("_")(_ => TTerm.TAuto())
  private def id[$: P]: P[String] = P((CharIn("a-zA-Z_") ~~ CharIn("a-zA-Z0-9_").repX).!)
  private def tId[$: P]: P[TTerm] = PT(id.filter(!keywords(_)))(TTerm.TId(_))
  private def tLevelLiteral[$: P]: P[TTerm] =
    PT(CharIn("0-9").rep(1).! ~~ "L")(s => TTerm.TLevelLiteral(s.toInt))
  private def tDef[$: P]: P[TTerm] =
    PT(("." ~~ id).repX(1).!)(s => TTerm.TDef(QualifiedName.from(s.drop(1))))
  private def tU[$: P]: P[TTerm] = PT("U" ~/ atom)(TTerm.TU(_))
  private def tForce[$: P]: P[TTerm] = PT("force" ~/ atom)(TTerm.TForce(_))

  private def atom[$: P]: P[TTerm] = P(
    "(" ~/ tTerm ~ ")" | tAuto | tDef | tLevelLiteral | tForce | tU | tId,
  )
  private def tThunk[$: P]: P[TTerm] = PT("thunk" ~/ tTerm)(TTerm.TThunk(_))
  private def tF[$: P]: P[TTerm] =
    PT("<" ~/ tTerm.? ~ ">" ~ ("[" ~/ tTerm ~ "]").? ~ tRedex)((effect, usage, ty) =>
      TTerm.TF(
        ty,
        effect.getOrElse(TTerm.TDef(Builtins.TotalQn)(using SourceInfo.SiEmpty)),
        usage.getOrElse(TTerm.TAuto()(using SourceInfo.SiEmpty)),
      ),
    )
  private def tLet[$: P]: P[TTerm] =
    PT(
      "let" ~/ id ~
        (":" ~/ ("<" ~/ tTerm ~ ">").? ~ ("[" ~/ tTerm ~ "]").? ~ tTerm).? ~
        "=" ~/ indented(_.tTerm) ~
        tTerm,
    ):
      case (name, Some(effect, usage, ty), value, body) =>
        TTerm.TLet(
          name,
          value,
          ty,
          effect.getOrElse(TTerm.TAuto()(using SourceInfo.SiEmpty)),
          usage.getOrElse(TTerm.TAuto()(using SourceInfo.SiEmpty)),
          body,
        )
      case (name, None, value, body) =>
        TTerm.TLet(name, value, TTerm.TAuto(), TTerm.TAuto(), TTerm.TAuto(), body)
  private def elim[$: P]: P[Elimination[TTerm]] = PT(
    atom.map(t => Left(t)) | "#" ~~/ id.map(n => Right(n)),
  ):
    case Left(t)  => Elimination.ETerm(t)
    case Right(n) => Elimination.EProj(Name.Normal(n))

  private def tRedex[$: P]: P[TTerm] = PT(atom ~ indented(_.elim.rep)):
    case (f, elims) =>
      if elims.isEmpty then f else TTerm.TRedex(f, elims.toList)

  private def escapeStatus[$: P]: P[EscapeStatus] =
    P(
      "loc".map(_ => EscapeStatus.EsLocal) | "ret".map(_ => EscapeStatus.EsReturned) | "esc".map(
        _ => EscapeStatus.EsUnknown,
      ),
    )

  private def escapeStatusOpt[$: P]: P[EscapeStatus] = escapeStatus.?.map(_.getOrElse(EsUnknown))

  private def tBinding[$: P]: P[TBinding] =
    PT((id ~ ":").? ~/ ("[" ~/ tTerm ~ "]").? ~ tRedex)((name, usage, ty) =>
      TBinding(
        name.getOrElse("_"),
        ty,
        usage.getOrElse(TTerm.TDef(Builtins.UsageAnyQn)(using SourceInfo.SiEmpty)),
      ),
    )

  private inline def xFunctionType[$: P](resultP: => P[TTerm]): P[TTerm] =
    P(
      (NoCut(("<" ~/ tTerm ~ ">").? ~ escapeStatusOpt ~ tBinding ~ "->").rep ~ resultP).map:
        (effectAndBindings, ty) =>
          effectAndBindings.foldRight(ty):
            case ((effect, escapeStatus, binding), ty) =>
              TTerm.TFunctionType(
                binding,
                ty,
                effect.getOrElse(TTerm.TDef(Builtins.TotalQn)(using SourceInfo.SiEmpty)),
                escapeStatus,
              ),
    )

  private def tFunctionType[$: P]: P[TTerm] = xFunctionType(tF | tRedex)

  private def tDataFunctionType[$: P]: P[TTerm] = xFunctionType(
    tRedex.map(r =>
      given SourceInfo = SiEmpty
      TTerm.TF(r, TTerm.TDef(Builtins.TotalQn), TTerm.TDef(Builtins.UsageOneQn))(using
        r.sourceInfo,
      ),
    ),
  )

  private def tTerm[$: P]: P[TTerm] = P(
    (tFunctionType | tThunk | tLet)
      .rep(1)
      .map(_.reduceRight((t, body) =>
        given SourceInfo = SiEmpty
        TTerm.TLet("_", t, TTerm.TAuto(), TTerm.TAuto(), TTerm.TDef(Builtins.UsageZeroQn), body)(
          using SourceInfo.merge(t.sourceInfo, body.sourceInfo),
        ),
      )),
  )
  // TODO[P1]: Add handler parser here
  private def indented[$: P, R](f: Parser => Whitespace ?=> P[R]): P[R] =
    NoCut(
      Index
        .map(index => indexToColumn(index, text))
        .filter(newIndent => newIndent > indent)
        .flatMapX(newIndent =>
          val parser = new Parser(text, path, newIndent)
          f(parser)(using parser.whitespace),
        ),
    )

  private def tTermEnd[$: P]: P[TTerm] = P(tTerm ~ End)

  private def tBindingAndVariance[$: P]: P[(TBinding, Variance)] = P(
    (("+" | "-").!.? ~ "(" ~/ tBinding ~ ")").map:
      case (Some("+"), b) => (b, Variance.COVARIANT)
      case (Some("-"), b) => (b, Variance.CONTRAVARIANT)
      case (None, b)      => (b, Variance.INVARIANT)
      case _              => throw new RuntimeException("Impossible"),
  )

  private def tConstructor[$: P]: P[TConstructor] = P(
    (id ~ ":" ~/ indented(_.tDataFunctionType)).map(TConstructor.apply),
  )

  private def tData[$: P]: P[TDeclaration] = P(
    ("data" ~/ id ~ tBindingAndVariance.rep ~ ":" ~/ indented(
      _.tDataFunctionType,
    ) ~ tConstructor.rep)
      .map(TData.apply),
  )

  private def tCofield[$: P]: P[TCofield] = P(
    (id ~ ":" ~/ indented(_.tFunctionType)).map(TCofield.apply),
  )

  private def tCorecord[$: P]: P[TDeclaration] = P(
    ("corecord" ~/ (id ~ ":").?.map(
      _.getOrElse("self"),
    ) ~ id ~ tBindingAndVariance.rep ~ ":" ~/ indented(_.tRedex) ~ tCofield.rep).map(TCorecord.apply),
  )

  private def tProjection[$: P]: P[TCoPattern] = PT("#" ~/ id)(TCoPattern.TcProjection.apply)

  private def tpVar[$: P]: P[TPattern] = PT(id)(TPattern.TpId.apply)
  private def tpXConstructor[$: P]: P[TPattern] =
    PT(".".!.?.map(_.isDefined) ~ id ~ tPattern.rep)(TPattern.TpXConstructor.apply)
  private def tpForced[$: P]: P[TPattern] = PT("." ~ "(" ~/ tTerm ~ ")")(TPattern.TpForced.apply)
  private def tpAbsurd[$: P]: P[TPattern] = PT("()")(_ => TPattern.TPAbsurd())
  private def tPattern[$: P]: P[TPattern] = P(
    tpAbsurd | "(" ~/ tpXConstructor ~ ")" | tpVar | tpForced,
  )

  private def tCoPattern[$: P]: P[TCoPattern] = P(
    tProjection | tPattern.map(TCoPattern.TcPattern.apply),
  )

  private def tClause[$: P]: P[TClause] = P(
    (NoCut(tCoPattern).rep ~ "=" ~ indented(_.tTerm).?).map(TClause.apply),
  )

  private def tDefinition[$: P]: P[TDeclaration] = P(
    ("def" ~ id ~ ("(" ~ escapeStatusOpt ~ tBinding ~ ")")
      .map((a, b) =>
        (b, a),
      ) // swap escape status and binding since they are reverted in declaration type
      .rep ~ ":" ~/ indented(
      _.tFunctionType,
    ) ~ tClause.rep)
      .map(TDefinition.apply),
  )

  private def tDeclaration[$: P]: P[TDeclaration] = P(tData | tCorecord | tDefinition)

  private def tDeclarationEnd[$: P]: P[TDeclaration] = P(tDeclaration ~ End)

  private def tDeclarationsEnd[$: P]: P[Seq[TDeclaration]] = P(tDeclaration.rep ~ End)

object Parser:
  def parseTTerm(path: Path): TTerm = runParser(_.tTermEnd, path)
  def parseDeclaration(path: Path): TDeclaration = runParser(_.tDeclarationEnd, path)
  def parseDeclarations(path: Path): Seq[TDeclaration] = runParser(_.tDeclarationsEnd, path)

  private def runParser[T](p: Parser => P[?] ?=> P[T], path: Path): T =
    val text = os.read(path)
    def parser[$: P] = p(new Parser(text, Some(path), 0))
    fastparse.parse(text, parser(using _)) match
      case Parsed.Success(value, _)    => value
      case Parsed.Failure(_, _, extra) => throw new RuntimeException(extra.trace().longAggregateMsg)

  def parseTTerm(text: String): TTerm = runParserString(_.tTermEnd, text)
  def parseDeclaration(text: String): TDeclaration = runParserString(_.tDeclarationEnd, text)
  def parseDeclarations(text: String): Seq[TDeclaration] = runParserString(_.tDeclarationsEnd, text)

  private def runParserString[T](p: Parser => P[?] ?=> P[T], text: String): T =
    def parser[$: P] = p(new Parser(text, None, 0))

    fastparse.parse(text, parser(using _)) match
      case Parsed.Success(value, _)    => value
      case Parsed.Failure(_, _, extra) => throw new RuntimeException(extra.trace().longAggregateMsg)
