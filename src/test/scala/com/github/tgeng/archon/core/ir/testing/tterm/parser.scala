package com.github.tgeng.archon.core.ir.testing.tterm

import com.github.tgeng.archon.common.parsing.{SignificantWhitespace, indexToColumn}
import com.github.tgeng.archon.core.common.QualifiedName
import com.github.tgeng.archon.core.ir.SourceInfo.SiEmpty
import com.github.tgeng.archon.core.ir.testing.tterm.TDeclaration.*
import com.github.tgeng.archon.core.ir.{Builtins, SourceInfo, TokenRange, Variance}
import fastparse.{*, given}
import os.Path

import scala.language.unsafeNulls

class Parser(val text: String, val path: Option[Path], val indent: Int):
  given whitespace: Whitespace = SignificantWhitespace(indent)
  private val keywords = Set("U", "force", "thunk", "auto", "F", "let", "handler", "_")
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
    PT(("." ~~ id).rep(1).!)(s => TTerm.TDef(QualifiedName.from(s.drop(1))))
  private def tU[$: P]: P[TTerm] = PT("U" ~/ atom)(TTerm.TU(_))
  private def tForce[$: P]: P[TTerm] = PT("force" ~/ atom)(TTerm.TForce(_))
  private def atom[$: P]: P[TTerm] = P(
    "(" ~/ tTerm ~ ")" | tAuto | tDef | tLevelLiteral | tForce | tU | tId,
  )
  private def tThunk[$: P]: P[TTerm] = PT("thunk" ~/ tTerm)(TTerm.TThunk(_))
  private def tF[$: P]: P[TTerm] =
    PT("<" ~/ tTerm.? ~ ">" ~ ("[" ~/ tTerm ~ "]").? ~ tApp)((effect, usage, ty) =>
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
  private def tApp[$: P]: P[TTerm] =
    (atom ~ indented(_.atom.rep)).map((f, args) => args.foldLeft(f)(TTerm.TApp(_, _)))

  private def tBinding[$: P]: P[TBinding] =
    PT((id ~ ":").? ~/ ("[" ~/ tTerm ~ "]").? ~ tApp)((name, usage, ty) =>
      TBinding(
        name.getOrElse("_"),
        ty,
        usage.getOrElse(TTerm.TDef(Builtins.UsageAnyQn)(using SourceInfo.SiEmpty)),
      ),
    )

  private inline def xFunctionType[$: P](resultP: => P[TTerm]): P[TTerm] =
    P(
      (NoCut(("<" ~/ tTerm ~ ">").? ~ tBinding ~ "->").rep ~ resultP).map:
        (effectAndBindings, ty) =>
          effectAndBindings.foldRight(ty):
            case ((effect, binding), ty) =>
              TTerm.TFunctionType(
                binding,
                ty,
                effect.getOrElse(TTerm.TDef(Builtins.TotalQn)(using SourceInfo.SiEmpty)),
              ),
    )

  private def tFunctionType[$: P]: P[TTerm] = xFunctionType(tF | tApp)

  private def tDataFunctionType[$: P]: P[TTerm] = xFunctionType(
    tApp.map(r =>
      given SourceInfo = SiEmpty
      TTerm.TF(r, TTerm.TDef(Builtins.TotalQn), TTerm.TDef(Builtins.UsageOneQn))(using
        r.sourceInfo,
      ),
    ),
  )

  private def tTerm[$: P]: P[TTerm] = P(
    tFunctionType | tThunk | tLet | tApp
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
    (("+" | "-").!.? ~ "(" ~ tBinding ~ ")").map:
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

  private def tField[$: P]: P[TField] = P(
    (id ~ ":" ~/ indented(_.tFunctionType)).map(TField.apply),
  )

  private def tRecord[$: P]: P[TDeclaration] = P(
    ("record" ~/ (id ~ ":").?.map(
      _.getOrElse("self"),
    ) ~ id ~ tBindingAndVariance.rep ~ ":" ~/ indented(_.tApp) ~ tField.rep).map(TRecord.apply),
  )

  private def tProjection[$: P]: P[TCoPattern] = PT("#" ~/ id)(TCoPattern.TcProjection.apply)

  private def tpVar[$: P]: P[TPattern] = PT(id)(TPattern.TpVar.apply)
  private def tpXConstructor[$: P]: P[TPattern] =
    PT(".".!.?.map(_.isDefined) ~ id ~ "{" ~/ tPattern.rep ~ "}")(TPattern.TpXConstructor.apply)
  private def tpForced[$: P]: P[TPattern] = PT("." ~ "(" ~/ tTerm ~ ")")(TPattern.TpForced.apply)
  private def tpAbsurd[$: P]: P[TPattern] = PT("()")(_ => TPattern.TPAbsurd())
  private def tPattern[$: P]: P[TPattern] = P(tpAbsurd | tpForced | tpXConstructor | tpVar)

  private def tCoPattern[$: P]: P[TCoPattern] = P(
    tProjection | tPattern.map(TCoPattern.TcPattern.apply),
  )

  private def tClause[$: P]: P[TClause] = P(
    (tCoPattern.rep ~ "=" ~ indented(_.tTerm).?).map(TClause.apply),
  )

  private def tDefinition[$: P]: P[TDeclaration] = P(
    ("def" ~ id ~ ("(" ~ tBinding ~ ")").rep ~ ":" ~/ indented(_.tFunctionType) ~ tClause.rep)
      .map(TDefinition.apply),
  )

  private def tDeclaration[$: P]: P[TDeclaration] = P(tData | tRecord | tDefinition)

  private def tDeclarationEnd[$: P]: P[TDeclaration] = P(tDeclaration ~ End)

object Parser:
  def parseTTerm(path: Path): TTerm =
    val text = os.read(path)
    val parser = new Parser(text, Some(path), 0)
    fastparse.parse(text, parser.tTermEnd(using _)) match
      case Parsed.Success(value, _)    => value
      case Parsed.Failure(_, _, extra) => throw new RuntimeException(extra.trace().longAggregateMsg)

  def parseDeclaration(path: Path): TDeclaration =
    val text = os.read(path)
    val parser = new Parser(text, Some(path), 0)
    fastparse
      .parse(text, parser.tDeclarationEnd(using _)) match
      case Parsed.Success(value, _)    => value
      case Parsed.Failure(_, _, extra) => throw new RuntimeException(extra.trace().longAggregateMsg)
