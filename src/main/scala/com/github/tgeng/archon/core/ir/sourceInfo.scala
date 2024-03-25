package com.github.tgeng.archon.core.ir

import com.github.tgeng.archon.common.*
import os.Path

trait SourceInfoOwner[T]:
  def sourceInfo: SourceInfo
  def withSourceInfo(sourceInfo: SourceInfo): T

case class TokenRange
  (
    /** Inclusive */
    start: Nat,
    /** Exclusive */
    end: Nat,
  ):
  def +(that: TokenRange): TokenRange =
    TokenRange(math.min(this.start, that.start), math.max(this.end, that.end))

extension (s: String) def substring(r: TokenRange): String = s.substring(r.start, r.end).nn

enum SourceInfo:
  case SiEmpty
  case SiText(text: String, path: Option[Path], ranges: Seq[TokenRange])

  override def toString: String = this match
    case SiEmpty                 => "ε"
    case SiText(text, _, ranges) => ranges.map(text.substring(_)).mkString("…")

object SourceInfo:
  def combine(sourceInfos: SourceInfo*): SourceInfo =
    sourceInfos.foldLeft(SiEmpty):
      case (SiEmpty, si2) => si2
      case (si1, SiEmpty) => si1
      case (SiText(text1, path1, ranges1), SiText(text2, path2, ranges2)) =>
        assert(text1 == text2)
        assert(path1 == path2)
        SiText(text1, path1, ranges1 ++ ranges2)

  def merge(sourceInfos: SourceInfo*): SourceInfo =
    sourceInfos.foldLeft(SiEmpty):
      case (SiEmpty, si2) => si2
      case (si1, SiEmpty) => si1
      case (SiText(text1, path1, ranges1), SiText(text2, path2, ranges2)) =>
        assert(text1 == text2)
        assert(path1 == path2)
        SiText(text1, path1, mergeRanges(ranges1 ++ ranges2))

  private def mergeRanges(ranges: Seq[TokenRange]): Seq[TokenRange] =
    if ranges.isEmpty then Seq()
    else Seq(TokenRange(ranges.map(_.start).min, ranges.map(_.end).max))
