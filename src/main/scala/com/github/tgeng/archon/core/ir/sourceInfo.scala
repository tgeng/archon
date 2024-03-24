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
    case SiEmpty                    => "ε"
    case SiText(text, path, ranges) => ranges.map(text.substring(_)).mkString("…")

object SourceInfo:
  def merge(si1: SourceInfo, si2: SourceInfo): SourceInfo = (si1, si2) match
    case (SiEmpty, _) => si2
    case (_, SiEmpty) => si1
    case (SiText(text1, path1, ranges1), SiText(text2, path2, ranges2)) =>
      assert(text1 == text2)
      assert(path1 == path2)
      SiText(text1, path1, ranges1 ++ ranges2)
