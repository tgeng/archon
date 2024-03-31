package com.github.tgeng.archon.common.parsing

import fastparse.internal.Msgs
import fastparse.{ParsingRun, Whitespace}

class SignificantWhitespace(val requiredIndent: Int) extends Whitespace {
  override def apply(ctx: ParsingRun[?]): ParsingRun[Unit] =
    var index = ctx.index
    val input = ctx.input
    var continue = true

    while continue && input.isReachable(index) do
      input(index) match {
        case ' ' => index += 1
        case '\n' =>
          val endIndex = index + 1 + requiredIndent
          if input
              .isReachable(endIndex - 1) && input.slice(index + 1, endIndex) == " " * requiredIndent
          then index = endIndex
          else continue = false
        case _ => continue = false
      }
    if ctx.verboseFailures then ctx.reportTerminalMsg(index, Msgs.empty)
    ctx.freshSuccessUnit(index = index)

}
