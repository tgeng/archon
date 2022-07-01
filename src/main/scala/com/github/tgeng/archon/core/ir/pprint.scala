package com.github.tgeng.archon.core.ir

import com.github.tgeng.archon.common.*
import com.github.tgeng.archon.core.common.*

object TermPrettyPrinter extends Visitor[IndexedSeq[Name], Block]:
  override def combine(blocks: Block*)(using ctx: IndexedSeq[Name])(using Σ: Signature) = ???

