package io.github.tgeng.archon.parser.mixfix

import io.github.tgeng.archon.common.*
import io.github.tgeng.archon.parser.mixfix.*
import io.github.tgeng.archon.parser.combinators.*

import java.io.File
import scala.io.Source

class MixfixParserSpec extends SingleFileBasedSpec("parser/mixfix"):
  override def runTest(file: File, source: Source) =
    val parts = file.read().split2("\n====")
    val rulesString = parts(0)
    val testsString = parts(1)
//    PrecedenceRule.precedenceRuleParser.parse(???)
