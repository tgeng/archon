package io.github.tgeng.archon.parser

import io.github.tgeng.archon.common.*
import java.io.File
import scala.io.Source

class MixfixParserSpec extends SingleFileBasedSpec("parser/mixfix"):
  override def runTest(file: File, source: Source) =
    println("yoo")
