package com.github.tgeng.archon.core.ir.testing.tterm

import com.github.tgeng.archon.common.FileBasedFreeSpec
import os.Path

class TDeclarationParserSpec extends FileBasedFreeSpec("t_declaration_spec"):

  override protected def runTestImpl(testDir: Path): Unit =
    val inputPath = testDir / "input.tdecl"
    val actual = TTermParserSpec.tTermPprint.apply(Parser.parseDeclarations(inputPath)).plainText
    val outputPath = testDir / "parse_output.scala"
    val expected = if os.exists(outputPath) then os.read(outputPath) else ""
    if actual != expected then
      os.write.over(outputPath, actual)
      fail(s"Expected:\n$expected\nActual:\n$actual")

  "data_nat" in:
    runTest()

  "def_trivial" in:
    runTest()

  "data_vec" in:
    runTest()

  "data_eq" in:
    runTest()

  "def_plus" in:
    runTest()

  "record_stream" in:
    runTest()

  "def_prec" in:
    runTest()

  "def_escape_status" in:
    runTest()
          