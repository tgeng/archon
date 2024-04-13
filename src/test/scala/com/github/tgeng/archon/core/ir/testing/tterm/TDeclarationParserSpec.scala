package com.github.tgeng.archon.core.ir.testing.tterm

import com.github.tgeng.archon.common.FileBasedFreeSpec
import os.Path

class TDeclarationParserSpec extends FileBasedFreeSpec:

  override protected def runTestImpl(testDir: Path): Unit =
    val inputPath = testDir / "input.tdecl"
    val actual = TTermParserSpec.tTermPprint.apply(Parser.parseDeclaration(inputPath)).plainText
    val outputPath = testDir / "output.txt"
    val expected = if os.exists(outputPath) then os.read(outputPath) else ""
    if actual != expected then
      os.write.over(outputPath, actual)
      fail(s"Expected:\n$expected\nActual:\n$actual")

  "data_nat" in:
    runTest()

  "def_trivial" in:
    runTest()
