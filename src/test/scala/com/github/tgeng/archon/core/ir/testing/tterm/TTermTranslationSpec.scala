package com.github.tgeng.archon.core.ir.testing.tterm

import com.github.tgeng.archon.common.{FileBasedFreeSpec, cTermPprint}
import com.github.tgeng.archon.core.common.qn
import os.Path

class TTermTranslationSpec extends FileBasedFreeSpec("t_term_spec"):

  override protected def runTestImpl(testDir: Path): Unit =
    val inputPath = testDir / "input.tterm"
    val tTerm = Parser.parseTTerm(inputPath)
    val ctx = TranslationContext(qn"test", ignoreUnresolvableGlobalName = true)
    val cTerm = tTerm.toCTerm(using ctx)
    val actual = cTermPprint.apply(cTerm).plainText
    val outputPath = testDir / "translation_output.scala"
    val expected = if os.exists(outputPath) then os.read(outputPath) else ""
    if actual != expected then
      os.write.over(outputPath, actual)
      fail(s"Expected:\n$expected\nActual:\n$actual")

  "simple id" in:
    runTest()

  "simple_def" in:
    runTest()

  "simple_force" in:
    runTest()

  "simple_u" in:
    runTest()

  "simple_F" in:
    runTest()

  "function_type_1" in:
    runTest()

  "function_type_2" in:
    runTest()

  "function_type_3" in:
    runTest()

  "let_1" in:
    runTest()

  "let_2" in:
    runTest()

  "let_3" in:
    runTest()

  "let_4" in:
    runTest()

  "app_1" in:
    runTest()

  "app_2" in:
    runTest()

  "statements_1" in:
    runTest()
