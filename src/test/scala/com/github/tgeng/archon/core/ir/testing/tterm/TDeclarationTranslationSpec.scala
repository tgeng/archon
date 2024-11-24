package com.github.tgeng.archon.core.ir.testing.tterm

import com.github.tgeng.archon.common.FileBasedFreeSpec
import com.github.tgeng.archon.core.common.qn
import com.github.tgeng.archon.core.ir.verbosePPrinter
import os.Path

class TDeclarationTranslationSpec extends FileBasedFreeSpec("t_declaration_spec"):

  override protected def runTestImpl(testDir: Path): Unit =
    val inputPath = testDir / "input.tdecl"
    val tDecls = Parser.parseDeclarations(inputPath)
    val ctx = TranslationContext(qn"test", ignoreUnresolvableGlobalName = true).bindDecls(tDecls)
    val preDecl = tDecls.map(_.toPreDeclaration(using ctx))
    val actual = verbosePPrinter.apply(preDecl).plainText
    val outputPath = testDir / "translation_output.scala"
    val expected = if os.exists(outputPath) then os.read(outputPath) else ""
    if actual != expected then
      os.write.over(outputPath, actual)
      fail(s"Expected:\n$expected\nActual:\n$actual")

  "data_nat" in:
    runTest()

  "data_eq" in:
    runTest()

  "data_vec" in:
    runTest()

  "def_plus" in:
    runTest()

  "def_trivial" in:
    runTest()

  "record_stream" in:
    runTest()

  "def_prec" in:
    runTest()

  "def_escape_status" in:
    runTest()
          