package com.github.tgeng.archon.core.ir.testing.tterm

import com.github.tgeng.archon.common.{FileBasedFreeSpec, cTermPprint}
import com.github.tgeng.archon.core.common.qn
import os.Path

class TDeclarationTranslationSpec extends FileBasedFreeSpec("t_declaration_spec"):

  override protected def runTestImpl(testDir: Path): Unit =
    val inputPath = testDir / "input.tdecl"
    val tDecls = Parser.parseDeclarations(inputPath)
    val ctx = TranslationContext(qn"test", ignoreUnresolvableGlobalName = true)
    tDecls.foreach(tDecl => ctx.bindDef(tDecl.name))
    val preDecl = tDecls.map(_.toPreDeclaration(using ctx))
    val actual = cTermPprint.apply(preDecl).plainText
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
