package com.github.tgeng.archon.core.ir.testing.tterm

import com.github.tgeng.archon.common.FileBasedFreeSpec

import java.nio.file.Path

class TranslationSpec extends FileBasedFreeSpec {

  override def runTestImpl(testDir: Path): Unit =
    // TODO: implement this
    println(testDir)

  "basic" in:
    runTest()

  "handler" in:
    runTest()

}
