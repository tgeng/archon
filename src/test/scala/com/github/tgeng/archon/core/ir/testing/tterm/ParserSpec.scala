package com.github.tgeng.archon.core.ir.testing.tterm

import com.github.tgeng.archon.common.FileBasedFreeSpec
import com.github.tgeng.archon.core.common.{Name, QualifiedName}
import os.Path

object ParserSpec:
  val tTermPprint = pprint.copy(
    additionalHandlers = {
      case qn: QualifiedName => pprint.Tree.Literal(qn.toString)
      case n: Name           => pprint.Tree.Literal(n.toString)
      case t: TTerm =>
        pprint.Tree
          .Infix(pprint.treeify(t, false, true), "@", pprint.Tree.Literal(t.sourceInfo.toString))
    },
  )

class ParserSpec extends FileBasedFreeSpec:

  override protected def runTestImpl(testDir: Path): Unit =
    val inputPath = testDir / "input.tterm"
    val actual = ParserSpec.tTermPprint.apply(Parser.parse(inputPath)).plainText
    val outputPath = testDir / "output.txt"
    val expected = if os.exists(outputPath) then os.read(outputPath) else ""
    if actual != expected then
      os.write.over(outputPath, actual)
      fail(s"Expected:\n$expected\nActual:\n$actual")

  "simple id" in:
    runTest()
