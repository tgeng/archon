package com.github.tgeng.archon.core.ir.testing.tterm

import com.github.tgeng.archon.common.FileBasedFreeSpec
import com.github.tgeng.archon.core.common.{Name, QualifiedName}
import os.Path

import scala.collection.mutable

object TTermParserSpec:
  def tTermPprint: pprint.PPrinter =
    val visited = mutable.Set.empty[TTerm]
    def p: pprint.PPrinter = pprint.copy(
      additionalHandlers = {
        case qn: QualifiedName => pprint.Tree.Literal(s"qn\"${qn.toString}\"")
        case n: Name           => pprint.Tree.Literal(s"n\"${n.toString}\"")
        case t: TTerm if !visited.contains(t) =>
          visited += t
          pprint.Tree
            .Infix(
              p.treeify(t, false, true),
              "@",
              pprint.Tree.Literal(t.sourceInfo.toString),
            )
      },
    )
    p

class TTermParserSpec extends FileBasedFreeSpec:

  override protected def runTestImpl(testDir: Path): Unit =
    val inputPath = testDir / "input.tterm"
    val actual = TTermParserSpec.tTermPprint.apply(Parser.parseTTerm(inputPath)).plainText
    val outputPath = testDir / "output.txt"
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
          