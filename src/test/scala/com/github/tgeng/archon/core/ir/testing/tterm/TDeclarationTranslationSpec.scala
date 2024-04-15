package com.github.tgeng.archon.core.ir.testing.tterm

import com.github.tgeng.archon.common.FileBasedFreeSpec
import com.github.tgeng.archon.core.common.{Name, QualifiedName, qn}
import com.github.tgeng.archon.core.ir.CTerm
import os.Path

import scala.collection.mutable

class TDeclarationTranslationSpec extends FileBasedFreeSpec:

  def cTermPprint: pprint.PPrinter =
    val visited = mutable.Set.empty[CTerm]
    def p: pprint.PPrinter = pprint.copy(
      additionalHandlers = {
        case qn: QualifiedName => pprint.Tree.Literal(s"qn\"${qn.toString}\"")
        case n: Name           => pprint.Tree.Literal(s"n\"${n.toString}\"")
        // TODO[P0]: figure out a way to print content of PreDeclaration. Or just make content of
        //  PreDeclaration part of the normal case class fields
        case t: CTerm if !visited.contains(t) =>
          visited += t
          pprint.Tree
            .Infix(
              p.treeify(t, false, true),
              "@",
              pprint.Tree.Literal(pprint.apply(t.sourceInfo.toString).toString),
            )
      },
    )
    p

  override protected def runTestImpl(testDir: Path): Unit =
    val inputPath = testDir / "input.tdecl"
    val tDecls = Parser.parseDeclarations(inputPath)
    val ctx = TranslationContext(qn"test", ignoreUnresolvableGlobalName = true)
    tDecls.foreach(tDecl => ctx.bindDef(tDecl.name))
    val preDecl = tDecls.map(_.toPreDeclaration(using ctx))
    val actual = cTermPprint.apply(preDecl).plainText
    val outputPath = testDir / "output.txt"
    val expected = if os.exists(outputPath) then os.read(outputPath) else ""
    if actual != expected then
      os.write.over(outputPath, actual)
      fail(s"Expected:\n$expected\nActual:\n$actual")

  "data_nat" in:
    runTest()
