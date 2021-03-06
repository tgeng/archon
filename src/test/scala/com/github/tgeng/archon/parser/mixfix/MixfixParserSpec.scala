package com.github.tgeng.archon.parser.mixfix

import java.io.File
import io.Source
import collection.mutable
import collection.mutable.ArrayBuffer
import collection.immutable.ArraySeq

import com.github.tgeng.archon.common.{*, given}
import com.github.tgeng.archon.core.common.{*, given}
import com.github.tgeng.archon.parser.combinators.{*, given}
import com.github.tgeng.archon.parser.mixfix.*


class MixfixParserSpec extends SingleFileBasedSpec("parser/mixfix") :
  override def runTest(file: File, source: Source) =
    import MixfixParserSpec.*
    import QualifiedName.*
    import PrecedenceGraphBuilder.*
    val expected = file.readText()
    val parts = expected.split2("\n====\n")
    assert(parts.size == 2)
    val rules = rulesParser.parse(parts(0)).asRight
    val gb = PrecedenceGraphBuilder()
    val operatorMap = mutable.Map[String, Operator]()
    for rule <- rules do
      for operatorName <- rule.operatorNames do
        val operator = Operator(
          Root,
          rule.fixity,
          operatorName
            .split2("_")
            .filter(_.nonEmpty)
            .map(_.split2("\\b").toSeq)
            .toList
        )
        operatorMap(operatorName) = operator

    for rule <- rules do
      val headOperator = operatorMap(rule.operatorNames.head)
      val precedences = rule.precedences.map(
        (kind, operatorName) => Precedence(
          operatorMap(
            operatorName
          ), kind
        )
      )
      assert(gb.add(headOperator, precedences) == Right(()))
      for operatorName <- rule.operatorNames.tail do
        val operator = operatorMap(operatorName)
        assert(gb.add(operator, List(Precedence(headOperator, PrecedenceKind.SameAs))) == Right(()))
    val g = gb.build()

    given NamePart[String] with
      override def asString(n: String): String = n

    given ParserCache[String, List] = ParserCache()

    val p = createMixfixParser[String, List, Unit](g, P.fail("<literal>"))

    val testCases = parts(1).split2("\n\n")
    val actualParts = ArrayBuffer[String]()
    timed(file.getName.!!) {
      for testCase <- testCases
        do
          val actualPart = StringBuilder()
          val parts = testCase.split("\n----\n").asInstanceOf[Array[String]]
          if parts.size < 1 then fail(s"incomplete test case in $file")
          val input = parts.head
          val outputs = parts.tail
          actualPart.append(input)
          actualPart.append("\n----\n")
          p.doParse(0)(using ArraySeq.unsafeWrapArray(input.split2("\\s"))) match
            case r@ParseResult(results, errors, _) => results match
              case Nil =>
                actualPart.append(r.mkErrorString(input))
              case l: List[(Int, Any)] =>
                actualPart.append(l.map((advance, t) => s"$advance | $t").mkString("\n----\n"))
          actualParts.append(actualPart.toString)
    }

    val actual = parts(0) + "\n====\n" + actualParts.mkString("\n\n")
    if expected != actual then
      file.writeText(actual)
      fail(s"Test comparison failed for ${file.getName}. Test data has been updated.")


object MixfixParserSpec:

  val rulesParser = PrecedenceRule.precedenceRuleParser.++
