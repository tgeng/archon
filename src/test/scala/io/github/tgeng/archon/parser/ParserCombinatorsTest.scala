package io.github.tgeng.archon.parser

import io.github.tgeng.archon.common.{*, given}
import io.github.tgeng.archon.parser.{*, given}
import junit.framework.ComparisonFailure
import org.scalatest.freespec.AnyFreeSpec

import java.net.URL
import java.io.File
import scala.annotation.nowarn
import scala.collection.mutable.ArrayBuffer
import scala.io.Source
import scala.util.Using

class Parsers[M[+_]](using MonadPlus[ParserM[Char, M]])(using MonadPlus[M]):
  def any = P(P.any << P.eos)
  def doubleQuoted = P(P.quoted() << P.eos)
  def abc = P(P.anyOf("abc") << P.eos)
  def threeWords = P(
    for (first, _, second, _, third) <- (P.word, P.spaces, P.word, P.spaces, P.word)
    yield (first, second, third)
  )
  def integer = P(P.integer)
  def decimal = P(P.decimal)
  def simpleCommitCase = P("a" << !"b" | "a")
  def commitHasLimitedEffects = P {
    def b = P(!"b")
    "a" << b | "a"
  }
  def expression : ParserT[Char, String, M] = P {
    def atom = P(decimal.map(_.toString) | "(" >> expression << ")")

    def factor = P(atom chainedLeftBy
      P.spaces >> P.anyOf("*/").map {
        op => (a: String, b: String) => s"($a $op $b)"
      } << P.spaces)
    factor chainedLeftBy
      P.spaces >> P.anyOf("+-").map {
        op => (a: String, b: String) => s"($a $op $b)"
      } << P.spaces
  }
  def expressionEos = P(expression << P.eos)

class ParserCombinatorsTest extends AnyFreeSpec {
  "single" - {
    import io.github.tgeng.archon.parser.single.given
    testParsers(false)
  }

  "multi" - {
    import io.github.tgeng.archon.parser.multi.given
    testParsers(true)
  }

  private def testParsers[M[+_]](updateTestData: Boolean)(using MonadPlus[ParserM[Char, M]])(using MonadPlus[M]) =
    import scala.io.Source
    val obj = Parsers()
    val parsers = obj.getClass.getDeclaredMethods.!!.filter(!_.!!.getName.!!.contains("$")).map(_.!!.invoke(obj).asInstanceOf[ParserT[Char, Any, M]])
    for parser <- parsers
      do
        val parserName = parser.targetName.get
        parserName in {
          val testDataFile = TestDataConstants.testResourcesRoot / s"/parserCombinators/$parserName.txt"
          if !testDataFile.exists() then
            testDataFile.write("TODO: add test data")
            fail(s"No test data for $parserName. Created placeholder file.")
          val (expected, actual) = testParser(parser, testDataFile)
          if expected != actual then
            if updateTestData then
              testDataFile.write(actual)
              fail(s"Test comparison failed for $parserName. Test data has been updated.")
            else
              throw new ComparisonFailure(s"Test comparison failed for $parserName.", expected, actual)
        }

  @nowarn
  private def testParser[M[+_]](p: ParserT[Char, Any, M], testDataFile: File) : (String, String) =
    val testDataString = Source.fromFile(testDataFile).use { source =>
      source.mkString.replace(System.lineSeparator(), "\n").!!
    }
    val actualParts = ArrayBuffer[String]()
    val expectedParts = ArrayBuffer[String]()
    for testCase <- testDataString.split("\n\n").asInstanceOf[Array[String]]
      do
        val actualPart = StringBuilder()
        val expectedPart = StringBuilder()
        val parts = testCase.split("\n----\n").asInstanceOf[Array[String]]
        if parts.size < 1 then fail(s"incomplete test case in $testDataFile")
        val input = parts.head
        val outputs = parts.tail
        actualPart.append(input)
        actualPart.append("\n----\n")
        expectedPart.append(input)
        expectedPart.append("\n----\n")
        p.doParse(0)(using input)(using Nil) match
          case ParseResult.Success(results) => results match
            case Some((advance, t)) =>
              actualPart.append(s"$advance | $t")
              expectedPart.append(outputs(0))
            case l: List[(Int, Any)] =>
              actualPart.append(l.map((advance, t) => s"$advance | $t").mkString("\n----\n"))
              expectedPart.append(outputs.mkString("\n----\n"))
            case _ => fail("impossible")
          case f: ParseResult.Failure[?, ?] =>
            actualPart.append(f.mkString(input))
            expectedPart.append(outputs.lift(0).getOrElse(""))
        expectedParts.append(expectedPart.toString)
        actualParts.append(actualPart.toString)
    (expectedParts.mkString("\n\n"), actualParts.mkString("\n\n"))
}