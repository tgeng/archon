package io.github.tgeng.archon.parser

import io.github.tgeng.archon.common.{*, given}
import io.github.tgeng.archon.parser.{*, given}
import org.scalatest.freespec.AnyFreeSpec

import java.net.URL
import java.io.File
import scala.annotation.nowarn
import scala.collection.mutable.ArrayBuffer
import scala.io.Source
import scala.util.Using

class Parsers[M[+_]](using MonadPlus[ParserM[Char, M]])(using MonadPlus[M]):
  def doubleQuoted = P(P.quoted())

class ParserTest extends AnyFreeSpec {
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
    val parsers = obj.getClass.getDeclaredMethods.!!.map(_.!!.invoke(obj).asInstanceOf[ParserT[Char, Any, M]])
    for parser <- parsers
      do
        val parserName = parser.targetName.get
        parserName in {
          val testDataFile = TestDataConstants.testResourcesRoot / s"/parserCombinators/$parserName.txt"
          if !testDataFile.exists() then fail(s"no test data for $parserName")
          val (expected, actual) = testParser(parser, testDataFile)
          if expected != actual then
            if updateTestData then
              testDataFile.write(actual)
              fail(s"Test comparison failed for $parserName. Test data has been updated.")
            else
              fail(s"Test comparison failed for $parserName.")
        }

  @nowarn
  private def testParser[M[+_]](p: ParserT[Char, Any, M], testDataFile: File) : (String, String) =
    val testDataString = Source.fromFile(testDataFile).use { source =>
      source.mkString.replace(System.lineSeparator(), "\n").!!
    }
    val actualParts = ArrayBuffer[String]()
    for testCase <- testDataString.split("\n====\n").asInstanceOf[Array[String]]
      do
        val actualPart = StringBuilder()
        val parts = testCase.split("\n----\n").asInstanceOf[Array[String]]
        if parts.size < 2 then fail(s"incomplete test case in $testDataFile")
        val input = parts.head
        actualPart.append(input)
        actualPart.append("\n----\n")
        p.doParse(0)(using input)(using Nil) match
          case ParseResult.Success(results) => results match
            case Some((advance, t)) =>
              actualPart.append(s"$advance\n$t")
            case l: List[(Int, Any)] =>
              actualPart.append(l.map((advance, t) => s"$advance\n$t").mkString("\n----\n"))
            case _ => fail("impossible")
          case f: ParseResult.Failure[?, ?] =>
            actualPart.append(f.mkString(input))
        actualParts.append(actualPart.toString)
    (testDataString, actualParts.mkString("\n====\n"))
}