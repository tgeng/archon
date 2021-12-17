package io.github.tgeng.archon.parser

import io.github.tgeng.archon.common.{*, given}
import io.github.tgeng.archon.parser.{*, given}
import org.scalatest.freespec.AnyFreeSpec

import java.net.URL
import java.io.File
import scala.annotation.nowarn
import scala.io.Source

class Parsers[M[+_]](using MonadPlus[ParserM[Char, M]])(using MonadPlus[M]):
  def doubleQuoted = P(P.quoted())

class ParserTest extends AnyFreeSpec {
  "single" in {
    import io.github.tgeng.archon.parser.single.given
    testParsers()
  }

  "multi" in {
    import io.github.tgeng.archon.parser.multi.given
    testParsers()
  }

  private def testParsers[M[+_]]()(using MonadPlus[ParserM[Char, M]])(using MonadPlus[M]) =
    import scala.io.Source
    val obj = Parsers()
    val parsers = obj.getClass.getDeclaredMethods.!!.map(_.!!.invoke(obj).asInstanceOf[ParserT[Char, Any, M]])
    for parser <- parsers
      do
        val parserName = parser.targetName.get
        val testDataUrl = getClass.getResource(s"/parserCombinators/$parserName.txt")
        if (testDataUrl == null) fail(s"no test data for $parserName")
        testParser(parser, testDataUrl)

  @nowarn
  private def testParser[M[+_]](p: ParserT[Char, Any, M], testData: URL) =
    val testDataString = Source.fromURL(testData).mkString
    for testCase <- testDataString.split("\n====").asInstanceOf[Array[String]]
      do
        val parts = testCase.split("\n----").asInstanceOf[Array[String]]
        if (parts.size < 2) fail(s"incomplete test case in $testData")
        val input = parts.head
        val outputs = parts.tail.toSeq
        p.doParse(0)(using input)(using Nil) match
          case ParseResult.Success(results) => results match
            case Some((advance, t)) => assert(s"$advance\n$t" == outputs.head)
            case l: List[(Int, Any)] => assert(l.map((advance, t) => s"$advance\n$t") == outputs)
            case _ => fail("impossible")
          case f: ParseResult.Failure[?, ?] => assert(f.mkString(input) == outputs.head)

}