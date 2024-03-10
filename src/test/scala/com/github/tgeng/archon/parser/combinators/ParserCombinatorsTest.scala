package com.github.tgeng.archon.parser.combinators

import com.github.tgeng.archon.common.{*, given}
import com.github.tgeng.archon.parser.combinators.{*, given}
import org.scalatest.freespec.AnyFreeSpec

import java.io.File
import java.nio.file.Path
import scala.annotation.nowarn
import scala.collection.mutable.ArrayBuffer
import scala.io.Source

enum JValue {
  case JNull
  case JBoolean(value: Boolean)
  case JNumber(value: Double)
  case JString(value: String)
  case JArray(value: IndexedSeq[JValue])
  case JObject(value: Map[String, JValue])
}

import com.github.tgeng.archon.parser.combinators.JValue.*

class Parsers:
  def any = P(P.any << P.eos)

  def doubleQuoted = P(P.quoted() << P.eos)

  def abc = P(P.anyOf("abc") << P.eos)

  def threeWords = P(
    for (first, _, second, _, third) <- P.lift(
        (P.word, P.spaces, P.word, P.spaces, P.word),
      )
    yield (first, second, third),
  )

  def integer = P(P.integer)

  def decimal = P(P.decimal)

  def prefixCommit = P("a" << !"b" | "a")

  def prefixCommitHasLimitedEffects = P {
    def b = P(!"b")

    "a" << b | "a"
  }

  def postfixCommit = P("a".! << "b" | "a")

  def postfixCommitHasLimitedEffects = P {
    def b = P("b".!)

    "a" << b | "a"
  }

  def noBacktrack = P {
    val whitespaces = P(P.whitespaces)
    val word = P(P.word)
    val words = P(word sepByGreedy whitespaces)
    val end = P(whitespaces >> P.from("abc") <%< P.from(";"))
    P.lift((words, end))
  }

  def backtrack = P {
    val whitespaces = P(P.whitespaces)
    val word = P(P.word)
    val words = P(word sepBy whitespaces)
    val end = P(whitespaces >> P.from("abc") <%< P.from(";"))
    P.lift((words, end))
  }

  def expression: Parser[Char, String] = P {
    def atom = P(decimal.map(_.toString) | "(" >> expression << ")")

    def factor = P(
      atom chainedLeftBy
        P.spaces >> P.anyOf("*/").!.map { op => (a: String, b: String) =>
          s"($a $op $b)"
        } << P.spaces,
    )

    factor chainedLeftBy
      P.spaces >> P.anyOf("+-").!.map { op => (a: String, b: String) =>
        s"($a $op $b)"
      } << P.spaces
  }

  def expressionEos = P(expression << P.eos)

  def ambiguous = P("ab" | "a" << "b" | "a" >> "b" | "a" << "X")

  def indentedBlock = P(
    P.indentedBlock {
      (P.word sepBy1 P.newlineWithIndent) << P.eob
    },
  )

  def json = P {
    import JValue.*
    def jValue: Parser[Char, JValue] =
      jNull | jBoolean | jNumber | jString | jArray | jObject

    def jNull = P("null".! as JNull)

    def jBoolean =
      P(("true".! as JBoolean(true)) | ("false".! as JBoolean(false)))

    def jNumber = P(P.decimal map JNumber.apply)

    def jString = P(P.quoted() map JString.apply)

    def jArray = P(
      "[".! >%> (jValue sepBy ",".!.% map (a => JArray(a.toIndexedSeq))) <%< "]",
    )

    def jObject = P {
      def jObjectEntry: Parser[Char, (String, JValue)] =
        for
          key <- P.quoted() << ":".%
          value <- jValue
        yield (key, value)

      "{".! >%> (jObjectEntry sepBy ",".!.% map (m => JObject(m.toMap))) <%< "}"
    }

    jValue << P.eos
  }

  import com.github.tgeng.archon.parser.mixfix.PrecedenceRule

  def precedenceRule = PrecedenceRule.precedenceRuleParser

class ParserCombinatorsTest extends AnyFreeSpec:
  testParsers()

  private def testParsers() =
    val obj = Parsers()
    val parsers =
      obj.getClass.getDeclaredMethods.nn.filter(!_.nn.getName.nn.contains("$"))
        .map(
          _.nn.invoke(
            obj,
          ).asInstanceOf[Parser[Char, Any]],
        )
    for parser <- parsers
    do
      val parserName = parser.targetName.get
      parserName in {
        val testDataFile =
          TestDataConstants.testResourcesRoot / s"parser/combinators/$parserName.txt"
        if !testDataFile.exists() then
          testDataFile.writeText("TODO: add test data")
          fail(s"No test data for $parserName. Created placeholder file.")
        val (expected, actual) = testParser(parser, testDataFile)
        if expected != actual then
          testDataFile.writeText(actual)
          fail(
            s"Test comparison failed for $parserName. Test data has been updated.",
          )
      }

  @nowarn
  private def testParser(p: Parser[Char, Any], testDataFile: Path): (String, String) =
    val testDataString = Source.fromFile(testDataFile.toFile.nn).use { source =>
      source.mkString.replace(System.lineSeparator(), "\n").nn
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
      p.doParse(0)(using input) match
        case r @ ParseResult(results, errors, _) =>
          results match
            case Nil =>
              actualPart.append(r.mkErrorString(input))
              expectedPart.append(outputs.lift(0).getOrElse(""))
            case l: List[(Int, Any)] =>
              actualPart.append(
                l.map((advance, t) => s"$advance | $t").mkString("\n----\n"),
              )
              expectedPart.append(outputs.mkString("\n----\n"))
            case _ => fail("impossible")
      expectedParts.append(expectedPart.toString)
      actualParts.append(actualPart.toString)
    (expectedParts.mkString("\n\n"), actualParts.mkString("\n\n"))
