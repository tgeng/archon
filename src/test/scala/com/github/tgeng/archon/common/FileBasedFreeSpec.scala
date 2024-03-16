package com.github.tgeng.archon.common

import com.github.tgeng.archon.common.*
import org.scalatest.freespec.AnyFreeSpec
import org.scalatest.matchers.should.Matchers.should

import java.nio.file.Path
import scala.annotation.tailrec
import scala.language.unsafeNulls

abstract class FileBasedFreeSpec extends AnyFreeSpec:
  private val currentTestNameStorage = new ThreadLocal[String]
  private val testResourceDir =
    TestDataConstants.testResourcesRoot / this.getClass.getCanonicalName
      .split('.')
      .map(camelToSnake)
      .mkString("/")

  private def camelToSnake(s: String): String =
    @tailrec def camelToSnake(s: String, output: String, lastUppercase: Boolean): String =
      if s.isEmpty then output
      else
        val c = if s.head.isUpper && !lastUppercase then "_" + s.head.toLower else s.head.toLower
        camelToSnake(s.tail, output + c, s.head.isUpper && !lastUppercase)

    camelToSnake(s, "", true)

  "meta" - {
    "test cases are complete" in:
      val testsMissingTestCases = (testResourceDir
        .listFiles()
        .map(_.getFileName.toString)
        .toSet -- this.testNames).toSeq.sorted
        .map { testCase =>
          s"""
  "${testCase}" in:
    runTest()
          """
        }

      if testsMissingTestCases.nonEmpty then
        fail(
          s"The following test cases are missing:\n${testsMissingTestCases.mkString("")}",
        )
  }

  override def withFixture(test: NoArgTest) =
    currentTestNameStorage.set(test.name)
    val outcome = super.withFixture(test)
    currentTestNameStorage.set(null)
    outcome

  private def currentTestName: String =
    val testName = currentTestNameStorage.get()
    assert(testName != null, "currentTestName should only be called in a test")
    testName

  protected def runTest(): Unit = runTestImpl(testResourceDir / currentTestName)

  protected def runTestImpl(testDir: Path): Unit
