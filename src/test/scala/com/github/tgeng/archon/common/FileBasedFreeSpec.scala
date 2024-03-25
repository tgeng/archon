package com.github.tgeng.archon.common

import org.scalatest.exceptions.TestFailedException
import org.scalatest.freespec.AnyFreeSpec
import org.scalatest.matchers.should.Matchers.should
import os.{Path, RelPath}

import scala.annotation.tailrec
import scala.language.unsafeNulls

abstract class FileBasedFreeSpec extends AnyFreeSpec:
  private val currentTestNameStorage = new ThreadLocal[String]
  private val testResourceDir =
    TestDataConstants.testResourcesRoot / RelPath(
      this.getClass.getCanonicalName
        .split('.')
        .map(camelToSnake)
        .mkString("/"),
    )

  private def camelToSnake(s: String): String =
    @tailrec def camelToSnake(s: String, output: String, lastUppercase: Boolean): String =
      if s.isEmpty then output
      else
        val c = if s.head.isUpper && !lastUppercase then "_" + s.head.toLower else s.head.toLower
        camelToSnake(s.tail, output + c, s.head.isUpper && !lastUppercase)

    camelToSnake(s, "", true)

  private def testNameToFIleName(testName: String): String =
    testName.replace(" ", "_").replace("'", "")

  "meta" - {
    "test cases are complete" in:
      val missingTestNames = (os
        .list(testResourceDir)
        .map(_.last)
        .toSet -- this.testNames.map(testNameToFIleName)).toSeq.sorted

      val missingTestCases =
        missingTestNames.map { testCase =>
          s"""
          |  "${testCase}" in:
          |    runTest()
          """.stripMargin
        }

      for missingTestName <- missingTestNames do
        try runTest(missingTestName)
        // ignore test failures so that any side effects of the test (for example update test
        // output) are still executed
        catch case _: TestFailedException => {}

      if missingTestCases.nonEmpty then
        val testFile =
          TestDataConstants.testSrcRoot / RelPath(
            this.getClass.getCanonicalName.replace('.', '/') + ".scala",
          )
        val missingTestCaseString = missingTestCases.mkString("\n")
        os.write.append(testFile, missingTestCaseString)
        fail(
          s"${this.getClass.getSimpleName} is missing some test cases and the test cases have been added to '$testFile'.",
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

  private def runTest(testName: String): Unit = runTestImpl(
    testResourceDir / testNameToFIleName(testName),
  )

  protected def runTest(): Unit = runTest(currentTestName)

  protected def runTestImpl(testDir: Path): Unit
