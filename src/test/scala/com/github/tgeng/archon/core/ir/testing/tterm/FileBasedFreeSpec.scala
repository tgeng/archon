package com.github.tgeng.archon.core.ir.testing.tterm

import com.github.tgeng.archon.common.*
import org.scalatest.freespec.AnyFreeSpec
import org.scalatest.matchers.should.Matchers.should

import java.nio.file.Path
import scala.language.unsafeNulls

abstract class FileBasedFreeSpec extends AnyFreeSpec:
  private val currentTestNameStorage = new ThreadLocal[String]
  private val testResourceDir =
    TestDataConstants.testResourcesRoot / this.getClass.getCanonicalName.replace('.', '/')

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

  override def withFixture(test: NoArgTest) = {
    currentTestNameStorage.set(test.name)
    val outcome = super.withFixture(test)
    currentTestNameStorage.set(null)
    outcome
  }

  private def currentTestName: String = {
    val testName = currentTestNameStorage.get()
    assert(testName != null, "currentTestName should only be called in a test")
    testName
  }

  protected def runTest(): Unit = runTestImpl(testResourceDir / currentTestName)

  protected def runTestImpl(testDir: Path): Unit
