package com.github.tgeng.archon.common

import org.scalatest.freespec.AnyFreeSpec

import java.nio.file.Path
import scala.io.Source
import scala.language.unsafeNulls

abstract class SingleFileBasedSpec
  (
    relativePath: String,
    fileFilter: Path => Boolean = _ => true,
  )
  extends AnyFreeSpec:
  private val testDataDir = TestDataConstants.testResourcesRoot / relativePath
  for file <- testDataDir.listFiles() if fileFilter(file) do
    file.getName.toString in {
      Source.fromFile(file.toFile).use { source =>
        runTest(file, source)
      }
    }
  def runTest(testData: Path, source: Source): Unit
