package com.github.tgeng.archon.common

import java.io.File
import scala.io.Source
import org.scalatest.freespec.AnyFreeSpec

abstract class SingleFileBasedSpec(
  relativePath: String,
  fileFilter: File => Boolean = _ => true
) extends AnyFreeSpec:
  private val testDataDir = TestDataConstants.testResourcesRoot / relativePath
  for file <- testDataDir.listFiles().!! if fileFilter(file.!!) do
    file.!!.getName.!! in {
      Source.fromFile(file.!!).use { source =>
        runTest(file.!!, source)
      }
    }
  def runTest(testData: File, source: Source): Unit
