package com.github.tgeng.archon.common

import org.scalatest.freespec.AnyFreeSpec
import os.Path

import scala.io.Source
import scala.language.unsafeNulls

abstract class SingleFileBasedSpec
  (
    relativePath: String,
    fileFilter: Path => Boolean = _ => true,
  )
  extends AnyFreeSpec:
  private val testDataDir = TestDataConstants.testResourcesRoot / relativePath
  for file <- os.list(testDataDir) if fileFilter(file) do
    file.last in:
      Source.fromFile(file.toIO).use { source =>
        runTest(file, source)
      }
  def runTest(testData: Path, source: Source): Unit
