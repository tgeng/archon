package com.github.tgeng.archon.common

import os.Path

object TestDataConstants:
  val testResourcesRoot: Path =
    val pathString = sys.env("TEST_RESOURCES_ROOT")
    if pathString.startsWith("/") then os.Path(pathString)
    else os.pwd / os.RelPath(pathString)

  val testSrcRoot: Path = testResourcesRoot / os.up / "scala"
