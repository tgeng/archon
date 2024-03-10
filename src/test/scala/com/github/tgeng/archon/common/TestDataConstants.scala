package com.github.tgeng.archon.common

import java.io.File
import java.nio.file.{Path, Paths}

object TestDataConstants {
  val testResourcesRoot: Path = Paths.get(sys.env("TEST_RESOURCES_ROOT")).nn
}
