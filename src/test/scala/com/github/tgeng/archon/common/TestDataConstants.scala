package com.github.tgeng.archon.common

import os.Path

object TestDataConstants:
  val testResourcesRoot: Path = os.Path(sys.env("TEST_RESOURCES_ROOT"))
