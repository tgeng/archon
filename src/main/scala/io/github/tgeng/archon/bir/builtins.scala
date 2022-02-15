package io.github.tgeng.archon.bir

import io.github.tgeng.archon.common.*

import QualifiedName.*
import VTerm.*

object Builtins {
  val UnitTy = DataType(Builtin/"Unit")
  val Unit = Con(Name.Normal("Unit"))
}
