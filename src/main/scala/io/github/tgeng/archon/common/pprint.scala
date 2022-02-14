package io.github.tgeng.archon.common

import scala.compiletime.*
import scala.deriving.*

trait PPrint[T]:
  def pprint(t: T, indent: Int): String

object PPrint:
  inline given derived[T] (using m: Mirror.Of[T]): PPrint[T] =
    inline m match
      case s: Mirror.SumOf[T] => ???