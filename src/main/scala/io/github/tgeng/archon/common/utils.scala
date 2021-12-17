package io.github.tgeng.archon.common

extension[T] (t: T | Null)
  def !! : T =
    assert(t != null)
    t
