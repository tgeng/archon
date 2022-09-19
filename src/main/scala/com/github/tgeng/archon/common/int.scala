package com.github.tgeng.archon.common

extension(i: Int) {
  def sub: String = i.toString.map(i => (i - '0' + '₀').toChar)
}
