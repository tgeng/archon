package com.github.tgeng.archon.common.parsing

def indexToColumn(index: Int, text: String) = {
  val lastWhitespaceIndex = index - 1
  var i = lastWhitespaceIndex
  while i >= 0 && text(i) != '\n' do i -= 1
  lastWhitespaceIndex - i
}
