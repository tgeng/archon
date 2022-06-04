package com.github.tgeng.archon.core.ast

class BasicTypeCheckingSpec extends SignatureSpec {
  +b"h: Heap"

  "built-ins" in ~ {
    +b"l: Level"

    t"L0" hasType t"<> Level"
    t"h" hasType t"<> Heap"
    t"l" hasType t"<> Level"
  }
}