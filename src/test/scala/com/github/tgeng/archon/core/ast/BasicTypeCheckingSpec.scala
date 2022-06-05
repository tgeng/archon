package com.github.tgeng.archon.core.ast

class BasicTypeCheckingSpec extends SignatureSpec {
  +b"h: Heap"

  "built-ins" in ~ {
    +b"l: Level"

    t"L0" hasType t"<> Level"
    t"L0" doesNotHaveType  t"<> Effects"
    t"h" hasType t"<> Heap"
    t"h" doesNotHaveType  t"<> Level"
    t"l" hasType t"<> Level"
    t"l" doesNotHaveType  t"<> Effects"

    t"Heap" hasType t"<> (Type L0)"
    t"Effects" hasType t"<> (Type L0)"
    t"Level" hasType t"<> TYPE0"
  }
}
