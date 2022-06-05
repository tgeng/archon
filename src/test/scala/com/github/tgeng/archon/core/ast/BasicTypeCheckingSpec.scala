package com.github.tgeng.archon.core.ast

class BasicTypeCheckingSpec extends SignatureSpec {
  +b"h: Heap"

  "built-ins" in ~ {
    +b"l: Level"

//    t"L0" hasType t"<> Level"
//    t"L0" doesNotHaveType  t"<> Effects"
//    t"h" hasType t"<> Heap"
//    t"h" doesNotHaveType  t"<> Level"
//    t"l" hasType t"<> Level"
//    t"l" doesNotHaveType  t"<> Effects"
//
//    t"Heap" hasType t"<> Type L0"
//    t"Effects" hasType t"<> Type L0"
//    t"Level" hasType t"<> TYPE0"

    debug {
      t"Cell L0 h Effects" hasType t"<> Type L0"
    }

//    t"Refl L0 Effects total total" hasType t"<> Equality L0 Effects total total"
  }
}
