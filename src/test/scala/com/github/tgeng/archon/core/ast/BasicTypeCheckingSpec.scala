package com.github.tgeng.archon.core.ast

class BasicTypeCheckingSpec extends SignatureSpec {
  +b"h: Heap"

  "built-ins" in ~ {
    +b"l: Level"

    t"L0" hasType t"Level"
    t"L0" doesNotHaveType t"Effects"
    t"h" hasType t"Heap"
    t"h" doesNotHaveType t"Level"
    t"global" hasType t"Heap"
    t"l" hasType t"Level"
    t"l" doesNotHaveType t"Effects"

    t"Type L0" hasType t"Type L1"
    t"Type L1" hasType t"Type L2"
    t"Type L0" hasType t"Type L2"
    t"Type L0" doesNotHaveType t"Type L0"
    t"Type L0" ⪯ t"Type L1"

    t"L0" ⋠ t"L1"

    t"CType L0 <>" hasType t"CType L1 <>"
    t"CType L1 <>" hasType t"CType L2 <>"
    t"CType L0 <>" hasType t"CType L2 <>"
    t"CType L0 <>" doesNotHaveType t"CType L0 <>"
    t"CType L0 <>" ⪯ t"CType L1 <>"

    t"Heap" hasType t"Type L0"
    t"Effects" hasType t"Type L0"
    t"heap global" hasType t"Effects"
    t"Level" hasType t"TYPE0"

    t"Cell L0 h Effects" hasType t"Type L0"
    t"UCell L0 h Effects" hasType t"Type L0"

    t"Equality L0 Effects <> <>" hasType t"Type L0"
    t"Equality L0 Heap h global" hasType t"Type L0"
    t"Refl L0 Effects <>" hasType t"Equality L0 Effects <> <>"
    t"Refl L0 Heap h" doesNotHaveType t"Equality L0 Effects h global"

    t"Effects -> Effects" hasType t"CType L0 <>"
    t"Effects -> Effects -> Effects" hasType t"CType L0 <>"
    t"Level -> Effects" hasType t"CTYPE0"
  }

  +d"""
     pure data Nat: Type L0;
       Z: Nat;
       S: Nat -> Nat;
   """

  "nat" in ~ {
    t"Z" hasType t"Nat"
    t"Z" doesNotHaveType t"Level"
    t"S Z" hasType t"Nat"
    t"S (S Z)" hasType t"Nat"
    t"Nat" hasType t"Type L0"
  }

  +d"""
     pure data Vector (l: Level) (A: Type l): Nat -> Type l;
       Nil: Vector l A Z;
       Cons: n: Nat -> A -> Vector l A n -> Vector l A (S n);
   """

  "vector" in ~ {
    t"Nil L0 Nat" hasType t"Vector L0 Nat Z"
    t"Cons L0 Nat (S Z) Z (Nil L0 Nat)" hasType t"Vector L0 Nat (S Z)"
  }

  "basic definitions" in ~ {
    +d"""
       def foo1: Type L0;
         {} = U Nat : Type L0;
     """
    +d"""
       def foo2: Type L0;
         {} = U (<heap global> Nat) : Type L0;
   """
  }
}
