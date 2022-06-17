package com.github.tgeng.archon.core.ast

import com.github.tgeng.archon.common.*
import com.github.tgeng.archon.core.ir.*

import scala.collection.mutable

class BasicTypeCheckingSpec extends SignatureSpec {

  given MutableContext = mutable.ArrayBuffer()

  given TestSignature = TestSignature()

  "built-ins" in scope {
    +b"h: Heap"
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
    Builtins.builtinData.foreach { (qn, v) =>
      v match
        case (data, constructors) =>
          assertRight(checkData(data))
          constructors.foreach { con =>
            assertRight(checkDataConstructor(qn, con))
          }
    }
    Builtins.builtinDefinitions.foreach { (qn, v) =>
      v match
        case (definition, clauses) =>
          assertRight(checkDef(definition))
          clauses.foreach { clause =>
            assertRight(checkClause(qn, clause))
          }
    }
  }

  +d"""
     pure data Nat: Type L0;
       Z: Nat;
       S: Nat -> Nat;
   """

  "nat" in scope {
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

  "vector" in scope {
    t"Nil L0 Nat" hasType t"Vector L0 Nat Z"
    t"Cons L0 Nat (S Z) Z (Nil L0 Nat)" hasType t"Vector L0 Nat (S Z)"
  }

  "trivial definitions" in scope {
    +d"""
        def foo1: Type L0;
          {} = U Nat : Type L0;
        def foo2: Type L0;
          {} = U (<heap global> Nat) : Type L0;
        def succ: Nat -> Nat;
          {n: Nat} n = S n : Nat;
     """
  }
  +d"""
     def plus: Nat -> Nat -> Nat;
       {n: Nat} Z{} n = n : Nat;
       {m: Nat, n: Nat} S{m} n = S (plus m n) : Nat;
  """

  "nat ops" in scope {
    t"plus Z Z" ≡ t"Z"
    t"plus (S Z) Z" ≡ t"S Z"
    t"plus (S Z) (S Z)" ≡ t"S (S Z)"
    t"Refl L0 Nat (S (S Z))" hasType t"Equality L0 Nat (plus (S Z) (S Z)) (S (S Z))"
    t"Refl L0 Nat (S (S Z))" doesNotHaveType t"Equality L0 Nat (plus (S Z) (S Z)) Z"
  }

  "heap effect" in scope {
    t"""
        hpv a <>;
        L0
     """ hasType t"Level"
    t"""
        hpv a <>;
        L0
     """ ≡ t"L0"
    t"""
        hpv a <>;
        let v = alloc L0 a Nat ;
        let v = set L0 a Nat v Z;
        get L0 a Nat v
     """ hasType t"Nat"
  }
}
