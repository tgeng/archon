package com.github.tgeng.archon.core.ast

import com.github.tgeng.archon.common.*
import com.github.tgeng.archon.core.common.*
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
    t"Cell L0 h Effects" ⪯ t"UCell L0 h Effects"

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
    Builtins.builtinRecords.foreach { (qn, v) =>
      v match
        case (record, fields) =>
          assertRight(checkRecord(record))
          fields.foreach { field =>
            assertRight(checkRecordField(qn, field))
          }
    }
    Builtins.builtinEffects.foreach { (qn, v) =>
      v match
        case (effect, operators) =>
          assertRight(checkEffect(effect))
          operators.foreach { operator =>
            assertRight(checkOperator(qn, operator))
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
    t"Cons L0 Unit Z MkUnit (Nil L0 Unit)" hasType t"Vector L0 Unit (S Z)"
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

    def concat (l: Level) (A: Type l) : m: Nat -> n: Nat -> Vector l A m -> Vector l A n -> Vector l A (plus m n);
      {n: Nat, v_n: Vector l A n} Z{} n Nil{} v_n = v_n : Vector l A n;
      {a: A, m: Nat, n: Nat, v_m: Vector l A m, v_n: Vector l A n} S{m} n Cons{m a v_m} v_n = Cons l A (plus m n) a (concat l A m n v_m v_n) : Vector l A (S (plus m n));
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
        let v = alloc L0 a Nat;
        let v = set L0 a Nat v Z;
        get L0 a Nat v
     """ hasType t"Nat"
  }

  +d"""
     effect exception (l: Level) (A: Type l);
       throw: A -> Nothing;
     pure data Nothing: Type L0;
   """

  "effect handler" in scope {
    t"throw L0 Nat (S Z)" hasType t"<exception L0 Nat> Nothing"

    t"""
       hdl exception{L0 Nat} <> Nat {
         throw n -> n;
       };
       throw L0 Nat (S Z);
       Z
     """ ≡ t"""S Z"""
  }

  +d"""
     pure data Fin: Nat -> Type L0;
       FZ: k: Nat -> Fin (S k);
       FS: k: Nat -> Fin k -> Fin (S k);

     effect dice (numFaces: Nat);
       roll: Fin numFaces;

     def finToNat: bound: Nat -> Fin bound -> Nat;
       {n: Nat} S{n} FZ{n} = Z: Nat;
       {n: Nat, f: Fin n} S{n} FS{n f} = S (finToNat n f): Nat;
   """

  "dice" in scope {
    t"""
       let n1 = S Z;
       let n2 = S n1;
       let n3 = S n2;
       hdl dice{n3} <> Nat {
         roll -> plus
                   (plus
                     ((frc resume) (FZ n2))
                     ((frc resume) (FS n2 (FZ n1)))
                   )
                   ((frc resume) (FS n2 (FS n1 (FZ Z))));
       };
       finToNat n3 (roll n3)
     """ ≡ t"S (S (S Z))"

    t"""
       let n1 = S Z;
       let n2 = S n1;
       let n3 = S n2;
       hpv a <>;
       hdl dice{n3} <> Nat {
         roll -> plus
                   (plus
                     ((frc resume) (FZ n2))
                     ((frc resume) (FS n2 (FZ n1)))
                   )
                   ((frc resume) (FS n2 (FS n1 (FZ Z))));
       };
       let v = alloc L0 a Nat;
       let v = set L0 a Nat v Z;
       let r = finToNat n3 (roll n3);
       set L0 a Nat v (plus (get L0 a Nat v) r);
       get L0 a Nat v
     """ ≡ t"S (S (S (S Z)))"

     t"""
        let n1 = S Z;
        let n2 = S n1;
        let n3 = S n2;
        hdl dice{n3} <> Nat {
          roll -> plus
                    (plus
                      ((frc resume) (FZ n2))
                      ((frc resume) (FS n2 (FZ n1)))
                    )
                    ((frc resume) (FS n2 (FS n1 (FZ Z))));
        };
        hpv a <>;
        let v = alloc L0 a Nat;
        let v = set L0 a Nat v Z;
        let r = finToNat n3 (roll n3);
        set L0 a Nat v (plus (get L0 a Nat v) r);
        get L0 a Nat v
      """ ≡ t"S (S (S Z))"
  }
}
