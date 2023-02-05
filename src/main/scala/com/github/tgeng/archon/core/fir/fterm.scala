package com.github.tgeng.archon.core.fir

import com.github.tgeng.archon.common.*
import com.github.tgeng.archon.core.common.*

/** Syntax
  * ```
  * user: def repeat : (x: Nat) -> [*] A -> <eff x> Vector A x
  *           repeat 0 a => Nil
  *           repeat (S n) a => a :: repeat n a
  * 
  * full: def repeat {l: [0] Level, A: [0] Type l} : (x: [1] Nat) -> [*] A -> <eff x> [1] Vector A x
  * 
  * user: def (Nat) + (Nat) : Nat
  *           0 + n => n
  *           (S m) + n => S (m + n)
  * ```
  * 
  * * Use '_' for automatically inferred value, like in Agda and Idris
  * * Use '$' for placeholder of unbound variables, like '_' in Scala. Specifically, '$0' binds to
  *   the first parameter, '$1' the second, etc
  * 
  * ```
  * handler <eff1 a | eff2 b> with [1] getParam c d : <eff3 a | eff4 d> [1] OutputType
  *   dispose p => somehowDispose p
  *   replicate p => somehowReplicate p
  *   return p x => somehowDispose p; x
  *   op1 p arg1 arg2 c => c.resume p (doSomething1 arg1 arg2)
  *   op2 p arg1 arg2 c => c.dispose p
  * ```
  */

enum FPattern:
  case FPVar(name: Name)
  case FPDataType(qn: QualifiedName, args: List[FPattern], forced: Boolean)
  case FPConstructor(name: Name, args: List[FPattern], forced: Boolean)
  case FPForced(term: FTerm)
  case FPAbsurd

enum FCoPattern:
  case FCPattern(pattern: FPattern)
  case FCProjection(name: Name)

enum FTerm:
  case FDef(qn: QualifiedName)
  case FVar(name: Name)
  case FFunctionType(argName: Name, argTy: FTerm, bodyTy: FTerm, effects: FTerm)
  case FRedux(head: FTerm, elims: List[Either[Name, FTerm]])
  case FBlock(statements: List[FStatement])
  case FLambda(ty: FTerm, clauses: List[FClause])

enum FStatement:
  case FSTerm(term: FTerm)
  case FSBinding(name: Name, term: FTerm)
  case FSHandler
    (
      eff: FTerm,
      parameter: FTerm,
    ) // TODO: add more
  case FSHeapHandler() // TODO: add more

case class FClause(lhs: List[FCoPattern], rhs: Option[FTerm])
