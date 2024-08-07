package com.github.tgeng.archon.core.fir

import com.github.tgeng.archon.core.common.*

import scala.collection.immutable.SeqMap

/** # Syntax
  *
  * ## Hard keywrods: -> ; , ( ) { } $ => ## Soft keywords: < > [ ]
  *
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
  * * Use `_` for automatically inferred value, like in Agda and Idris * Use `$` for placeholder of
  * unbound variables, like `_` in Scala. Specifically, `$0` binds to the first parameter, `$1` the
  * second, etc. Also, internal names of operator has holes filled with `$`. So the `+` operator in
  * `1 + 2` has internal name `$+$`.
  *
  * ## Handler
  *
  * ```
  * handler <eff1 a | eff2 b> with (getParam c d: [1] ParamType) : <eff3 a | eff4 d> [1] OutputType
  *   dispose p => somehowDispose p
  *   replicate p => somehowReplicate p
  *   return p x => somehowDispose p; x
  *   op foo p (A x) arg2 c => c.resume p (doSomething1 x arg2)
  *      foo p (B y) _ c => c.resume p (doSomethingElse1 y)
  *   op bar p arg1 arg2 c => c.dispose p; someResult
  * ```
  * # Lambda
  * ```
  * user: filter { e => e % 2 == 0 } [1, 2, 3]
  * full: filter {
  *         Nat -> Boolean
  *         e => e % 2 == 0
  *       } [1, 2, 3]
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
  case FRedex(head: FTerm, elims: List[Either[Name, FTerm]])
  case FBlock(statements: List[FStatement])
  // TODO: Properly handle lambda requires term synthesis. Otherwise, usage of captured terms must
  //  be provided manually, which is very cumbersome.
  // case FLambda(ty: FTerm, clauses: List[FClause])

case class HandlerParameter
  (
    parameter: FTerm,
    parameterUsage: FTerm,
    parameterType: FTerm,
    parameterDisposer: Option[FTerm],
    parameterReplicator: Option[FTerm],
  )

enum FStatement:
  case FSTerm(term: FTerm)
  case FSBinding(name: Name, term: FTerm)
  case FSHandler
    (
      eff: FTerm,
      parameter: Option[HandlerParameter],
      outputEffects: FTerm,
      outputUsage: FTerm,
      outputType: FTerm,
      transform: Option[FTerm],
      // TODO: Properly handle handler implementation requires term synthesis and type-drive
      //  qualified name resolution. Otherwise, manually write down these is very cumbersome.
      handlers: SeqMap[QualifiedName, FTerm],
    )
  case FSHeapHandler(name: Name)

case class FClause(lhs: List[FCoPattern], rhs: Option[FTerm])
