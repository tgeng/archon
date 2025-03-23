package com.github.tgeng.archon.core.ir

import com.github.tgeng.archon.core.common.*
import com.github.tgeng.archon.core.ir.CheckVisibilityMode.{IMPLEMENTATION, INTERFACE}
import com.github.tgeng.archon.core.ir.IrError.*
import com.github.tgeng.archon.core.ir.SourceInfo.*

import scala.math.Ordered.orderingToOrdered

enum Variance:
  case INVARIANT, COVARIANT, CONTRAVARIANT
  def flip: Variance = this match
    case INVARIANT     => INVARIANT
    case COVARIANT     => CONTRAVARIANT
    case CONTRAVARIANT => COVARIANT

given SourceInfo = SiEmpty

enum Declaration:
  case Data
    (
      qn: QualifiedName,
      context: TContext,
      /* binding: + context */
      tIndexTys: Telescope,
      /* binding: + context */
      level: VTerm,
      interfaceScope: QualifiedName,
      implementationScope: QualifiedName,
    )
  case Corecord
    (
      qn: QualifiedName,
      context: TContext,
      /* binding += context */
      level: VTerm,
      selfBinding: Binding[VTerm],
      interfaceScope: QualifiedName,
      implementationScope: QualifiedName,
    )

  case Definition
    (
      qn: QualifiedName,
      context: EContext,
      /* binding += context */
      ty: CTerm,
      interfaceScope: QualifiedName,
      implementationScope: QualifiedName,
    )

  case Effect
    (
      qn: QualifiedName,
      context: Context,
      // binding += context
      continuationUsage: VTerm,
      interfaceScope: QualifiedName,
      implementationScope: QualifiedName,
    )

  def qn: QualifiedName

  /** The scope in which the interface of this declaration is visible
    */
  def interfaceScope: QualifiedName

  /** The scope in which the implementation of this declaration is visible
    */
  def implementationScope: QualifiedName

import com.github.tgeng.archon.core.ir.Declaration.*

case class Constructor
  (
    name: Name,
    paramTys: Telescope = Nil, /* binding += context */
    /** Arguments passed to the data type constructor. The length should be identical with
      * `tIndexTys`. Hence, for non-indexed type this should just be `Nil`. For indexed families,
      * the argument here can be any expressions. For example, for `Vec (A: Type) : (n: Nat) ->
      * Type`, this would be [0] for constructor `Nil` and `[n + 1]` for constructor `Cons`.
      */
    tArgs: Arguments = Nil, /* binding += context + paramTys */
  )

case class Cofield(name: Name, /* binding += context + 1 for self */ ty: CTerm)

case class Clause
  (
    // contains def.context + elaborated variables from lhs co-patterns
    context: Context,
    lhs: List[CoPattern], /* bindings += clause.context */
    rhs: CTerm, /* bindings += clause.context */
    ty: CTerm, /* bindings += clause.context */
  )

case class Operation
  (
    name: Name,
    paramTys: Telescope, /* + context */
    resultTy: VTerm /* + context + paramTys */,
    resultUsage: VTerm, /* + context + paramTys */
  )

trait Signature:
  type S <: Signature
  def addDeclaration(d: Declaration): S
  def replaceDeclaration(d: Declaration): S

  def addConstructor(qn: QualifiedName, c: Constructor): S

  def addCofield(qn: QualifiedName, f: Cofield): S

  def addClause(qn: QualifiedName, c: Clause): S

  def addCaseTree(qn: QualifiedName, ct: CaseTree): S

  def addOperation(qn: QualifiedName, o: Operation): S

  def getDataOptionImpl(qn: QualifiedName): Option[Data]

  def getData(qn: QualifiedName)(using TypingContext): Either[IrError, Data] =
    checkDeclarationHead(qn, getDataOptionImpl(qn))

  def getConstructorsOptionImpl(qn: QualifiedName): Option[IndexedSeq[Constructor]]

  def getConstructors
    (qn: QualifiedName)
    (using TypingContext)
    : Either[IrError, IndexedSeq[Constructor]] =
    checkDeclarationBody(qn, getDataOptionImpl(qn), getConstructorsOptionImpl(qn))

  def getConstructor
    (qn: QualifiedName, conName: Name)
    (using TypingContext)
    : Either[IrError, Constructor] =
    getConstructors(qn).flatMap:
      _.collectFirst:
        case con if con.name == conName => con
      match
        case None      => Left(MissingConstructor(conName, qn))
        case Some(con) => Right(con)

  def getCorecordOptionImpl(qn: QualifiedName): Option[Corecord]

  def getCorecord(qn: QualifiedName)(using TypingContext): Either[IrError, Corecord] =
    checkDeclarationHead(qn, getCorecordOptionImpl(qn))

  def getCofieldsOptionImpl(qn: QualifiedName): Option[IndexedSeq[Cofield]]

  def getCofields(qn: QualifiedName)(using TypingContext): Either[IrError, IndexedSeq[Cofield]] =
    checkDeclarationBody(qn, getCorecordOptionImpl(qn), getCofieldsOptionImpl(qn))

  def getCofield
    (qn: QualifiedName, cofieldName: Name)
    (using TypingContext)
    : Either[IrError, Cofield] =
    getCofields(qn).flatMap:
      _.collectFirst:
        case cofield if cofield.name == cofieldName => cofield
      match
        case None          => Left(MissingCofield(cofieldName, qn))
        case Some(cofield) => Right(cofield)

  // In a previous design I had derived definitions for effects, data, and corecord. But that turns
  // out to be not good. Instead, data type and value constructors, corecord type constructors, and
  // effect type constructors and operators directly contribute to global names that are recognized
  // by the global mix-fix parser. This way, type checking is much simpler and more predictable.
  // Also, any name conflicts are caught during parsing. Corecord cofield will have a special syntax for
  // projection. Type class also contributes to the mix-fix parser and it's basically syntax sugar
  // of corecords under the hood.
  def getDefinitionOptionImpl(qn: QualifiedName): Option[Definition]

  def getDefinition(qn: QualifiedName)(using TypingContext): Either[IrError, Definition] =
    checkDeclarationHead(qn, getDefinitionOptionImpl(qn))

  def getClausesOptionImpl(qn: QualifiedName): Option[IndexedSeq[Clause]]

  def getClauses(qn: QualifiedName)(using TypingContext): Either[IrError, IndexedSeq[Clause]] =
    checkDeclarationBody(qn, getDefinitionOptionImpl(qn), getClausesOptionImpl(qn))

  def getCaseTreeOptionImpl(qn: QualifiedName): Option[CaseTree]

  def getCaseTree(qn: QualifiedName)(using TypingContext): Either[IrError, CaseTree] =
    checkDeclarationBody(qn, getDefinitionOptionImpl(qn), getCaseTreeOptionImpl(qn))

  def getEffectOptionImpl(qn: QualifiedName): Option[Effect]
  def getEffect(qn: QualifiedName)(using TypingContext): Either[IrError, Effect] =
    checkDeclarationHead(qn, getEffectOptionImpl(qn))

  def getOperationsOptionImpl(qn: QualifiedName): Option[IndexedSeq[Operation]]
  def getOperations
    (qn: QualifiedName)
    (using TypingContext)
    : Either[IrError, IndexedSeq[Operation]] =
    checkDeclarationBody(qn, getEffectOptionImpl(qn), getOperationsOptionImpl(qn))

  def getOperation
    (qn: QualifiedName, opName: Name)
    (using TypingContext)
    : Either[IrError, Operation] =
    getOperations(qn).flatMap:
      _.collectFirst:
        case operation if operation.name == opName => operation
      match
        case None            => Left(MissingOperation(opName, qn))
        case Some(operation) => Right(operation)

  def getOperation(qn: QualifiedName)(using TypingContext): Either[IrError, Operation] =
    qn match
      case QualifiedName.Node(qn, name) => getOperation(qn, name)
      case _                            => throw IllegalArgumentException(s"missing operation $qn")

  private def checkDeclarationHead[D <: Declaration]
    (qn: QualifiedName, decl: Option[D])
    (using TypingContext)
    : Either[IrError, D] =
    decl match
      case None => Left(MissingDeclaration(qn))
      case Some(decl) =>
        checkVisibility(decl, CheckVisibilityMode.INTERFACE) match
          case None        => Right(decl)
          case Some(error) => Left(error)

  private def checkDeclarationBody[D <: Declaration, R]
    (qn: QualifiedName, decl: Option[D], body: => Option[R])
    (using TypingContext)
    : Either[IrError, R] =
    decl match
      case None => Left(MissingDeclaration(qn))
      case Some(decl) =>
        checkVisibility(decl, CheckVisibilityMode.IMPLEMENTATION) match
          case None =>
            body match
              case None       => Left(MissingDeclarationBody(qn))
              case Some(body) => Right(body)
          case Some(error) => Left(error)

  /** Visibilities are set on two things: head (interface) and body (implementation), where head
    * should always have an equal or less restrictive visibility.
    *
    * For both head and body, visibility setting controls at which scope the entity is visible,
    * where scope is basically the fully qualified name of the current declaration that's being
    * elaborated currently. Note that, this means a "public" function would expose the head and body
    * of all internal lambda and local functions. This may be undesirable from the perspective of
    * the user language but would nevertheless align with the idea of a "public" implementation.
    * It's probably desirable to separately add some mechanism in the user language to prevent
    * references to lambda and local functions.
    *
    * For example, a definition called `baz` in module `foo.bar` has fully qualified name
    * `foo.bar.baz`. If a declaration is declared to be visible to scope `foo.bar`, then that
    * declaration can be accessed when * elaborating `foo.bar.baz`.
    *
    * This mechanism can be used to model common visibility idioms seen in various programming
    * languages.
    *
    *   - public export in idris: this means a declaration is public for both its head and body (aka
    *     signature and implementation). That is,
    *     - head: _root_
    *     - body: _root_
    *   - public in idris: this means a declaration's head is public but body is module accessible
    *     - head: _root_
    *     - body: %parent% (aka, `foo.bar` for `foo.bar.baz`)
    *   - opaque type: this means the head is public, yet the body is private to itself (of course
    *     one can limit the "opaqueness" by setting the appropriate body visibility scope. Note: the
    *     type is not opaque for member declarations in its scope, this way, one can still create
    *     helper functions to manipulate this opaque type
    *     - head: _root_
    *     - body: %current% (aka `foo.bar.baz` for `foo.bar.baz`)
    *   - common private in most languages:
    *     - head: %parent%
    *     - body: %current%
    *
    * In addition, visibility consistency needs to be checked. That is, during elaboration of a head
    * or a body, the type checker must ensure all the declarations accessed align with the declared
    * visibility scope of the thing being elaborated. For example, when elaborating head of
    * `foo.bar.baz`, which has visibility scope `_root_`, in addition to ensure the referenced thing
    * is visible to scope `foo.bar.baz`, the type checker also needs to ensure it is visible to
    * `_root_`. Otherwise, `foo.bar.baz` would be exposing things that are not visible to `_root_`.
    */

  private def checkVisibility
    (decl: Declaration, mode: CheckVisibilityMode)
    (using ctx: TypingContext)
    : Option[IrError] =
    val visibleScope = mode match
      case INTERFACE      => decl.interfaceScope
      case IMPLEMENTATION => decl.implementationScope

    if visibleScope > ctx.contextScope then
      return Some(DeclarationIsInvisibleError(decl.qn, mode, ctx.contextScope, visibleScope))

    if visibleScope > ctx.exposedScope then
      return Some(ExposingInvisibleDeclarationError(decl.qn, mode, ctx.exposedScope, visibleScope))

    None
