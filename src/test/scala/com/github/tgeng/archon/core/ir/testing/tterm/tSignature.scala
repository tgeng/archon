package com.github.tgeng.archon.core.ir.testing.tterm

import com.github.tgeng.archon.core.ir.{EscapeStatus, SourceInfo, Variance}

enum TDeclaration(val name: String):
  case TData
    (
      override val name: String,
      tParamTys: Seq[(TBinding, Variance)],
      ty: TTerm,
      constructors: Seq[TConstructor],
    ) extends TDeclaration(name)
  case TRecord
    (
      selfName: String,
      override val name: String,
      tParamTys: Seq[(TBinding, Variance)],
      ty: TTerm,
      fields: Seq[TField],
    ) extends TDeclaration(name)
  case TDefinition
    (
      override val name: String,
      tParamTys: Seq[(TBinding, EscapeStatus)],
      ty: TTerm,
      clauses: Seq[TClause],
    ) extends TDeclaration(name)
  // TODO: add TEffect

case class TConstructor
  (
    name: String,
    ty: TTerm,
  )

case class TField
  (
    name: String,
    ty: TTerm,
  )

case class TClause
  (
    patterns: Seq[TCoPattern],
    body: Option[TTerm],
  )

enum TCoPattern(val sourceInfo: SourceInfo):
  case TcProjection(name: String)(using sourceInfo: SourceInfo) extends TCoPattern(sourceInfo)
  case TcPattern(pattern: TPattern) extends TCoPattern(pattern.sourceInfo)

enum TPattern(val sourceInfo: SourceInfo):
  case TpId(name: String)(using sourceInfo: SourceInfo) extends TPattern(sourceInfo)
  case TpXConstructor
    (forced: Boolean, name: String, args: Seq[TPattern])
    (using sourceInfo: SourceInfo) extends TPattern(sourceInfo)
  case TpForced(tTerm: TTerm)(using sourceInfo: SourceInfo) extends TPattern(sourceInfo)
  case TPAbsurd()(using sourceInfo: SourceInfo) extends TPattern(sourceInfo)
