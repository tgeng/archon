package com.github.tgeng.archon.core.ir.testing.tterm

import com.github.tgeng.archon.core.ir.{SourceInfo, Variance}

enum TDeclaration:
  case TData
    (
      name: String,
      tParamTys: Seq[(TBinding, Variance)],
      ty: TTerm,
      constructors: Seq[TConstructor],
    )
  case TRecord
    (
      selfName: String,
      name: String,
      tParamTys: Seq[(TBinding, Variance)],
      ty: TTerm,
      fields: Seq[TField],
    )
  case TDefinition
    (
      name: String,
      tParamTys: Seq[TBinding],
      ty: TTerm,
      clauses: Seq[TClause],
    )
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
  case TpVar(name: String)(using sourceInfo: SourceInfo) extends TPattern(sourceInfo)
  case TpXConstructor(forced: Boolean, name: String, args: Seq[TPattern])(using sourceInfo: SourceInfo)
    extends TPattern(sourceInfo)
  case TpForced(tTerm: TTerm)(using sourceInfo: SourceInfo) extends TPattern(sourceInfo)
  case TPAbsurd()(using sourceInfo: SourceInfo) extends TPattern(sourceInfo)

