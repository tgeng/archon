package com.github.tgeng.archon.core.ir.testing.tterm

import com.github.tgeng.archon.core.ir.{SourceInfo, Variance}

enum TDeclaration:
  case TData
    (
      name: String,
      tParamTys: List[(TBinding, Variance)],
      ty: TTerm,
      constructors: List[TConstructor],
    )
  case TRecord
    (
      selfName: String,
      name: String,
      tParamTys: List[(TBinding, Variance)],
      ty: TTerm,
      fields: List[TField],
    )
  case TDefinition
    (
      name: String,
      tParamTys: List[TBinding],
      ty: TTerm,
      clauses: List[TClause],
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
    patterns: List[TCoPattern],
    body: Option[TTerm],
  )

enum TCoPattern(val sourceInfo: SourceInfo):
  case TcProjection(name: String)(using sourceInfo: SourceInfo) extends TCoPattern(sourceInfo)
  case TcPattern(pattern: TPattern) extends TCoPattern(pattern.sourceInfo)

enum TPattern(val sourceInfo: SourceInfo):
  case TpVar(name: String)(using sourceInfo: SourceInfo) extends TPattern(sourceInfo)
  case TpXConstructor(name: String, args: List[TPattern], forced: Boolean)(using sourceInfo: SourceInfo)
    extends TPattern(sourceInfo)
  case TpForced(tTerm: TTerm)(using sourceInfo: SourceInfo) extends TPattern(sourceInfo)
  case TPAbsurd()(using sourceInfo: SourceInfo) extends TPattern(sourceInfo)

