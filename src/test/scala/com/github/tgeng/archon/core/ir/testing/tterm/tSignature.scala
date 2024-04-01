package com.github.tgeng.archon.core.ir.testing.tterm

import com.github.tgeng.archon.core.ir.Variance

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
    body: TTerm,
  )

enum TCoPattern:
  // TODO: implement this
  case Foo
