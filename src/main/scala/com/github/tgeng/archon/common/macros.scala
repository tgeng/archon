package com.github.tgeng.archon.common

import scala.quoted.*

inline def enclosingName(inline e: Any): String = ${
  enclosingNameImpl('e)
}

private def enclosingNameImpl(e: Expr[Any])(using Quotes): Expr[String] = {
  import quotes.reflect.*
  Expr(Symbol.spliceOwner.owner.owner.name)
}

inline def stringify(inline e: Any): String = ${
  stringifyImpl('e)
}

private def stringifyImpl(e: Expr[Any])(using Quotes): Expr[String] = {
  import quotes.reflect.*
  Expr(e.show)
}
