package com.github.tgeng.archon.core.ir.testing.tterm

enum TranslationError extends Exception:
  case UnresolvedSymbol(name: String)
