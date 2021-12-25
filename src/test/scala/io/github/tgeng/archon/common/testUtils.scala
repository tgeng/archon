package io.github.tgeng.archon.common

extension[L, R] (e: Either[L, R])
  def asRight : R = e match
    case Left(l) => throw IllegalArgumentException(l.toString)
    case Right(r) => r

  def asLeft : L = e match
    case Right(r) => throw IllegalArgumentException(r.toString)
    case Left(l) => l
