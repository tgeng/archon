package com.github.tgeng.archon.common

import scala.concurrent.duration.Duration
import com.github.tgeng.archon.common.{*, given}
import com.github.tgeng.archon.parser.combinators.{*, given}

extension[L, R] (e: Either[L, R])
  def asRight : R = e match
    case Left(l) => throw IllegalArgumentException(l.toString)
    case Right(r) => r

  def asLeft : L = e match
    case Right(r) => throw IllegalArgumentException(r.toString)
    case Left(l) => l

def timed[T](description: String)(action: =>T): T =
  val start = System.currentTimeMillis()
  val result = action
  val end = System.currentTimeMillis()
  val duration = Duration.fromNanos((end - start) * 1000000)
  println(s"$description took $duration")
  result
