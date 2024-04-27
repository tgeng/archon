package com.github.tgeng.archon.common

import com.github.tgeng.archon.core.common.{HasException, Name, QualifiedName}
import com.github.tgeng.archon.core.ir.{Binding, CTerm, VTerm}

import scala.collection.mutable
import scala.concurrent.duration.Duration

extension [L, R](e: Either[L, R])
  def asRight: R = e match
    case Left(l) =>
      if l.isInstanceOf[HasException] then
        throw IllegalStateException(
          l.toString,
          l.asInstanceOf[HasException].exception,
        )
      else throw IllegalStateException(l.toString)
    case Right(r) => r

  def asLeft: L = e match
    case Right(r) => throw IllegalArgumentException(r.toString)
    case Left(l)  => l

def timed[T](description: String)(action: => T): T =
  val start = System.currentTimeMillis()
  val result = action
  val end = System.currentTimeMillis()
  val duration = Duration.fromNanos((end - start) * 1000000)
  println(s"$description took $duration")
  result

