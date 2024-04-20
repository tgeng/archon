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

def cTermPprint: pprint.PPrinter =
  val visited = mutable.Set.empty[Any]

  def p: pprint.PPrinter = pprint.copy(
    additionalHandlers = {
      case qn: QualifiedName => pprint.Tree.Literal(s"qn\"${qn.toString}\"")
      case n: Name           => pprint.Tree.Literal(s"n\"${n.toString}\"")
      case b: Binding[?] if !visited.contains((b, b.name)) =>
        visited.add((b, b.name))
        pprint.Tree
          .Infix(
            p.treeify(b, false, true),
            "@",
            pprint.Tree.Literal(pprint.apply(b.name.value.toString).toString),
          )
      case t: VTerm if !visited.contains((t, t.sourceInfo)) =>
        visited.add((t, t.sourceInfo))
        pprint.Tree
          .Infix(
            p.treeify(t, false, true),
            "@",
            pprint.Tree.Literal(pprint.apply(t.sourceInfo.toString).toString),
          )
      case t: CTerm if !visited.contains((t, t.sourceInfo)) =>
        visited.add((t, t.sourceInfo))
        pprint.Tree
          .Infix(
            p.treeify(t, false, true),
            "@",
            pprint.Tree.Literal(pprint.apply(t.sourceInfo.toString).toString),
          )
    },
  )

  p
