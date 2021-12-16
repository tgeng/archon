package io.github.tgeng.archon.parser

import io.github.tgeng.archon.common.{*, given}
import io.github.tgeng.archon.parser.ParseResult.*
import io.github.tgeng.archon.parser.{*, given}

extension[I, T, M[+_]] (using env: MonadPlus[ParserM[I, M]])(using MonadPlus[M])(p: ParserT[I, T, M])
  def map[S](g: T => S) = env.map(p, g)

  infix def <*>[S](f: => ParserT[I, T => S, M]) = env.starApply(p, f)

  def flatMap[S](f: T => ParserT[I, S, M]) = env.flatMap(p, f)

  infix def |(q: => ParserT[I, T, M]) = env.or(p, q)

  inline def withFilter(inline predicate: T => Boolean) =
    for
      t <- p
      filtered <- if predicate(t) then P.pure(t) else P.fail(s"'$t' need to satisfy `${stringify(predicate)}`")
    yield filtered

  def ? = p.map(Some.apply) | P.pure(None)

  def * : ParserT[I, List[T], M] = (p +) | P.pure(Nil)

  def + : ParserT[I, List[T], M] =
    for
      first <- p
      rest <- p *
    yield
      first :: rest

  infix def >>[S](q: ParserT[I, S, M]) =
    for
      _ <- p
      result <- q
    yield
      result

  infix def <<[S](q: ParserT[I, S, M]) =
    for
      result <- p
      _ <- q
    yield
      result

  infix def sepBy1[S](delimiter: ParserT[I, S, M]) =
    for
      first <- p
      rest <- (delimiter >> p) *
    yield
      first :: rest

  infix def sepBy[S](delimiter: ParserT[I, S, M]) = (p sepBy1 delimiter) | P.pure(Nil)

extension[I, M[+_]] (using pm: MonadPlus[ParserM[I, M]])(using mm: MonadPlus[M])(e: P.type)
  def any: ParserT[I, I, M] = P.satisfy(
    "any",
    current => if current.isEmpty then None else Some(1, current(0))
  )

  def eos: ParserT[I, Unit, M] = P.satisfy(
    "eos",
    current => if current.isEmpty then Some(0, ()) else None
  )

  def lift[T](ps: List[ParserT[I, T, M]]) : ParserT[I, List[T], M] =
    ps match
      case Nil => P.pure(Nil)
      case x :: xs =>
        for
          x <- x
          xs <- P.lift(xs)
        yield
          x :: xs

  def lift[Ps <: Tuple](ps: Ps) : ParserT[I, ExtractT[I, Ps, M], M] =
    val parsers = ps.toList.asInstanceOf[List[ParserT[I, Any, M]]]
    for
      xs <- P.lift(parsers)
    yield
      runtime.Tuples.fromArray(xs.toArray.asInstanceOf[Array[Object]]).asInstanceOf[ExtractT[I, Ps, M]]

/**
 * Example:
 * (ParserT[I, A, M], ParserT[I, B, M]) -> (A, B)
 */
type ExtractT[I, T <: Tuple, M[+_]] <: Tuple = T match
  case EmptyTuple => EmptyTuple
  case ParserT[I, x, M] *: xs => x *: ExtractT[I, xs, M]
