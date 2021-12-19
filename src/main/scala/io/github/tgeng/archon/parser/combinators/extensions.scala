package io.github.tgeng.archon.parser.combinators

import io.github.tgeng.archon.common.{*, given}
import io.github.tgeng.archon.parser.combinators.{*, given}

extension[I, T, M[+_]] (using env: MonadPlus[ParserM[I, M]])(using MonadPlus[M])(p: ParserT[I, T, M])
  infix def map[S](g: T => S) = env.map(p, g)

  infix def <*>[S](f: => ParserT[I, T => S, M]) = env.starApply(p, f)

  infix def flatMap[S](f: T => ParserT[I, S, M]) = env.flatMap(p, f)

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

  infix def as[S](s: S) = p.map(_ => s)

  infix def chainedLeftBy(op: ParserT[I, (T, T) => T, M]) : ParserT[I, T, M] = P.foldLeft(p, op, p)
  infix def chainedRightBy(op: ParserT[I, (T, T) => T, M]) : ParserT[I, T, M] = P.foldRight(p, op, p)

extension[I, M[+_]] (using pm: MonadPlus[ParserM[I, M]])(using mm: MonadPlus[M])(e: P.type)
  def nothing: ParserT[I, Unit, M] = P.satisfy("<nothing>", _ => Some(0, ()))

  def any: ParserT[I, I, M] = P.satisfy(
    "<any>",
    current => if current.isEmpty then None else Some(1, current(0))
  )

  def eos: ParserT[I, Unit, M] = P.satisfy(
    "<eos>",
    current => if current.isEmpty then Some(0, ()) else None
  )

  def satisfySingle(description: String, predicate: I => Boolean) = P.satisfy(
    description,
    current => if current.isEmpty || !predicate(current(0)) then None else Some((1, current(0)))
  )

  def anyOf(collection: IterableOnce[I]) =
    val set = Set.from(collection)
    P.satisfySingle(s"<any of $set>", i => set.contains(i))

  def foldLeft[L, R](acc: ParserT[I, L, M], op: ParserT[I, (L, R) => L, M], elem: ParserT[I, R, M]) : ParserT[I, L, M] =
    for
      acc <- acc
      opElems <- (op, elem)*
    yield
      opElems.foldLeft(acc) { (acc, opElem) =>
        val (op, elem) = opElem
        op(acc, elem)
      }

  def foldRight[L, R](elem: ParserT[I, L, M], op: ParserT[I, (L, R) => R, M], acc: ParserT[I, R, M]) : ParserT[I, R, M] =
    for
      opElems <- (elem, op).*
      acc <- acc
    yield
      opElems.foldRight(acc) { (elemOp, acc) =>
        val (elem, op) = elemOp
        op(elem, acc)
      }

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

given [I, Ps <: Tuple, M[+_]](using pm: MonadPlus[ParserM[I, M]])(using mm: MonadPlus[M]): Conversion[Ps, ParserT[I, ExtractT[I, Ps, M], M]] = P.lift(_)

/**
 * Example:
 * (ParserT[I, A, M], ParserT[I, B, M]) -> (A, B)
 */
type ExtractT[I, T <: Tuple, M[+_]] <: Tuple = T match
  case EmptyTuple => EmptyTuple
  case ParserT[I, x, M] *: xs => x *: ExtractT[I, xs, M]