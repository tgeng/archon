TLet(
  name = "a",
  t = TLet(
    name = "a1",
    t = TId(id = "getA1") @ "getA1",
    ty = TAuto() @ """let a1 = getA1
  let a2 = getA2
  plus a1 a2""",
    effects = TAuto(),
    usage = TAuto(),
    body = TLet(
      name = "a2",
      t = TId(id = "getA2") @ "getA2",
      ty = TAuto(),
      effects = TAuto(),
      usage = TAuto(),
      body = TRedex(
        c = TId(id = "plus") @ "plus",
        elims = List(ETerm(v = TId(id = "a1") @ "a1"), ETerm(v = TId(id = "a2") @ "a2"))
      ) @ "plus a1 a2"
    ) @ """let a2 = getA2
  plus a1 a2"""
  ) @ """let a1 = getA1
  let a2 = getA2
  plus a1 a2""",
  ty = TAuto(),
  effects = TAuto(),
  usage = TAuto(),
  body = TLet(
    name = "b",
    t = TId(id = "getB") @ "getB",
    ty = TAuto(),
    effects = TAuto(),
    usage = TAuto(),
    body = TRedex(
      c = TId(id = "plus"),
      elims = List(ETerm(v = TId(id = "a") @ "a"), ETerm(v = TId(id = "b") @ "b"))
    ) @ "plus a b"
  ) @ """let b = getB
plus a b"""
) @ """let a =
  let a1 = getA1
  let a2 = getA2
  plus a1 a2
let b = getB
plus a b"""