TLet(
  name = "a",
  t = TId(id = "getA") @ "getA",
  ty = TId(id = "A") @ "A",
  effects = TId(id = "effA") @ "effA",
  usage = TId(id = "uA") @ "uA",
  body = TLet(
    name = "b",
    t = TId(id = "getB") @ "getB",
    ty = TId(id = "B") @ "B",
    effects = TId(id = "effB") @ "effB",
    usage = TId(id = "uB") @ "uB",
    body = TRedex(
      c = TId(id = "plus") @ "plus",
      elims = List(ETerm(v = TId(id = "a") @ "a"), ETerm(v = TId(id = "b") @ "b"))
    ) @ "plus a b"
  ) @ """let b: <effB> [uB] B = getB
plus a b"""
) @ """let a: <effA> [uA] A = getA
let b: <effB> [uB] B = getB
plus a b"""