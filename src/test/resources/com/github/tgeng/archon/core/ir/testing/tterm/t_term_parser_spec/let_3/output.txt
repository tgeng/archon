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
      body = TApp(
        f = TApp(f = TId(id = "plus") @ "plus", arg = TId(id = "a1") @ "a1") @ "plus a1",
        arg = TId(id = "a2") @ "a2"
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
    body = TApp(
      f = TApp(f = TId(id = "plus"), arg = TId(id = "a") @ "a") @ "plus a",
      arg = TId(id = "b") @ "b"
    ) @ "plus a b"
  ) @ """let b = getB
plus a b"""
) @ """let a = let a1 = getA1
        let a2 = getA2
        plus a1 a2
let b = getB
plus a b"""