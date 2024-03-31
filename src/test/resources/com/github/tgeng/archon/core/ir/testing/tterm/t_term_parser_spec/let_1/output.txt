TLet(
  name = "a",
  t = TId(id = "getA") @ "getA",
  ty = TAuto() @ """let a = getA
let b = getB
plus a b""",
  effects = TAuto(),
  usage = TAuto(),
  body = TLet(
    name = "b",
    t = TId(id = "getB") @ "getB",
    ty = TAuto(),
    effects = TAuto(),
    usage = TAuto(),
    body = TApp(
      f = TApp(f = TId(id = "plus") @ "plus", arg = TId(id = "a") @ "a") @ "plus a",
      arg = TId(id = "b") @ "b"
    ) @ "plus a b"
  ) @ """let b = getB
plus a b"""
) @ """let a = getA
let b = getB
plus a b"""