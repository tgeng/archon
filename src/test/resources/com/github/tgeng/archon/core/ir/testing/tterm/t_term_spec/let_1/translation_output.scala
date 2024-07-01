Let(
  t = Def(qn = qn"__unresolved__.getA") @ "getA",
  tBinding = Binding(
    ty = Auto() @ """let a = getA
let b = getB
plus a b""",
    usage = Auto()
  ) @ "a",
  eff = Auto(),
  body = Let(
    t = Def(qn = qn"__unresolved__.getB") @ "getB",
    tBinding = Binding(
      ty = Auto() @ """let b = getB
plus a b""",
      usage = Auto()
    ) @ "b",
    eff = Auto(),
    body = Redex(
      t = Def(qn = qn"__unresolved__.plus") @ "plus",
      elims = List(ETerm(v = Var(idx = 1) @ "a"), ETerm(v = Var(idx = 0) @ "b"))
    ) @ "plus a b"
  ) @ """let b = getB
plus a b"""
) @ """let a = getA
let b = getB
plus a b"""