Let(
  t = Let(
    t = Def(qn = qn"__unresolved__.getA1") @ "getA1",
    tBinding = Binding(
      ty = Auto() @ """let a1 = getA1
        let a2 = getA2
        plus a1 a2""",
      usage = Auto()
    ) @ "a1",
    eff = Auto(),
    body = Let(
      t = Def(qn = qn"__unresolved__.getA2") @ "getA2",
      tBinding = Binding(
        ty = Auto() @ """let a2 = getA2
        plus a1 a2""",
        usage = Auto()
      ) @ "a2",
      eff = Auto(),
      body = Redex(
        t = Def(qn = qn"__unresolved__.plus") @ "plus",
        elims = List(ETerm(v = Var(idx = 1) @ "a1"), ETerm(v = Var(idx = 0) @ "a2"))
      ) @ "plus a1 a2"
    ) @ """let a2 = getA2
        plus a1 a2"""
  ) @ """let a1 = getA1
        let a2 = getA2
        plus a1 a2""",
  tBinding = Binding(
    ty = Auto() @ """let a = let a1 = getA1
        let a2 = getA2
        plus a1 a2
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
) @ """let a = let a1 = getA1
        let a2 = getA2
        plus a1 a2
let b = getB
plus a b"""