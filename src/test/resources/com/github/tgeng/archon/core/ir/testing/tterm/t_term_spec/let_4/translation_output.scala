Let(
  t = Let(
    t = Def(qn = qn"__unresolved__.getA1") @ "getA1",
    ty = Auto() @ """let a1 = getA1
  let a2 = getA2
  plus a1 a2""",
    eff = Auto(),
    usage = Collapse(
      cTm = Return(v = Auto(), usage = Auto() @ "ε") @ """let a1 = getA1
  let a2 = getA2
  plus a1 a2"""
    ) @ "ε",
    body = Let(
      t = Def(qn = qn"__unresolved__.getA2") @ "getA2",
      ty = Auto() @ """let a2 = getA2
  plus a1 a2""",
      eff = Auto(),
      usage = Collapse(
        cTm = Return(v = Auto(), usage = Auto()) @ """let a2 = getA2
  plus a1 a2"""
      ),
      body = Let(
        t = Return(v = Var(idx = 0) @ "a2", usage = Auto()) @ "a2",
        ty = Auto(),
        eff = Auto(),
        usage = Auto(),
        body = Redex(
          t = Let(
            t = Return(v = Var(idx = 2) @ "a1", usage = Auto()) @ "a1",
            ty = Auto(),
            eff = Auto(),
            usage = Auto(),
            body = Redex(
              t = Def(qn = qn"__unresolved__.plus") @ "plus",
              elims = List(ETerm(v = Var(idx = 0) @ "ε"))
            ) @ "plus a1"
          ) @ "ε",
          elims = List(ETerm(v = Var(idx = 0)))
        ) @ "plus a1 a2"
      ) @ "ε"
    ) @ """let a2 = getA2
  plus a1 a2"""
  ) @ """let a1 = getA1
  let a2 = getA2
  plus a1 a2""",
  ty = Auto() @ """let a =
  let a1 = getA1
  let a2 = getA2
  plus a1 a2
let b = getB
plus a b""",
  eff = Auto(),
  usage = Collapse(
    cTm = Return(v = Auto(), usage = Auto()) @ """let a =
  let a1 = getA1
  let a2 = getA2
  plus a1 a2
let b = getB
plus a b"""
  ),
  body = Let(
    t = Def(qn = qn"__unresolved__.getB") @ "getB",
    ty = Auto() @ """let b = getB
plus a b""",
    eff = Auto(),
    usage = Collapse(
      cTm = Return(v = Auto(), usage = Auto()) @ """let b = getB
plus a b"""
    ),
    body = Let(
      t = Return(v = Var(idx = 0) @ "b", usage = Auto()) @ "b",
      ty = Auto(),
      eff = Auto(),
      usage = Auto(),
      body = Redex(
        t = Let(
          t = Return(v = Var(idx = 2) @ "a", usage = Auto()) @ "a",
          ty = Auto(),
          eff = Auto(),
          usage = Auto(),
          body = Redex(
            t = Def(qn = qn"__unresolved__.plus") @ "plus",
            elims = List(ETerm(v = Var(idx = 0)))
          ) @ "plus a"
        ),
        elims = List(ETerm(v = Var(idx = 0)))
      ) @ "plus a b"
    )
  ) @ """let b = getB
plus a b"""
) @ """let a =
  let a1 = getA1
  let a2 = getA2
  plus a1 a2
let b = getB
plus a b"""