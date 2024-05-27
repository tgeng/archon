Let(
  t = Def(qn = qn"__unresolved__.getA") @ "getA",
  ty = Auto() @ """let a = getA
let b = getB
plus a b""",
  eff = Auto(),
  usage = Collapse(
    cTm = Return(v = Auto(), usage = Auto() @ "ε") @ """let a = getA
let b = getB
plus a b"""
  ) @ "ε",
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
            elims = List(ETerm(v = Var(idx = 0) @ "ε"))
          ) @ "plus a"
        ) @ "ε",
        elims = List(ETerm(v = Var(idx = 0)))
      ) @ "plus a b"
    ) @ "ε"
  ) @ """let b = getB
plus a b"""
) @ """let a = getA
let b = getB
plus a b"""