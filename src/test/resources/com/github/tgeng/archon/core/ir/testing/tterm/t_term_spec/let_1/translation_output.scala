Let(
  t = Let(
    t = Def(qn = qn"__unresolved__.getA") @ "getA",
    ty = Auto() @ """let a = getA
let b = getB
plus a b""",
    eff = Auto(),
    usage = Auto(),
    body = Let(
      t = Let(
        t = Def(qn = qn"__unresolved__.getB") @ "getB",
        ty = Auto() @ """let b = getB
plus a b""",
        eff = Auto(),
        usage = Auto(),
        body = Let(
          t = Redex(
            t = Let(
              t = Redex(
                t = Def(qn = qn"__unresolved__.plus") @ "plus",
                elims = List(ETerm(v = Var(idx = 5) @ "a"))
              ) @ "plus a",
              ty = Auto() @ "ε",
              eff = Auto(),
              usage = Auto(),
              body = Return(v = Var(idx = 0) @ "ε", usage = Auto()) @ "ε"
            ) @ "ε",
            elims = List(ETerm(v = Var(idx = 0) @ "b"))
          ) @ "plus a b",
          ty = Auto(),
          eff = Auto(),
          usage = Auto(),
          body = Return(v = Var(idx = 0), usage = Auto())
        ) @ "ε"
      ) @ """let b = getB
plus a b""",
      ty = Auto(),
      eff = Auto(),
      usage = Auto(),
      body = Return(v = Var(idx = 0), usage = Auto())
    ) @ "ε"
  ) @ """let a = getA
let b = getB
plus a b""",
  ty = Auto(),
  eff = Auto(),
  usage = Auto(),
  body = Return(v = Var(idx = 0), usage = Auto())
) @ "ε"